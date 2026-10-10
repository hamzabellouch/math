import Mathlib
import OAI.Probability.IsingPerceptron.GaussianFamilyGenerator

namespace OAI

/-! Finite Gaussian Variation. -/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

structure AffineGaussianStep (I : Set ℝ) where
  a : ℝ
  v : ℝ
  d : ℝ
  m : ℝ
  hd : 0 ≤ d
  hm : 0 < m
  hs : ∀ t ∈ I, m ≤ a+v*t

def gaussianFamilyFold {I : Set ℝ} (hI : IsOpen I) (F : GaussianFamily I) :
    List (AffineGaussianStep I) → GaussianFamily I
  | [] => F
  | s::L => (gaussianFamilyFold hI F L).transform hI s.a s.v s.hd s.hm s.hs

def boundarySlope {I : Set ℝ} : List (AffineGaussianStep I) → ℝ
  | [] => 0
  | s::L => boundarySlope L-s.v

def boundaryCoefficient {I : Set ℝ} : List (AffineGaussianStep I) → ℝ
  | [] => 1
  | s::_ => s.d

def variationWeights {I : Set ℝ} : (L : List (AffineGaussianStep I)) → Fin L.length → ℝ
  | [] => fun i => Fin.elim0 i
  | s::L => Fin.cons ((boundaryCoefficient L-s.d)*boundarySlope L) (variationWeights L)

 
def gaussianFoldCertificate {I : Set ℝ} (hI : IsOpen I) (F : GaussianFamily I)
    (hT : ∀ p, F.T p=0) : (L : List (AffineGaussianStep I)) →
    VariationCertificate (gaussianFamilyFold hI F L) L.length (boundarySlope L)
      (boundaryCoefficient L) (variationWeights L)
  | [] => VariationCertificate.empty hT 1
  | s::L => (gaussianFoldCertificate hI F hT L).prepend hI s.a s.v s.hd s.hm s.hs

lemma boundarySlope_eq_neg_sum {I : Set ℝ} (L : List (AffineGaussianStep I)) :
    boundarySlope L = -(L.map AffineGaussianStep.v).sum := by
  induction L with
  | nil => simp [boundarySlope]
  | cons s L ih => simp only [boundarySlope,List.map_cons,List.sum_cons,ih]; ring

lemma gaussianFamilyFold_value {I : Set ℝ} (hI : IsOpen I) (F : GaussianFamily I)
    (L : List (AffineGaussianStep I)) (t x : ℝ) :
    (gaussianFamilyFold hI F L).U (t,x) =
      L.foldr (fun s U => gaussianTransform (s.a+s.v*t) s.d U) (fun y => F.U (t,y)) x := by
  induction L generalizing x with
  | nil => rfl
  | cons s L ih =>
    change gaussianTransform (s.a+s.v*t) s.d (fun y => (gaussianFamilyFold hI F L).U (t,y)) x = _
    simp only [List.foldr_cons,ih]

lemma GaussianFamily.time_derivative {I : Set ℝ} (F : GaussianFamily I) (x : ℝ) {t : ℝ}
    (ht : t ∈ I) : HasDerivAt (fun a => F.U (a,x)) (F.T (t,x)) t := by
  have hd := (F.derivative (t,x) ht).comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  convert hd using 1 <;> try rfl
  simp [pairLinear]

lemma VariationCertificate.time_nonpos {I : Set ℝ} {F : GaussianFamily I} {n : ℕ} {e : ℝ}
    {w : Fin n → ℝ} (V : VariationCertificate F n 0 e w) (hw : FinTailNonneg w)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) : F.T p ≤ 0 := by
  have h := V.formula p hp
  simp only [zero_div,zero_mul,add_zero] at h
  rw [h]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (finite_tail_pairing_nonneg w (fun i => V.c i p) hw (fun i => V.nonneg i p) (V.monotone p))

 

theorem gaussianFold_decreases {I : Set ℝ} (hI : IsOpen I) (F : GaussianFamily I)
    (hT : ∀ p, F.T p=0) (L : List (AffineGaussianStep I))
    (hsum : (L.map AffineGaussianStep.v).sum = 0) (hw : FinTailNonneg (variationWeights L))
    {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁) (hseg : Set.Icc t₀ t₁ ⊆ I) (x : ℝ) :
    L.foldr (fun s U => gaussianTransform (s.a+s.v*t₁) s.d U) (fun y => F.U (t₁,y)) x ≤
      L.foldr (fun s U => gaussianTransform (s.a+s.v*t₀) s.d U) (fun y => F.U (t₀,y)) x := by
  let G := gaussianFamilyFold hI F L
  have hb : boundarySlope L = 0 := by rw [boundarySlope_eq_neg_sum,hsum,neg_zero]
  have V : VariationCertificate G L.length 0 (boundaryCoefficient L) (variationWeights L) := by
    rw [← hb]
    exact gaussianFoldCertificate hI F hT L
  have hd : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt (fun a => G.U (a,x)) (G.T (t,x)) t :=
    fun t ht => G.time_derivative x (hseg ht)
  have hm : AntitoneOn (fun t => G.U (t,x)) (Set.Icc t₀ t₁) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => V.time_nonpos hw (hseg (interior_subset ht)))
  have h := hm (show t₀ ∈ Set.Icc t₀ t₁ from ⟨le_rfl,hle⟩)
    (show t₁ ∈ Set.Icc t₀ t₁ from ⟨hle,le_rfl⟩) hle
  simpa only [G,gaussianFamilyFold_value] using h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def affineVarianceFloor {n : ℕ} (a b : Fin n → ℝ) (i : Fin n) : ℝ := min (a i) (b i)/2

def affineVarianceDomain {n : ℕ} (a b : Fin n → ℝ) : Set ℝ :=
  {t | ∀ i, affineVarianceFloor a b i < a i+(b i-a i)*t}

lemma affineVarianceDomain_open {n : ℕ} (a b : Fin n → ℝ) :
    IsOpen (affineVarianceDomain a b) := by
  simp only [affineVarianceDomain,Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (by fun_prop))

lemma affineVarianceFloor_pos {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (i : Fin n) :
    0 < affineVarianceFloor a b i := div_pos (lt_min (ha i) (hb i)) (by norm_num)

lemma affineVarianceDomain_segment {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) : Icc (0:ℝ) 1 ⊆ affineVarianceDomain a b := by
  intro t ht i
  have hlo := min_le_left (a i) (b i)
  have hhi := min_le_right (a i) (b i)
  have hp := lt_min (ha i) (hb i)
  have h1 := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr ht.2)
  have h2 := mul_nonneg (sub_nonneg.mpr hhi) ht.1
  unfold affineVarianceFloor
  nlinarith

def finiteAffineStep {n : ℕ} (a b d : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 ≤ d i) (i : Fin n) :
    AffineGaussianStep (affineVarianceDomain a b) where
  a := a i
  v := b i-a i
  d := d i
  m := affineVarianceFloor a b i
  hd := hd i
  hm := affineVarianceFloor_pos ha hb i
  hs := fun _ ht => (ht i).le

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {I : Set ℝ}

def variationWeightAt (L : List (AffineGaussianStep I)) (i : ℕ) : ℝ :=
  if hi : i < L.length then variationWeights L ⟨i,hi⟩ else 0

lemma variationWeightAt_zero (s : AffineGaussianStep I) (L : List (AffineGaussianStep I)) :
    variationWeightAt (s::L) 0 = (boundaryCoefficient L-s.d)*boundarySlope L := by
  simp [variationWeightAt,variationWeights]

lemma variationWeightAt_succ (s : AffineGaussianStep I) (L : List (AffineGaussianStep I)) (i : ℕ) :
    variationWeightAt (s::L) (i+1) = variationWeightAt L i := by
  by_cases hi : i < L.length
  · simp only [variationWeightAt,List.length_cons,Nat.add_lt_add_iff_right,hi,dite_eq_left,
      variationWeights]
    rfl
  · simp [variationWeightAt,hi]

def ofFnWeights {n : ℕ} (s : Fin n → AffineGaussianStep I) (i : Fin n) : ℝ :=
  variationWeightAt (List.ofFn s) i.val

def afterCoefficient {n : ℕ} (s : Fin n → AffineGaussianStep I) (i : Fin n) : ℝ :=
  if h : i.val+1 < n then (s ⟨i.val+1,h⟩).d else 1

lemma boundarySlope_ofFn {n : ℕ} (s : Fin n → AffineGaussianStep I) :
    boundarySlope (List.ofFn s) = -∑ i, (s i).v := by
  rw [boundarySlope_eq_neg_sum,List.map_ofFn,List.sum_ofFn]
  rfl

lemma ofFnWeights_zero {n : ℕ} (s : Fin (n+1) → AffineGaussianStep I) :
    ofFnWeights s 0 = (afterCoefficient s 0-(s 0).d)*(-∑ i : Fin n, (s i.succ).v) := by
  unfold ofFnWeights
  simp only [List.ofFn_succ]
  simp only [Fin.val_zero,variationWeightAt_zero,boundarySlope_ofFn]
  congr 1
  cases n with
  | zero => simp [boundaryCoefficient,afterCoefficient]
  | succ n => simp [List.ofFn_succ,boundaryCoefficient,afterCoefficient]

lemma ofFnWeights_succ {n : ℕ} (s : Fin (n+1) → AffineGaussianStep I) (i : Fin n) :
    ofFnWeights s i.succ = ofFnWeights (fun j : Fin n => s j.succ) i := by
  unfold ofFnWeights
  simp only [List.ofFn_succ,Fin.val_succ,variationWeightAt_succ]

lemma afterCoefficient_succ {n : ℕ} (s : Fin (n+1) → AffineGaussianStep I) (i : Fin n) :
    afterCoefficient s i.succ = afterCoefficient (fun j : Fin n => s j.succ) i := by
  unfold afterCoefficient
  simp only [Fin.val_succ,Nat.add_lt_add_iff_right]
  split <;> rfl

lemma ofFnWeights_eq {n : ℕ} (s : Fin n → AffineGaussianStep I) (i : Fin n) :
    ofFnWeights s i = (afterCoefficient s i-(s i).d)*
      (-∑ j : Fin n, if i < j then (s j).v else 0) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [ofFnWeights_zero,Fin.sum_univ_succ]
      simp
    · rw [ofFnWeights_succ,ih,afterCoefficient_succ,Fin.sum_univ_succ]
      simp only [Fin.not_lt_zero,ite_false,Fin.succ_lt_succ_iff,zero_add]

lemma FinTailNonneg_ofFnWeights {n : ℕ} (s : Fin n → AffineGaussianStep I)
    (h : FinTailNonneg (ofFnWeights s)) : FinTailNonneg (variationWeights (List.ofFn s)) := by
  have hn : (List.ofFn s).length = n := List.length_ofFn
  intro j
  have he : (∑ i : Fin (List.ofFn s).length, if j ≤ i then variationWeights (List.ofFn s) i else 0) =
      ∑ i : Fin n, if Fin.cast hn j ≤ i then ofFnWeights s i else 0 := by
    apply Fintype.sum_equiv (finCongr hn)
    intro i
    simp only [finCongr_apply,Fin.le_iff_val_le_val,Fin.val_cast,ofFnWeights,variationWeightAt]
    simp only [i.isLt,dite_eq_left]
  rw [he]
  exact h (Fin.cast hn j)

end IsingPerceptron

 

 

open scoped BigOperators
namespace IsingPerceptron

lemma finite_delta_sum (v : ℕ → ℝ) (n : ℕ) :
    (∑ i : Fin n, (v (i.val+1)-v i.val)) = v n-v 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    ring

lemma finite_tail_delta_sum (v : ℕ → ℝ) (n i : ℕ) (hi : i < n) :
    (∑ j : Fin n, if i < j.val then (v (j.val+1)-v j.val) else 0) = v n-v (i+1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    by_cases h : i < n
    · rw [ite_eq_left h,ih h]
      ring
    · have he : i=n := by omega
      subst i
      simp only [lt_self_iff_false,ite_false,add_zero,sub_self]
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (by omega)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma continuous_gaussianTransform_param {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2)) (hs : Continuous s)
    (hx : Continuous x) {K : ℝ} (hK : ∀ t y, |U t y| ≤ K) (d : ℝ) :
    Continuous (fun t => gaussianTransform (s t) d (U t) (x t)) := by
  let A := fun t z => U t (x t+Real.sqrt (s t)*z)
  have hA : Continuous (fun p : E × ℝ => A p.1 p.2) := by
    exact hU.comp (continuous_fst.prodMk ((hx.comp continuous_fst).add
      (((Real.continuous_sqrt.comp hs).comp continuous_fst).mul continuous_snd)))
  have hm (t : E) : Measurable (A t) :=
    (hA.comp (continuous_const.prodMk continuous_id)).measurable
  have hc (z : ℝ) : Continuous (fun t => A t z) :=
    hA.comp (continuous_id.prodMk continuous_const)
  by_cases hz : d=0
  · subst d
    simp only [gaussianTransform,ite_true]
    apply continuous_iff_continuousAt.mpr
    intro t
    exact tendsto_integral_filter_of_dominated_convergence (fun _ => K)
      (Eventually.of_forall (fun t => (hm t).aestronglyMeasurable))
      (Eventually.of_forall (fun t => ae_of_all _ (fun z => by
        simpa only [Real.norm_eq_abs] using hK t (x t+Real.sqrt (s t)*z))))
      (integrable_const _) (ae_of_all _ (fun z => (hc z).continuousAt))
  · have hZ : Continuous (fun t => ∫ z, Real.exp (d*A t z) ∂gaussianReal 0 1) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      apply tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp (|d| * K))
      · exact Eventually.of_forall (fun t => ((measurable_const.mul (hm t)).exp).aestronglyMeasurable)
      · apply Eventually.of_forall
        intro t
        apply ae_of_all
        intro z
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          d*A t z ≤ |d*A t z| := le_abs_self _
          _ = |d| * |A t z| := abs_mul _ _
          _ ≤ |d| * K := mul_le_mul_of_nonneg_left (hK t _) (abs_nonneg _)
      · exact integrable_const _
      · exact ae_of_all _ (fun z => (Real.continuous_exp.comp (continuous_const.mul (hc z))).continuousAt)
    have hp (t : E) : 0 < ∫ z, Real.exp (d*A t z) ∂gaussianReal 0 1 :=
      integral_pos_exp_of_bound (gaussianReal 0 1) (hm t) (fun z => hK t _) d
    simp only [gaussianTransform,hz,ite_false]
    exact (hZ.log (fun t => ne_of_gt (hp t))).div_const d

 

lemma continuous_gaussianFold_param {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List ((E → ℝ) × ℝ))
    (hs : ∀ sd ∈ L, Continuous sd.1) (hd : ∀ sd ∈ L, 0 ≤ sd.2)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ y, |f y| ≤ K) :
    Continuous (fun p : E × ℝ =>
      L.foldr (fun sd U => gaussianTransform (sd.1 p.1) sd.2 U) f p.2) ∧
    ∀ t y, |L.foldr (fun sd U => gaussianTransform (sd.1 t) sd.2 U) f y| ≤ K := by
  induction L with
  | nil => exact ⟨hf.comp continuous_snd,fun t y => hK y⟩
  | cons sd L ih =>
    obtain ⟨hc,hb⟩ := ih (fun e he => hs e (List.mem_cons_of_mem _ he))
      (fun e he => hd e (List.mem_cons_of_mem _ he))
    constructor
    · simp only [List.foldr_cons]
      apply continuous_gaussianTransform_param (K := K)
      · exact hc.comp (continuous_fst.fst.prodMk continuous_snd)
      · exact (hs sd (List.mem_cons_self)).comp continuous_fst
      · exact continuous_snd
      · exact fun p y => hb p.1 y
    · intro t y
      exact gaussianTransform_abs_le
        (hc.comp (continuous_const.prodMk continuous_id)).measurable
        (hb t) _ (hd sd List.mem_cons_self) y

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

structure BoundedC2Data (f : ℝ → ℝ) where
  df : ℝ → ℝ
  ddf : ℝ → ℝ
  K : ℝ
  C : ℝ
  D : ℝ
  mf : Measurable f
  mdf : Measurable df
  mddf : Measurable ddf
  bf : ∀ x, |f x| ≤ K
  bdf : ∀ x, |df x| ≤ C
  bddf : ∀ x, |ddf x| ≤ D
  der : ∀ x, HasDerivAt f (df x) x
  derdf : ∀ x, HasDerivAt df (ddf x) x

def BoundedC2Data.family {f : ℝ → ℝ} (F : BoundedC2Data f) (I : Set ℝ) : GaussianFamily I :=
  GaussianFamily.terminal F.mf F.mdf F.mddf F.bf F.bdf F.bddf F.der F.derdf

lemma BoundedC2Data.continuous {f : ℝ → ℝ} (F : BoundedC2Data f) : Continuous f :=
  continuous_iff_continuousAt.mpr (fun x => (F.der x).continuousAt)

def nodalGaussianFold {n : ℕ} (q : ℕ → ℝ) (d : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (List.ofFn (fun i : Fin n => (q (i.val+1)-q i.val,d i))).foldr
    (fun sd U => gaussianTransform sd.1 sd.2 U) f x

def nextCoefficient {n : ℕ} (d : Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : i.val+1 < n then d ⟨i.val+1,h⟩ else 1

 

theorem nodalGaussianFold_antitone_strict {n : ℕ} (a b : ℕ → ℝ) (d : Fin n → ℝ)
    (ha : ∀ i : Fin n, a i.val < a (i.val+1))
    (hb : ∀ i : Fin n, b i.val < b (i.val+1)) (hd : ∀ i, 0 ≤ d i)
    (hfirst : a 0=b 0) (hlast : a n=b n)
    (hweight : FinTailNonneg (fun i => (nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))))
    {f : ℝ → ℝ} (F : BoundedC2Data f) (x : ℝ) :
    nodalGaussianFold b d f x ≤ nodalGaussianFold a d f x := by
  let A : Fin n → ℝ := fun i => a (i.val+1)-a i.val
  let B : Fin n → ℝ := fun i => b (i.val+1)-b i.val
  have hA : ∀ i, 0 < A i := fun i => sub_pos.mpr (ha i)
  have hB : ∀ i, 0 < B i := fun i => sub_pos.mpr (hb i)
  let s := finiteAffineStep A B d hA hB hd
  let v : ℕ → ℝ := fun i => b i-a i
  have hs (i : Fin n) : (s i).v = v (i.val+1)-v i.val := by
    dsimp [s,finiteAffineStep,v,A,B]
    ring
  have hv0 : v 0=0 := by simp [v,hfirst]
  have hvn : v n=0 := by simp [v,hlast]
  have hsum : ((List.ofFn s).map AffineGaussianStep.v).sum=0 := by
    rw [List.map_ofFn,List.sum_ofFn]
    simp only [Function.comp_apply,hs,finite_delta_sum,hv0,hvn,sub_self]
  have hw : FinTailNonneg (variationWeights (List.ofFn s)) := by
    apply FinTailNonneg_ofFnWeights
    have he : ofFnWeights s = fun i => (nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1)) := by
      funext i
      rw [ofFnWeights_eq]
      simp only [hs,Fin.lt_def,finite_tail_delta_sum v n i.val i.isLt,hvn,zero_sub,neg_neg]
      rfl
    rw [he]
    exact hweight
  have hh := gaussianFold_decreases (affineVarianceDomain_open A B)
    (F.family (affineVarianceDomain A B)) (fun _ => rfl) (List.ofFn s) hsum hw
    (t₀ := 0) (t₁ := 1) (by norm_num) (affineVarianceDomain_segment hA hB) x
  simp only [BoundedC2Data.family,GaussianFamily.terminal] at hh
  have he (t : ℝ) : (List.ofFn s).foldr
      (fun e U => gaussianTransform (e.a+e.v*t) e.d U) f x =
      (List.ofFn (fun i : Fin n => (A i+(B i-A i)*t,d i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) f x := by
    have hm : List.ofFn (fun i : Fin n => (A i+(B i-A i)*t,d i)) =
        (List.ofFn s).map (fun e => (e.a+e.v*t,e.d)) := by
      rw [List.map_ofFn]
      rfl
    rw [hm,List.foldr_map]
  rw [he,he] at hh
  simpa only [mul_one,mul_zero,add_zero,add_sub_cancel,A,B,nodalGaussianFold] using hh

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma continuous_nodalGaussianFold_param {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {n : ℕ} (q : E → ℕ → ℝ) (d : Fin n → ℝ)
    (hq : ∀ i, Continuous (fun t => q t i)) (hd : ∀ i, 0 ≤ d i)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ y, |f y| ≤ K) (x : ℝ) :
    Continuous (fun t => nodalGaussianFold (q t) d f x) := by
  let L := List.ofFn (fun i : Fin n => ((fun t => q t (i.val+1)-q t i.val),d i))
  have hs : ∀ sd ∈ L, Continuous sd.1 := by
    intro sd hsd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hsd
    exact (hq _).sub (hq _)
  have hds : ∀ sd ∈ L, 0 ≤ sd.2 := by
    intro sd hsd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hsd
    exact hd i
  have hc := (continuous_gaussianFold_param L hs hds hf hK).1.comp
    (continuous_id.prodMk (continuous_const (y := x)))
  convert hc using 1
  funext t
  unfold nodalGaussianFold
  dsimp only [Function.comp_def,Prod.fst,Prod.snd]
  change (List.ofFn (fun i : Fin n => (q t (i.val+1)-q t i.val,d i))).foldr _ f x = _
  have he : List.ofFn (fun i : Fin n => (q t (i.val+1)-q t i.val,d i)) =
      L.map (fun sd => (sd.1 t,sd.2)) := by
    dsimp only [L]
    rw [List.map_ofFn]
    rfl
  rw [he,List.foldr_map]
  rfl

 

theorem nodalGaussianFold_antitone {n : ℕ} (a b : ℕ → ℝ) (d : Fin n → ℝ)
    (ha : ∀ i : Fin n, a i.val ≤ a (i.val+1))
    (hb : ∀ i : Fin n, b i.val ≤ b (i.val+1)) (hd : ∀ i, 0 ≤ d i)
    (hfirst : a 0=b 0) (hlast : a n=b n)
    (hweight : FinTailNonneg (fun i => (nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))))
    {f : ℝ → ℝ} (F : BoundedC2Data f) (x : ℝ) :
    nodalGaussianFold b d f x ≤ nodalGaussianFold a d f x := by
  let ar := fun ε i => a i+ε*(i:ℝ)
  let br := fun ε i => b i+ε*(i:ℝ)
  have har : Continuous (fun ε : ℝ => nodalGaussianFold (ar ε) d f x) :=
    continuous_nodalGaussianFold_param ar d (fun i => by fun_prop) hd F.continuous F.bf x
  have hbr : Continuous (fun ε : ℝ => nodalGaussianFold (br ε) d f x) :=
    continuous_nodalGaussianFold_param br d (fun i => by fun_prop) hd F.continuous F.bf x
  have he (ε : ℝ) (hε : 0 < ε) :
      nodalGaussianFold (br ε) d f x ≤ nodalGaussianFold (ar ε) d f x := by
    apply nodalGaussianFold_antitone_strict (ar ε) (br ε) d
    · intro i
      dsimp [ar]
      push_cast
      have := ha i
      nlinarith
    · intro i
      dsimp [br]
      push_cast
      have := hb i
      nlinarith
    · exact hd
    · simp only [ar,br,hfirst]
    · simp only [ar,br,hlast]
    · have hw : (fun i : Fin n => (nextCoefficient d i-d i)*(br ε (i.val+1)-ar ε (i.val+1))) =
          (fun i : Fin n => (nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))) := by
        funext i
        dsimp [ar,br]
        ring
      rw [hw]
      exact hweight
    · exact F
  have hb0 : Tendsto (fun ε => nodalGaussianFold (br ε) d f x) (𝓝[>] (0:ℝ))
      (𝓝 (nodalGaussianFold (br 0) d f x)) := hbr.continuousAt.tendsto.mono_left inf_le_left
  have ha0 : Tendsto (fun ε => nodalGaussianFold (ar ε) d f x) (𝓝[>] (0:ℝ))
      (𝓝 (nodalGaussianFold (ar 0) d f x)) := har.continuousAt.tendsto.mono_left inf_le_left
  have hle : ∀ᶠ ε in 𝓝[>] (0:ℝ), nodalGaussianFold (br ε) d f x ≤ nodalGaussianFold (ar ε) d f x := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact he ε hε
  simpa only [ar,br,zero_mul,add_zero] using le_of_tendsto_of_tendsto hb0 ha0 hle

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def uniformNodal (q : ℕ → ℝ) (n j : ℕ) : ℝ :=
  if j=0 then 0 else if j ≤ n+1 then q (j-1) else 1

def uniformCoefficient (n : ℕ) (i : Fin (n+2)) : ℝ := (i.val:ℝ)/(n+1:ℕ)

lemma uniformNodal_zero (q : ℕ → ℝ) (n : ℕ) : uniformNodal q n 0=0 := by
  simp [uniformNodal]

lemma uniformNodal_last (q : ℕ → ℝ) (n : ℕ) : uniformNodal q n (n+2)=1 := by
  simp [uniformNodal]

lemma uniformNodal_value (q : ℕ → ℝ) (n i : ℕ) (hi : i < n+1) :
    uniformNodal q n (i+1)=q i := by
  simp [uniformNodal,show i+1 ≤ n+1 by omega]

lemma uniformNodal_increasing {q : ℕ → ℝ} (n : ℕ) (hq : Monotone q)
    (hb : ∀ i, q i ∈ Icc (0:ℝ) 1) (i : Fin (n+2)) :
    uniformNodal q n i.val ≤ uniformNodal q n (i.val+1) := by
  by_cases hi : i.val=0
  · simp only [hi,uniformNodal_zero,zero_add,uniformNodal_value q n 0 (by omega)]
    exact (hb 0).1
  · by_cases hj : i.val < n+1
    · rw [uniformNodal_value q n i.val hj]
      simp only [uniformNodal,hi,ite_false,show i.val ≤ n+1 by omega,ite_true]
      exact hq (Nat.sub_le _ _)
    · have he : i.val=n+1 := by omega
      rw [he]
      change uniformNodal q n (n+1) ≤ uniformNodal q n (n+2)
      rw [uniformNodal_last,uniformNodal_value q n n (by omega)]
      exact (hb n).2

lemma uniformCoefficient_nonneg (n : ℕ) (i : Fin (n+2)) : 0 ≤ uniformCoefficient n i := by
  unfold uniformCoefficient
  positivity

lemma uniformCoefficient_difference (n : ℕ) (i : Fin (n+1)) :
    nextCoefficient (uniformCoefficient n) i.castSucc-uniformCoefficient n i.castSucc = 1/(n+1:ℕ) := by
  have hi : i.val+1 < n+2 := by omega
  simp only [nextCoefficient,Fin.val_castSucc,hi,dite_eq_left,uniformCoefficient]
  push_cast
  ring

lemma uniformWeight_castSucc (a b : ℕ → ℝ) (n : ℕ) (i : Fin (n+1)) :
    (nextCoefficient (uniformCoefficient n) i.castSucc-uniformCoefficient n i.castSucc)*
      (uniformNodal b n (i.castSucc.val+1)-uniformNodal a n (i.castSucc.val+1)) =
      (1/(n+1:ℕ))*(b i.val-a i.val) := by
  rw [uniformCoefficient_difference]
  simp only [Fin.val_castSucc,uniformNodal_value _ n i.val i.isLt]

lemma uniformWeight_last (a b : ℕ → ℝ) (n : ℕ) :
    (nextCoefficient (uniformCoefficient n) (Fin.last (n+1))-uniformCoefficient n (Fin.last (n+1)))*
      (uniformNodal b n ((Fin.last (n+1)).val+1)-uniformNodal a n ((Fin.last (n+1)).val+1)) = 0 := by
  simp only [Fin.val_last,show n+1+1=n+2 by omega,uniformNodal_last,sub_self,mul_zero]

lemma uniformPattern_eq_nodal (q : OverlapPath) (f : ℝ → ℝ) (n : ℕ) :
    uniformPattern f q n = nodalGaussianFold (uniformNodal (cellAverage q (n+1)) n) (uniformCoefficient n) f 0 := by
  unfold uniformPattern nodalGaussianFold
  apply congrArg (fun L : List (ℝ × ℝ) => L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f 0)
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · by_cases hi : i.val < n+1
    · rw [uniformNodal_value _ n i.val hi]
      simp only [hi,ite_true,uniformNodal]
      by_cases hz : i.val=0
      · simp [hz]
      · simp [hz,show i.val ≤ n+1 by omega,show i.val-1 < n+1 by omega]
    · have he : i.val=n+1 := by omega
      simp only [he,show n+1+1=n+2 by omega,uniformNodal_last]
      simp [uniformNodal]
  · rfl

end IsingPerceptron

end

end OAI
