import Mathlib
import OAI.Probability.SKFluctuations.Diagonal
import OAI.Probability.SKFluctuations.ScalarSourceJet

namespace OAI

/-! Projection. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E]

 theorem ExpNormBounded.const (a : ℝ) : ExpNormBounded (fun _ : E => a) := by
  refine ⟨continuous_const, |a|, 0, abs_nonneg _, le_rfl, ?_⟩
  simp

 theorem ExpNormBounded.neg {f : E → ℝ} (hf : ExpNormBounded f) : ExpNormBounded (fun x => -f x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  exact ⟨hf.1.neg, C,c,hC,hc, fun x => by simpa using hb x⟩

 theorem ExpNormBounded.add {f g : E → ℝ} (hf : ExpNormBounded f) (hg : ExpNormBounded g) :
    ExpNormBounded (fun x => f x + g x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  obtain ⟨D,d,hD,hd,he⟩ := hg.2
  refine ⟨hf.1.add hg.1, C+D,c+d,add_nonneg hC hD,add_nonneg hc hd,fun x => ?_⟩
  have hf' : |f x| ≤ C * Real.exp ((c+d)*‖x‖) := (hb x).trans (by gcongr; nlinarith [norm_nonneg x])
  have hg' : |g x| ≤ D * Real.exp ((c+d)*‖x‖) := (he x).trans (by gcongr; nlinarith [norm_nonneg x])
  calc
    |f x+g x| ≤ |f x|+|g x| := abs_add_le _ _
    _ ≤ C * Real.exp ((c+d)*‖x‖) + D * Real.exp ((c+d)*‖x‖) := add_le_add hf' hg'
    _ = _ := by ring

 theorem ExpNormBounded.sub {f g : E → ℝ} (hf : ExpNormBounded f) (hg : ExpNormBounded g) :
    ExpNormBounded (fun x => f x - g x) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

 theorem ExpNormBounded.mul {f g : E → ℝ} (hf : ExpNormBounded f) (hg : ExpNormBounded g) :
    ExpNormBounded (fun x => f x*g x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  obtain ⟨D,d,hD,hd,he⟩ := hg.2
  refine ⟨hf.1.mul hg.1,C*D,c+d,mul_nonneg hC hD,add_nonneg hc hd,fun x => ?_⟩
  calc
    |f x*g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C*Real.exp (c*‖x‖))*(D*Real.exp (d*‖x‖)) :=
      mul_le_mul (hb x) (he x) (abs_nonneg _) (mul_nonneg hC (Real.exp_nonneg _))
    _ = C*D*Real.exp ((c+d)*‖x‖) := by rw [add_mul,Real.exp_add]; ring

 theorem ExpNormBounded.const_mul {f : E → ℝ} (hf : ExpNormBounded f) (a : ℝ) :
    ExpNormBounded (fun x => a*f x) := (ExpNormBounded.const a).mul hf

 theorem ExpNormBounded.pow {f : E → ℝ} (hf : ExpNormBounded f) (k : ℕ) :
    ExpNormBounded (fun x => f x^k) := by
  induction k with
  | zero => simpa using ExpNormBounded.const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

 theorem ExpNormBounded.integrable {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hf : ExpNormBounded f) (q : ι → ℝ≥0) :
    Integrable f (Measure.pi fun i => gaussianReal 0 (q i)) := by
  simpa only [zero_add,one_smul] using hf.affine_integrable (exponentialIncrement_gaussian q) 0 1

 theorem ExpNormBounded.sum {κ : Type*} (s : Finset κ) {f : κ → E → ℝ}
    (hf : ∀ i ∈ s, ExpNormBounded (f i)) : ExpNormBounded (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ExpNormBounded.const (E := E) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal

 
def gaussianTiltScore (m : ℝ) (F₁ : ℝ → ℝ) (z : ℝ) : ℝ := z-m*F₁ z

 theorem gaussianTiltScore_expBounded (m : ℝ) {F₁ : ℝ → ℝ} (hF₁ : BddSmooth 0 F₁) :
    ExpBounded (gaussianTiltScore m F₁) :=
  ExpBounded.id.sub ((ExpBounded.of_bddSmooth hF₁).const_mul m)

 theorem tiltedMean_expBounded_mono {F A B : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) (hA : ExpBounded A) (hB : ExpBounded B)
    (hAB : ∀ z, A z ≤ B z) :
    tiltedMean (gaussianReal 0 1) m F A ≤ tiltedMean (gaussianReal 0 1) m F B := by
  have hW := ExpBounded.exp_lipschitz hF m
  apply div_le_div_of_nonneg_right _ (partition_pos m hW.integrable).le
  exact integral_mono (hA.mul hW).integrable (hB.mul hW).integrable
    (fun z => mul_le_mul_of_nonneg_right (hAB z) (Real.exp_nonneg _))

 

 theorem tiltedMean_score {F F₁ A A₁ : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hF₁ : BddSmooth 0 F₁)
    (hdF : ∀ z, HasDerivAt F (F₁ z) z)
    (hA : ExpBounded A) (hA₁ : ExpBounded A₁)
    (hdA : ∀ z, HasDerivAt A (A₁ z) z) (m : ℝ) :
    tiltedMean (gaussianReal 0 1) m F (fun z => A z*gaussianTiltScore m F₁ z) =
      tiltedMean (gaussianReal 0 1) m F A₁ := by
  let W := fun z => Real.exp (m*F z)
  have hW : ExpBounded W := ExpBounded.exp_lipschitz hF m
  have hB : ExpBounded (fun z => m*F₁ z) := (ExpBounded.of_bddSmooth hF₁).const_mul m
  have hs := standardGaussian_stein
    (f := fun z => A z*W z)
    (f₁ := fun z => A₁ z*W z + A z*(m*F₁ z)*W z)
    (fun z => ((hdA z).mul ((hdF z).const_mul m |>.exp)).congr_deriv (by dsimp [W]; ring))
    (hA.mul hW).integrable
    ((hA₁.mul hW).add ((hA.mul hB).mul hW)).integrable
    (ExpBounded.id.mul (hA.mul hW)).integrable
  rw [integral_add (hA₁.mul hW).integrable ((hA.mul hB).mul hW).integrable] at hs
  unfold tiltedMean
  congr 1
  calc
    (∫ z, A z*gaussianTiltScore m F₁ z*Real.exp (m*F z) ∂gaussianReal 0 1) =
        (∫ z, z*(A z*W z) - A z*(m*F₁ z)*W z ∂gaussianReal 0 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by dsimp [gaussianTiltScore,W]; ring
    _ = (∫ z, z*(A z*W z) ∂gaussianReal 0 1) -
        (∫ z, A z*(m*F₁ z)*W z ∂gaussianReal 0 1) :=
      integral_sub (ExpBounded.id.mul (hA.mul hW)).integrable ((hA.mul hB).mul hW).integrable
    _ = _ := by rw [hs]; ring

 theorem tiltedMean_score_even_step {F F₁ F₂ : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hF₁ : BddSmooth 0 F₁) (hF₂ : BddSmooth 0 F₂)
    (hdF : ∀ z, HasDerivAt F (F₁ z) z) (hdF₁ : ∀ z, HasDerivAt F₁ (F₂ z) z)
    (hconv : ∀ z, 0 ≤ F₂ z) {m : ℝ} (hm : 0 ≤ m) (k : ℕ) :
    tiltedMean (gaussianReal 0 1) m F (fun z => gaussianTiltScore m F₁ z^(2*k+2)) ≤
      (2*k+1:ℝ) * tiltedMean (gaussianReal 0 1) m F (fun z => gaussianTiltScore m F₁ z^(2*k)) := by
  let S := gaussianTiltScore m F₁
  have hS : ExpBounded S := gaussianTiltScore_expBounded m hF₁
  have hS₁ : ExpBounded (fun z => 1-m*F₂ z) :=
    (ExpBounded.const 1).sub ((ExpBounded.of_bddSmooth hF₂).const_mul m)
  have hdS (z : ℝ) : HasDerivAt S (1-m*F₂ z) z :=
    (hasDerivAt_id z).sub ((hdF₁ z).const_mul m)
  have hA₁ : ExpBounded (fun z => (2*k+1:ℝ)*S z^(2*k)*(1-m*F₂ z)) :=
    ((hS.pow (2*k)).const_mul _).mul hS₁
  have h := tiltedMean_score hF hF₁ hdF (hS.pow (2*k+1)) hA₁ (fun z => by
    convert (hdS z).pow (2*k+1) using 1; first | rfl | simp [Nat.cast_add,Nat.cast_mul]) m
  have heq : (fun z => S z^(2*k+1)*gaussianTiltScore m F₁ z) =
      (fun z => S z^(2*k+2)) := by
        funext z
        change S z^(2*k+1)*S z = S z^((2*k+1)+1)
        exact (pow_succ _ _).symm
  rw [heq] at h
  calc
    _ = tiltedMean (gaussianReal 0 1) m F (fun z => (2*k+1:ℝ)*S z^(2*k)*(1-m*F₂ z)) := h
    _ ≤ tiltedMean (gaussianReal 0 1) m F (fun z => (2*k+1:ℝ)*S z^(2*k)) := by
      apply tiltedMean_expBounded_mono hF m hA₁ ((hS.pow (2*k)).const_mul _)
      intro z
      have hpow : 0 ≤ S z^(2*k) := pow_nonneg (sq_nonneg (S z)) k |>.trans_eq (by rw [← pow_mul])
      have hn : 0 ≤ (2*k+1:ℝ)*S z^(2*k) := mul_nonneg (by positivity) hpow
      nlinarith [mul_nonneg hm (hconv z)]
    _ = _ := by
      simp only [tiltedMean]
      rw [show (fun z => (2*k+1:ℝ)*S z^(2*k)*Real.exp (m*F z)) =
        (fun z => (2*k+1:ℝ)*(S z^(2*k)*Real.exp (m*F z))) by funext z; ring,
        integral_const_mul]
      ring

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal

 
def gaussianEvenConstant : ℕ → ℝ
  | 0 => 1
  | k+1 => (2*k+1:ℝ)*gaussianEvenConstant k

 theorem gaussianEvenConstant_pos (k : ℕ) : 0 < gaussianEvenConstant k := by
  induction k with
  | zero => norm_num [gaussianEvenConstant]
  | succ k ih => exact mul_pos (by positivity) ih

 theorem tiltedMean_score_even_bound {F F₁ F₂ : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hF₁ : BddSmooth 0 F₁) (hF₂ : BddSmooth 0 F₂)
    (hdF : ∀ z, HasDerivAt F (F₁ z) z) (hdF₁ : ∀ z, HasDerivAt F₁ (F₂ z) z)
    (hconv : ∀ z, 0 ≤ F₂ z) {m : ℝ} (hm : 0 ≤ m) (k : ℕ) :
    tiltedMean (gaussianReal 0 1) m F (fun z => gaussianTiltScore m F₁ z^(2*k)) ≤
      gaussianEvenConstant k := by
  induction k with
  | zero =>
    have hn := partition_pos m (ExpBounded.exp_lipschitz hF m).integrable
    simp only [Nat.mul_zero,pow_zero,tiltedMean,one_mul,div_self hn.ne',gaussianEvenConstant,le_refl]
  | succ k ih =>
    have h := tiltedMean_score_even_step hF hF₁ hF₂ hdF hdF₁ hconv hm k
    calc
      _ ≤ (2*k+1:ℝ)*tiltedMean (gaussianReal 0 1) m F (fun z => gaussianTiltScore m F₁ z^(2*k)) := by
        simpa only [Nat.mul_add,Nat.mul_one] using h
      _ ≤ (2*k+1:ℝ)*gaussianEvenConstant k := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := rfl

 

 theorem hierarchy_line_score_bound {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (x v : ι → ℝ) {m : ℝ} (hm : 0 ≤ m) (k : ℕ) :
    tiltedMean (gaussianReal 0 1) m (fun z => gaussianHierarchy w φ steps (x+z • v))
      (fun z => (z-m*gaussianHierarchyMean w φ (fun s => φ s v) steps (x+z • v))^(2*k)) ≤
      gaussianEvenConstant k := by
  let L : ℝ →L[ℝ] (ι → ℝ) := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have he (z : ℝ) : L z = z • v := rfl
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  have hl : LipschitzWith (C*‖L‖₊) (fun z : ℝ => gaussianHierarchy w φ steps (x+z • v)) := by
    have hline : LipschitzWith ‖L‖₊ (fun z : ℝ => x+L z) := by
      apply LipschitzWith.of_dist_le_mul
      intro z t
      simpa only [dist_add_left] using L.lipschitzWith.dist_le_mul z t
    exact hC.comp hline
  have hG := (gaussianHierarchyMean_smooth hw φ (fun s => φ s v) steps ha 0).affine L x
  have hH := (gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v steps ha 0).affine L x
  apply tiltedMean_score_even_bound hl hG hH
    (gaussianHierarchy_hasDerivAt hw φ steps ha x v)
    (gaussianHierarchyMean_hasDerivAt hw φ (fun s => φ s v) steps ha x v) _ hm k
  intro z
  exact gaussianHierarchyHessian_nonneg hw φ steps ha (x+z • v) v

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators

 def vectorDot {ι : Type*} [Fintype ι] (v z : ι → ℝ) : ℝ := ∑ i, v i*z i

 theorem ExpNormBounded.vectorDot {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ExpNormBounded (vectorDot v) := by
  apply ExpNormBounded.sum Finset.univ
  intro i _
  exact (ExpNormBounded.lipschitz (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).lipschitzWith).const_mul (v i)

 theorem standardGaussianVector_directional_stein {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} {D : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hf : ExpNormBounded f) (hD : ∀ i, ExpNormBounded (D i))
    (hd : ∀ i x t, HasDerivAt (fun s : ℝ => f (x+s • Pi.single i 1))
      (D i (x+t • Pi.single i 1)) t) (v : Fin (n+1) → ℝ) :
    (∫ z, vectorDot v z*f z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      ∫ z, ∑ i, v i*D i z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  have hs (i : Fin (n+1)) :
      (∫ z, z i*f z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
        ∫ z, D i z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
    apply standardGaussianVector_stein i _ (hf.integrable (fun _ => 1)) ((hD i).integrable (fun _ => 1))
      (by simpa only [zero_add,one_smul] using hf.affine_coord_integrable (fun _ => 1) 0 1 i)
    intro y t
    have he (s : ℝ) : i.insertNth 0 y+s • Pi.single i 1 = i.insertNth s y := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · obtain ⟨k,rfl⟩ := (Fin.eq_self_or_eq_succAbove i j).resolve_left hj
        simp
    simpa only [he] using hd i (i.insertNth 0 y) t
  simp only [vectorDot,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun i _ =>
    (by simpa only [zero_add,one_smul] using
      (hf.affine_coord_integrable (fun _ => 1) 0 1 i).const_mul (v i)))]
  simp_rw [integral_const_mul,hs]
  rw [integral_finsetSum _ (fun i _ => ((hD i).integrable (fun _ => 1)).const_mul (v i))]
  simp only [integral_const_mul]

 def gaussianVectorScore {ι : Type*} [Fintype ι] (m : ℝ)
    (G : ι → (ι → ℝ) → ℝ) (v z : ι → ℝ) : ℝ :=
  vectorDot v z-m*(∑ i, v i*G i z)

 theorem gaussianVectorScore_expBounded {ι : Type*} [Fintype ι] (m : ℝ)
    {G : ι → (ι → ℝ) → ℝ} (hG : ∀ i, BddSmooth 0 (G i)) (v : ι → ℝ) :
    ExpNormBounded (gaussianVectorScore m G v) := by
  exact (ExpNormBounded.vectorDot v).sub
    ((ExpNormBounded.sum Finset.univ (fun i _ => (ExpNormBounded.bddSmooth (hG i)).const_mul (v i))).const_mul m)

 

 theorem tiltedMean_vectorScore {n : ℕ}
    {F A : (Fin (n+1) → ℝ) → ℝ}
    {G D : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i))
    (hdF : ∀ i x t, HasDerivAt (fun s : ℝ => F (x+s • Pi.single i 1))
      (G i (x+t • Pi.single i 1)) t)
    (hA : ExpNormBounded A) (hD : ∀ i, ExpNormBounded (D i))
    (hdA : ∀ i x t, HasDerivAt (fun s : ℝ => A (x+s • Pi.single i 1))
      (D i (x+t • Pi.single i 1)) t) (m : ℝ) (v : Fin (n+1) → ℝ) :
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
      (fun z => A z*gaussianVectorScore m G v z) =
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
      (fun z => ∑ i, v i*D i z) := by
  let W := fun z => Real.exp (m*F z)
  have hW : ExpNormBounded W := ExpNormBounded.exp_lipschitz hF m
  let B := fun z => m*(∑ i, v i*G i z)
  have hB : ExpNormBounded B := (ExpNormBounded.sum Finset.univ
    (fun i _ => (ExpNormBounded.bddSmooth (hG i)).const_mul (v i))).const_mul m
  have hDsum : ExpNormBounded (fun z => ∑ i, v i*D i z) :=
    ExpNormBounded.sum Finset.univ (fun i _ => (hD i).const_mul (v i))
  have hs := standardGaussianVector_directional_stein (hA.mul hW)
    (fun i => ((hD i).mul hW).add
      ((hA.mul ((ExpNormBounded.bddSmooth (hG i)).const_mul m)).mul hW))
    (fun i x t => ((hdA i x t).mul ((hdF i x t).const_mul m |>.exp)).congr_deriv
      (by dsimp [W]; ring)) v
  have he (z : Fin (n+1) → ℝ) :
      (∑ i, v i*(D i z*W z+A z*(m*G i z)*W z)) =
        (∑ i, v i*D i z)*W z+A z*B z*W z := by
    dsimp [B]
    simp only [mul_add,Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
    · rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _; ring
  simp_rw [he] at hs
  rw [integral_add (hDsum.mul hW |>.integrable (fun _ => 1))
    ((hA.mul hB).mul hW |>.integrable (fun _ => 1))] at hs
  unfold tiltedMean
  congr 1
  calc
    (∫ z, A z*gaussianVectorScore m G v z*Real.exp (m*F z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
        (∫ z, vectorDot v z*(A z*W z)-A z*B z*W z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by dsimp [gaussianVectorScore,W,B]; ring
    _ = (∫ z, vectorDot v z*(A z*W z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))-
        (∫ z, A z*B z*W z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) :=
      integral_sub ((ExpNormBounded.vectorDot v).mul (hA.mul hW) |>.integrable (fun _ => 1))
        ((hA.mul hB).mul hW |>.integrable (fun _ => 1))
    _ = _ := by rw [hs]; ring

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators

 theorem vectorDot_line {ι : Type*} [Fintype ι] (v x u : ι → ℝ) (s : ℝ) :
    vectorDot v (x+s • u) = vectorDot v x+s*vectorDot v u := by
  simp only [vectorDot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem vectorDot_single {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (i : ι) :
    vectorDot v (Pi.single i 1) = v i := by simp [vectorDot,Pi.single_apply]

 theorem gaussianVectorScore_hasDerivAt {n : ℕ}
    {G : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {H : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hdG : ∀ j i x t, HasDerivAt (fun s : ℝ => G j (x+s • Pi.single i 1))
      (H j i (x+t • Pi.single i 1)) t) (m : ℝ) (v : Fin (n+1) → ℝ)
    (i : Fin (n+1)) (x : Fin (n+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussianVectorScore m G v (x+s • Pi.single i 1))
      (v i-m*∑ j, v j*H j i (x+t • Pi.single i 1)) t := by
  have hdot : HasDerivAt (fun s : ℝ => vectorDot v (x+s • Pi.single i 1)) (v i) t := by
    simp_rw [vectorDot_line,vectorDot_single]
    simpa only [mul_one,one_mul,id_eq] using ((hasDerivAt_id t).mul_const (v i)).const_add (vectorDot v x)
  have hg := HasDerivAt.sum (u := Finset.univ) (fun j _ => (hdG j i x t).const_mul (v j))
  simp only [Finset.sum_fn] at hg
  exact hdot.sub (hg.const_mul m)

 theorem tiltedMean_expNormBounded_mono {n : ℕ}
    {F A B : (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) (hA : ExpNormBounded A) (hB : ExpNormBounded B)
    (hAB : ∀ z, A z ≤ B z) :
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F A ≤
      tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F B := by
  have hW := ExpNormBounded.exp_lipschitz hF m
  apply div_le_div_of_nonneg_right _ (partition_pos m (hW.integrable (fun _ => 1))).le
  exact integral_mono ((hA.mul hW).integrable (fun _ => 1)) ((hB.mul hW).integrable (fun _ => 1))
    (fun z => mul_le_mul_of_nonneg_right (hAB z) (Real.exp_nonneg _))

 theorem tiltedMean_vectorScore_even_step {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ}
    {G : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {H : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i))
    (hH : ∀ i j, BddSmooth 0 (H i j))
    (hdF : ∀ i x t, HasDerivAt (fun s : ℝ => F (x+s • Pi.single i 1))
      (G i (x+t • Pi.single i 1)) t)
    (hdG : ∀ j i x t, HasDerivAt (fun s : ℝ => G j (x+s • Pi.single i 1))
      (H j i (x+t • Pi.single i 1)) t)
    (v : Fin (n+1) → ℝ) (hconv : ∀ z, 0 ≤ ∑ i, v i*(∑ j, v j*H j i z))
    {m : ℝ} (hm : 0 ≤ m) (k : ℕ) :
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
        (fun z => gaussianVectorScore m G v z^(2*k+2)) ≤
      (2*k+1:ℝ)*(∑ i, v i^2)*tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
        (fun z => gaussianVectorScore m G v z^(2*k)) := by
  let S := gaussianVectorScore m G v
  let Q := fun z => ∑ i, v i*(∑ j, v j*H j i z)
  let ds := fun i z => v i-m*∑ j, v j*H j i z
  have hS : ExpNormBounded S := gaussianVectorScore_expBounded m hG v
  have hQ : ExpNormBounded Q := ExpNormBounded.sum Finset.univ fun i _ =>
    (ExpNormBounded.sum Finset.univ (fun j _ => (ExpNormBounded.bddSmooth (hH j i)).const_mul (v j))).const_mul (v i)
  have hds (i : Fin (n+1)) : ExpNormBounded (ds i) :=
    (ExpNormBounded.const (v i)).sub ((ExpNormBounded.sum Finset.univ
      (fun j _ => (ExpNormBounded.bddSmooth (hH j i)).const_mul (v j))).const_mul m)
  have hh := tiltedMean_vectorScore hF hG hdF (hS.pow (2*k+1))
    (fun i => ((hS.pow (2*k)).const_mul (2*k+1:ℝ)).mul (hds i))
    (fun i x t => by
      have hd := gaussianVectorScore_hasDerivAt hdG m v i x t
      convert hd.pow (2*k+1) using 1; first | rfl | simp [Nat.cast_add,Nat.cast_mul,S,ds]) m v
  have heq : (fun z => S z^(2*k+1)*gaussianVectorScore m G v z) = (fun z => S z^(2*k+2)) := by
    funext z
    change S z^(2*k+1)*S z = S z^((2*k+1)+1)
    exact (pow_succ _ _).symm
  have he (z : Fin (n+1) → ℝ) :
      (∑ i, v i*((2*k+1:ℝ)*S z^(2*k)*ds i z)) =
        (2*k+1:ℝ)*S z^(2*k)*((∑ i, v i^2)-m*Q z) := by
    dsimp [ds,Q]
    rw [mul_sub,Finset.mul_sum]
    simp_rw [show ∀ i, v i*((2*k+1:ℝ)*S z^(2*k)*(v i-m*∑ j, v j*H j i z)) =
        (2*k+1:ℝ)*S z^(2*k)*(v i^2)-(2*k+1:ℝ)*S z^(2*k)*m*(v i*∑ j, v j*H j i z) by
      intro i; ring]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  rw [heq] at hh
  simp_rw [he] at hh
  calc
    _ = tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
      (fun z => (2*k+1:ℝ)*S z^(2*k)*((∑ i, v i^2)-m*Q z)) := hh
    _ ≤ tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
      (fun z => (2*k+1:ℝ)*(∑ i, v i^2)*S z^(2*k)) := by
      apply tiltedMean_expNormBounded_mono hF m
        (((hS.pow (2*k)).const_mul _).mul ((ExpNormBounded.const _).sub (hQ.const_mul m)))
        ((hS.pow (2*k)).const_mul _)
      intro z
      have hpow : 0 ≤ S z^(2*k) := pow_nonneg (sq_nonneg (S z)) k |>.trans_eq (by rw [← pow_mul])
      have hc : 0 ≤ (2*k+1:ℝ)*S z^(2*k) := mul_nonneg (by positivity) hpow
      have hq := mul_nonneg hm (hconv z)
      dsimp [Q] at hc ⊢
      nlinarith
    _ = _ := by
      simp only [tiltedMean,mul_assoc,integral_const_mul]
      ring

 theorem tiltedMean_vectorScore_even_bound {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ}
    {G : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {H : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i))
    (hH : ∀ i j, BddSmooth 0 (H i j))
    (hdF : ∀ i x t, HasDerivAt (fun s : ℝ => F (x+s • Pi.single i 1))
      (G i (x+t • Pi.single i 1)) t)
    (hdG : ∀ j i x t, HasDerivAt (fun s : ℝ => G j (x+s • Pi.single i 1))
      (H j i (x+t • Pi.single i 1)) t)
    (v : Fin (n+1) → ℝ) (hconv : ∀ z, 0 ≤ ∑ i, v i*(∑ j, v j*H j i z))
    {m : ℝ} (hm : 0 ≤ m) (k : ℕ) :
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
        (fun z => gaussianVectorScore m G v z^(2*k)) ≤
      gaussianEvenConstant k*(∑ i, v i^2)^k := by
  induction k with
  | zero =>
    have hn := partition_pos m ((ExpNormBounded.exp_lipschitz hF m).integrable (fun _ => 1))
    simp only [Nat.mul_zero,pow_zero,tiltedMean,one_mul,div_self hn.ne',gaussianEvenConstant,mul_one,le_refl]
  | succ k ih =>
    have h := tiltedMean_vectorScore_even_step hF hG hH hdF hdG v hconv hm k
    calc
      _ ≤ (2*k+1:ℝ)*(∑ i, v i^2)*tiltedMean
          (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
          (fun z => gaussianVectorScore m G v z^(2*k)) := by
        simpa only [Nat.mul_add,Nat.mul_one] using h
      _ ≤ (2*k+1:ℝ)*(∑ i, v i^2)*(gaussianEvenConstant k*(∑ i, v i^2)^k) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))))
      _ = _ := by rw [gaussianEvenConstant,pow_succ]; ring

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem finite_covariance_identity {S : Type*} [Fintype S] (p A B : S → ℝ)
    (hp : ∑ s, p s = 1) :
    (∑ s, ∑ t, p s*p t*(A s-A t)*(B s-B t)) =
      2*((∑ s, p s*A s*B s)-(∑ s, p s*A s)*(∑ s, p s*B s)) := by
  have he (s t : S) : p s*p t*(A s-A t)*(B s-B t) =
      p s*A s*B s*p t-(p s*A s)*(p t*B t)-(p s*B s)*(p t*A t)+p s*(p t*A t*B t) := by ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,
    hp,mul_one,one_mul]
  ring

 theorem finite_covariance_nonneg {S : Type*} [Fintype S] (p A B : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (hAB : ∀ s t, 0 ≤ (A s-A t)*(B s-B t)) :
    0 ≤ (∑ s, p s*A s*B s)-(∑ s, p s*A s)*(∑ s, p s*B s) := by
  have hsum : 0 ≤ ∑ s, ∑ t, p s*p t*(A s-A t)*(B s-B t) := by
    apply Finset.sum_nonneg
    intro s _
    apply Finset.sum_nonneg
    intro t _
    simpa only [mul_assoc] using mul_nonneg (mul_nonneg (hp s) (hp t)) (hAB s t)
  rw [finite_covariance_identity p A B hs] at hsum
  linarith

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 noncomputable def hierarchyCovariance (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A B : S → ℝ) (steps : List (GaussianStep ι)) (x : ι → ℝ) : ℝ :=
  gaussianHierarchyMean w φ (fun s => A s*B s) steps x-
    gaussianHierarchyMean w φ A steps x*gaussianHierarchyMean w φ B steps x

 theorem hierarchyCovariance_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A B : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (r : ℕ) :
    BddSmooth r (hierarchyCovariance w φ A B steps) :=
  (gaussianHierarchyMean_smooth hw φ _ steps ha r).sub
    ((gaussianHierarchyMean_smooth hw φ A steps ha r).mul (gaussianHierarchyMean_smooth hw φ B steps ha r))

 theorem hierarchyCovariance_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A B : S → ℝ)
    (hAB : ∀ s t, 0 ≤ (A s-A t)*(B s-B t)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    0 ≤ hierarchyCovariance w φ A B steps x := by
  have h := finite_covariance_nonneg (fun s => hierarchyAtom w φ steps s x) A B
    (fun s => hierarchyAtom_nonneg hw φ steps ha s x) (hierarchyAtom_sum hw φ steps ha x) hAB
  simpa only [hierarchyCovariance,gaussianHierarchyMean_atoms hw φ steps ha,
    mul_comm,mul_left_comm,mul_assoc] using h

 

 theorem gaussianHierarchyResponse_comonotone_lower {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (v : ι → ℝ)
    (hA : ∀ s t, 0 ≤ (A s-A t)*(φ s v-φ t v)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    a*hierarchyCovariance w φ A (fun s => φ s v) steps x ≤
      gaussianHierarchyResponse w φ A v steps x := by
  induction steps generalizing a x with
  | nil =>
    have hn := hierarchyCovariance_nonneg hw φ A (fun s => φ s v) hA [] ha x
    have h := mul_le_mul_of_nonneg_right ha.2 hn
    simpa only [one_mul,hierarchyCovariance,gaussianHierarchyResponse,gaussianHierarchyMean,mul_assoc] using h
  | cons st steps ih =>
    rcases st with ⟨m,q⟩
    let ν := Measure.pi fun i => gaussianReal 0 (q i)
    let F := gaussianHierarchy w φ steps
    let MA := gaussianHierarchyMean w φ A steps
    let MB := gaussianHierarchyMean w φ (fun s => φ s v) steps
    let MAB := gaussianHierarchyMean w φ (fun s => A s*φ s v) steps
    have hi := gaussianHierarchy_integrable hw φ steps ha.2.2.2 m q x
    have hcov := hierarchyCovariance_smooth hw φ A (fun s => φ s v) steps ha.2.2.2 0
    have h := shiftedMean_mono (ν := ν) (m := m) (F := F) (hcov.const_mul m)
      (gaussianHierarchyResponse_smooth hw φ A v steps ha.2.2.2 0)
      (fun y => ih ha.2.2.2 y) hi
    rw [shiftedMean_const_mul] at h
    change m*shiftedMean ν m F (fun y => MAB y-MA y*MB y) x ≤ _ at h
    rw [shiftedMean_sub (gaussianHierarchyMean_smooth hw φ _ steps ha.2.2.2 0)
      ((gaussianHierarchyMean_smooth hw φ A steps ha.2.2.2 0).mul
        (gaussianHierarchyMean_smooth hw φ (fun s => φ s v) steps ha.2.2.2 0)) hi] at h
    have hm : m*hierarchyCovariance w φ A (fun s => φ s v) ((m,q)::steps) x ≤
        gaussianHierarchyResponse w φ A v ((m,q)::steps) x := by
      change m*(shiftedMean ν m F MAB x-shiftedMean ν m F MA x*shiftedMean ν m F MB x) ≤
        shiftedMean ν m F (gaussianHierarchyResponse w φ A v steps) x+
        m*(shiftedMean ν m F (fun y => MA y*MB y) x-shiftedMean ν m F MA x*shiftedMean ν m F MB x)
      nlinarith only [h]
    exact (mul_le_mul_of_nonneg_right ha.2.1
      (hierarchyCovariance_nonneg hw φ A (fun s => φ s v) hA _ ha x)).trans hm

end SKFluctuations.Hierarchy

end

end OAI
