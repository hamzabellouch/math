import Mathlib
import OAI.Probability.IsingPerceptron.NodalGaussianLipschitz

namespace OAI

/-! Gaussian Variance. -/

noncomputable section

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology

def CoordinateLipschitz {n : ℕ} (c : Fin n → ℝ) (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀i x y,(∀j,j≠i → x j=y j) → |F x-F y|≤c i*|x i-y i|

lemma coordinateLipschitz_global {n : ℕ} {c : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ}
    (hc : CoordinateLipschitz c F) (x y : Fin n → ℝ) :
    |F x-F y|≤∑i,c i*|x i-y i| := by
  induction n with
  | zero => have he : x=y := Subsingleton.elim _ _; simp [he]
  | succ n ih =>
    let z := Fin.cons (y 0) (Fin.tail x)
    have h0 : |F x-F z|≤c 0*|x 0-y 0| := by
      apply hc 0
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; rfl
    have ht : CoordinateLipschitz (fun i : Fin n => c i.succ)
        (fun v => F (Fin.cons (y 0) v)) := by
      intro i u v huv
      apply hc i.succ
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro _; rfl
      · intro hk; exact huv k (fun h => hk (congrArg Fin.succ h))
    have h1 := ih ht (Fin.tail x) (Fin.tail y)
    rw [Fin.cons_self_tail] at h1
    rw [Fin.sum_univ_succ]
    calc _ ≤ |F x-F z|+|F z-F y| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h0 h1

lemma coordinateLipschitz_memLp {n : ℕ} {c : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (hc0 : ∀i,0≤c i) (hc : CoordinateLipschitz c F) :
    MemLp F 2 (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hs : MemLp (fun g : Fin n → ℝ => ∑i,c i*|g i|) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) :=
    memLp_finsetSum _ (fun i _ =>
      ((memLp_id_gaussianReal (μ:=0) (v:=1) 2).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).abs.const_mul (c i))
  apply ((memLp_const |F 0|).add hs).mono hF.aestronglyMeasurable
  filter_upwards [] with g
  have h := coordinateLipschitz_global hc g 0
  simp only [Pi.zero_apply,sub_zero] at h
  simp only [Pi.add_apply,Real.norm_eq_abs]
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hc0 i) (abs_nonneg _))))]
  have ht := abs_add_le (F g-F 0) (F 0)
  simp only [sub_add_cancel] at ht
  linarith

lemma standardGaussian_second_moment :
    (∫x : ℝ,x^2 ∂gaussianReal 0 1)=1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ:=0) (v:=1) 2)
  simpa only [variance_id_gaussianReal,NNReal.coe_one,Pi.pow_apply,id_eq,
    integral_id_gaussianReal,zero_pow (by decide : 2≠0),sub_zero] using h.symm

lemma gaussian_variance_le_square {F : ℝ → ℝ} (hF : Measurable F) {c : ℝ}
    (h : ∀x,|F x-F 0|≤c*|x|) : variance F (gaussianReal 0 1)≤c^2 := by
  have hi : MemLp (fun x => c*|x|) 2 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).abs.const_mul c
  have hF0 : MemLp (fun x => F x-F 0) 2 (gaussianReal 0 1) := by
    apply hi.mono (hF.sub measurable_const).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs]
      exact (h x).trans (le_abs_self _)
  have hb : (∫x,(F x-F 0)^2 ∂gaussianReal 0 1) ≤
      ∫x,c^2*x^2 ∂gaussianReal 0 1 := by
    apply integral_mono hF0.integrable_sq
      ((memLp_id_gaussianReal 2).integrable_sq.const_mul (c^2))
    intro x
    calc (F x-F 0)^2 = |F x-F 0|^2 := (sq_abs _).symm
      _ ≤ (c*|x|)^2 := pow_le_pow_left₀ (abs_nonneg _) (h x) 2
      _ = c^2*x^2 := by rw [mul_pow,sq_abs]
  rw [integral_const_mul,standardGaussian_second_moment,mul_one] at hb
  rw [← variance_sub_const hF.aestronglyMeasurable (F 0)]
  exact (variance_le_expectation_sq (hF.sub measurable_const).aestronglyMeasurable).trans hb

lemma variance_prod_le_of_slices {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hF : MemLp F 2 (μ.prod ν))
    (hSlices : ∀y,MemLp (fun x => F (x,y)) 2 μ)
    (hG : MemLp (fun y => ∫x,F (x,y) ∂μ) 2 ν) {c : ℝ}
    (hc : ∀y,variance (fun x => F (x,y)) μ≤c) :
    variance F (μ.prod ν) ≤ c+variance (fun y => ∫x,F (x,y) ∂μ) ν := by
  have hiF := hF.integrable (by norm_num)
  have hiF2 := hF.integrable_sq
  have hiG2 := hG.integrable_sq
  have hs (y : B) : (∫x,F (x,y)^2 ∂μ)≤c+(∫x,F (x,y) ∂μ)^2 := by
    have h := hc y
    rw [variance_eq_sub (hSlices y)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hb := integral_mono hiF2.integral_prod_right ((integrable_const c).add hiG2) hs
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const _) hiG2,integral_const] at hb
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hb
  rw [variance_eq_sub hF,variance_eq_sub hG]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hiF2,integral_prod_symm _ hiF]
  linarith

theorem gaussian_pi_variance_le {n : ℕ} {c : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (hc0 : ∀i,0≤c i) (hc : CoordinateLipschitz c F) :
    variance F (Measure.pi (fun _ => gaussianReal 0 1)) ≤ ∑i,c i^2 := by
  induction n with
  | zero =>
    have he : F=fun _ => F Fin.elim0 := by funext x; congr 1; exact Subsingleton.elim _ _
    rw [he,variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
    let H : ℝ × (Fin n → ℝ) → ℝ := fun p => F (Fin.cons p.1 p.2)
    have hmH : Measurable H := by
      apply hF.comp
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst
      · exact (measurable_pi_apply j).comp measurable_snd
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).symm
    have he (p : ℝ × (Fin n → ℝ)) :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p=Fin.cons p.1 p.2 := by
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    have hH : MemLp H 2 ((gaussianReal 0 1).prod ν) := by
      have hh := (coordinateLipschitz_memLp hF hc0 hc).comp_measurePreserving hmp
      have hhfun : F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm=H := by
        funext p; exact congrArg F (he p)
      rw [hhfun] at hh
      exact hh
    have hslice (y : Fin n → ℝ) : ∀x,|H (x,y)-H (0,y)|≤c 0*|x| := by
      intro x
      have ht := hc 0 (Fin.cons x y) (Fin.cons 0 y) (by
        intro j; refine Fin.cases ?_ (fun k => ?_) j
        · intro h; exact (h rfl).elim
        · intro _; rfl)
      simpa only [Fin.cons_zero,sub_zero] using ht
    have hmSlice (y : Fin n → ℝ) : Measurable (fun x => H (x,y)) :=
      hmH.comp (measurable_id.prodMk measurable_const)
    have hiSlice (y : Fin n → ℝ) : MemLp (fun x => H (x,y)) 2 (gaussianReal 0 1) := by
      apply ((memLp_const |H (0,y)|).add ((memLp_id_gaussianReal 2).abs.const_mul (c 0))).mono
        (hmSlice y).aestronglyMeasurable
      filter_upwards [] with x
      simp only [Pi.add_apply,Real.norm_eq_abs,Pi.abs_apply,id_eq]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (hc0 _) (abs_nonneg _)))]
      have h := hslice y x
      have ht := abs_add_le (H (x,y)-H (0,y)) (H (0,y))
      simp only [sub_add_cancel] at ht
      linarith
    let G : (Fin n → ℝ) → ℝ := fun y => ∫x,H (x,y) ∂gaussianReal 0 1
    have hmG : Measurable G := hmH.stronglyMeasurable.integral_prod_left'.measurable
    have hcG : CoordinateLipschitz (fun i : Fin n => c i.succ) G := by
      intro i x y hxy
      dsimp only [G]
      rw [← integral_sub ((hiSlice x).integrable (by norm_num)) ((hiSlice y).integrable (by norm_num))]
      apply bounded_mean
      intro a
      have ht := hc i.succ (Fin.cons a x) (Fin.cons a y) (by
        intro j; refine Fin.cases ?_ (fun k => ?_) j
        · intro _; rfl
        · intro h; exact hxy k (fun he => h (congrArg Fin.succ he)))
      exact ht
    have hG := coordinateLipschitz_memLp hmG (fun i => hc0 i.succ) hcG
    have hb := variance_prod_le_of_slices (gaussianReal 0 1) ν hH hiSlice hG
      (fun y => gaussian_variance_le_square (hmSlice y) (hslice y))
    have hvar : variance F (Measure.pi (fun _ => gaussianReal 0 1))=
        variance H ((gaussianReal 0 1).prod ν) := by
      rw [← hmp.map_eq,variance_map hF.aemeasurable hmp.measurable.aemeasurable]
      congr 1; funext p; exact congrArg F (he p)
    rw [hvar,Fin.sum_univ_succ]
    exact hb.trans (add_le_add le_rfl (ih hmG (fun i => hc0 i.succ) hcG))

end IsingPerceptron.Main

namespace IsingPerceptron
namespace Main
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

abbrev Spins (N : ℕ) := Fin N → Bool

def spin {N : ℕ} (x : Spins N) (i : Fin N) : ℝ := if x i then 1 else -1

def patternCount (α : ℝ) (N : ℕ) : ℕ := ⌊α * N⌋₊

abbrev Disorder (α : ℝ) (N : ℕ) := Fin (patternCount α N) → Fin N → ℝ

def disorderLaw (α : ℝ) (N : ℕ) : Measure (Disorder α N) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

def patternEvaluation {α : ℝ} {N : ℕ} (g : Disorder α N)
    (a : Fin (patternCount α N)) (x : Spins N) : ℝ :=
  (∑ i : Fin N, g a i * spin x i) / Real.sqrt N

def partitionFunction (α : ℝ) (f : ℝ → ℝ) (N : ℕ) (g : Disorder α N) : ℝ :=
  (∑ x : Spins N, Real.exp (∑ a, f (patternEvaluation g a x))) / (2 : ℝ) ^ N

def pressure (α : ℝ) (f : ℝ → ℝ) (N : ℕ) (g : Disorder α N) : ℝ :=
  Real.log (partitionFunction α f N g) / N

def meanPressure (α : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∫ g, pressure α f N g ∂disorderLaw α N

structure Partition where
  count : ℕ
  positive : 0 < count
  ζ : Fin (count + 1) → ℝ
  strictMono : StrictMono ζ
  first : ζ 0 = 0
  last : ζ (Fin.last count) = 1

structure StepPath where
  partition : Partition
  value : Fin partition.count → ℝ
  monotone : Monotone value

def StepPath.stepValue (h : StepPath) (u : ℝ) : ℝ :=
  ∑ i : Fin h.partition.count,
    if h.partition.ζ i.castSucc ≤ u ∧ u < h.partition.ζ i.succ then h.value i else 0

abbrev StepField := {h : StepPath // ∀ i, 0 ≤ h.value i}
abbrev StepOverlap := {q : StepPath // ∀ i, q.value i ∈ Set.Icc (0 : ℝ) 1}

def gaussianTransform (s d : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  if d = 0 then ∫ G, U (x + Real.sqrt s * G) ∂gaussianReal 0 1
  else (Real.log (∫ G, Real.exp (d * U (x + Real.sqrt s * G)) ∂gaussianReal 0 1)) / d

def StepPath.increment (q : StepPath) (top : ℝ) (i : ℕ) : ℝ :=
  (if hi : i < q.partition.count then q.value ⟨i, hi⟩ else top) -
  (if i = 0 then 0 else
    if hi : i - 1 < q.partition.count then q.value ⟨i - 1, hi⟩ else top)

def stepPattern (f : ℝ → ℝ) (q : StepOverlap) : ℝ :=
  ((List.finRange (q.val.partition.count + 1)).foldr
    (fun (i : Fin (q.val.partition.count + 1)) U => gaussianTransform (q.val.increment 1 i) (q.val.partition.ζ i) U) f) 0

def fieldFunctional (h : StepField) : ℝ :=
  let last := h.val.value ⟨h.val.partition.count - 1, by have := h.val.partition.positive; omega⟩
  ((List.finRange h.val.partition.count).foldr
    (fun (i : Fin h.val.partition.count) U => gaussianTransform (h.val.increment last i) (h.val.partition.ζ i.castSucc) U)
    (fun x => Real.log (Real.cosh x) - last / 2)) 0

abbrev OpenUnit := Set.Ioo (0 : ℝ) 1
abbrev OverlapRep := OpenUnit →o Set.Icc (0 : ℝ) 1

def extendRep (q : OverlapRep) (u : ℝ) : ℝ :=
  if hu : u ∈ Set.Ioo (0 : ℝ) 1 then (q ⟨u, hu⟩ : ℝ) else 0

def pathSetoid : Setoid OverlapRep where
  r q r := extendRep q =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] extendRep r
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def OverlapPath := Quotient pathSetoid

def uniformPartition (m : ℕ) (hm : 0 < m) : Partition where
  count := m
  positive := hm
  ζ i := (i : ℝ) / m
  strictMono := by
    intro i j hij
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by exact_mod_cast hm)
  first := by simp
  last := by simp [ne_of_gt hm]

def midpoint (m : ℕ) (hm : 0 < m) (i : Fin m) : OpenUnit :=
  ⟨((i : ℝ) + 1 / 2) / m, by
    have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    have hi' : (i : ℝ) < m := by exact_mod_cast i.isLt
    constructor
    · exact div_pos (by positivity) hm'
    · apply (div_lt_one hm').mpr
      have hi'' : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
      linarith⟩

lemma midpoint_monotone (m : ℕ) (hm : 0 < m) : Monotone (midpoint m hm) := by
  intro i j hij
  change ((i : ℝ) + 1 / 2) / m ≤ ((j : ℝ) + 1 / 2) / m
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

def dyadicStep (q : OverlapPath) (n : ℕ) : StepOverlap :=
  let m := 2 ^ n
  have hm : 0 < m := pow_pos (by decide) _
  ⟨⟨uniformPartition m hm,
      (fun i => (q.out (midpoint m hm i) : ℝ)),
      fun i j hij => (q.out.monotone (midpoint_monotone m hm hij))⟩,
    fun i => (q.out (midpoint m hm i)).property⟩

def patternFunctional (f : ℝ → ℝ) (q : OverlapPath) : ℝ :=
  Filter.limUnder atTop (fun n => stepPattern f (dyadicStep q n))

def isingEntropy (q : OverlapPath) : EReal :=
  ⨆ h : StepField,
    ((fieldFunctional h + (1 / 2) *
      ∫ u in Set.Ioo (0 : ℝ) 1, h.val.stepValue u * extendRep q.out u) : ℝ)

def variationalValue (α : ℝ) (f : ℝ → ℝ) : EReal :=
  ⨅ q : OverlapPath, ((α * patternFunctional f q : ℝ) : EReal) + isingEntropy q

def PressureConvergesInProbability (α : ℝ) (f : ℝ → ℝ) (p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun N => disorderLaw α N {g | ε < |pressure α f N g - p|}) atTop (𝓝 0)

end Main
end IsingPerceptron

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped BigOperators NNReal ENNReal Topology Classical

lemma spin_card (N : ℕ) : Fintype.card (Spins N) = 2^N := by simp [Spins]

lemma finite_exp_average_pos {S : Type*} [Fintype S] [Nonempty S] (H : S → ℝ) :
    0 < (∑x,exp (H x))/(Fintype.card S : ℝ) := by
  apply div_pos
  · exact Finset.sum_pos (fun x _ => exp_pos _) Finset.univ_nonempty
  · exact_mod_cast Fintype.card_pos

lemma finite_log_average_le {S : Type*} [Fintype S] [Nonempty S]
    (H K : S → ℝ) (d : ℝ) (h : ∀x,H x≤K x+d) :
    log ((∑x,exp (H x))/(Fintype.card S : ℝ)) ≤
    log ((∑x,exp (K x))/(Fintype.card S : ℝ))+d := by
  have hsum : ∑x,exp (H x) ≤ exp d * ∑x,exp (K x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    calc exp (H x) ≤ exp (K x+d) := exp_le_exp.mpr (h x)
      _ = exp d*exp (K x) := by rw [exp_add,mul_comm]
  have hcard : (0:ℝ)<Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hl := log_le_log (finite_exp_average_pos H)
    (div_le_div_of_nonneg_right hsum hcard.le)
  rw [mul_div_assoc,log_mul (exp_pos _).ne' (finite_exp_average_pos K).ne',log_exp] at hl
  linarith

lemma finite_log_average_abs {S : Type*} [Fintype S] [Nonempty S]
    (H : S → ℝ) (d : ℝ) (h : ∀x,|H x|≤d) :
    |log ((∑x,exp (H x))/(Fintype.card S : ℝ))|≤d := by
  have hcard : (Fintype.card S : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hu := finite_log_average_le H (fun _ => 0) d (fun x => by simpa using (abs_le.mp (h x)).2)
  have hl := finite_log_average_le (fun _ => 0) H d (fun x => by have := (abs_le.mp (h x)).1; linarith)
  simp only [exp_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,div_self hcard,log_one] at hu hl
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma finite_log_average_difference {S : Type*} [Fintype S] [Nonempty S]
    (H K : S → ℝ) (d : ℝ) (h : ∀x,|H x-K x|≤d) :
    |log ((∑x,exp (H x))/(Fintype.card S : ℝ))-
      log ((∑x,exp (K x))/(Fintype.card S : ℝ))|≤d := by
  have hu := finite_log_average_le H K d (fun x => by have := (abs_le.mp (h x)).2; linarith)
  have hl := finite_log_average_le K H d (fun x => by have := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma pressure_measurable (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (pressure α f N) := by
  unfold pressure partitionFunction patternEvaluation
  fun_prop

lemma pressure_bounded (α : ℝ) {f : ℝ → ℝ} {C : ℝ} (hC : ∀x,|f x|≤C)
    (N : ℕ) (g : Disorder α N) :
    |pressure α f N g| ≤ (patternCount α N : ℝ)*C/N := by
  have hH (x : Spins N) : |∑a,f (patternEvaluation g a x)|≤(patternCount α N : ℝ)*C := by
    calc |∑a,f (patternEvaluation g a x)| ≤ ∑a,|f (patternEvaluation g a x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_a : Fin (patternCount α N),C := Finset.sum_le_sum (fun a _ => hC _)
      _ = _ := by simp
  have hL := finite_log_average_abs (fun x : Spins N => ∑a,f (patternEvaluation g a x)) _ hH
  rw [spin_card] at hL
  simpa only [pressure,partitionFunction,abs_div,abs_of_nonneg (show (0:ℝ)≤N from Nat.cast_nonneg N),Nat.cast_pow,Nat.cast_ofNat] using
    div_le_div_of_nonneg_right hL (Nat.cast_nonneg N)

lemma pressure_row_difference (α : ℝ) {f : ℝ → ℝ} {C : ℝ} (hC : ∀x,|f x|≤C)
    (N : ℕ) (a : Fin (patternCount α N)) (g g' : Disorder α N)
    (heq : ∀b,b≠a → g b=g' b) :
    |pressure α f N g-pressure α f N g'|≤2*C/N := by
  have hH (x : Spins N) :
      |(∑b,f (patternEvaluation g b x))-(∑b,f (patternEvaluation g' b x))|≤2*C := by
    rw [← Finset.sum_sub_distrib,Finset.sum_eq_single a]
    · calc |f (patternEvaluation g a x)-f (patternEvaluation g' a x)| ≤
          |f (patternEvaluation g a x)|+|f (patternEvaluation g' a x)| := abs_sub _ _
        _ ≤ _ := by linarith [hC (patternEvaluation g a x),hC (patternEvaluation g' a x)]
    · intro b _ hba
      have hargument : patternEvaluation g b x=patternEvaluation g' b x := by
        unfold patternEvaluation
        rw [heq b hba]
      rw [hargument,sub_self]
    · simp
  have hL := finite_log_average_difference
    (fun x : Spins N => ∑b,f (patternEvaluation g b x))
    (fun x : Spins N => ∑b,f (patternEvaluation g' b x)) (2*C) hH
  rw [spin_card] at hL
  simpa only [pressure,partitionFunction,← sub_div,abs_div,abs_of_nonneg (show (0:ℝ)≤N from Nat.cast_nonneg N),Nat.cast_pow,Nat.cast_ofNat] using
    div_le_div_of_nonneg_right hL (Nat.cast_nonneg N)

theorem pressure_variance_bound (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀x,|f x|≤C) (N : ℕ) :
    variance (pressure α f N) (disorderLaw α N) ≤
      (patternCount α N : ℝ)*(2*C/N)^2 := by
  have h := variance_pi_bounded_differences
    (fun _ : Fin (patternCount α N) => (Measure.pi fun _ : Fin N => gaussianReal 0 1))
    (pressure_measurable α hf N) (pressure_bounded α hC N)
    (fun _ => 2*C/N) (pressure_row_difference α hC N)
  simpa only [disorderLaw,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

lemma pressure_variance_rate (α : ℝ) (hα : 0≤α) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀x,|f x|≤C) {N : ℕ} (hN : 0<N) :
    variance (pressure α f N) (disorderLaw α N) ≤ 4*α*C^2/N := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  refine (pressure_variance_bound α hf hC N).trans ?_
  calc (patternCount α N : ℝ)*(2*C/N)^2 ≤ α*N*(2*C/N)^2 :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (mul_nonneg hα hNr.le)) (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem pressure_tail_bound (α : ℝ) (hα : 0≤α) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀x,|f x|≤C) {N : ℕ} (hN : 0<N) {ε : ℝ} (hε : 0<ε) :
    disorderLaw α N {g | ε < |pressure α f N g-meanPressure α f N|} ≤
      ENNReal.ofReal ((4*α*C^2/ε^2)/N) := by
  have : IsProbabilityMeasure (disorderLaw α N) := by
    dsimp [disorderLaw]; infer_instance
  have hL := meas_ge_le_variance_div_sq
    (bounded_memLp (disorderLaw α N) (pressure_measurable α hf N) (pressure_bounded α hC N)) hε
  have hsubset : {g | ε < |pressure α f N g-meanPressure α f N|} ⊆
      {g | ε ≤ |pressure α f N g-meanPressure α f N|} := by
    intro g hg
    exact (show ε < |pressure α f N g-meanPressure α f N| from hg).le
  refine (measure_mono hsubset).trans (hL.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  calc variance (pressure α f N) (disorderLaw α N)/ε^2 ≤ (4*α*C^2/N)/ε^2 :=
      div_le_div_of_nonneg_right (pressure_variance_rate α hα hf hC hN) (sq_nonneg _)
    _ = _ := by ring

theorem pressure_centered_concentration (α : ℝ) (hα : 0≤α) {f : ℝ → ℝ}
    (hf : Measurable f) (hbounded : ∃C,∀x,|f x|≤C) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun N => disorderLaw α N
      {g | ε < |pressure α f N g-meanPressure α f N|}) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := hbounded
  have hrate : Tendsto (fun N : ℕ => ENNReal.ofReal ((4*α*C^2/ε^2)/N)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (4*α*C^2/ε^2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact pressure_tail_bound α hα hf hC hN hε

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology
variable {S : Type*} [Fintype S] [Nonempty S]

def finiteGibbs (H V : S → ℝ) : ℝ := (∑x,exp (H x)*V x)/(∑x,exp (H x))

lemma finiteGibbs_den_pos (H : S → ℝ) : 0<∑x,exp (H x) :=
  Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty

lemma finiteGibbs_abs (H V : S → ℝ) {C : ℝ} (h : ∀x,|V x|≤C) :
    |finiteGibbs H V|≤C := by
  rw [finiteGibbs,abs_div,abs_of_pos (finiteGibbs_den_pos H)]
  apply (div_le_iff₀ (finiteGibbs_den_pos H)).mpr
  calc |∑x,exp (H x)*V x| ≤ ∑x,|exp (H x)*V x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑x,exp (H x)*C := Finset.sum_le_sum (fun x _ => by
      rw [abs_mul,abs_of_pos (exp_pos _)]; exact mul_le_mul_of_nonneg_left (h x) (exp_pos _).le)
    _ = C*∑x,exp (H x) := by rw [← Finset.sum_mul,mul_comm]

omit [Nonempty S] in
lemma finiteGibbs_add (H V W : S → ℝ) :
    finiteGibbs H (fun x => V x+W x)=finiteGibbs H V+finiteGibbs H W := by
  simp only [finiteGibbs,mul_add,Finset.sum_add_distrib,add_div]

omit [Nonempty S] in
lemma finiteGibbs_mul_const (H V : S → ℝ) (c : ℝ) :
    finiteGibbs H (fun x => V x*c)=finiteGibbs H V*c := by
  simp only [finiteGibbs,← mul_assoc,← Finset.sum_mul]
  ring

omit [Nonempty S] in
lemma finiteGibbs_div_const (H V : S → ℝ) (c : ℝ) :
    finiteGibbs H (fun x => V x/c)=finiteGibbs H V/c := by
  simp only [div_eq_mul_inv,finiteGibbs_mul_const]

omit [Nonempty S] in
lemma finiteGibbs_measurable {A : Type*} [MeasurableSpace A]
    {H V : A → S → ℝ} (hH : ∀x,Measurable (fun a => H a x))
    (hV : ∀x,Measurable (fun a => V a x)) :
    Measurable (fun a => finiteGibbs (H a) (V a)) := by
  unfold finiteGibbs
  fun_prop

theorem finiteGibbs_derivative {H V : ℝ → S → ℝ} {HD VD : S → ℝ} {t : ℝ}
    (hH : ∀x,HasDerivAt (fun t => H t x) (HD x) t)
    (hV : ∀x,HasDerivAt (fun t => V t x) (VD x) t) :
    HasDerivAt (fun t => finiteGibbs (H t) (V t))
      (finiteGibbs (H t) (fun x => VD x+V t x*HD x)-
        finiteGibbs (H t) (V t)*finiteGibbs (H t) HD) t := by
  have hnum := HasDerivAt.fun_sum (u:=Finset.univ)
    (fun x _ => (hH x).exp.mul (hV x))
  have hden := HasDerivAt.fun_sum (u:=Finset.univ) (fun x _ => (hH x).exp)
  apply (hnum.fun_div hden (finiteGibbs_den_pos (H t)).ne').congr_deriv
  simp only [finiteGibbs,Pi.mul_apply]
  have he : (∑x,(exp (H t x)*HD x*V t x+exp (H t x)*VD x))=
      ∑x,exp (H t x)*(VD x+V t x*HD x) := by
    apply Finset.sum_congr rfl; intro x _; ring
  rw [he]
  field_simp [(finiteGibbs_den_pos (H t)).ne']

omit [Nonempty S] in
lemma finiteGibbs_sum {I : Type*} (s : Finset I) (H : S → ℝ) (V : I → S → ℝ) :
    finiteGibbs H (fun x => ∑i ∈ s,V i x)=∑i ∈ s,finiteGibbs H (V i) := by
  simp only [finiteGibbs,Finset.mul_sum,Finset.sum_div]
  exact Finset.sum_comm

omit [Nonempty S] in
lemma finiteGibbs_const_mul (H V : S → ℝ) (c : ℝ) :
    finiteGibbs H (fun x => c*V x)=c*finiteGibbs H V := by
  simpa only [mul_comm] using finiteGibbs_mul_const H V c

def finiteGibbsPair (H : S → ℝ) (V : S → S → ℝ) : ℝ :=
  finiteGibbs H (fun x => finiteGibbs H (V x))

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology

lemma standardDensity_derivative (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have heq : gaussianPDFReal 0 1 =
      (fun y : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(y^2)/2)) := by
    funext y
    simp [gaussianPDFReal]
  rw [heq]
  have h : HasDerivAt (fun y : ℝ => Real.exp (-(y^2)/2))
      (-x*Real.exp (-(x^2)/2)) x := by
    convert! ((hasDerivAt_id x).pow 2 |>.neg |>.div_const 2).exp using 1
    simp only [Pi.neg_apply, Pi.pow_apply, id_eq]; ring
  exact (h.const_mul ((Real.sqrt (2*Real.pi))⁻¹)).congr_deriv (by ring)

lemma standardDensity_times_id_integrable :
    Integrable (fun x : ℝ => gaussianPDFReal 0 1 x*x) := by
  have h := (integrable_mul_exp_neg_mul_sq (b:=(1:ℝ)/2) (by positivity)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert h using 1
  ext x
  simp [gaussianPDFReal]
  ring_nf

theorem gaussian_integration_by_parts {F F' : ℝ → ℝ} {C D : ℝ}
    (hd : ∀x,HasDerivAt F (F' x) x) (hm : Measurable F')
    (hC : ∀x,|F x|≤C) (hD : ∀x,|F' x|≤D) :
    (∫x,x*F x ∂gaussianReal 0 1) = ∫x,F' x ∂gaussianReal 0 1 := by
  have hF : Measurable F := (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable
  have hbase : Integrable (fun x => gaussianPDFReal 0 1 x*F x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hF.aestronglyMeasurable
      (ae_of_all _ fun x => hC x)
  have hfirst : Integrable (fun x => gaussianPDFReal 0 1 x*F' x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun x => hD x)
  have hsecond : Integrable (fun x => gaussianPDFReal 0 1 x*(x*F x)) := by
    simpa only [mul_assoc] using standardDensity_times_id_integrable.mul_bdd
      hF.aestronglyMeasurable (ae_of_all _ fun x => hC x)
  have hderiv (x : ℝ) : HasDerivAt (fun x => gaussianPDFReal 0 1 x*F x)
      (gaussianPDFReal 0 1 x*F' x-gaussianPDFReal 0 1 x*(x*F x)) x := by
    exact ((standardDensity_derivative x).mul (hd x)).congr_deriv (by ring)
  have hi := integral_eq_zero_of_hasDerivAt_of_integrable hderiv
    (hfirst.sub hsecond) hbase
  rw [integral_sub hfirst hsecond] at hi
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal)≠0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal)≠0)]
  simpa only [smul_eq_mul] using (sub_eq_zero.mp hi).symm

theorem gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n+1))
    {F D : (Fin (n+1) → ℝ) → ℝ} (hF : Measurable F) (hD : Measurable D)
    {C E : ℝ} (hC : ∀g,|F g|≤C) (hE : ∀g,|D g|≤E)
    (hd : ∀(y : Fin n → ℝ) t,
      HasDerivAt (fun t => F (i.insertNth t y)) (D (i.insertNth t y)) t) :
    (∫g,g i*F g ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫g,D g ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  have hm := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hmap (p : ℝ × (Fin n → ℝ)) : e.symm p=i.insertNth p.1 p.2 := rfl
  have hf : Measurable (fun p : ℝ × (Fin n → ℝ) => F (i.insertNth p.1 p.2)) :=
    hF.comp e.symm.measurable
  have hdM : Measurable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2)) :=
    hD.comp e.symm.measurable
  have hi : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1*F (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) :=
    (IsGaussian.integrable_id (μ:=gaussianReal 0 1)).comp_fst ν |>.mul_bdd
      hf.aestronglyMeasurable (ae_of_all _ fun p => hC _)
  have hiD : Integrable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) :=
    Integrable.of_bound hdM.aestronglyMeasurable E
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hE (i.insertNth p.1 p.2))
  rw [← hm.integral_comp' (fun g => g i*F g), ← hm.integral_comp' D]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_apply_same]
  change (∫p,p.1*F (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν) =
    ∫p,D (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν
  rw [integral_prod_symm _ hi,integral_prod_symm _ hiD]
  apply integral_congr_ae
  exact ae_of_all _ fun y => gaussian_integration_by_parts (hd y)
    (hdM.comp (measurable_id.prodMk measurable_const)) (fun t => hC _) (fun t => hE _)

end IsingPerceptron.Main

end

end OAI
