import Mathlib
import OAI.Probability.SKFluctuations.AbsTiltedMeanLe

namespace OAI

/-! Terminal. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Type*} [Fintype S] [Nonempty S]

 

def SourceContinuation.terminal {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (v : E) : SourceContinuation v 1 := by
  let M : E → ℝ := fun x => ∑ s, spinWeight w φ x s * φ s v
  let Q : E → ℝ := fun x => ∑ s, spinWeight w φ x s * (φ s v)^2
  let H : E → ℝ := fun x => Q x - (M x)^2
  have hMs (n : ℕ) : BddSmooth n M :=
    BddSmooth.sum Finset.univ fun s _ => (bddSmooth_spinWeight hw φ n s).mul (BddSmooth.const n (φ s v))
  have hQs (n : ℕ) : BddSmooth n Q :=
    BddSmooth.sum Finset.univ fun s _ => (bddSmooth_spinWeight hw φ n s).mul (BddSmooth.const n ((φ s v)^2))
  have hHs (n : ℕ) : BddSmooth n H := by
    simpa only [H, pow_two] using (hQs n).sub ((hMs n).mul (hMs n))
  have hvar (x : E) : 0 ≤ Q x - (M x)^2 := by
    have he : (∑ s, spinWeight w φ x s * (φ s v - M x)^2) = Q x - (M x)^2 := by
      calc
        _ = ∑ s, (spinWeight w φ x s * (φ s v)^2 -
            2 * M x * (spinWeight w φ x s * φ s v) + (M x)^2 * spinWeight w φ x s) := by
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = Q x - (M x)^2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            sum_spinWeight hw φ x]
          change Q x - 2 * M x * M x + (M x)^2 * 1 = Q x - (M x)^2
          ring
    rw [← he]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (spinWeight_nonneg hw φ x s) (sq_nonneg _)
  refine { potential := spinLogPartition w φ, mean := M, secondMoment := Q, hessian := H
           regular := potentialRegularity_spinLogPartition hw φ
           mean_smooth := hMs, second_smooth := hQs, hessian_smooth := hHs
           first := hasDerivAt_spinLogPartition hw φ (v := v)
           mass_nonneg := by norm_num
           mass_le_one := le_rfl
           variance_nonneg := hvar
           lower := fun x => by dsimp [H]; simp only [one_mul, le_refl]
           upper := fun x => le_rfl
           second := ?_ }
  intro x t
  have hd := HasDerivAt.sum (u := Finset.univ) (fun s _ =>
    (hasDerivAt_spinWeight hw φ s x v t).mul_const (φ s v))
  have he : (∑ s, spinWeight w φ (x + t • v) s *
      (φ s v - M (x + t • v)) * φ s v) = H (x + t • v) := by
    calc
      _ = ∑ s, (spinWeight w φ (x + t • v) s * (φ s v)^2 -
          (spinWeight w φ (x + t • v) s * φ s v) * M (x + t • v)) := by
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = H (x + t • v) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        change Q (x + t • v) - M (x + t • v) * M (x + t • v) = _
        simp only [H, pow_two]
  simpa only [M, Finset.sum_fn] using hd.congr_deriv he

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

abbrev GaussianStep (ι : Type*) := ℝ × (ι → ℝ≥0)

def OrderedSteps (a : ℝ) : List (GaussianStep ι) → Prop
  | [] => 0 ≤ a ∧ a ≤ 1
  | (m, _) :: tail => 0 ≤ a ∧ a ≤ m ∧ 0 < m ∧ OrderedSteps m tail

 
def gaussianHierarchy (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    List (GaussianStep ι) → (ι → ℝ) → ℝ
  | [] => spinLogPartition w φ
  | (m, v) :: tail => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) m
      (gaussianHierarchy w φ tail)

 

def gaussianHierarchyMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) : List (GaussianStep ι) → (ι → ℝ) → ℝ
  | [] => fun x => ∑ s, spinWeight w φ x s * A s
  | (m, v) :: tail => shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) m
      (gaussianHierarchy w φ tail) (gaussianHierarchyMean w φ A tail)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
def SourceContinuation.weaken {v : E} {a b : ℝ} (T : SourceContinuation v a)
    (hb : 0 ≤ b) (hba : b ≤ a) : SourceContinuation v b where
  potential := T.potential
  mean := T.mean
  secondMoment := T.secondMoment
  hessian := T.hessian
  regular := T.regular
  mean_smooth := T.mean_smooth
  second_smooth := T.second_smooth
  hessian_smooth := T.hessian_smooth
  first := T.first
  second := T.second
  mass_nonneg := hb
  mass_le_one := hba.trans T.mass_le_one
  variance_nonneg := T.variance_nonneg
  lower x := (mul_le_mul_of_nonneg_right hba (T.variance_nonneg x)).trans (T.lower x)
  upper := T.upper

 

theorem gaussianHierarchy_source {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) :
    ∃ T : SourceContinuation v a,
      T.potential = gaussianHierarchy w φ steps ∧
      T.mean = gaussianHierarchyMean w φ (fun s => φ s v) steps ∧
      T.secondMoment = gaussianHierarchyMean w φ (fun s => (φ s v)^2) steps := by
  induction steps generalizing a with
  | nil =>
    exact ⟨(SourceContinuation.terminal hw φ v).weaken ha.1 ha.2, rfl, rfl, rfl⟩
  | cons step tail ih =>
    rcases step with ⟨m, q⟩
    obtain ⟨T, hF, hM, hQ⟩ := ih ha.2.2.2
    let ν := Measure.pi fun i => gaussianReal 0 (q i)
    let T' := (T.step ν (exponentialIncrement_gaussian q) m ha.2.2.1 le_rfl).weaken ha.1 ha.2.1
    refine ⟨T', ?_, ?_, ?_⟩
    · change shiftedContinuation ν m T.potential = _
      rw [hF]
      rfl
    · change shiftedMean ν m T.potential T.mean = _
      rw [hF, hM]
      rfl
    · change shiftedMean ν m T.potential T.secondMoment = _
      rw [hF, hQ]
      rfl

 

theorem gaussianHierarchy_hessian_bounds {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) :
    ∃ H : (ι → ℝ) → ℝ,
      (∀ x t, HasDerivAt (fun s : ℝ => gaussianHierarchy w φ steps (x + s • v))
        (gaussianHierarchyMean w φ (fun j => φ j v) steps (x + t • v)) t) ∧
      (∀ x t, HasDerivAt (fun s : ℝ => gaussianHierarchyMean w φ (fun j => φ j v) steps (x + s • v))
        (H (x + t • v)) t) ∧
      (∀ x, a * (gaussianHierarchyMean w φ (fun j => (φ j v)^2) steps x -
        (gaussianHierarchyMean w φ (fun j => φ j v) steps x)^2) ≤ H x) ∧
      (∀ x, H x ≤ gaussianHierarchyMean w φ (fun j => (φ j v)^2) steps x -
        (gaussianHierarchyMean w φ (fun j => φ j v) steps x)^2) := by
  obtain ⟨T, hF, hM, hQ⟩ := gaussianHierarchy_source hw φ v steps ha
  refine ⟨T.hessian, ?_, ?_, ?_, ?_⟩
  · simpa only [← hF, ← hM] using T.first
  · simpa only [← hM] using T.second
  · simpa only [← hM, ← hQ] using T.lower
  · simpa only [← hM, ← hQ] using T.upper

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BddSmooth.hasDerivAt_line {n : ℕ} {f : E → ℝ} (hf : BddSmooth (n+1) f)
    (x v : E) (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • v))
      (lineDeriv ℝ f (x + t • v) v) t := by
  obtain ⟨g, _, hd⟩ := hf.2 v
  have he (y : E) : lineDeriv ℝ f y v = g y := by
    apply HasLineDerivAt.lineDeriv
    simpa only [HasLineDerivAt, zero_smul, add_zero] using hd y 0
  rw [he]
  exact hd x t

theorem BddSmooth.lineDeriv_smooth {n : ℕ} {f : E → ℝ} (hf : BddSmooth (n+1) f)
    (v : E) : BddSmooth n (fun x => lineDeriv ℝ f x v) := by
  obtain ⟨g, hg, hd⟩ := hf.2 v
  have he : (fun x => lineDeriv ℝ f x v) = g := by
    funext x
    apply HasLineDerivAt.lineDeriv
    simpa only [HasLineDerivAt, zero_smul, add_zero] using hd x 0
  rwa [he]

 

theorem BddSmooth.lineDeriv_add {f : E → ℝ} (hf : BddSmooth 1 f) (x v w : E) :
    lineDeriv ℝ f x (v + w) = lineDeriv ℝ f x v + lineDeriv ℝ f x w := by
  let g := fun s t : ℝ => f (x + s • v + t • w)
  let g₁ := fun s t : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (lineDeriv ℝ f (x + s • v + t • w) v)
  let g₂ := fun s t : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (lineDeriv ℝ f (x + s • v + t • w) w)
  have hd₁ (p : ℝ × ℝ) : HasFDerivAt (fun s => g s p.2) (g₁ p.1 p.2) p.1 := by
    have h := (hf.hasDerivAt_line (x + p.2 • w) v p.1).hasFDerivAt
    simpa only [g, g₁, add_right_comm x] using h
  have hd₂ (p : ℝ × ℝ) : HasFDerivAt (fun t => g p.1 t) (g₂ p.1 p.2) p.2 :=
    (hf.hasDerivAt_line (x + p.1 • v) w p.2).hasFDerivAt
  have hc₁ : Continuous (fun p : ℝ × ℝ => g₁ p.1 p.2) := by
    have h := (hf.lineDeriv_smooth v).continuous
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
      (h.comp (by fun_prop))
  have hc₂ : Continuous (fun p : ℝ × ℝ => g₂ p.1 p.2) := by
    have h := (hf.lineDeriv_smooth w).continuous
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
      (h.comp (by fun_prop))
  have hp := hasStrictFDerivAt_uncurry_coprod
    (u := ((0, 0) : ℝ × ℝ)) (f := g) (f₁ := g₁) (f₂ := g₂) (Eventually.of_forall hd₁) (Eventually.of_forall hd₂)
    hc₁.continuousAt hc₂.continuousAt
  have hd := hp.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, s)) 0 ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  change HasDerivAt (fun s : ℝ => g s s) ((g₁ 0 0) 1 + (g₂ 0 0) 1) 0 at hd
  have he (s : ℝ) : x + s • (v + w) = x + s • v + s • w := by module
  have hline : HasLineDerivAt ℝ f (lineDeriv ℝ f x v + lineDeriv ℝ f x w) x (v + w) := by
    simpa only [HasLineDerivAt, Function.comp_def, Function.uncurry_def, g, g₁, g₂,
      ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
      zero_smul, add_zero, one_smul, he] using hd
  exact hline.lineDeriv

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def BddSmooth.lineDerivLinear {f : E → ℝ} (hf : BddSmooth 1 f)
    (x : E) : E →ₗ[ℝ] ℝ where
  toFun := lineDeriv ℝ f x
  map_add' := hf.lineDeriv_add x
  map_smul' := by intro c v; exact lineDeriv_smul

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BddSmooth.lineDeriv_pi {f : (ι → ℝ) → ℝ} (hf : BddSmooth 1 f)
    (x v : ι → ℝ) : lineDeriv ℝ f x v =
      ∑ i, v i * lineDeriv ℝ f x (Pi.single i 1) := by
  let D := hf.lineDerivLinear x
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  change D v = _
  conv_lhs => rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact D.map_smul (v i) (Pi.single i 1)

theorem BddSmooth.uniform_first_bound {f : (ι → ℝ) → ℝ} (hf : BddSmooth 1 f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x v, |lineDeriv ℝ f x v| ≤ B * ‖v‖ := by
  choose C hC hb using fun i => (hf.lineDeriv_smooth (Pi.single i 1)).bound
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro x v
  rw [hf.lineDeriv_pi x v, Finset.sum_mul]
  calc
    _ ≤ ∑ i, |v i * lineDeriv ℝ f x (Pi.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C i * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_comm]
      exact mul_le_mul (hb i x) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (abs_nonneg _) (hC i)

theorem BddSmooth.second_pi {f : (ι → ℝ) → ℝ} (hf : BddSmooth 2 f)
    (x v : ι → ℝ) : lineDeriv ℝ (fun y => lineDeriv ℝ f y v) x v =
      ∑ i, v i * lineDeriv ℝ (fun y => lineDeriv ℝ f y (Pi.single i 1)) x v := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((hf.lineDeriv_smooth (Pi.single i 1)).hasDerivAt_line x v 0).const_mul (v i))
  apply HasLineDerivAt.lineDeriv
  have he : (fun t : ℝ => lineDeriv ℝ f (x + t • v) v) =
      fun t : ℝ => ∑ i, v i * lineDeriv ℝ f (x + t • v) (Pi.single i 1) :=
    funext fun t => hf.down.lineDeriv_pi (x + t • v) v
  rw [HasLineDerivAt, he]
  simpa only [Finset.sum_fn, zero_smul, add_zero] using hd

theorem BddSmooth.uniform_second_bound {f : (ι → ℝ) → ℝ} (hf : BddSmooth 2 f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x v, |lineDeriv ℝ (fun y => lineDeriv ℝ f y v) x v| ≤ B * ‖v‖ ^ 2 := by
  choose C hC hb using fun i => (hf.lineDeriv_smooth (Pi.single i 1)).uniform_first_bound
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro x v
  rw [hf.second_pi x v, Finset.sum_mul]
  calc
    _ ≤ ∑ i, |v i * lineDeriv ℝ (fun y => lineDeriv ℝ f y (Pi.single i 1)) x v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C i * ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      calc
        _ ≤ ‖v‖ * (C i * ‖v‖) := mul_le_mul
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i) (hb i x v)
          (abs_nonneg _) (norm_nonneg _)
        _ = C i * ‖v‖ ^ 2 := by ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 
theorem gaussianHierarchy_regular {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (n : ℕ) :
    PotentialRegularity n (gaussianHierarchy w φ steps) := by
  obtain ⟨T, hF, _, _⟩ := gaussianHierarchy_source hw φ 0 steps ha
  simpa only [← hF] using T.regular n

theorem gaussianHierarchy_integrable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (m : ℝ) (q : ι → ℝ≥0) (x : ι → ℝ) :
    Integrable (fun z => Real.exp (m * gaussianHierarchy w φ steps (x + z)))
      (Measure.pi fun i => gaussianReal 0 (q i)) := by
  obtain ⟨C, hC⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  exact (exponentialIncrement_gaussian q).integrable_shift hC m x

theorem gaussianHierarchyMean_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (n : ℕ) :
    BddSmooth n (gaussianHierarchyMean w φ A steps) := by
  induction steps generalizing a with
  | nil => exact BddSmooth.sum Finset.univ fun s _ =>
      (bddSmooth_spinWeight hw φ n s).mul (BddSmooth.const n (A s))
  | cons step tail ih =>
    rcases step with ⟨m, q⟩
    exact (ih ha.2.2.2).shiftedMean (gaussianHierarchy_regular hw φ tail ha.2.2.2 n)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q)

theorem gaussianHierarchy_hasDerivAt {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussianHierarchy w φ steps (x + s • v))
      (gaussianHierarchyMean w φ (fun j => φ j v) steps (x + t • v)) t := by
  obtain ⟨T, hF, hM, _⟩ := gaussianHierarchy_source hw φ v steps ha
  simpa only [← hF, ← hM] using T.first x t

 

def gaussianHierarchyResponse (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (v : ι → ℝ) : List (GaussianStep ι) → (ι → ℝ) → ℝ
  | [] => fun x => (∑ s, spinWeight w φ x s * A s * φ s v) -
      gaussianHierarchyMean w φ A [] x * gaussianHierarchyMean w φ (fun s => φ s v) [] x
  | (m, q) :: tail => fun x =>
      let ν := Measure.pi fun i => gaussianReal 0 (q i)
      let F := gaussianHierarchy w φ tail
      let MA := gaussianHierarchyMean w φ A tail
      let MV := gaussianHierarchyMean w φ (fun s => φ s v) tail
      shiftedMean ν m F (gaussianHierarchyResponse w φ A v tail) x + m *
        (shiftedMean ν m F (fun y => MA y * MV y) x -
          gaussianHierarchyMean w φ A ((m, q) :: tail) x *
            gaussianHierarchyMean w φ (fun s => φ s v) ((m, q) :: tail) x)

theorem gaussianHierarchyResponse_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (v : ι → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (n : ℕ) :
    BddSmooth n (gaussianHierarchyResponse w φ A v steps) := by
  induction steps generalizing a with
  | nil =>
    exact (BddSmooth.sum Finset.univ fun s _ =>
      ((bddSmooth_spinWeight hw φ n s).mul (BddSmooth.const n (A s))).mul
        (BddSmooth.const n (φ s v))).sub
      ((gaussianHierarchyMean_smooth hw φ A [] ha n).mul
        (gaussianHierarchyMean_smooth hw φ (fun s => φ s v) [] ha n))
  | cons step tail ih =>
    rcases step with ⟨m, q⟩
    have hR := gaussianHierarchy_regular hw φ tail ha.2.2.2 n
    have hi := gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q
    exact ((ih ha.2.2.2).shiftedMean hR hi).add
      (((((gaussianHierarchyMean_smooth hw φ A tail ha.2.2.2 n).mul
        (gaussianHierarchyMean_smooth hw φ (fun s => φ s v) tail ha.2.2.2 n)).shiftedMean hR hi).sub
      ((gaussianHierarchyMean_smooth hw φ A ((m,q)::tail) ha n).mul
        (gaussianHierarchyMean_smooth hw φ (fun s => φ s v) ((m,q)::tail) ha n))).const_mul m)

theorem gaussianHierarchyMean_hasDerivAt {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussianHierarchyMean w φ A steps (x + s • v))
      (gaussianHierarchyResponse w φ A v steps (x + t • v)) t := by
  induction steps generalizing a x t with
  | nil =>
    have hd := HasDerivAt.sum (u := Finset.univ) (fun s _ =>
      (hasDerivAt_spinWeight hw φ s x v t).mul_const (A s))
    simp only [Finset.sum_fn] at hd
    simp only [gaussianHierarchyMean]
    apply hd.congr_deriv
    dsimp only [gaussianHierarchyResponse, gaussianHierarchyMean]
    calc
      _ = ∑ s, (spinWeight w φ (x + t • v) s * A s * φ s v -
          spinWeight w φ (x + t • v) s * A s *
            (∑ j, spinWeight w φ (x + t • v) j * φ j v)) := by
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  | cons step tail ih =>
    rcases step with ⟨m, q⟩
    have hF := gaussianHierarchy_regular hw φ tail ha.2.2.2 0
    obtain ⟨C, hC⟩ := hF.1
    have hA := gaussianHierarchyMean_smooth hw φ A tail ha.2.2.2 0
    have hV := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) tail ha.2.2.2 0
    have hD := gaussianHierarchyResponse_smooth hw φ A v tail ha.2.2.2 0
    obtain ⟨B, hB, hb⟩ := hV.bound
    obtain ⟨D, hD', hd⟩ := hA.bound
    obtain ⟨L, hL, hl⟩ := hD.bound
    exact hasDerivAt_shiftedMean hB (add_nonneg hD' hL)
      hC.continuous hV.continuous hA.continuous hD.continuous
      (gaussianHierarchy_hasDerivAt hw φ tail ha.2.2.2 · v ·)
      (ih ha.2.2.2) hb (fun y => (hd y).trans (by linarith))
      (fun y => (hl y).trans (by linarith))
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q) x t

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 
def gaussianHierarchyHessian (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (x v u : ι → ℝ) : ℝ :=
  gaussianHierarchyResponse w φ (fun s => φ s v) u steps x

theorem gaussianHierarchyResponse_eq_lineDeriv {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v : ι → ℝ) :
    gaussianHierarchyResponse w φ A v steps x =
      lineDeriv ℝ (gaussianHierarchyMean w φ A steps) x v := by
  symm
  apply HasLineDerivAt.lineDeriv
  simpa only [HasLineDerivAt, zero_smul, add_zero] using
    gaussianHierarchyMean_hasDerivAt hw φ A steps ha x v 0

omit [Nonempty S] in
theorem gaussianHierarchyHessian_symm (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (x v u : ι → ℝ) :
    gaussianHierarchyHessian w φ steps x v u = gaussianHierarchyHessian w φ steps x u v := by
  unfold gaussianHierarchyHessian
  induction steps generalizing x with
  | nil =>
    dsimp only [gaussianHierarchyResponse]
    have he : (∑ s, spinWeight w φ x s * φ s v * φ s u) =
        (∑ s, spinWeight w φ x s * φ s u * φ s v) := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [he, mul_comm (gaussianHierarchyMean w φ (fun s => φ s v) [] x)]
  | cons step tail ih =>
    rcases step with ⟨m, q⟩
    have hr : gaussianHierarchyResponse w φ (fun s => φ s v) u tail =
        gaussianHierarchyResponse w φ (fun s => φ s u) v tail := funext ih
    have hp : (fun y => gaussianHierarchyMean w φ (fun s => φ s v) tail y *
        gaussianHierarchyMean w φ (fun s => φ s u) tail y) =
        (fun y => gaussianHierarchyMean w φ (fun s => φ s u) tail y *
        gaussianHierarchyMean w φ (fun s => φ s v) tail y) := funext fun _ => mul_comm _ _
    simp only [gaussianHierarchyResponse, hr, hp]
    rw [mul_comm (gaussianHierarchyMean w φ (fun s => φ s v) ((m,q)::tail) x)]

theorem gaussianHierarchyHessian_add_right {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v u z : ι → ℝ) :
    gaussianHierarchyHessian w φ steps x v (u + z) =
      gaussianHierarchyHessian w φ steps x v u + gaussianHierarchyHessian w φ steps x v z := by
  simp only [gaussianHierarchyHessian, gaussianHierarchyResponse_eq_lineDeriv hw φ _ steps ha]
  exact (gaussianHierarchyMean_smooth hw φ (fun s => φ s v) steps ha 1).lineDeriv_add x u z

theorem gaussianHierarchyHessian_smul_right {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v u : ι → ℝ) (c : ℝ) :
    gaussianHierarchyHessian w φ steps x v (c • u) =
      c * gaussianHierarchyHessian w φ steps x v u := by
  simp only [gaussianHierarchyHessian, gaussianHierarchyResponse_eq_lineDeriv hw φ _ steps ha,
    lineDeriv_smul, smul_eq_mul]

theorem gaussianHierarchyHessian_add_left {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v u z : ι → ℝ) :
    gaussianHierarchyHessian w φ steps x (v + u) z =
      gaussianHierarchyHessian w φ steps x v z + gaussianHierarchyHessian w φ steps x u z := by
  rw [gaussianHierarchyHessian_symm w φ steps x (v+u) z,
    gaussianHierarchyHessian_add_right hw φ steps ha,
    gaussianHierarchyHessian_symm w φ steps x z v,
    gaussianHierarchyHessian_symm w φ steps x z u]

theorem gaussianHierarchyHessian_smul_left {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v u : ι → ℝ) (c : ℝ) :
    gaussianHierarchyHessian w φ steps x (c • v) u =
      c * gaussianHierarchyHessian w φ steps x v u := by
  rw [gaussianHierarchyHessian_symm w φ steps x (c • v) u,
    gaussianHierarchyHessian_smul_right hw φ steps ha,
    gaussianHierarchyHessian_symm w φ steps x u v]

theorem gaussianHierarchyHessian_bounds {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v : ι → ℝ) :
    a * (gaussianHierarchyMean w φ (fun s => (φ s v)^2) steps x -
      (gaussianHierarchyMean w φ (fun s => φ s v) steps x)^2) ≤
        gaussianHierarchyHessian w φ steps x v v ∧
    gaussianHierarchyHessian w φ steps x v v ≤
      gaussianHierarchyMean w φ (fun s => (φ s v)^2) steps x -
      (gaussianHierarchyMean w φ (fun s => φ s v) steps x)^2 := by
  obtain ⟨T, hF, hM, hQ⟩ := gaussianHierarchy_source hw φ v steps ha
  have hd := gaussianHierarchyMean_hasDerivAt hw φ (fun s => φ s v) steps ha x v 0
  rw [← hM] at hd
  have he : gaussianHierarchyHessian w φ steps x v v = T.hessian x := by
    have h := hd.unique (T.second x 0)
    simpa only [zero_smul, add_zero, gaussianHierarchyHessian] using h
  rw [he, ← hM, ← hQ]
  exact ⟨T.lower x, T.upper x⟩

theorem gaussianHierarchyHessian_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v : ι → ℝ) :
    0 ≤ gaussianHierarchyHessian w φ steps x v v := by
  obtain ⟨T, _, hM, hQ⟩ := gaussianHierarchy_source hw φ v steps ha
  have hlo := (gaussianHierarchyHessian_bounds hw φ steps ha x v).1
  rw [← hM, ← hQ] at hlo
  exact (mul_nonneg T.mass_nonneg (T.variance_nonneg x)).trans hlo

 

theorem gaussianHierarchyHessian_block_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v u : ι → ℝ) (c : ℝ) :
    0 ≤ gaussianHierarchyHessian w φ steps x v v -
      2 * c * gaussianHierarchyHessian w φ steps x v u +
      c^2 * gaussianHierarchyHessian w φ steps x u u := by
  have h := gaussianHierarchyHessian_nonneg hw φ steps ha x (v + (-c) • u)
  rw [gaussianHierarchyHessian_add_left hw φ steps ha,
    gaussianHierarchyHessian_smul_left hw φ steps ha,
    gaussianHierarchyHessian_add_right hw φ steps ha,
    gaussianHierarchyHessian_smul_right hw φ steps ha,
    gaussianHierarchyHessian_add_right hw φ steps ha,
    gaussianHierarchyHessian_smul_right hw φ steps ha,
    gaussianHierarchyHessian_symm w φ steps x u v] at h
  nlinarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem BddSmooth.compCLM {n : ℕ} {f : E → ℝ} (hf : BddSmooth n f)
    (L : D →L[ℝ] E) : BddSmooth n (fun x => f (L x)) := by
  induction n generalizing f with
  | zero =>
    obtain ⟨B, hB, hb⟩ := hf.bound
    exact ⟨hf.continuous.comp L.continuous, B, hB, fun x => hb (L x)⟩
  | succ n ih =>
    refine ⟨ih hf.1, fun v => ?_⟩
    obtain ⟨g, hg, hd⟩ := hf.2 (L v)
    refine ⟨fun x => g (L x), ih hg, fun x t => ?_⟩
    simpa only [map_add, map_smul] using hd (L x) t

variable {ι S κ : Type*} [Fintype ι] [Fintype S] [Nonempty S] [Fintype κ]

theorem gaussianHierarchyHessian_sum_left {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x u : ι → ℝ)
    {α : Type*} (s : Finset α) (v : α → ι → ℝ) :
    gaussianHierarchyHessian w φ steps x (∑ i ∈ s, v i) u =
      ∑ i ∈ s, gaussianHierarchyHessian w φ steps x (v i) u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using gaussianHierarchyHessian_smul_left hw φ steps ha x (0 : ι → ℝ) u 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, gaussianHierarchyHessian_add_left hw φ steps ha, ih]

 

def driverMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (L : D →L[ℝ] (ι → ℝ)) (V : κ → ι → ℝ)
    (x : D) (i : κ) : ℝ := gaussianHierarchyMean w φ (fun s => φ s (V i)) steps (L x)

def driverSource (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (L : D →L[ℝ] (ι → ℝ)) (V : κ → ι → ℝ)
    (σ : S) (x : D) : ι → ℝ :=
  ∑ i, (φ σ (V i) - driverMean w φ steps L V x i) • V i

 
def driverObservable (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (L : D →L[ℝ] (ι → ℝ)) (V : κ → ι → ℝ)
    (σ : S) (x : D) : ℝ :=
  ∑ i, (φ σ (V i) * driverMean w φ steps L V x i - (driverMean w φ steps L V x i)^2 / 2)

omit [Fintype κ] in
theorem driverMean_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (L : D →L[ℝ] (ι → ℝ))
    (V : κ → ι → ℝ) (i : κ) (n : ℕ) :
    BddSmooth n (fun x => driverMean w φ steps L V x i) :=
  (gaussianHierarchyMean_smooth hw φ _ steps ha n).compCLM L

theorem driverObservable_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (L : D →L[ℝ] (ι → ℝ))
    (V : κ → ι → ℝ) (σ : S) (n : ℕ) :
    BddSmooth n (driverObservable w φ steps L V σ) := by
  apply BddSmooth.sum Finset.univ
  intro i _
  have h := driverMean_smooth hw φ steps ha L V i n
  convert (h.const_mul (φ σ (V i))).sub ((h.mul h).const_mul (1/2)) using 1
  funext x
  ring

omit [Fintype κ] in
theorem driverMean_hasDerivAt {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (L : D →L[ℝ] (ι → ℝ))
    (V : κ → ι → ℝ) (x v : D) (i : κ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => driverMean w φ steps L V (x + s • v) i)
      (gaussianHierarchyHessian w φ steps (L (x + t • v)) (V i) (L v)) t := by
  simpa only [driverMean, gaussianHierarchyHessian, map_add, map_smul] using
    gaussianHierarchyMean_hasDerivAt hw φ (fun s => φ s (V i)) steps ha (L x) (L v) t

theorem driverObservable_hasDerivAt {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (L : D →L[ℝ] (ι → ℝ))
    (V : κ → ι → ℝ) (σ : S) (x v : D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => driverObservable w φ steps L V σ (x + s • v))
      (gaussianHierarchyHessian w φ steps (L (x + t • v))
        (driverSource w φ steps L V σ (x + t • v)) (L v)) t := by
  have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    ((driverMean_hasDerivAt hw φ steps ha L V x v i t).const_mul (φ σ (V i))).sub
      (((driverMean_hasDerivAt hw φ steps ha L V x v i t).pow 2).div_const 2)
  simp only [Finset.sum_fn] at h
  have he : gaussianHierarchyHessian w φ steps (L (x + t • v))
      (driverSource w φ steps L V σ (x + t • v)) (L v) =
      ∑ i, (φ σ (V i) * gaussianHierarchyHessian w φ steps (L (x + t • v)) (V i) (L v) -
        (2 : ℝ) * driverMean w φ steps L V (x + t • v) i ^ (2 - 1) *
          gaussianHierarchyHessian w φ steps (L (x + t • v)) (V i) (L v) / 2) := by
    rw [driverSource, gaussianHierarchyHessian_sum_left hw φ steps ha]
    apply Finset.sum_congr rfl
    intro i _
    rw [gaussianHierarchyHessian_smul_left hw φ steps ha]
    ring
  rw [he]
  exact h

 

def driverEnergy (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (L : D →L[ℝ] (ι → ℝ)) (V : κ → ι → ℝ)
    (σ : S) (x : D) : ℝ :=
  ∑ i, ∑ j, (φ σ (V i) - driverMean w φ steps L V x i) *
    (φ σ (V j) - driverMean w φ steps L V x j) *
      gaussianHierarchyHessian w φ steps (L x) (V i) (V j)

theorem driverEnergy_eq {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (L : D →L[ℝ] (ι → ℝ))
    (V : κ → ι → ℝ) (σ : S) (x : D) :
    driverEnergy w φ steps L V σ x =
      gaussianHierarchyHessian w φ steps (L x) (driverSource w φ steps L V σ x)
        (driverSource w φ steps L V σ x) := by
  rw [driverSource, gaussianHierarchyHessian_sum_left hw φ steps ha]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussianHierarchyHessian_smul_left hw φ steps ha,
    gaussianHierarchyHessian_symm w φ steps (L x) (V i),
    gaussianHierarchyHessian_sum_left hw φ steps ha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussianHierarchyHessian_smul_left hw φ steps ha,
    gaussianHierarchyHessian_symm w φ steps (L x) (V j) (V i)]
  ring

theorem driverEnergy_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (L : D →L[ℝ] (ι → ℝ))
    (V : κ → ι → ℝ) (σ : S) (n : ℕ) :
    BddSmooth n (driverEnergy w φ steps L V σ) := by
  apply BddSmooth.sum Finset.univ
  intro i _
  apply BddSmooth.sum Finset.univ
  intro j _
  exact (((BddSmooth.const n _).sub (driverMean_smooth hw φ steps ha L V i n)).mul
    ((BddSmooth.const n _).sub (driverMean_smooth hw φ steps ha L V j n))).mul
      ((gaussianHierarchyResponse_smooth hw φ _ (V j) steps ha n).compCLM L)

end SKFluctuations.Hierarchy

end

end OAI
