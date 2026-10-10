import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCoefficientJets
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetTimeDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Smooth time dependence of the bounded spatial jets of actual coefficients. -/

noncomputable section
namespace ForcedComputation

open Set Filter ShearFlows
open scoped Topology ContDiff BoundedContinuousFunction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Repeated time differentiation, retaining space as a parameter. -/
def timePartial : ℕ → (ℝ × Plane → F) → ℝ × Plane → F
  | 0, f => f
  | n+1, f => fun p => fderiv ℝ (timePartial n f) p (1,0)

theorem timePartial_smooth {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (timePartial n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem timePartial_hasDerivAt {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => timePartial n f (s,x)) (timePartial (n+1) f (t,x)) t :=
  timeSlice_hasDerivAt (timePartial_smooth hf n) t x

theorem timePartial_periodic {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, PlanePeriodic (fun x => f (t,x))) (n : ℕ) (t : ℝ) :
    PlanePeriodic (fun x => timePartial n f (t,x)) := by
  induction n generalizing t with
  | zero => exact hp t
  | succ n ih =>
    intro x z
    exact congrArg (fun L : (ℝ × Plane) →L[ℝ] F => L (1,0))
      (planePeriodic_totalDerivative (timePartial_smooth hf n) ih t x z)

theorem timePartial_supported {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    {T : ℝ} (hT : 0 < T) {K : Set Plane}
    (hs : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, f (t,x) = 0)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : Plane) (hx : x ∉ K) :
    timePartial n f (t,x) = 0 := by
  induction n generalizing t with
  | zero => exact hs t ht x hx
  | succ n ih =>
    have hd : HasDerivWithinAt (fun _ : ℝ => (0 : F))
        (timePartial (n+1) f (t,x)) (Icc (0 : ℝ) T) t :=
      (timePartial_hasDerivAt hf n t x).hasDerivWithinAt.congr
        (fun s hs => (ih s hs).symm) (ih t ht).symm
    exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ hd
      (hasDerivWithinAt_const t (Icc (0 : ℝ) T) (0 : F))

namespace CoefficientTimeJets

abbrev Jet (k : ℕ) := BoundedSpatialJets.Space Plane ℝ k

/-- Constant continuation is used only to state derivatives within the closed time slab. -/
def extend {T : ℝ} (hT : 0 ≤ T) {k : ℕ} (J : C(Icc (0 : ℝ) T, Jet k))
    (t : ℝ) : Jet k := J (projIcc 0 T hT t)

theorem continuous_extend {T : ℝ} (hT : 0 ≤ T) {k : ℕ}
    (J : C(Icc (0 : ℝ) T, Jet k)) : Continuous (extend hT J) :=
  J.continuous.comp continuous_projIcc

theorem extend_eq {T : ℝ} (hT : 0 ≤ T) {k : ℕ}
    (J : C(Icc (0 : ℝ) T, Jet k)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    extend hT J t = J ⟨t,ht⟩ := by
  unfold extend
  rw [projIcc_of_mem hT ht]

/-- The next actual coefficient derivative supplies the derivative of its jet curve. -/
theorem hasDerivWithinAt_extend {T : ℝ} (hT : 0 ≤ T) {k : ℕ}
    {f : ℝ × Plane → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (J J' : C(Icc (0 : ℝ) T, Jet k))
    (hJ : ∀ t x, BoundedSpatialJets.function Plane ℝ k (J t) x = timePartial n f (t.val,x))
    (hJ' : ∀ t x, BoundedSpatialJets.function Plane ℝ k (J' t) x = timePartial (n+1) f (t.val,x))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (extend hT J) (extend hT J' t) (Icc (0 : ℝ) T) t := by
  apply BoundedSpatialJets.hasDerivWithinAt_of_pointwise_derivative k
    (extend hT J) (extend hT J') (continuous_extend hT J) (continuous_extend hT J') _ ht
  intro s hs x
  have he : (fun r => BoundedSpatialJets.function Plane ℝ k (extend hT J r) x)
      =ᶠ[𝓝 s] (fun r => timePartial n f (r,x)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    rw [extend_eq hT J ⟨hr.1.le,hr.2.le⟩]
    exact hJ ⟨r,hr.1.le,hr.2.le⟩ x
  have hd := (timePartial_hasDerivAt hf n s x).congr_of_eventuallyEq he
  rw [extend_eq hT J' ⟨hs.1.le,hs.2.le⟩, hJ']
  exact hd

/-- A continuous hierarchy of actual time derivatives gives all time regularity, at endpoints too. -/
theorem smooth_extend_of_representatives {T : ℝ} (hT : 0 < T) {k : ℕ}
    {f : ℝ × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (J : ℕ → C(Icc (0 : ℝ) T, Jet k))
    (hJ : ∀ n t x, BoundedSpatialJets.function Plane ℝ k (J n t) x = timePartial n f (t.val,x))
    (n : ℕ) : ContDiffOn ℝ ∞ (extend hT.le (J n)) (Icc (0 : ℝ) T) := by
  have hd (i : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    hasDerivWithinAt_extend hT.le hf i (J i) (J (i+1)) (hJ i) (hJ (i+1)) ht
  have hall : ∀ m : ℕ, ∀ i : ℕ,
      ContDiffOn ℝ m (extend hT.le (J i)) (Icc (0 : ℝ) T) := by
    intro m
    induction m with
    | zero => intro i; exact contDiffOn_zero.mpr (continuous_extend hT.le (J i)).continuousOn
    | succ m ih =>
      intro i
      rw [Nat.cast_add, Nat.cast_one,
        contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
      refine ⟨fun t ht => (hd i t ht).differentiableWithinAt, ?_, ?_⟩
      · simp
      · apply (ih (i+1)).congr
        intro t ht
        exact (hd i t ht).derivWithin (uniqueDiffOn_Icc hT t ht)
  exact contDiffOn_infty.mpr (fun m => hall m n)

/-- Smooth periodic scalar coefficients have continuous jets for every time derivative. -/
theorem exists_periodic {T : ℝ} (hT : 0 < T) (k : ℕ)
    {f : ℝ × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, PlanePeriodic (fun x => f (t,x))) :
    ∃ J : ℕ → C(Icc (0 : ℝ) T, Jet k),
      (∀ n t x, BoundedSpatialJets.function Plane ℝ k (J n t) x = timePartial n f (t.val,x)) ∧
      (∀ n, ContDiffOn ℝ ∞ (extend hT.le (J n)) (Icc (0 : ℝ) T)) := by
  have he (n : ℕ) := exists_periodic_jet_curve (timePartial_smooth hf n)
    (timePartial_periodic hf hp n) k T
  choose J hJ using he
  exact ⟨J, hJ, smooth_extend_of_representatives hT hf J hJ⟩

/-- Common compact spatial support is preserved by every time derivative on the slab. -/
theorem exists_supported {T : ℝ} (hT : 0 < T) (k : ℕ)
    {f : ℝ × Plane → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsCompact K)
    (hs : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, f (t,x) = 0) :
    ∃ J : ℕ → C(Icc (0 : ℝ) T, Jet k),
      (∀ n t x, BoundedSpatialJets.function Plane ℝ k (J n t) x = timePartial n f (t.val,x)) ∧
      (∀ n, ContDiffOn ℝ ∞ (extend hT.le (J n)) (Icc (0 : ℝ) T)) := by
  have he (n : ℕ) := exists_supported_jet_curve (timePartial_smooth hf n) hK T
    (timePartial_supported hf hT hs n) k
  choose J hJ using he
  exact ⟨J, hJ, smooth_extend_of_representatives hT hf J hJ⟩

private theorem extend_eq_of_representatives {T : ℝ} (hT : 0 ≤ T) {k : ℕ}
    (J J' : C(Icc (0 : ℝ) T, Jet k))
    (he : ∀ t x, BoundedSpatialJets.function Plane ℝ k (J t) x =
      BoundedSpatialJets.function Plane ℝ k (J' t) x) : extend hT J = extend hT J' := by
  funext t
  apply BoundedSpatialJets.function_injective Plane ℝ k
  apply BoundedContinuousFunction.ext
  intro x
  exact he _ x

/-- Smoothness holds for any representative, including the curves in compatible data. -/
theorem periodic_curve_smooth {T : ℝ} (hT : 0 < T) {k : ℕ}
    {f : ℝ × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, PlanePeriodic (fun x => f (t,x)))
    (J : C(Icc (0 : ℝ) T, Jet k))
    (hJ : ∀ t x, BoundedSpatialJets.function Plane ℝ k (J t) x = f (t.val,x)) :
    ContDiffOn ℝ ∞ (extend hT.le J) (Icc (0 : ℝ) T) := by
  obtain ⟨A,hA,hAs⟩ := exists_periodic hT k hf hp
  have he := extend_eq_of_representatives hT.le J (A 0) (fun t x => (hJ t x).trans (hA 0 t x).symm)
  rw [he]
  exact hAs 0

theorem supported_curve_smooth {T : ℝ} (hT : 0 < T) {k : ℕ}
    {f : ℝ × Plane → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsCompact K)
    (hs : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, f (t,x) = 0)
    (J : C(Icc (0 : ℝ) T, Jet k))
    (hJ : ∀ t x, BoundedSpatialJets.function Plane ℝ k (J t) x = f (t.val,x)) :
    ContDiffOn ℝ ∞ (extend hT.le J) (Icc (0 : ℝ) T) := by
  obtain ⟨A,hA,hAs⟩ := exists_supported hT k hf hK hs
  have he := extend_eq_of_representatives hT.le J (A 0) (fun t x => (hJ t x).trans (hA 0 t x).symm)
  rw [he]
  exact hAs 0

end CoefficientTimeJets
end ForcedComputation

end

end OAI
