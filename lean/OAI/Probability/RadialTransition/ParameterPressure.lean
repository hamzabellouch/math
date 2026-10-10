import OAI.Probability.RadialTransition.FamilyIdeal

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

abbrev Parameter := EuclideanSpace ℝ (Fin 2)
def parameter (β h : ℝ) : Parameter := WithLp.toLp 2 ![β,h]
def positiveParameters : Set Parameter := {x | 0 < x 0}
def onParameters (Q : Pressure) (x : Parameter) : ℝ := Q (x 0) (x 1)

@[simp] lemma parameter_zero (β h : ℝ) : parameter β h 0 = β := rfl
@[simp] lemma parameter_one (β h : ℝ) : parameter β h 1 = h := rfl
@[simp] lemma parameter_eta (x : Parameter) : parameter (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

lemma parameter_inner (x y : Parameter) : inner ℝ x y = x 0*y 0+x 1*y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma parameter_coord_abs_le (x : Parameter) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2:ℝ≥0∞)) x i

lemma parameter_norm_le (x : Parameter) : ‖x‖ ≤ |x 0|+|x 1| := by
  have hh : ‖x‖^2 = |x 0|^2+|x 1|^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  nlinarith [norm_nonneg x, abs_nonneg (x 0), abs_nonneg (x 1),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

lemma continuous_parameter {X : Type uX} [TopologicalSpace X] (β h : X → ℝ) (hβ : Continuous β) (hh : Continuous h) :
    Continuous (fun x => parameter (β x) (h x)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact hβ
  · exact hh

lemma isOpen_positiveParameters : IsOpen positiveParameters := by
  exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) (0:Fin 2))

lemma convex_positiveParameters : Convex ℝ positiveParameters := by
  intro x hx y hy a b ha hb hab
  change 0 < a*x 0+b*y 0
  have hh := lt_min (show 0 < x 0 from hx) (show 0 < y 0 from hy)
  have hm := mul_pos (show 0 < a+b by linarith) hh
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (x 0) (y 0)) ha
  have h2 := mul_le_mul_of_nonneg_left (min_le_right (x 0) (y 0)) hb
  nlinarith

lemma pressureSupport_iff {Q : Pressure} {x v : Parameter} :
    pressureSupport Q (x 0) (x 1) (v 0) (v 1) ↔
      SupportsOn (onParameters Q) positiveParameters x v := by
  constructor
  · intro hs y hy
    have hh := hs (y 0) (y 1) hy
    simpa only [onParameters, parameter_inner, PiLp.sub_apply, add_assoc] using hh
  · intro hs β h hβ
    have hh := hs (parameter β h) hβ
    simpa only [onParameters, parameter_inner, PiLp.sub_apply, parameter_zero, parameter_one, add_assoc] using hh

lemma convexOn_grandPressure {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t : ℝ} (hst : StableWith φ B) (ht : 0 < t)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → φ r ≤ 0) :
    ConvexOn ℝ positiveParameters (onParameters (grandPressure φ t)) := by
  refine ⟨convex_positiveParameters, ?_⟩
  intro x hx y hy a b ha hbb hab
  exact grandPressure_convex_mix hφ hb hst ht hc hx.le hy.le (x 1) (y 1) ha hbb hab

lemma convexOn_attractionBranch {Q : Pressure} (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (a u : ℝ) : ConvexOn ℝ positiveParameters (onParameters (attractionBranch Q a u)) := by
  refine ⟨convex_positiveParameters, ?_⟩
  intro x hx y hy c d hc hd hcd
  have hh := hQ.2 (show parameter (x 0) (x 1+x 0*a*u) ∈ positiveParameters from hx)
    (show parameter (y 0) (y 1+y 0*a*u) ∈ positiveParameters from hy) hc hd hcd
  have he : c • parameter (x 0) (x 1+x 0*a*u)+d • parameter (y 0) (y 1+y 0*a*u) =
      parameter (c*x 0+d*y 0) (c*x 1+d*y 1+(c*x 0+d*y 0)*a*u) := by
    ext i
    fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply]; ring
  rw [he] at hh
  dsimp only [onParameters, attractionBranch, parameter_zero, parameter_one] at hh ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hh ⊢
  nlinarith

lemma convexOn_idealAttraction {Q : Pressure} (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    {a : ℝ} (hactive : ∀ β h, 0 < β → ∃ u, ActiveShift Q a β h u) :
    ConvexOn ℝ positiveParameters (onParameters (idealAttraction Q a)) := by
  refine ⟨convex_positiveParameters, ?_⟩
  intro x hx y hy c d hc hd hcd
  have hz := convex_positiveParameters hx hy hc hd hcd
  obtain ⟨u, hu⟩ := hactive _ _ hz
  obtain ⟨v, hv⟩ := hactive _ _ hx
  obtain ⟨w, hw⟩ := hactive _ _ hy
  have hh := (convexOn_attractionBranch hQ a u).2 hx hy hc hd hcd
  change idealAttraction Q a _ _ ≤ c*idealAttraction Q a _ _+d*idealAttraction Q a _ _
  rw [idealAttraction_eq_of_active hu, idealAttraction_eq_of_active hv, idealAttraction_eq_of_active hw]
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hv u) hc) (mul_le_mul_of_nonneg_left (hw u) hd))

end RadialTransition
end

end OAI
