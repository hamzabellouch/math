import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolventEquation
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1

namespace OAI

/-! Closure of the actual manufactured-well inequality on the planar
Sobolev graph. The bounded potential acts on actual L² classes, and the
form is continuous in the function-and-gradient norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

namespace PlanarSobolev

def originalIntegral (f : PlanarPosition → ℝ) : ℝ := ∫ x, f x

private abbrev originalMeasurable : MeasurableSpace PlanarPosition := inferInstance

private abbrev originalBorel : @BorelSpace PlanarPosition _ originalMeasurable := inferInstance

def originalIntegrable (f : PlanarPosition → ℝ) : Prop := Integrable f

theorem planar_integrable_change_borel
    (m : MeasurableSpace PlanarPosition) (hm : @BorelSpace PlanarPosition _ m)
    (f : PlanarPosition → ℝ) :
    (letI : MeasurableSpace PlanarPosition := m
     letI : BorelSpace PlanarPosition := hm
     letI : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
     Integrable f) ↔ originalIntegrable f := by
  have he : m = originalMeasurable :=
    hm.measurable_eq.trans originalBorel.measurable_eq.symm
  cases he
  rfl

theorem planar_integral_change_borel
    (m : MeasurableSpace PlanarPosition) (hm : @BorelSpace PlanarPosition _ m)
    (f : PlanarPosition → ℝ) :
    (letI : MeasurableSpace PlanarPosition := m
     letI : BorelSpace PlanarPosition := hm
     letI : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
     ∫ x, f x) = originalIntegral f := by
  have he : m = originalMeasurable :=
    hm.measurable_eq.trans originalBorel.measurable_eq.symm
  cases he
  rfl

local instance : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance : BorelSpace PlanarPosition := ⟨rfl⟩
local instance : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

abbrev Sobolev := RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
  (μ := (volume : Measure PlanarPosition)) (E := PlanarPosition)

abbrev Target := Lp ℝ 2 (volume : Measure PlanarPosition) ×
  Lp PlanarPosition 2 (volume : Measure PlanarPosition)

abbrev Test := RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c
  (E := PlanarPosition)

private theorem well_bounded : ∃ B : ℝ, ∀ x, ‖manufacturedPlanarWell x‖ ≤ B :=
  manufacturedPlanarWell_C7.continuous.bounded_above_of_compact_support
    manufacturedPlanarWell_hasCompactSupport

def wellBound : ℝ := Classical.choose well_bounded

theorem wellBound_spec (x : PlanarPosition) :
    ‖manufacturedPlanarWell x‖ ≤ wellBound := Classical.choose_spec well_bounded x

theorem wellBound_nonnegative : 0 ≤ wellBound :=
  (norm_nonneg (manufacturedPlanarWell 0)).trans (wellBound_spec 0)

theorem well_mul_memLp (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    MemLp (fun x => manufacturedPlanarWell x * u x) 2 := by
  apply (Lp.memLp u).of_le_mul (c := wellBound)
    (manufacturedPlanarWell_C7.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall (fun x => by
    change ‖manufacturedPlanarWell x * u x‖ ≤ wellBound * ‖u x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (wellBound_spec x) (norm_nonneg _))

def wellMultiply (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (well_mul_memLp u).toLp (fun x => manufacturedPlanarWell x * u x)

theorem wellMultiply_ae (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    wellMultiply u =ᵐ[volume] fun x => manufacturedPlanarWell x * u x :=
  (well_mul_memLp u).coeFn_toLp

private def wellMultiplyLinear : Lp ℝ 2 (volume : Measure PlanarPosition) →ₗ[ℝ]
    Lp ℝ 2 (volume : Measure PlanarPosition) where
  toFun := wellMultiply
  map_add' u v := by
    apply Lp.ext
    filter_upwards [wellMultiply_ae (u + v), wellMultiply_ae u, wellMultiply_ae v,
      Lp.coeFn_add u v, Lp.coeFn_add (wellMultiply u) (wellMultiply v)] with x h h₁ h₂ h₃ h₄
    simp only [h, h₄, h₃, Pi.add_apply, h₁, h₂]
    exact mul_add _ _ _
  map_smul' c u := by
    apply Lp.ext
    change (wellMultiply (c • u) : PlanarPosition → ℝ) =ᵐ[volume]
      (c • wellMultiply u : Lp ℝ 2 volume)
    filter_upwards [wellMultiply_ae (c • u), wellMultiply_ae u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (wellMultiply u)] with x h h₁ h₂ h₃
    simp only [h, h₃, h₁, h₂, Pi.smul_apply, smul_eq_mul]
    ring

def wellMultiplier : Lp ℝ 2 (volume : Measure PlanarPosition) →L[ℝ]
    Lp ℝ 2 (volume : Measure PlanarPosition) :=
  wellMultiplyLinear.mkContinuous wellBound (fun u =>
    Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [wellMultiply_ae u] with x hx
      change ‖wellMultiply u x‖ ≤ wellBound * ‖u x‖
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (wellBound_spec x) (norm_nonneg _)))

def form (u : Target) : ℝ :=
  (1 / 2 : ℝ) * ‖u.2‖ ^ 2 + inner ℝ u.1 (wellMultiplier u.1)

theorem form_continuous : Continuous form :=
  (continuous_const.mul (continuous_snd.norm.pow 2)).add
    (continuous_fst.inner (wellMultiplier.continuous.comp continuous_fst))

private theorem l2_norm_sq (u : Lp PlanarPosition 2 (volume : Measure PlanarPosition)) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem l2_real_norm_sq (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, sq]

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem grad_coordinate (u : PlanarPosition → ℝ) (x : PlanarPosition) (a : Fin 2) :
    grad u x a = planarPartial u (planarAxis a) x := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (x := planarAxis a) (y := fderiv ℝ u x)
  simpa only [grad, planarPartial, planarAxis, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul] using h

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem graph_mass (u : Test) :
    ‖(graph (μ := volume) u).1‖ ^ 2 = ∫ x, u.val x ^ 2 := by
  rw [l2_real_norm_sq]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp] with x hx
  exact congrArg (fun t : ℝ => t ^ 2) hx

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem graph_kinetic (u : Test) :
    ‖(graph (μ := volume) u).2‖ ^ 2 =
      ∑ a : Fin 2, ∫ x, planarPartial u.val (planarAxis a) x ^ 2 := by
  rw [l2_norm_sq]
  have hi (a : Fin 2) : Integrable (fun x => planarPartial u.val (planarAxis a) x ^ 2) := by
    have hc : HasCompactSupport (planarPartial u.val (planarAxis a)) :=
      u.property.2.fderiv_apply ℝ (planarAxis a)
    have hs : HasCompactSupport (fun x => planarPartial u.val (planarAxis a) x ^ 2) :=
      hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    exact ((planarPartial_continuous u.property.1 (planarAxis a)).pow 2).integrable_of_hasCompactSupport hs
  rw [← integral_finsetSum Finset.univ (fun a _ => hi a)]
  apply integral_congr_ae
  filter_upwards [(memLp_grad_of_mem_C1c (μ := volume) u.property).coeFn_toLp] with x hx
  change ‖toL2Grad (μ := volume) u x‖ ^ 2 = _
  change toL2Grad (μ := volume) u x = grad u.val x at hx
  rw [hx, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun t : ℝ => t ^ 2) (grad_coordinate _ _ _))

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem graph_form (u : Test) :
    form (graph (μ := volume) u) = planarTestForm manufacturedPlanarWell u.val := by
  unfold form planarTestForm
  rw [graph_kinetic, L2.inner_def]
  have he (f : PlanarPosition → ℝ) := planar_integral_change_borel
    (borel PlanarPosition) ⟨rfl⟩ f
  apply congrArg₂ (· + ·)
  · congr 1
    exact Finset.sum_congr rfl (fun a _ => he _)
  · change (∫ x, inner ℝ ((graph (μ := volume) u).1 x)
        (wellMultiplier (graph (μ := volume) u).1 x)) =
      originalIntegral (fun x => manufacturedPlanarWell x * u.val x ^ 2)
    rw [← he (fun x => manufacturedPlanarWell x * u.val x ^ 2)]
    apply integral_congr_ae
    filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      wellMultiply_ae (toL2 (μ := volume) u)] with x hx hw
    change toL2 (μ := volume) u x = u.val x at hx
    change inner ℝ (toL2 (μ := volume) u x) (wellMultiply (toL2 (μ := volume) u) x) = _
    rw [hw, hx, RCLike.inner_apply, conj_trivial]
    ring

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
/-- The proved inequality survives closure in the actual Sobolev norm. -/
theorem form_lower (u : Sobolev) :
    -(1 / 2 : ℝ) * ‖u.val.1‖ ^ 2 ≤ form u.val := by
  have hclosed : IsClosed {v : Target | -(1 / 2 : ℝ) * ‖v.1‖ ^ 2 ≤ form v} :=
    isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2)) form_continuous
  have hdense : (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target) ⊆
      {v | -(1 / 2 : ℝ) * ‖v.1‖ ^ 2 ≤ form v} := by
    rintro _ ⟨v, rfl⟩
    change -(1 / 2 : ℝ) * ‖(graph (μ := volume) v).1‖ ^ 2 ≤ form (graph (μ := volume) v)
    rw [graph_mass, graph_form]
    rw [planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩]
    exact manufacturedPlanarWell_test_lower v.val v.property.1 v.property.2
  exact closure_minimal hdense hclosed u.property

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
