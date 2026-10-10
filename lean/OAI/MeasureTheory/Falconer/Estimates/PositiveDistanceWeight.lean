import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceMasks
import OAI.MeasureTheory.Falconer.Estimates.SourceStrongSeparation

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def spatialWeight (d : PositiveDistanceData) (z : Plane × Plane) : ℝ :=
  (dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)))^(-(1/2:ℝ)) * d.minimalMask z

@[fun_prop] theorem measurable_spatialWeight (d : PositiveDistanceData) :
    Measurable d.spatialWeight := by
  unfold spatialWeight
  exact ((continuous_fst.dist continuous_snd).measurable.div_const _).pow_const _ |>.mul
    d.measurable_minimalMask

theorem spatialWeight_nonneg (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (z : Plane × Plane) : 0 ≤ d.spatialWeight z :=
  mul_nonneg (Real.rpow_nonneg (div_nonneg dist_nonneg (by positivity)) _)
    (d.minimalMask_bounds hQ z).1

def StronglySeparated (d : PositiveDistanceData) : Prop :=
  (d.Q.descendant d.X).side ≤ (2:ℝ)^(-(d.a:ℝ)) ∧
  (d.Q.descendant d.Y).side ≤ (2:ℝ)^(-(d.a:ℝ)) ∧
  100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ∧
  dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ))

theorem stronglySeparated_of_unit (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (hl : 100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center)
    (hu : dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ))) :
    d.StronglySeparated := by
  refine ⟨?_,?_,hl,hu⟩
  · simp only [DyadicSquare.descendant_side,hQ,hX,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div,le_refl]
  · simp only [DyadicSquare.descendant_side,hQ,hY,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div,le_refl]

theorem separated_distance_ratio (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) :
    96 ≤ dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ∧
    dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ≤ 2004 := by
  have h := dyadic_strong_separation_endpoints _ _
    (d.Q.descendant_side_pos hQ d.X) (d.Q.descendant_side_pos hQ d.Y)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hx hy
  exact ⟨(le_div_iff₀ (by positivity)).mpr h.1,
    (div_le_iff₀ (by positivity)).mpr h.2⟩

theorem spatialWeight_le_one (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) : d.spatialWeight z ≤ 1 := by
  have hr := d.separated_distance_ratio hQ hs hx hy
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos (by linarith :
    1 ≤ dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ))) (by norm_num : -(1/2:ℝ) ≤ 0)
  exact (mul_le_of_le_one_left (d.minimalMask_bounds hQ z).1 hpow).trans
    (d.minimalMask_bounds hQ z).2

theorem spatialWeight_lower (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) (hm : d.minimalMask z = 1) :
    (2004:ℝ)^(-(1/2:ℝ)) ≤ d.spatialWeight z := by
  rw [spatialWeight,hm,mul_one]
  have hr := d.separated_distance_ratio hQ hs hx hy
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hr.2 (by norm_num)

theorem ae_cellPair_mem (d : PositiveDistanceData) [SFinite d.ρ] :
    ∀ᵐ z ∂d.cellPair, z.1 ∈ (d.Q.descendant d.X).carrier ∧
      z.2 ∈ (d.Q.descendant d.Y).carrier := by
  exact (Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem (d.Q.descendant d.X).measurable)).and
    (Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (d.Q.descendant d.Y).measurable))

theorem ae_spatialWeight_bounds (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ∀ᵐ z ∂d.cellPair, (0 ≤ d.spatialWeight z ∧ d.spatialWeight z ≤ 1) ∧
      (z ∈ d.good → (2004:ℝ)^(-(1/2:ℝ)) ≤ d.spatialWeight z) := by
  filter_upwards [d.ae_cellPair_mem,d.ae_minimalMask_eq_one_on_good hQ hcarry] with z hz hm
  exact ⟨⟨d.spatialWeight_nonneg hQ z,d.spatialWeight_le_one hQ hs hz.1 hz.2⟩,
    fun hg => d.spatialWeight_lower hQ hs hz.1 hz.2 (hm hg)⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
