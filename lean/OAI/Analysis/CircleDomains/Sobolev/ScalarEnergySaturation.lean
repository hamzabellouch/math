import OAI.Analysis.CircleDomains.Sobolev.ScalarImageEnergy
import OAI.Analysis.CircleDomains.Sobolev.ScalarImageGradient

namespace OAI

/-! All limiting gradient energy is accounted for by the smooth
conformal image. Both weak fields therefore vanish on its complement. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem zero_gradient_off_image (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∉ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      W.horizontal z = 0 ∧ W.vertical z = 0 := by
  let U := R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)
  let H : ℂ → ℝ := fun z => W.horizontal z ^ 2 + W.vertical z ^ 2
  have hU : IsOpen U := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have hH : Integrable H := (Lp.memLp W.horizontal).integrable_sq.add
    (Lp.memLp W.vertical).integrable_sq
  have hn : ∀ z, 0 ≤ H z := fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hE : (∫ z in U, H z) = ∫ x in realChartDomain d.physicalDomain,
      gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
    apply Eq.trans _ (R.imageScalar_energy hG i).2
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet,
      ae_restrict_of_ae (W.gradient_on_image hsch hG)] with z hz hg
    rcases hg hz with ⟨hx, hy⟩
    simp only [H, euclideanGradientEnergy, hx, hy]
  have hzero : (∫ z in Uᶜ, H z) = 0 := by
    have hsplit := integral_add_compl hU.measurableSet hH
    have hbound := W.energy
    have hpos : 0 ≤ ∫ z in Uᶜ, H z := integral_nonneg hn
    change (∫ z, H z) ≤ _ at hbound
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hn (hH.restrict (s := Uᶜ))).mp hzero
  change ∀ᵐ z ∂volume.restrict Uᶜ, H z = 0 at hae
  rw [ae_restrict_iff' hU.isClosed_compl.measurableSet] at hae
  filter_upwards [hae] with z hz hout
  have hh : W.horizontal z ^ 2 + W.vertical z ^ 2 = 0 := hz hout
  constructor
  · nlinarith [sq_nonneg (W.vertical z)]
  · nlinarith [sq_nonneg (W.horizontal z)]

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
