import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CoulombTransfer
import OAI.Analysis.CoulombRadii.Packets.FineNear

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma sqrt_young (x : ℝ) (hx : 0≤x) {ε : ℝ} (hε : 0<ε) :
    Real.sqrt x≤ε+x/(4*ε) := by
  have h := sq_nonneg (Real.sqrt x-2*ε)
  rw [sub_sq,Real.sq_sqrt hx] at h
  have he : x/(4*ε)*(4*ε)=x := div_mul_cancel₀ _ (by positivity)
  apply (mul_le_mul_iff_of_pos_right (show 0<4*ε by positivity)).mp
  nlinarith

theorem patch_raw_field_transfer {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a)
    (spin : Spins m) (x : Configuration m)
    (hcs : SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖})
    (hxy : ∀ i,position x i≠y) :
    |(coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
      patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y|≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      nearPotential y (r+2*b) x+nearPotential y (2*b) x+
      ((deletedLabels (patchRetained y t b) x).card:ℝ)/a+
      ((tfInteriorConstant thomasFermiKineticConstant/
        (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  let σ := retainedFineDensity b (patchRetained y t b x) (position x)
  let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
    (patch_nucleus_separation S ha hb ht.2 y hn)
  have hf := patch_potential_transfer S u ha hb hsmall ht y hn hr hra spin x hcs
  have hn' := retainedFine_near_le hb y r (patchRetained y t b x) x hxy
  have hdiff := patchFine_raw_deficit (t := t) hb ha (by linarith [ht.1]) y x hxy
  have ht' := abs_sub_le (nuclearPotential (unitNucleus y) x) (NeutralAtom.potentialOf σ y)
    (tfPotential (localTFMinimizer measurableSet_ball W) y)
  rw [abs_of_nonneg hdiff.1] at ht'
  have he : |(coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
      patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y|=
      |nuclearPotential (unitNucleus y) x-tfPotential (localTFMinimizer measurableSet_ball W) y| := by
    unfold patchTFScreenedField
    rw [show (coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
        (coreScreenedField S (u.coreSlice spin x).normalized y-tfPotential
        (localTFMinimizer measurableSet_ball W) y)=
        -(nuclearPotential (unitNucleus y) x-tfPotential (localTFMinimizer measurableSet_ball W) y) by ring,
      abs_neg]
  rw [he]
  have heint : (∫ z in Metric.ball y r,σ z*coulombKernel (y-z))=
      (∫ z in Metric.ball y r,coulombKernel (y-z)*σ z) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => mul_comm _ _)
  dsimp only [σ,W] at ht' heint
  dsimp only at hf
  rw [heint] at hf
  linarith
end Coulomb
end

end
end

end OAI
