import OAI.Geometry.NodalSets.Charts.SphereEnergyForm
import OAI.Geometry.NodalSets.Elliptic.CompactFirstJetFunctionalLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem sphereEnergyForm_limit (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (W : ℕ → Base → ℝ) (v u : Base → ℝ)
    (hW : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (W j))
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hconv : ∀ ds, TendstoUniformlyOn
      (fun j ↦ partialJet (W j ∘ sphereChartCoordMap seedPoint) ds)
      (partialJet (v ∘ sphereChartCoordMap seedPoint) ds) atTop Q) :
    Tendsto (fun j ↦ sphereEnergyForm a b lam (W j) u) atTop (𝓝 (sphereEnergyForm a b lam v u)) := by
  let ac : Fin 4 → Yau.Jets.Coord → ℝ := fun i x ↦
    roundCoordDensity x*a (sphereChartCoordMap seedPoint x)*roundCoordFactor x*
      Yau.coordPartial (u ∘ sphereChartCoordMap seedPoint) x i
  let bc : Yau.Jets.Coord → ℝ := fun x ↦
    roundCoordDensity x*lam*b (sphereChartCoordMap seedPoint x)*u (sphereChartCoordMap seedPoint x)
  have hac (i : Fin 4) : Continuous (ac i) :=
    (((roundCoordDensity_smooth.mul (spherePullback_smooth a ha seedPoint)).mul roundCoordFactor_smooth).mul
      (partialJet_smooth _ (spherePullback_smooth u hu seedPoint) [i])).continuous
  have hbc : Continuous bc :=
    (((roundCoordDensity_smooth.mul contDiff_const).mul (spherePullback_smooth b hb seedPoint)).mul
      (spherePullback_smooth u hu seedPoint)).continuous
  have hsupp (f : Base → ℝ) (hf : tsupport f ⊆ seedSphereFromCoord '' Q)
      (x : Yau.Jets.Coord) (hx : x ∉ Q) : f (sphereChartCoordMap seedPoint x)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    obtain ⟨y,hy,he⟩ := hf hh
    have hxy : y=x := (Function.LeftInverse.injective seedSphereToCoord_from) he
    exact hx (hxy ▸ hy)
  have heq (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) :
      sphereEnergyForm a b lam f u = ∫ x,
        (∑ i, ac i x*partialJet (f ∘ sphereChartCoordMap seedPoint) [i] x)-
          bc x*(f ∘ sphereChartCoordMap seedPoint) x := by
    rw [sphereEnergyForm_chart a b lam f u hf hu seedPoint]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by
      simp only [ac,bc,partialJet,Yau.coordPartial,Function.comp_apply,mul_sub,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · ring)
  simp_rw [heq _ (hW _),heq v hv]
  exact compact_first_jet_functional_limit Q hQ ac bc hac hbc
    (fun i x hx ↦ by simp [ac,hsupp a haQ x hx])
    (fun x hx ↦ by simp [bc,hsupp b hbQ x hx])
    (fun j ↦ W j ∘ sphereChartCoordMap seedPoint) (v ∘ sphereChartCoordMap seedPoint)
    (fun j ↦ spherePullback_smooth (W j) (hW j) seedPoint) (spherePullback_smooth v hv seedPoint) hconv

end
end Yau.Target

end OAI
