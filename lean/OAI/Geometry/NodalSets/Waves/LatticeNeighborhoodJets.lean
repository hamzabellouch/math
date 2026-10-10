import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Elliptic.NeighborhoodJetBound
import OAI.Geometry.NodalSets.Waves.LatticeGaussianSmallBall
import OAI.Geometry.NodalSets.Waves.SeededLatticeFieldBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_neighborhood_jet_bound (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    (hS : ContDiff ℝ ∞ S) (S0 T0 : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        ∀ x ∈ highEnvelopeRegion Ω S S0 n,
          ∀ z ∈ Metric.closedBall x ((n:ℝ)^2)⁻¹,
            ‖fderiv ℝ (fun y ↦ a.latticeSeededJet hUD n hfin
              (oscillatorySeed S0 T0 n) y coeff) z‖ ≤ (n:ℝ)^13 := by
  obtain ⟨R,hR,hΩR⟩ := hΩ.isBounded.exists_pos_norm_le
  let Q := Metric.closedBall (0:Coord) (R+1)
  have hQ : IsCompact Q := isCompact_closedBall _ _
  obtain ⟨A,hA,hAb⟩ := (hQ.image (hS.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  have hdS : ContDiff ℝ ∞ (fun z ↦ S0 z-S z) := hS0.sub hS
  obtain ⟨L,hL,hLb⟩ := (hQ.image (hdS.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  obtain ⟨B,hB,hfield⟩ := a.seeded_lattice_field_derivative_bound hUD hUb S0 T0 hS0 hT0 hQ
  have hfreq : ∀ᶠ n : ℕ in atTop, max L (6*(A+1)*B*Real.exp 1) ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hfield,hfreq,eventually_gt_atTop (0:ℕ)] with n hn hsize hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff hc x hx z hz
  obtain ⟨hu,hbnd⟩ := hb coeff hc
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hdist : ‖z-x‖ ≤ ((n:ℝ)^2)⁻¹ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hrad : ((n:ℝ)^2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ hn1)
  have hxQ : x ∈ Q := by
    change dist x 0 ≤ R+1
    rw [dist_zero_right]
    linarith [hΩR x hx.1]
  have hzQ : z ∈ Q := by
    change dist z 0 ≤ R+1
    rw [dist_zero_right]
    have ht := norm_le_norm_sub_add z x
    linarith [hΩR x hx.1,hdist.trans hrad]
  have hgap : (S0 z-S z)-(S0 x-S x) ≤ L*‖z-x‖ := by
    have h := (convex_closedBall (0:Coord) (R+1)).norm_image_sub_le_of_norm_fderiv_le
      (fun _ _ ↦ (hdS.differentiable (by simp)).differentiableAt)
      (fun y hy ↦ hLb _ ⟨y,hy,rfl⟩) hxQ hzQ
    exact (le_abs_self _).trans h
  have h := normalized_jet_neighborhood_derivative_bound
    (fun y ↦ oscillatorySeed S0 T0 n y+gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y)
    S S0 hu hS hnpos hx hA.le hB.le hL.le
    ((le_max_left _ _).trans hsize) ((le_max_right _ _).trans hsize)
    hdist hgap (hAb _ ⟨z,hzQ,rfl⟩)
    (fun k ↦ hbnd z hzQ ⟨k.val,by omega⟩)
  exact h

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
