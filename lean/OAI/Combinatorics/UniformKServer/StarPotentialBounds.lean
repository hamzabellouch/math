import Mathlib
import OAI.Combinatorics.UniformKServer.StarActualJumps
import OAI.Combinatorics.UniformKServer.StarLocalCharges

namespace OAI

                                          
section

/-! Law- and horizon-independent endpoint bounds for the actual three
persistent star potentials. -/
noncomputable section
namespace UniformKServer.StarPotentialBounds
open Finset StarRanks StarSchedules StarOutputData StarLocalCharges StarActualJumps RankTracking
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem mass_size (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    StarOutputData.mass d t ω ≤ 40*∑ i, held d t ω i := by
  unfold StarOutputData.mass
  rw [mul_sum]
  exact sum_le_sum fun i _ => core_bound d t ω i

theorem mass_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) : StarOutputData.mass d t ω ≤ 80*k := by
  linarith [mass_size d t ω,held_sum d t ω]

theorem deficit_k (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    deficit d StarConstants.delta t ω ≤ 240*k := by
  linarith [deficit_bound d t ω,held_sum d t ω]

theorem alpha_potential (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    |AlphaFiniteLedger.potential (alphaData d) t ω| ≤ 1200*alphaScale k*k := by
  have h := AlphaEmpty.input_bound ((alphaData d).param_valid t ω)
    (AlphaFiniteInput.input (alphaData d) t ω) (fun _ => 0)
    (AlphaFiniteInput.alpha (alphaData d) t ω) (AlphaFiniteInput.alpha_state (alphaData d) t ω)
  simp only [AlphaEmpty.potential_zero,sub_zero,
    abs_of_nonneg (AlphaFiniteInput.input_nonneg (alphaData d) t ω _)] at h
  change |AlphaFiniteLedger.potential (alphaData d) t ω| ≤
    15*AlphaEmpty.scale ((alphaData d).param t ω)*StarOutputData.mass d t ω at h
  have hs := mul_le_mul_of_nonneg_right (alpha_scale d t ω) (mass_nonneg d t ω)
  have hm := mul_le_mul_of_nonneg_left (mass_bound d t ω) (scale_nonneg k)
  nlinarith only [h,hs,hm]

theorem side_mass (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, SideFiniteInput.input (sideData d hk) t ω i) ≤ 80*k := by
  exact (sum_le_sum (fun i _ => StarTrackers.side_core_le d StarConstants.delta t ω i)).trans (mass_bound d t ω)

theorem side_potential (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    |SideFiniteLedger.potential (sideData d hk) t ω| ≤ 320*sideSlope k*k := by
  have h := AdaptiveSide.input_bound ((sideData d hk).param_valid t ω)
    (SideFiniteInput.input (sideData d hk) t ω) (fun _ => 0)
    (SideFiniteInput.tracker (sideData d hk) t ω) (deficit d StarConstants.delta t ω) 0
    (SideFiniteInput.tracker_state (sideData d hk) t ω)
  simp only [SideLinear.zero,sub_zero,
    abs_of_nonneg (SideFiniteInput.input_nonneg (sideData d hk) t ω _),
    abs_of_nonneg (deficit_nonneg d StarConstants.delta t ω)] at h
  change |SideFiniteLedger.potential (sideData d hk) t ω| ≤ sideSlope k*
    ((∑ i, SideFiniteInput.input (sideData d hk) t ω i)+deficit d StarConstants.delta t ω) at h
  have hm := mul_le_mul_of_nonneg_left (add_le_add (side_mass d hk t ω) (deficit_k d t ω)) (slope_nonneg k)
  nlinarith only [h,hm]

theorem switch_potential (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    SwitchFinite.potential (StarAllocator.switchData d) t ω ∈ Set.Icc (0:ℝ) (240*k) := by
  change SwitchTracker.potential (StarAllocator.tag d t ω) (StarOutputData.mass d t ω) (deficit d StarConstants.delta t ω) ∈ _
  cases StarAllocator.tag d t ω
  · exact ⟨deficit_nonneg d StarConstants.delta t ω,deficit_k d t ω⟩
  · exact ⟨mass_nonneg d t ω,(mass_bound d t ω).trans (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)⟩

theorem switch_wholesale (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    SwitchFinite.wholesale (StarAllocator.switchData d) t ω ≤ 160*wholesaleMass d t ω := by
  unfold SwitchFinite.wholesale
  change (if StarCaps.wholesale d t ω then StarOutputData.mass d (t+1) ω+deficit d StarConstants.delta (t+1) ω else 0) ≤ _
  unfold wholesaleMass
  split_ifs
  · linarith [mass_size d (t+1) ω,deficit_bound d (t+1) ω,
      sum_nonneg (s:=univ) (fun i _ => held_nonneg d t ω i)]
  · norm_num

theorem average_interval (d : Data Ω ι k) {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, |f ω| ≤ c) :
    average d.weight f ∈ Set.Icc (-c) c := by
  constructor
  · rw [←CoarseData.average_const d.weight d.total (-c)]
    exact average_mono (fun ω => (d.positive ω).le) (fun ω => (abs_le.mp (h ω)).1)
  · rw [←CoarseData.average_const d.weight d.total c]
    exact average_mono (fun ω => (d.positive ω).le) (fun ω => (abs_le.mp (h ω)).2)

end UniformKServer.StarPotentialBounds

end


end

end OAI
