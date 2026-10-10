import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteGapSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIndividualSymbol

namespace OAI

/-! The large incoming root never vanishes; its inverse is an order-zero
symbol. No gap between the two outgoing roots is needed. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_incoming_root_bound (c : Fin 2 → ℝ) (i : SpectralRemoteIndex)
    (hi : i.2 = 1) (hc : ∀ k, |c k| ≤ 1/32) :
    3/8 ≤ ‖spectralRemoteDiagonalRoot c i‖ := by
  have hs : ((if i.1 = 0 then 1 else -1) : ℝ)^2 = 1 := by split_ifs <;> norm_num
  simpa only [spectralRemoteDiagonalRoot,hi,show (1 : Fin 2) ≠ 0 by decide,ite_false] using
    (spectralRemote_root_branch_bounds _ _ hs (hc i.1)).2

theorem spectralRemote_incoming_inverse_symbol
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ}
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32)
    (i : SpectralRemoteIndex) (hi : i.2 = 1) :
    HasUniformLogJetBound L 0 (fun n t => (spectralRemoteDiagonalRoot (c n t) i)⁻¹) := by
  let C : Set (Fin 2 → ℝ) := Metric.closedBall 0 (1/32)
  let O : Set (Fin 2 → ℝ) := spectralRemoteRootDomain ∩
    {x | spectralRemoteDiagonalRoot x i ≠ 0}
  have hO : IsOpen O := spectralRemoteRootDomain_open.inter
    (isOpen_ne_fun (spectralRemote_diagonal_root_continuous i) continuous_const)
  have hCO : C ⊆ O := by
    intro x hx
    have hn : ‖x‖ ≤ 1/32 := by simpa only [C,Metric.mem_closedBall,dist_zero_right] using hx
    have hb (k : Fin 2) : |x k| ≤ 1/32 :=
      (show |x k| ≤ ‖x‖ from norm_le_pi_norm x k).trans hn
    refine ⟨fun k => (le_abs_self _).trans_lt ((hb k).trans_lt (by norm_num)),?_⟩
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3/8)
      (spectralRemote_incoming_root_bound x i hi hb))
  have hg : ContDiffOn ℝ ∞ (fun x => (spectralRemoteDiagonalRoot x i)⁻¹) O :=
    ((spectralRemote_diagonal_root_smooth i).mono inter_subset_left).inv (fun _ hx => hx.2)
  apply spectralRemote_uniform_compact_comp hO (isCompact_closedBall 0 (1/32)) hCO hg hc
  filter_upwards [hsmall] with n hn
  intro t ht
  change dist (c n t) 0 ≤ 1/32
  rw [dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/32)).mpr
    (fun k => by simpa only [Real.norm_eq_abs] using hn t ht k)

theorem spectralRemote_incoming_inverse_single (c : ℝ → Fin 2 → ℝ)
    (hc : HasLogJetBound 0 c) (hsmall : ∀ᶠ t in atTop, ∀ k, |c t k| ≤ 1/32)
    (i : SpectralRemoteIndex) (hi : i.2 = 1) :
    HasLogJetBound 0 (fun t => (spectralRemoteDiagonalRoot (c t) i)⁻¹) := by
  have hL : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨S,hS⟩ := eventually_atTop.mp hsmall
  have hs : ∀ᶠ n : ℕ in atTop, ∀ t ∈ Ioi (n : ℝ), ∀ k, |c t k| ≤ 1/32 := by
    filter_upwards [hL.eventually (eventually_ge_atTop S)] with n hn
    intro t ht
    exact hS t (hn.trans ht.le)
  exact (spectralRemote_incoming_inverse_symbol
    (HasUniformLogJetBound.of_single hc hL) hs i hi).to_single

end DefocusingNLS

end OAI
