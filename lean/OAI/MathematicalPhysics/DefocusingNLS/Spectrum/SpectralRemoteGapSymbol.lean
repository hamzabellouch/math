import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolFinite

namespace OAI

/-! The separated root denominators have uniform logarithmic jets. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

noncomputable def spectralRemoteRootDomain : Set (Fin 2 → ℝ) :=
  {c | ∀ i, c i < 1/16}

theorem spectralRemoteRootDomain_open : IsOpen spectralRemoteRootDomain := by
  change IsOpen {c : Fin 2 → ℝ | ∀ i, c i < 1/16}
  simpa only [ofPred_forall] using
    (isOpen_iInter_of_finite (fun i : Fin 2 => isOpen_lt (continuous_apply i) continuous_const))

theorem spectralRemote_diagonal_root_smooth (i : SpectralRemoteIndex) :
    ContDiffOn ℝ ∞ (fun c => spectralRemoteDiagonalRoot c i) spectralRemoteRootDomain := by
  apply (spectralRemote_root_smooth (if i.1 = 0 then 1 else -1)
    (if i.2 = 0 then 1 else -1)).comp
      (contDiff_apply ℝ ℝ i.1).contDiffOn
  exact fun c hc => hc i.1

theorem spectralRemote_diagonal_root_continuous (i : SpectralRemoteIndex) :
    Continuous (fun c => spectralRemoteDiagonalRoot c i) :=
  (spectralRemote_root_continuous (if i.1 = 0 then 1 else -1)
    (if i.2 = 0 then 1 else -1)).comp (continuous_apply i.1)

theorem spectralRemote_gap_inverse_symbol
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ}
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32)
    (i j : SpectralRemoteIndex) (hij : spectralRemoteBlock i ≠ spectralRemoteBlock j) :
    HasUniformLogJetBound L 0 (fun n t =>
      (spectralRemoteDiagonalRoot (c n t) i-spectralRemoteDiagonalRoot (c n t) j)⁻¹) := by
  let C : Set (Fin 2 → ℝ) := Metric.closedBall 0 (1/32)
  let O : Set (Fin 2 → ℝ) := spectralRemoteRootDomain ∩
    {x | spectralRemoteDiagonalRoot x i-spectralRemoteDiagonalRoot x j ≠ 0}
  have hO : IsOpen O := spectralRemoteRootDomain_open.inter
    (isOpen_ne_fun ((spectralRemote_diagonal_root_continuous i).sub
      (spectralRemote_diagonal_root_continuous j)) continuous_const)
  have hCO : C ⊆ O := by
    intro x hx
    have hn : ‖x‖ ≤ 1/32 := by simpa only [C,Metric.mem_closedBall,dist_zero_right] using hx
    have hb (k : Fin 2) : |x k| ≤ 1/32 :=
      (show |x k| ≤ ‖x‖ from norm_le_pi_norm x k).trans hn
    refine ⟨fun k => (le_abs_self _).trans_lt ((hb k).trans_lt (by norm_num)),?_⟩
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/4)
      (spectralRemote_block_gap x hb i j hij))
  have hg : ContDiffOn ℝ ∞ (fun x =>
      (spectralRemoteDiagonalRoot x i-spectralRemoteDiagonalRoot x j)⁻¹) O :=
    (((spectralRemote_diagonal_root_smooth i).mono inter_subset_left).sub
      ((spectralRemote_diagonal_root_smooth j).mono inter_subset_left)).inv (fun _ hx => hx.2)
  apply spectralRemote_uniform_compact_comp hO (isCompact_closedBall 0 (1/32)) hCO hg hc
  filter_upwards [hsmall] with n hn
  intro t ht
  change dist (c n t) 0 ≤ 1/32
  rw [dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/32)).mpr
    (fun k => by simpa only [Real.norm_eq_abs] using hn t ht k)

end DefocusingNLS

end OAI
