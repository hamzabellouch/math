import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootReduction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReductionDiagonal

namespace OAI

/-! The bounded-part exponent is chosen before the finite reduction order. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_uniform_exponent
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ} (hL : Tendsto L atTop atTop)
    (B : ℕ → ℝ → SpectralRemoteOperator) (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32)
    (hB : HasUniformLogJetBound L 0 B) :
    let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
    let K := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      let d := spectralRemoteReductionData Lambda B spectralRemoteBlockOperator K (m+1)
      ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖d.1 n t‖ ≤ C ∧ ‖d.1 n t+d.2 n t‖ ≤ C := by
  dsimp only
  let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
  let K := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
  have hK := spectralRemote_sylvester_uniform_symbol hL hc hsmall
  have hcomm := spectralRemote_root_sylvester hsmall
  obtain ⟨C,hC,hb⟩ := hB.bound 0
  have hb' : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖B n t‖ ≤ C := by
    simpa only [iteratedDeriv_zero,zero_mul,Real.exp_zero,mul_one] using hb
  refine ⟨‖spectralRemoteBlockOperator‖*C+2,by positivity,?_⟩
  intro m
  have hdiag := spectralRemote_reduction_diagonal_symbol hL Lambda B spectralRemoteBlockOperator K
    spectralRemoteBlockOperator_idempotent hB hK hcomm m
  have hrem := (spectralRemote_finite_reduction hL Lambda B spectralRemoteBlockOperator K
    spectralRemoteBlockOperator_idempotent hB hK hcomm (m+1)).2.1
  have hdsmall := hdiag.eventually_small hL (by norm_num : (-2 : ℝ) < 0) 1 (by norm_num)
  have hrsmall := hrem.eventually_small hL
    (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m]) 1 (by norm_num)
  filter_upwards [hb',hdsmall,hrsmall] with n hn hdn hrn
  intro t ht
  let A := (spectralRemoteReductionData Lambda B spectralRemoteBlockOperator K (m+1)).1 n t
  let R := (spectralRemoteReductionData Lambda B spectralRemoteBlockOperator K (m+1)).2 n t
  have hPA : ‖spectralRemoteBlockOperator (B n t)‖ ≤ ‖spectralRemoteBlockOperator‖*C :=
    (spectralRemoteBlockOperator.le_opNorm (B n t)).trans
      (mul_le_mul_of_nonneg_left (hn t ht) (norm_nonneg _))
  have hA : ‖A‖ ≤ 1+‖spectralRemoteBlockOperator‖*C := by
    have hh : ‖A‖ ≤ ‖A-spectralRemoteBlockOperator (B n t)‖+
        ‖spectralRemoteBlockOperator (B n t)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (A-spectralRemoteBlockOperator (B n t))
        (spectralRemoteBlockOperator (B n t))
    exact hh.trans (add_le_add (hdn t ht).le hPA)
  have hR : ‖R‖ ≤ 1 := (hrn t ht).le
  change ‖A‖ ≤ _ ∧ ‖A+R‖ ≤ _
  constructor
  · linarith
  · have hh := (norm_add_le A R).trans (add_le_add hA hR)
    linarith

end DefocusingNLS

end OAI
