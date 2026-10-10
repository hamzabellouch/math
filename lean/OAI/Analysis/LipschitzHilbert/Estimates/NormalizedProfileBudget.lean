import OAI.Analysis.LipschitzHilbert.Packets.NormalizedPacketProfiles
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! Choose the finite derivative order and Fourier-decay exponent before
any packet lattice. Their fixed profile cost fits the model's logarithmic
budget once the disparity parameter is large enough. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def requiredPacketOrder (D : ℕ) : ℕ := max 207 (6+2*(8*D+1))

theorem requiredPacketOrder_basic (D : ℕ) :
    207 ≤ requiredPacketOrder D ∧ 6+2*(8*D+1) ≤ requiredPacketOrder D :=
  ⟨le_max_left _ _,le_max_right _ _⟩

theorem exists_normalized_profile_budget (F G : SchwartzMap (ℝ×ℝ) ℂ) (D : ℕ) :
    ∃ q : ℕ, 4≤q ∧ ∃ C L₀ : ℝ, 0<C ∧ 16≤L₀ ∧
      (∀ nu : SymbolSpace,
        planarProfileConstant (synthesisProfile F q nu) (2*requiredPacketOrder D) ≤ C ∧
        planarProfileConstant (analysisProfile G q nu) (2*requiredPacketOrder D) ≤ C) ∧
      ∀ L : ℝ, L₀≤L →
        ((2:ℝ)^requiredPacketOrder D*C)*3^(2*requiredPacketOrder D) ≤ L^(1:ℝ) := by
  obtain ⟨q₀,C,hC,hprofiles⟩ := uniform_normalized_profile_pair F G (2*requiredPacketOrder D)
  let budget : ℝ := (2^requiredPacketOrder D*C)*3^(2*requiredPacketOrder D)
  refine ⟨max 4 q₀,le_max_left _ _,C,max 16 budget,hC,le_max_left _ _,?_,?_⟩
  · exact hprofiles (max 4 q₀) (le_max_right _ _)
  · intro L hL
    rw [Real.rpow_one]
    exact (le_max_right 16 budget).trans hL

end LipschitzHilbert.PacketRepresentation

end

end OAI
