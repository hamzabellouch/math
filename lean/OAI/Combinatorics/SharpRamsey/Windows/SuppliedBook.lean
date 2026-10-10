import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.BookScales

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter SourceScales
open scoped Topology
noncomputable section

theorem supplied_book (i : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ σ : ℝ in atTop,
    ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ = (q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V = i+4 → ∀ D R, Admissible σ η D R →
    let b := 16*scaleKstar σ η D
    let τ := σ^(-100*beta η)
    0 ≤ b ∧ 4 ≤ scaleP σ η D R ∧ b+log 1000000 ≤ scaleP σ η D R ∧
    0 ≤ τ ∧ τ ≤ 1/40000 ∧
    Nonempty (Book (K:=ZMod q) (V:=V) (Nat.card (ZMod q)) b τ
      (scaleP σ η D R) H ((i+1)+3)) := by
  obtain ⟨H,hH,hbook⟩ := uniform_book i
  refine ⟨H,hH,?_⟩
  intro η hη
  filter_upwards [hbook η hη 16 (by norm_num), eventually_book_scales hη,
    eventually_ge_atTop (1:ℝ)] with σ hb hs hσ
  intro q _ hq he V _ _ _ hd D R had
  obtain ⟨h0,hP,hbP,hτ,hτsmall⟩ := hs D R had
  dsimp only
  refine ⟨h0,hP,hbP,hτ.le,hτsmall,?_⟩
  simpa only [Nat.card_zmod] using hb q hq he V hd D R had
    (16*scaleKstar σ η D) (σ^(-100*beta η)) h0 le_rfl hτ (by
      have hh := rpow_nonneg (by linarith : 0 ≤ σ) (-100*beta η)
      linarith)
end
end SharpLogRamsey.ActualPivot

end

end OAI
