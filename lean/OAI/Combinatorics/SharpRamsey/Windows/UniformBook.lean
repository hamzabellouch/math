import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.Pivot

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real GeometricCover SourceScales Filter
open scoped Classical Topology
noncomputable section

theorem uniform_book (i : ℕ) : ∃ H : ℝ,0≤H ∧
    ∀ η : ℝ,0<η → ∀ C : ℝ,1≤C →
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=i+4 → ∀ D R,Admissible σ η D R →
    ∀ b τ : ℝ,0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
      Nonempty (Book (K:=ZMod q) (V:=V) q b τ (scaleP σ η D R) H (i+4)) := by
  obtain ⟨H,hH,huniform⟩ := uniform_all i
  refine ⟨H,hH,?_⟩
  intro η hη C hC
  let C' := 4*C+4
  have hC' : 1≤C' := by dsimp only [C']; linarith
  filter_upwards [huniform η hη C' hC',eventually_ge_atTop (1:ℝ)] with σ hs hσ
  intro q _ hq hex V _ _ _ hdim D R had b τ hb hbC hτ hτC
  have hK : 1≤ scaleKstar σ η D := by
    have hD : 1≤D := (one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
    exact one_le_mul_of_one_le_of_one_le hD (one_le_rpow hσ (by have hb := beta_pos hη; positivity))
  have hlog : 0≤log (4:ℝ) := log_nonneg (by norm_num)
  have hlog' : log (4:ℝ)≤3 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hb' : b+log 4≤C'*scaleKstar σ η D := by dsimp only [C']; nlinarith
  have hτ' : 4*τ≤C'*σ^(-100*beta η) := by
    have hpow := rpow_nonneg (show 0≤σ by linarith) (-100*beta η)
    dsimp only [C']
    nlinarith
  refine ⟨Book.ofValidated q b τ (scaleP σ η D R) H (i+4) ?_⟩
  intro U s t hh
  rcases hh with ⟨hs0,ht0,hsU,htU,hlo,hhi⟩
  exact hs q hq hex V hdim D R had U.1 U.2 s t (b+log 4) (4*τ)
    hs0 ht0 hsU htU (add_nonneg hb hlog) hb' (by positivity) hτ' hlo hhi

end
end SharpLogRamsey.ActualPivot

end

end OAI
