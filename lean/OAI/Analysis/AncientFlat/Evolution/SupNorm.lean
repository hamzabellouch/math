import Mathlib

namespace OAI
noncomputable section
open Set
namespace ParabolicInterior
variable {P E : Type*} [NormedAddCommGroup E]
def supValues (Ω : Set P) (f : P → E) : Set ℝ := {v | v=0 ∨ ∃ p∈Ω, v=‖f p‖}
def supNorm (Ω : Set P) (f : P → E) : ℝ := sSup (supValues Ω f)
lemma supValues_bounded {Ω : Set P} {f : P → E} {M : ℝ} (hM : 0≤M)
    (h : ∀ p∈Ω, ‖f p‖≤M) : ∀ v∈supValues Ω f, v≤M := by
  intro v hv
  rcases hv with rfl | ⟨p,hp,rfl⟩
  · exact hM
  · exact h p hp
lemma supNorm_le {Ω : Set P} {f : P → E} {M : ℝ} (hM : 0≤M)
    (h : ∀ p∈Ω, ‖f p‖≤M) : supNorm Ω f≤M :=
  csSup_le ⟨0,Or.inl rfl⟩ (supValues_bounded hM h)
lemma supNorm_nonneg {Ω : Set P} {f : P → E} {M : ℝ} (hM : 0≤M)
    (h : ∀ p∈Ω, ‖f p‖≤M) : 0≤ supNorm Ω f :=
  le_csSup ⟨M,supValues_bounded hM h⟩ (Or.inl rfl)
lemma supNorm_bound {Ω : Set P} {f : P → E} {M : ℝ} (hM : 0≤M)
    (h : ∀ p∈Ω, ‖f p‖≤M) : ∀ p∈Ω, ‖f p‖≤ supNorm Ω f :=
  fun p hp => le_csSup ⟨M,supValues_bounded hM h⟩ (Or.inr ⟨p,hp,rfl⟩)
end ParabolicInterior

end

end OAI
