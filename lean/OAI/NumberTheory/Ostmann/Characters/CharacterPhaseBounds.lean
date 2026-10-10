import OAI.NumberTheory.Ostmann.Characters.CharacterInitialPhase

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters

theorem norm_characterAmplitude_le {p:ℕ} [Fact p.Prime]
    (χ:MulChar (ZMod p) ℂ) (hχ:χ≠1) (a v:ZMod p) : ‖characterAmplitude χ a v‖≤1 := by
  by_cases hv:v=0
  · subst v; rw [characterAmplitude_zero,norm_zero]; norm_num
  · exact (norm_characterAmplitude χ hχ a v hv).le

theorem norm_initialPhase_le {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (hχ:∀i,χ i≠1)
    (a:∀i,ZMod (p i)) (s:ℤ) : ‖initialPhase p χ a s‖≤1 := by
  have he : initialPhase p χ a s=∏i,characterAmplitude (χ i) (a i) (Construction.crtFrequency p s i) := by
    simp only [characterAmplitude_crt,initialPhase]
  rw [he,norm_prod]
  exact Finset.prod_le_one₀ (fun i _=>norm_nonneg _) (fun i _=>norm_characterAmplitude_le _ (hχ i) _ _)

theorem initialPhase_zero {ι:Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i)) : initialPhase p χ a 0=0 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [← characterAmplitude_crt]
  simp only [Construction.crtFrequency,Int.cast_zero,zero_mul,characterAmplitude_zero]

end Ostmann.Characters

end

end OAI
