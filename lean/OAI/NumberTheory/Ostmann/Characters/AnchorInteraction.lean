import OAI.NumberTheory.Ostmann.Characters.AnchorCodes
import OAI.NumberTheory.Ostmann.Characters.Basic

namespace OAI

namespace Ostmann.Characters

theorem changed_code_one_sided (ε ε' c c' : ℤˣ) (hc : c≠c') :
    ((ε:ℤ)=(ε':ℤ) ∧
      ((ε:ℤ)*(c:ℤ)-(ε':ℤ)*(c':ℤ)=2 ∨
       (ε:ℤ)*(c:ℤ)-(ε':ℤ)*(c':ℤ)= -2) ∧
      (ε:ℤ)-(ε':ℤ)=0) ∨
    ((ε:ℤ)= -(ε':ℤ) ∧ (ε:ℤ)*(c:ℤ)-(ε':ℤ)*(c':ℤ)=0 ∧
      ((ε:ℤ)-(ε':ℤ)=2 ∨ (ε:ℤ)-(ε':ℤ)= -2)) := by
  have hcc : (c:ℤ)≠(c':ℤ) := fun h => hc (Units.ext h)
  rcases Int.isUnit_eq_one_or ε.isUnit with he | he <;>
  rcases Int.isUnit_eq_one_or ε'.isUnit with he' | he' <;>
  rcases Int.isUnit_eq_one_or c.isUnit with hh | hh <;>
  rcases Int.isUnit_eq_one_or c'.isUnit with hh' | hh' <;>
  (norm_num [hh, hh'] at hcc <;> norm_num [he, he', hh, hh'])

theorem square_or_inverse_ne_one {p:ℕ} (χ : MulChar (ZMod p) ℂ)
    (hχ : 2<orderOf χ) : χ^2≠1 ∧ (χ^2)⁻¹≠1 := by
  have h : χ^2≠1 := by
    intro he
    exact (not_le_of_gt hχ) (orderOf_le_of_pow_eq_one (by decide) he)
  exact ⟨h, inv_ne_one.mpr h⟩
end Ostmann.Characters

end OAI
