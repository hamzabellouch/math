import OAI.NumberTheory.Ostmann.Tree.TensorCharacters

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
local instance tensorParsevalFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

def tensorSeries (c : (I → MulChar F ℂ) → ℂ) (t : I → Fˣ) : ℂ :=
  ∑ ρ : I → MulChar F ℂ,c ρ*tensorCharacter ρ t

theorem tensorSeries_energy_complex (c : (I → MulChar F ℂ) → ℂ) :
    (∑ t : I → Fˣ,conj (tensorSeries c t)*tensorSeries c t) =
      (Fintype.card (I → Fˣ):ℂ)*∑ ρ : I → MulChar F ℂ,conj (c ρ)*c ρ := by
  classical
  simp only [tensorSeries,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ ρ : I → MulChar F ℂ,∑ τ : I → MulChar F ℂ,
        (conj (c τ)*c ρ)*(∑ t : I → Fˣ,tensorCharacter ρ t*conj (tensorCharacter τ t)) := by
      apply Finset.sum_congr rfl
      intro ρ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      simp_rw [tensorCharacter_kernel]
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      rw [← Finset.sum_mul,← Finset.mul_sum]
      ring

theorem tensorSeries_parseval (c : (I → MulChar F ℂ) → ℂ) :
    (Fintype.card (I → Fˣ):ℝ)⁻¹*(∑ t : I → Fˣ,‖tensorSeries c t‖^2) =
      ∑ ρ : I → MulChar F ℂ,‖c ρ‖^2 := by
  have hN : (Fintype.card (I → Fˣ):ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply Complex.ofReal_injective
  push_cast
  have he := tensorSeries_energy_complex c
  simp only [Complex.conj_mul'] at he
  rw [he]
  exact inv_mul_cancel_left₀ hN _

end
end Ostmann.FiniteField

end OAI
