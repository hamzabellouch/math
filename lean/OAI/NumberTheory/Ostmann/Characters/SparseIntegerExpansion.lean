import OAI.NumberTheory.Ostmann.Characters.SparsePrimitiveExpansion

namespace OAI

/-! # The primitive expansion on integers coprime to the selected primes -/
namespace Ostmann
open scoped Classical BigOperators

theorem liftPrimitiveCharacter_apply_nat (N a : ℕ) (ρ : PrimitiveComplexCharacter)
    (hd : ρ.modulus ∣ N) (ha : a.Coprime N) :
    liftPrimitiveCharacter N (some ρ) (a : ZMod N) = ρ.character (a : ZMod ρ.modulus) := by
  rw [liftPrimitiveCharacter, dite_eq_left hd]
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a N).mpr ha
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast hd]

theorem sparseWeight_integer_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K a : ℕ) (ha : a.Coprime (∏ i, p i)) :
    elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (a : ZMod (p i))) K ^ 2 =
      sparsePrimitiveCoefficient p E t K none +
      ∑ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone,
        sparsePrimitiveCoefficient p E t K (some ρ) * ρ.character (a : ZMod ρ.modulus) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a (∏ i, p i)).mpr ha
  have hv (i : Fin n) : (crtUnitEquiv p hc u i : ZMod (p i)) = a := by
    rw [crtUnitEquiv_apply]
    change ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
      (ZMod (p i)) (u : ZMod (∏ i, p i)) = _
    rw [hu, map_natCast]
  have hh := sparseWeight_primitive_expansion p hc E t K u
  have hl : (fun i => sparseAdditiveKernel (E i) t (crtUnitEquiv p hc u i)) =
      (fun i => sparseAdditiveKernel (E i) t (a : ZMod (p i))) := by
    funext i
    rw [hv]
  rw [hl] at hh
  apply hh.trans
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [hu, liftPrimitiveCharacter_apply_nat _ _ ρ
    (sparsePrimitiveSupport_modulus_dvd p E t K ρ hρ) ha]

end Ostmann

end OAI
