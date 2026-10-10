import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
universe u
variable {k : Type u} [Field k] [Infinite k]
variable {V W : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

omit [Infinite k] in
lemma IsRational.linHom (ρ : Representation k (SL2 k) V)
    (σ : Representation k (SL2 k) W) (hρ : IsRational k ρ) (hσ : IsRational k σ) :
    IsRational k (Representation.linHom ρ σ) := by
  let e := Representation.Equiv.dualTensorHom ρ σ
  exact IsRational.of_surjective k _ _ e.toLinearMap e.toLinearEquiv.surjective
    (fun g x => congrArg (fun t => t x) (e.isIntertwining' g))
    (IsRational.tensor k _ _ (IsRational.dual k ρ hρ) hσ)

omit [Infinite k] [Module.Finite k V] [Module.Finite k W] in
lemma linHom_weight_apply (ρ : Representation k (SL2 k) V)
    (σ : Representation k (SL2 k) W) (n m : ℤ) (f : V →ₗ[k] W) (v : V)
    (hf : ∀ a, (Representation.linHom ρ σ) (diagonalTorus k a) f =
      integerCharacter k n a • f)
    (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k m a • v) :
    ∀ a, σ (diagonalTorus k a) (f v) = integerCharacter k (n+m) a • f v := by
  intro a
  have h := congrArg (fun q : V →ₗ[k] W => q (ρ (diagonalTorus k a) v)) (hf a)
  simp only [Representation.linHom_apply, LinearMap.comp_apply] at h
  rw [Representation.inv_self_apply] at h
  have hh : integerCharacter k (n+m) a =
      integerCharacter k n a * integerCharacter k m a := by
    simp [integerCharacter, zpow_add]
  simpa only [LinearMap.smul_apply, hv, map_smul, smul_smul, hh, mul_comm] using h

 
omit [Module.Finite k W] in
lemma hasWeightsBetween_linHom (ρ : Representation k (SL2 k) V)
    (σ : Representation k (SL2 k) W) (hρ : IsRational k ρ) (a b : ℕ)
    (hA : HasWeightsBetween ρ (-(a : ℤ)) a)
    (hB : HasWeightsBetween σ (-(b : ℤ)) b) :
    HasWeightsBetween (Representation.linHom ρ σ) (-(a+b : ℤ)) (a+b) := by
  intro n f hn hf
  have hvanish (m : ℤ) (v : V)
      (hv : ∀ t, ρ (diagonalTorus k t) v = integerCharacter k m t • v) : f v = 0 := by
    by_cases hz : v = 0
    · simp [hz]
    have hm : -(a : ℤ) ≤ m ∧ m ≤ a := by
      constructor <;> by_contra hh <;> apply hz
      · exact hA m v (Or.inl (by omega)) hv
      · exact hA m v (Or.inr (by omega)) hv
    apply hB (n+m) (f v) (by omega)
    exact linHom_weight_apply ρ σ n m f v hf hv
  ext v
  obtain ⟨c,hc⟩ := rational_torus_integerExpansions k ρ hρ v
  have hs : v = ∑ n ∈ c.support, c n := by
    simpa [Finsupp.sum, integerCharacter] using hc 1
  rw [hs, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  exact hvanish m (c m) (integer_coefficient_eigen k ρ v c hc m)
end FiberFunctorProof

end OAI
