import OAI.Algebra.OddKaplansky.WreathBasis

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2

section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [sectionInstance13 : Group H] [Fintype H]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)

include hc in
lemma normal_coordinate (lmb μ : Base (H := H) M) (h g : H) :
    (rho M hζ (normal M hζ μ g) lmb (shift M h⁻¹ lmb)).coeff h =
      if μ = lmb ∧ g = h then 1 else 0 := by
  rw [rho_normal M hζ hc]
  by_cases hgh : g = h
  · subst g
    simp only [shift_shift_inverse, and_true]
    by_cases hml : μ = lmb
    · subst μ; simp
    · simp [hml, Ne.symm hml]
  · simp only [hgh, and_false, ite_false]
    split_ifs <;> simp [hgh]

include hc in
lemma normal_independent : LinearIndependent K (fun a : Base (H := H) M × H => normal M hζ a.1 a.2) := by
  rw [linearIndependent_iff']
  intro s c hs a ha
  have he := congrArg (fun z => (rho M hζ z a.1 (shift M a.2⁻¹ a.1)).coeff a.2) hs
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finset.sum_apply',
    Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul, map_zero, Matrix.zero_apply, MonoidAlgebra.coeff_zero] at he
  simp_rw [normal_coordinate M hζ hc] at he
  have hh (b : Base (H := H) M × H) : b.1 = a.1 ∧ b.2 = a.2 ↔ b = a := Prod.ext_iff.symm
  simpa only [hh, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_left ha] using he

instance : Fintype (Wreath (H := H) M) := Fintype.ofFinite _

lemma normal_card
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : Fintype.card (Base (H := H) M × H) =
    Module.finrank K (MonoidAlgebra K (Wreath (H := H) M)) := by
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis _ K)]
  apply Fintype.card_congr
  exact { toFun := fun a => ⟨a.1,a.2⟩
          invFun := fun g => (g.left,g.right)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

def normalBasis : Module.Basis (Base (H := H) M × H) K (MonoidAlgebra K (Wreath (H := H) M)) :=
  Module.Basis.mk (normal_independent M hζ hc)
    ((normal_independent M hζ hc).span_eq_top_of_card_eq_finrank' (normal_card (K := K) M)).ge
@[simp] lemma normalBasis_apply (a : Base (H := H) M × H) :
    normalBasis M hζ hc a = normal M hζ a.1 a.2 := Module.Basis.mk_apply _ _ _

end
end OddKaplansky.WreathFourier

end

end OAI
