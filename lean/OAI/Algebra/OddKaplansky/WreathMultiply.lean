import OAI.Algebra.OddKaplansky.WreathLinear

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2

section

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [sectionInstance14 : Fintype H]
variable (M : ℕ) [sectionInstance15 : NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)

@[simp] lemma topElt_mul
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (h g : H) : topElt (K := K) M h * topElt M g = topElt M (h*g) := by
  simp [topElt,MonoidAlgebra.single_mul_single, ← map_mul]
@[simp] lemma topElt_one
    {K : Type contextUniverse1}
    {H : Type contextUniverse2}
    [Field.{contextUniverse1} K]
    [Group.{contextUniverse2} H]
    [Fintype.{contextUniverse2} H]
    (M : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] : topElt (K := K) (H := H) M 1 = 1 := by rw [topElt,map_one]; rfl

lemma topElt_projector (h : H) (lmb : Base (H := H) M) :
    topElt M h * projector M hζ lmb = projector M hζ (shift M h lmb) * topElt M h := by
  calc
    _ = (topElt M h * projector M hζ lmb * topElt M h⁻¹) * topElt M h := by
      rw [mul_assoc _ (topElt M h⁻¹),topElt_mul,inv_mul_cancel,topElt_one,mul_one]
    _ = _ := by rw [translated]

include hc in
lemma normal_mul (lmb μ : Base (H := H) M) (h g : H) :
    normal M hζ lmb h * normal M hζ μ g =
      if lmb = shift M h μ then normal M hζ lmb (h*g) else 0 := by
  unfold normal
  have heq : (projector M hζ lmb * topElt M h) * (projector M hζ μ * topElt M g) =
      (projector M hζ lmb * projector M hζ (shift M h μ)) * (topElt M h * topElt M g) := by
    rw [mul_assoc, ← mul_assoc (topElt M h), topElt_projector]
    simp only [mul_assoc]
  rw [heq,topElt_mul]
  by_cases he : lmb = shift M h μ
  · rw [← he,projector_idempotent M hζ hc,ite_eq_left rfl]
  · rw [projector_orthogonal M hζ _ _ he,zero_mul,ite_eq_right he]

lemma normal_expansion (z : MonoidAlgebra K (Wreath (H := H) M)) :
    ∑ a : Base (H := H) M × H, (normalBasis M hζ hc).repr z a • normal M hζ a.1 a.2 = z := by
  simpa only [normalBasis_apply] using (normalBasis M hζ hc).sum_repr z

lemma normal_repr (z : MonoidAlgebra K (Wreath (H := H) M)) (a : Base (H := H) M × H) :
    (normalBasis M hζ hc).repr z a = (rho M hζ z a.1 (shift M a.2⁻¹ a.1)).coeff a.2 := by
  have he := congrArg (fun z => (rho M hζ z a.1 (shift M a.2⁻¹ a.1)).coeff a.2)
    (normal_expansion M hζ hc z)
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul] at he
  simp_rw [normal_coordinate M hζ hc] at he
  have hh (b : Base (H := H) M × H) : b.1 = a.1 ∧ b.2 = a.2 ↔ b = a := Prod.ext_iff.symm
  simpa only [hh,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using he

include hc in
lemma rho_injective : Function.Injective (rho (K := K) (H := H) M hζ) := by
  intro z t he
  apply (normalBasis M hζ hc).repr.injective
  ext a
  rw [normal_repr,normal_repr,he]

end
end OddKaplansky.WreathFourier

end

end OAI
