import OAI.Algebra.OddKaplansky.WreathRepresentation

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section

namespace OddKaplansky.CharacterIdempotents
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} [Field K] [Group A] [Fintype A]
lemma character_pairing (χ ψ : A →* Kˣ) :
    (∑ a : A, (χ a : K) * (ψ a : K)⁻¹) = if χ = ψ then (Fintype.card A : K) else 0 := by
  by_cases he : χ = ψ
  · subst ψ; simp
  · rw [ite_eq_right he]
    have hn : χ * ψ⁻¹ ≠ 1 := by
      intro h
      apply he
      apply MonoidHom.ext
      intro a
      exact mul_inv_eq_one.mp (congrArg (fun f : A →* Kˣ => f a) h)
    simpa using sum_character_eq_zero (χ * ψ⁻¹) hn

def evaluate (χ : A →* Kˣ) : MonoidAlgebra K A →ₐ[K] K :=
  MonoidAlgebra.lift K K A ((Units.coeHom K).comp χ)
lemma evaluate_projector (χ ψ : A →* Kˣ) (hc : (Fintype.card A : K) ≠ 0) :
    evaluate χ (projector ψ) = if χ = ψ then 1 else 0 := by
  simp only [evaluate, projector, map_smul, map_sum, MonoidAlgebra.lift_single,
    MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul]
  rw [show (∑ a : A, (ψ a : K)⁻¹ * (χ a : K)) =
        ∑ a : A, (χ a : K) * (ψ a : K)⁻¹ by apply Finset.sum_congr rfl; intros; exact mul_comm _ _]
  rw [character_pairing]
  split_ifs <;> simp [hc]
end
end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} {H : Type portUniverse4} [Field K] [Group H] [Fintype H]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

lemma rho_projector (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (lmb x y : Base (H := H) M) :
    rho M hζ (projector M hζ lmb) x y = if x = y ∧ x = lmb then 1 else 0 := by
  unfold projector
  rw [CharacterIdempotents.pushed_eq_sum, map_smul, map_sum]
  simp only [Matrix.smul_apply, Matrix.sum_apply, rho_single, base_left, base_right, shift_one,
    MulEquiv.refl_apply]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true,       true_and]
    have hs (f : Base (H := H) M → K) : (∑ a, MonoidAlgebra.single (1 : H) (f a)) =
        MonoidAlgebra.single 1 (∑ a, f a) :=
      (map_sum (MonoidAlgebra.singleAddHom (1 : H)) f Finset.univ).symm
    rw [hs]
    have he := CharacterIdempotents.character_pairing
      (Fourier.character M hζ x) (Fourier.character M hζ lmb)
    have hi : Fourier.character M hζ x = Fourier.character M hζ lmb ↔ x = lmb :=
      (Fourier.character_injective M hζ).eq_iff
    simp only [hi] at he
    simp_rw [mul_comm ((Fourier.character M hζ lmb _ : K)⁻¹)]
    rw [he]
    split_ifs
    · rw [MonoidAlgebra.smul_single, smul_eq_mul]
      change MonoidAlgebra.single (1 : H) ((Fintype.card (Base (H := H) M) : K)⁻¹ *
        (Fintype.card (Base (H := H) M) : K)) = MonoidAlgebra.single 1 1
      rw [inv_mul_cancel₀ hc]
    · simp
  · simp [hxy]

def normal (lmb : Base (H := H) M) (h : H) : MonoidAlgebra K (Wreath (H := H) M) :=
  projector M hζ lmb * topElt M h

lemma rho_normal (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (lmb : Base (H := H) M) (h : H) (x y : Base (H := H) M) :
    rho M hζ (normal M hζ lmb h) x y =
      if x = lmb ∧ x = shift M h y then MonoidAlgebra.single h 1 else 0 := by
  rw [normal, map_mul, Matrix.mul_apply, Finset.sum_eq_single x]
  · rw [rho_projector M hζ hc, rho_top]
    by_cases hxl : x = lmb <;> by_cases hxy : x = shift M h y <;> simp [hxl, hxy]
  · intro z _ hzx
    rw [rho_projector M hζ hc]
    simp [Ne.symm hzx]
  · simp

end
end OddKaplansky.WreathFourier

end

end OAI
