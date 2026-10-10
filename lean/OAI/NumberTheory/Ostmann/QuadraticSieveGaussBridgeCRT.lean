import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBridgePrime

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def crtLeftAddChar {m n : ℕ} (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod m) ℂ :=
  ψ.compAddMonoidHom
    { toFun := fun a => (ZMod.chineseRemainder h).symm (a, 0)
      map_zero' := by simp
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        simp }

noncomputable def crtRightAddChar {m n : ℕ} (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod n) ℂ :=
  ψ.compAddMonoidHom
    { toFun := fun b => (ZMod.chineseRemainder h).symm (0, b)
      map_zero' := by simp
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        simp }

lemma crtAddChar_apply {m n : ℕ} (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) (a : ZMod m) (b : ZMod n) :
    ψ ((ZMod.chineseRemainder h).symm (a, b)) =
      crtLeftAddChar h ψ a * crtRightAddChar h ψ b := by
  change ψ ((ZMod.chineseRemainder h).symm (a, b)) =
    ψ ((ZMod.chineseRemainder h).symm (a, 0)) * ψ ((ZMod.chineseRemainder h).symm (0, b))
  rw [← ψ.map_add_eq_mul, ← map_add]
  congr 1
  simp

lemma crtLeftAddChar_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (ψ : AddChar (ZMod (m * n)) ℂ) (hψ : ψ.IsPrimitive) :
    (crtLeftAddChar h ψ).IsPrimitive := by
  apply AddChar.zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  change ψ ((ZMod.chineseRemainder h).symm (a, 0)) = 1 at ha
  have hz := (hψ.zmod_char_eq_one_iff (m * n) _).mp ha
  have hz' := congrArg (fun x => ((ZMod.chineseRemainder h) x).1) hz
  simpa using hz'

lemma crtRightAddChar_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (ψ : AddChar (ZMod (m * n)) ℂ) (hψ : ψ.IsPrimitive) :
    (crtRightAddChar h ψ).IsPrimitive := by
  apply AddChar.zmod_char_primitive_of_eq_one_only_at_zero
  intro b hb
  change ψ ((ZMod.chineseRemainder h).symm (0, b)) = 1 at hb
  have hz := (hψ.zmod_char_eq_one_iff (m * n) _).mp hb
  have hz' := congrArg (fun x => ((ZMod.chineseRemainder h) x).2) hz
  simpa using hz'

theorem jacobiDirichletCharacter_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    jacobiDirichletCharacter (m * n) x =
      jacobiDirichletCharacter m ((ZMod.chineseRemainder h) x).1 *
        jacobiDirichletCharacter n ((ZMod.chineseRemainder h) x).2 := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast (ZMod.chineseRemainder h)]
  change jacobiDirichletCharacter (m * n) (a : ZMod (m * n)) =
    jacobiDirichletCharacter m (a : ZMod m) * jacobiDirichletCharacter n (a : ZMod n)
  rw [jacobiDirichletCharacter_intCast, jacobiDirichletCharacter_intCast,
    jacobiDirichletCharacter_intCast, jacobiSym.mul_right' a (NeZero.ne m) (NeZero.ne n), Int.cast_mul]

theorem quadratic_sum_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (ψ : AddChar (ZMod (m * n)) ℂ) :
    (∑ x : ZMod (m * n), ψ (x ^ 2)) =
      (∑ a : ZMod m, crtLeftAddChar h ψ (a ^ 2)) *
        (∑ b : ZMod n, crtRightAddChar h ψ (b ^ 2)) := by
  calc
    _ = ∑ x : ZMod m × ZMod n, ψ (((ZMod.chineseRemainder h).symm x) ^ 2) :=
      Fintype.sum_equiv (ZMod.chineseRemainder h).toEquiv
        (fun x : ZMod (m * n) => ψ (x ^ 2))
        (fun x : ZMod m × ZMod n => ψ (((ZMod.chineseRemainder h).symm x) ^ 2))
        (fun x => by simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply])
    _ = ∑ a : ZMod m, ∑ b : ZMod n,
        crtLeftAddChar h ψ (a ^ 2) * crtRightAddChar h ψ (b ^ 2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← map_pow (ZMod.chineseRemainder h).symm]
      have hp : ((a, b) : ZMod m × ZMod n) ^ 2 = (a ^ 2, b ^ 2) := by rfl
      rw [hp]
      exact crtAddChar_apply h ψ (a ^ 2) (b ^ 2)
    _ = _ := (Finset.sum_mul_sum _ _ _ _).symm

theorem jacobi_gauss_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (ψ : AddChar (ZMod (m * n)) ℂ) :
    gaussSum (jacobiDirichletCharacter (m * n)) ψ =
      gaussSum (jacobiDirichletCharacter m) (crtLeftAddChar h ψ) *
        gaussSum (jacobiDirichletCharacter n) (crtRightAddChar h ψ) := by
  unfold gaussSum
  calc
    _ = ∑ x : ZMod m × ZMod n, jacobiDirichletCharacter (m * n)
        ((ZMod.chineseRemainder h).symm x) * ψ ((ZMod.chineseRemainder h).symm x) :=
      Fintype.sum_equiv (ZMod.chineseRemainder h).toEquiv
        (fun x : ZMod (m * n) => jacobiDirichletCharacter (m * n) x * ψ x)
        (fun x : ZMod m × ZMod n => jacobiDirichletCharacter (m * n)
          ((ZMod.chineseRemainder h).symm x) * ψ ((ZMod.chineseRemainder h).symm x))
        (fun x => by simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply])
    _ = ∑ a : ZMod m, ∑ b : ZMod n,
        (jacobiDirichletCharacter m a * crtLeftAddChar h ψ a) *
          (jacobiDirichletCharacter n b * crtRightAddChar h ψ b) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [jacobiDirichletCharacter_crt h, RingEquiv.apply_symm_apply, crtAddChar_apply]
      ring
    _ = _ := (Finset.sum_mul_sum _ _ _ _).symm

end Ostmann.QuadraticSieve

end OAI
