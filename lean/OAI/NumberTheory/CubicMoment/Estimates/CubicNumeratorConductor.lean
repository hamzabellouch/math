import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorPrimaryNoncube

namespace OAI

/-! Primitive reduction of the actual cubic numerator character preserves
its cubic order, its global unit invariance, and its values on primary
arguments prime to the original modulus. -/
noncomputable section
namespace CubicFirstMoment

lemma ResidueCharacterInduces.cube_eq_one {q d : Eisenstein}
    (hq : q ≠ 0) {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (hind : ResidueCharacterInduces q d χ ψ) (hχ : χ^3=1) : ψ^3=1 := by
  apply MulChar.ext
  intro u
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : Residues d)
  have hdx : IsCoprime d x := isCoprime_of_residue_isUnit (by rw [hx]; exact u.isUnit)
  obtain ⟨y,hy,hdy⟩ := exists_coprime_residue_lift hq hdx
  have hqy : IsCoprime q y := hdy.of_mul_left_right
  have he : ψ u = χ (Ideal.Quotient.mk (modulus q) y) := by
    rw [←hx,←residue_eq_of_dvd_sub hy]
    exact hind.2 y hqy
  rw [MulChar.pow_apply' _ (by norm_num),he,MulChar.one_apply u.isUnit]
  have h := congrArg (fun ξ : MulChar (Residues q) ℂ => ξ (Ideal.Quotient.mk (modulus q) y)) hχ
  simpa only [MulChar.pow_apply' _ (by norm_num : (3:ℕ) ≠ 0),
    MulChar.one_apply (residue_isUnit_of_isCoprime hqy)] using h

/-- Exact primitive character associated with any nonzero numerator. -/
theorem cubicNumerator_primitive_conductor (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : v ≠ 0) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧
      d ∣ 9*v ∧ normNat d ≤ normNat (9*v) ∧ ψ^3=1 ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u)=1) ∧
      ResidueCharacterInduces (9*v) d (cubicNumeratorChar hpub v hv) ψ ∧
      (∀ x : Eisenstein, primary x → IsCoprime v x →
        ψ (Ideal.Quotient.mk (modulus d) x)=cubicSymbol x v) := by
  have hq : 9*v ≠ (0:Eisenstein) := mul_ne_zero (by norm_num) hv
  obtain ⟨d,ψ,hd,hi,hN,hp⟩ := primitive_residue_conductor_exists hq
    (cubicNumeratorChar hpub v hv)
  refine ⟨d,ψ,hd,hp,hi.1,hN,hi.cube_eq_one hq (cubicNumeratorChar_cube hpub v hv),
    hi.global_units (cubicNumeratorChar_units hpub v hv),hi,?_⟩
  intro x hx hcop
  have h9x : IsCoprime (9:Eisenstein) x := by
    convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
    norm_num
  exact (hi.2 x (h9x.mul_left hcop)).trans (cubicNumeratorChar_primary hpub v hv hx)

/-- For a primary noncube the primitive character is nonprincipal and
nonreal; no exceptional real character is introduced in conductor reduction. -/
theorem primaryNoncube_primitive_conductor (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : primary v) (hn : ¬∃ j : Eisenstein, j^3=v) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧ star ψ ≠ ψ ∧
      normNat d ≤ normNat (9*v) ∧ ψ^3=1 ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u)=1) ∧
      (∀ x : Eisenstein, primary x → IsCoprime v x →
        ψ (Ideal.Quotient.mk (modulus d) x)=cubicSymbol x v) := by
  obtain ⟨d,ψ,hd,hp,_,hN,h3,hu,hi,hval⟩ :=
    cubicNumerator_primitive_conductor hpub (primary_ne_zero hv)
  have hχ := cubicNumeratorChar_primary_noncube hpub hv hn
  obtain ⟨x,hx,hcop,hne⟩ := (cubicNumeratorChar_ne_one_iff hpub v (primary_ne_zero hv)).mp hχ
  have hψ : ψ ≠ 1 := hi.nonprincipal ⟨x,hcop,by
    rwa [cubicNumeratorChar_primary hpub v (primary_ne_zero hv) hx]⟩
  let : Finite (Residues d) := finite_residues hd
  exact ⟨d,ψ,hd,hp,hψ,odd_cubic_character_not_self_conjugate ψ h3 hψ,hN,h3,hu,hval⟩

end CubicFirstMoment

end

end OAI
