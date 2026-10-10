import OAI.NumberTheory.CubicMoment.Estimates.IdealHeatCompletion
import OAI.NumberTheory.CubicMoment.Estimates.ResidueThetaLattice
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeCharacter

namespace OAI

/-! Exact angular ideal/element theta reindexing, including all finite
Euler factors and the term at zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angular_char_unit_mul (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (x : EisensteinIdealExponent × Eisensteinˣ) :
    χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val)*
      theta ℓ (idealElementCoordinates x).val = angularResidueIdealChar q χ ℓ x.1 := by
  change χ (Ideal.Quotient.mk (modulus q) ((x.2:Eisenstein)*idealExponentGenerator x.1))*
    theta ℓ ((x.2:Eisenstein)*idealExponentGenerator x.1) = _
  rw [map_mul,map_mul,theta_mul]
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) x.2)*theta ℓ x.2)*
      (χ (Ideal.Quotient.mk (modulus q) (idealExponentGenerator x.1))*
        theta ℓ (idealExponentGenerator x.1)) := by ring
    _ = _ := by rw [hu,one_mul]; rfl

lemma angular_unitCompatible_dual {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ) :
    AngularUnitCompatible q (star χ) (-ℓ) := by
  intro u
  rw [MulChar.star_apply,←star_theta u.ne_zero ℓ,←star_mul,mul_comm (theta ℓ u),hu u,star_one]

lemma idealHeatTheta_lattice {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    {A κ t : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (ht : 0 < t) :
    (∑' a : {a : Eisenstein // a ≠ 0},
      (χ (Ideal.Quotient.mk (modulus q) a.val)*theta ℓ a.val)*
        ((norm a.val*t/A)^κ*Real.exp (-norm a.val*t/A):ℝ)) =
      (Nat.card (Eisensteinˣ):ℂ)*idealHeatTheta A κ (angularResidueIdealChar q χ ℓ) t := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let f : EisensteinIdealExponent → ℂ := fun ν =>
    angularResidueIdealChar q χ ℓ ν*
      ((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)
  have hf : Summable f := idealHeatTheta_summable hA hκ ht _
    (angularResidueIdealChar_norm_le_one hq χ ℓ)
  have hprod : Summable (fun x : EisensteinIdealExponent × Eisensteinˣ => f x.1) := by
    simpa only [mul_one] using summable_mul_of_summable_norm
      (g := fun _ : Eisensteinˣ => (1:ℂ)) hf.norm (hasSum_fintype _).summable
  rw [←idealElementCoordinates.tsum_eq]
  have he : (fun x : EisensteinIdealExponent × Eisensteinˣ =>
      (χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val)*
        theta ℓ (idealElementCoordinates x).val)*
      ((norm (idealElementCoordinates x).val*t/A)^κ*
        Real.exp (-norm (idealElementCoordinates x).val*t/A):ℝ)) = fun x => f x.1 := by
    funext x
    rw [angular_char_unit_mul q χ ℓ hu,idealElementCoordinates_norm]
  rw [he,hprod.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [tsum_mul_left]
  simp only [Nat.card_eq_fintype_card]
  rfl

def angularLatticeHeat (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (A κ t : ℝ) : ℂ :=
  ∑' a : Eisenstein, (χ (Ideal.Quotient.mk (modulus q) a)*theta ℓ a)*
    ((norm a*t/A)^κ*Real.exp (-norm a*t/A):ℝ)

lemma theta_at_zero {ℓ : ℤ} (hℓ : ℓ ≠ 0) : theta ℓ (0:Eisenstein) = 0 := by
  simp only [theta,Subalgebra.coe_zero,norm_zero,Complex.ofReal_zero,div_zero]
  exact zero_zpow _ hℓ

lemma angularLatticeHeat_eq {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1)
    {A κ t : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (ht : 0 < t) :
    angularLatticeHeat q χ ℓ A κ t =
      (Nat.card (Eisensteinˣ):ℂ)*idealHeatTheta A κ (angularResidueIdealChar q χ ℓ) t := by
  rw [←idealHeatTheta_lattice hq χ ℓ hu hA hκ ht]
  symm
  unfold angularLatticeHeat
  apply tsum_subtype_eq_of_support_subset (s := {a : Eisenstein | a ≠ 0})
    (f := fun a : Eisenstein => (χ (Ideal.Quotient.mk (modulus q) a)*theta ℓ a)*
      ((norm a*t/A)^κ*Real.exp (-norm a*t/A):ℝ))
  intro a ha
  by_contra he
  have hz : a = 0 := not_not.mp he
  subst a
  rcases hn with hℓ | hχ
  · simp only [Function.mem_support,theta_at_zero hℓ,mul_zero,zero_mul,ne_eq,not_true_eq_false] at ha
  · let : Nontrivial (Residues q) := residue_nontrivial_of_nonprincipal χ hχ
    simp only [Function.mem_support,map_zero,MulChar.map_zero,zero_mul,ne_eq,not_true_eq_false] at ha

lemma angularHeat_inversion_of_lattice {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1) {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) {root : ℂ}
    (hFE : ∀ t : ℝ, 0 < t → angularLatticeHeat q χ ℓ A κ (1/t) =
      root*(t:ℂ)*angularLatticeHeat q (star χ) (-ℓ) A κ t) :
    ∀ t : ℝ, 0 < t → idealHeatTheta A κ (angularResidueIdealChar q χ ℓ) (1/t) =
      root*(t:ℂ)*idealHeatTheta A κ (angularResidueIdealChar q (star χ) (-ℓ)) t := by
  have hd := angular_unitCompatible_dual hu
  have hnd : -ℓ ≠ 0 ∨ star χ ≠ 1 := by
    rcases hn with hℓ | hχ
    · exact Or.inl (neg_ne_zero.mpr hℓ)
    · right
      intro h
      apply hχ
      simpa using congrArg star h
  intro t ht
  have h := hFE t ht
  rw [angularLatticeHeat_eq hq χ ℓ hu hn hA hκ (one_div_pos.mpr ht),
    angularLatticeHeat_eq hq (star χ) (-ℓ) hd hnd hA hκ ht] at h
  apply mul_left_cancel₀ residueTheta_unit_multiplicity_ne_zero
  calc
    _ = root*(t:ℂ)*((Nat.card (Eisensteinˣ):ℂ)*
      idealHeatTheta A κ (angularResidueIdealChar q (star χ) (-ℓ)) t) := h
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
