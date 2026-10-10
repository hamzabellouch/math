import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters
import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra

namespace OAI

/-! The finite factor at 3 required by a fixed angular Hecke character.
The archimedean phase is retained separately, including after primitive
conductor reduction. Complete ideal sums therefore include every prime
at which the primitive character is unramified. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

private instance : Nontrivial (Residues (3 : Eisenstein)) := residue_three_nontrivial

lemma theta_ne_zero {x : Eisenstein} (hx : x ≠ 0) (ℓ : ℤ) : theta ℓ x ≠ 0 := by
  intro h
  have hn := norm_theta hx ℓ
  rw [h, norm_zero] at hn
  norm_num at hn

lemma star_theta {x : Eisenstein} (hx : x ≠ 0) (ℓ : ℤ) :
    star (theta ℓ x) = theta (-ℓ) x := by
  rw [show theta (-ℓ) x = (theta ℓ x)⁻¹ by simp only [theta, zpow_neg]]
  exact (Complex.inv_eq_conj (norm_theta hx ℓ)).symm

private lemma ne_zero_of_three_unit {x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)) : x ≠ 0 := by
  intro h
  simpa [h] using hx.ne_zero

/-- On elements prime to 3 this is precisely the unit correction
`theta_l(primaryNormalize x) / theta_l(x)`. It vanishes at the ramified
prime; it is a finite character, not an additional archimedean phase. -/
def angularUnitCorrection (ℓ : ℤ) (x : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus 3) x) then
    theta ℓ (primaryNormalize x) / theta ℓ x else 0

lemma angularUnitCorrection_one (ℓ : ℤ) : angularUnitCorrection ℓ 1 = 1 := by
  simp [angularUnitCorrection, primaryNormalize_eq_self (show primary 1 by simp [primary])]

lemma angularUnitCorrection_mul (ℓ : ℤ) (x y : Eisenstein) :
    angularUnitCorrection ℓ (x*y) = angularUnitCorrection ℓ x*angularUnitCorrection ℓ y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · by_cases hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)
    · simp only [angularUnitCorrection, map_mul, IsUnit.mul_iff, hx, hy,
        and_self, ite_true, primaryNormalize_mul_of_residue_units hx hy, theta_mul]
      exact mul_div_mul_comm _ _ _ _
    · simp [angularUnitCorrection, map_mul, IsUnit.mul_iff, hx, hy]
  · simp [angularUnitCorrection, map_mul, IsUnit.mul_iff, hx]

lemma angularUnitCorrection_primary {x : Eisenstein} (hx : primary x) (ℓ : ℤ) :
    angularUnitCorrection ℓ x = 1 := by
  rw [angularUnitCorrection, ite_eq_left (unit_residue_of_dvd_primary hx (dvd_refl x)),
    primaryNormalize_eq_self hx, div_self (theta_ne_zero (primary_ne_zero hx) ℓ)]

lemma angularUnitCorrection_congr (ℓ : ℤ) {x y : Eisenstein}
    (h3 : Ideal.Quotient.mk (modulus 3) x = Ideal.Quotient.mk (modulus 3) y) :
    angularUnitCorrection ℓ x = angularUnitCorrection ℓ y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hy : IsUnit (Ideal.Quotient.mk (modulus 3) y) := h3 ▸ hx
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hp : primary (y*(u:Eisenstein)) := by
      apply (primary_iff_residue_one _).mpr
      rw [map_mul, ←h3, ←map_mul, hu]
      exact (primary_iff_residue_one _).mp (primaryNormalize_primary hx)
    have he : primaryNormalize y = y*(u:Eisenstein) :=
      primary_associated_eq (primaryNormalize_primary hy) hp
        ((primaryNormalize_associated y).symm.trans ⟨u,rfl⟩)
    simp only [angularUnitCorrection, ite_eq_left hx, ite_eq_left hy, he, ←hu, theta_mul]
    rw [mul_div_cancel_left₀ _ (theta_ne_zero (ne_zero_of_three_unit hx) ℓ),
      mul_div_cancel_left₀ _ (theta_ne_zero (ne_zero_of_three_unit hy) ℓ)]
  · have hy : ¬ IsUnit (Ideal.Quotient.mk (modulus 3) y) := by
      simpa only [←h3] using hx
    simp [angularUnitCorrection, hx, hy]

/-- The correction is literally a multiplicative residue character
modulo 3. Thus its conductor divides 3. -/
def angularCorrectionChar (ℓ : ℤ) : MulChar (Residues (3 : Eisenstein)) ℂ where
  toFun v := angularUnitCorrection ℓ (residueRepresentative 3 v)
  map_one' := by
    rw [angularUnitCorrection_congr ℓ (show
      Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 1) =
        Ideal.Quotient.mk (modulus 3) 1 by rw [residueRepresentative_spec, map_one])]
    exact angularUnitCorrection_one ℓ
  map_mul' v w := by
    rw [angularUnitCorrection_congr ℓ (show
      Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 (v*w)) =
        Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 v*residueRepresentative 3 w)
          by rw [map_mul, residueRepresentative_spec, residueRepresentative_spec,
            residueRepresentative_spec])]
    exact angularUnitCorrection_mul ℓ _ _
  map_nonunit' v hv := by
    simp only [angularUnitCorrection, residueRepresentative_spec, ite_eq_right hv]

@[simp] lemma angularCorrectionChar_mk (ℓ : ℤ) (x : Eisenstein) :
    angularCorrectionChar ℓ (Ideal.Quotient.mk (modulus 3) x) =
      angularUnitCorrection ℓ x :=
  angularUnitCorrection_congr ℓ (residueRepresentative_spec _ _)

lemma angularUnitCorrection_compensates (ℓ : ℤ) {x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)) :
    angularUnitCorrection ℓ x*theta ℓ x = theta ℓ (primaryNormalize x) := by
  rw [angularUnitCorrection, ite_eq_left hx]
  exact div_mul_cancel₀ _ (theta_ne_zero (ne_zero_of_three_unit hx) ℓ)

lemma angularCorrectionChar_unit (ℓ : ℤ) (u : Eisensteinˣ) :
    angularCorrectionChar ℓ (Ideal.Quotient.mk (modulus 3) u)*theta ℓ u = 1 := by
  rw [angularCorrectionChar_mk,
    angularUnitCorrection_compensates ℓ (u.isUnit.map (Ideal.Quotient.mk (modulus 3))),
    primaryNormalize_unit u.isUnit, theta_one]

/-- The correct unit condition for infinity type `ell`. For `ell=0`
it reduces to triviality on global units. -/
def AngularUnitCompatible (q : Eisenstein) (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) : Prop :=
  ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u = 1

lemma ResidueCharacterInduces.angular_units {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) {ℓ : ℤ}
    (hu : AngularUnitCompatible q χ ℓ) : AngularUnitCompatible d ψ ℓ := by
  intro u
  rw [h.2 u (show IsCoprime q (u:Eisenstein) from ⟨0,(u⁻¹:Eisensteinˣ),by simp⟩)]
  exact hu u

/-- Full primitive coefficients, before removing any Euler factor. -/
def angularResidueIdealChar (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν : EisensteinIdealExponent) : ℂ :=
  residueIdealChar q χ ν*theta ℓ (idealExponentGenerator ν)

lemma angularResidueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν κ : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ (ν+κ) =
      angularResidueIdealChar q χ ℓ ν*angularResidueIdealChar q χ ℓ κ := by
  simp only [angularResidueIdealChar, residueIdealChar_add, idealExponentGenerator_add, theta_mul]
  ring

lemma angularResidueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    ‖angularResidueIdealChar q χ ℓ ν‖ ≤ 1 := by
  rw [angularResidueIdealChar, norm_mul, norm_theta (idealExponentGenerator_ne_zero ν), mul_one]
  exact residueIdealChar_norm_le_one hq χ ν

lemma star_angularResidueIdealChar (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    star (angularResidueIdealChar q χ ℓ ν) = angularResidueIdealChar q (star χ) (-ℓ) ν := by
  simp only [angularResidueIdealChar, residueIdealChar, star_mul, MulChar.star_apply,
    star_theta (idealExponentGenerator_ne_zero ν)]
  ring

lemma angular_character_associated {q x y : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hxy : Associated x y) :
    χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x =
      χ (Ideal.Quotient.mk (modulus q) y)*theta ℓ y := by
  obtain ⟨u,rfl⟩ := hxy
  rw [map_mul, map_mul, theta_mul]
  symm
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x)*
        (χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u) := by ring
    _ = _ := by rw [hu u, mul_one]

lemma angularResidueIdealChar_at_element {q x : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hx : x ≠ 0) :
    angularResidueIdealChar q χ ℓ (idealExponentOf x) =
      χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x :=
  angular_character_associated χ hu (idealExponentOf_associated hx)

lemma induced_angularResidueIdealChar {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ ν =
      if ∀ p ∈ (idealExponentOf q).support, ν p = 0 then
        angularResidueIdealChar d ψ ℓ ν else 0 := by
  rw [angularResidueIdealChar, induced_residueIdealChar hq h]
  split <;> simp [angularResidueIdealChar]

/-- Primitive reduction preserves the angular factor and restores
the actual omitted local Euler factors with their exact rescalings. -/
theorem induced_angular_smooth_euler {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' ν, angularResidueIdealChar q χ ℓ ν*W (idealExponentNorm ν/Z)) =
      ∑ T ∈ (idealExponentOf q).support.powerset,
        (-1:ℂ)^T.card*angularResidueIdealChar d ψ ℓ (primeSetExponent T)*
          ∑' κ, angularResidueIdealChar d ψ ℓ κ*
            W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  have he := smooth_ideal_euler_exclusion (idealExponentOf q).support
    (angularResidueIdealChar d ψ ℓ) (angularResidueIdealChar_add d ψ ℓ) W hW hZ
  rw [←he]
  apply tsum_congr
  intro ν
  rw [induced_angularResidueIdealChar hq h]
  split <;> simp

def primaryAngularMixedLift (ℓ : ℤ) (a b x : Eisenstein) : ℂ :=
  angularUnitCorrection ℓ x*primaryMixedLift a b x

lemma primaryAngularMixedLift_one (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) : primaryAngularMixedLift ℓ a b 1 = 1 := by
  rw [primaryAngularMixedLift, angularUnitCorrection_one, primaryMixedLift_one ha hb, mul_one]

lemma primaryAngularMixedLift_mul (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (x y : Eisenstein) :
    primaryAngularMixedLift ℓ a b (x*y) =
      primaryAngularMixedLift ℓ a b x*primaryAngularMixedLift ℓ a b y := by
  simp only [primaryAngularMixedLift, angularUnitCorrection_mul, primaryMixedLift_mul ha hb]
  ring

lemma primaryAngularMixedLift_congr (ℓ : ℤ) {a b x y : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (3*(a*b))) x =
      Ideal.Quotient.mk (modulus (3*(a*b))) y) :
    primaryAngularMixedLift ℓ a b x = primaryAngularMixedLift ℓ a b y := by
  have hd : 3*(a*b) ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have h3 : Ideal.Quotient.mk (modulus 3) x = Ideal.Quotient.mk (modulus 3) y :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ((dvd_mul_right 3 (a*b)).trans hd))
  rw [primaryAngularMixedLift, primaryAngularMixedLift,
    angularUnitCorrection_congr ℓ h3, primaryMixedLift_congr h]

/-- The actual finite part of `theta_l * mixedCubic a b`, with the
necessary unit compensation at 3. Its values on primary elements equal
the mixed cubic symbol, but its values on units depend on `ell`. -/
def primaryAngularMixedChar (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) : MulChar (Residues (3*(a*b))) ℂ where
  toFun v := primaryAngularMixedLift ℓ a b (residueRepresentative (3*(a*b)) v)
  map_one' := by
    rw [primaryAngularMixedLift_congr ℓ (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) 1) =
        Ideal.Quotient.mk (modulus (3*(a*b))) 1 by rw [residueRepresentative_spec, map_one])]
    exact primaryAngularMixedLift_one ℓ ha hb
  map_mul' v w := by
    rw [primaryAngularMixedLift_congr ℓ (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) (v*w)) =
        Ideal.Quotient.mk (modulus (3*(a*b)))
          (residueRepresentative (3*(a*b)) v*residueRepresentative (3*(a*b)) w) by
            rw [map_mul, residueRepresentative_spec, residueRepresentative_spec,
              residueRepresentative_spec])]
    exact primaryAngularMixedLift_mul ℓ ha hb _ _
  map_nonunit' v hv := by
    rw [primaryAngularMixedLift,
      primaryMixedLift_nonunit ha hb (by rwa [residueRepresentative_spec]), mul_zero]

@[simp] lemma primaryAngularMixedChar_mk (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (x : Eisenstein) :
    primaryAngularMixedChar ℓ a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      primaryAngularMixedLift ℓ a b x :=
  primaryAngularMixedLift_congr ℓ (residueRepresentative_spec _ _)

lemma primaryAngularMixedChar_primary (ℓ : ℤ) {a b x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) :
    primaryAngularMixedChar ℓ a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      mixedCubic a b x := by
  rw [primaryAngularMixedChar_mk, primaryAngularMixedLift,
    angularUnitCorrection_primary hx, primaryMixedLift_primary hx, one_mul]

lemma primaryAngularMixedChar_compatible (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) :
    AngularUnitCompatible (3*(a*b)) (primaryAngularMixedChar ℓ a b ha hb) ℓ := by
  intro u
  rw [primaryAngularMixedChar_mk, primaryAngularMixedLift,
    primaryMixedLift_unit ha hb u.isUnit, mul_one]
  exact angularUnitCorrection_compensates ℓ
    (u.isUnit.map (Ideal.Quotient.mk (modulus 3))) |>.trans (by
      rw [primaryNormalize_unit u.isUnit, theta_one])

lemma primaryAngularMixedIdealChar_at_primary (ℓ : ℤ) {a b x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) :
    angularResidueIdealChar (3*(a*b)) (primaryAngularMixedChar ℓ a b ha hb) ℓ
      (idealExponentOf x) = mixedCubic a b x*theta ℓ x := by
  rw [angularResidueIdealChar_at_element _ (primaryAngularMixedChar_compatible ℓ ha hb)
    (primary_ne_zero hx), primaryAngularMixedChar_primary ℓ ha hb hx]

/-- Primitive reduction is now applied to the actual compensated finite
character. It preserves its infinity type and the conductor norm bound. -/
theorem primitive_angular_mixed_exists (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ), d ≠ 0 ∧
      ResidueCharacterInduces (3*(a*b)) d (primaryAngularMixedChar ℓ a b ha hb) ψ ∧
      normNat d ≤ normNat (3*(a*b)) ∧ PrimitiveResidueCharacter d ψ ∧
      AngularUnitCompatible d ψ ℓ := by
  have hq : (3:Eisenstein)*(a*b) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
  obtain ⟨d,ψ,hd,hi,hN,hP⟩ :=
    primitive_residue_conductor_exists hq (primaryAngularMixedChar ℓ a b ha hb)
  exact ⟨d,ψ,hd,hi,hN,hP,hi.angular_units (primaryAngularMixedChar_compatible ℓ ha hb)⟩

end CubicFirstMoment

end

end OAI
