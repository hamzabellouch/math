import OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent

namespace OAI

noncomputable section

namespace PiExponent

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

theorem primeLocalDirectional_polynomial (v : ι → Q.ResidueField) (p : MvPolynomial ι C) :
    primeLocalDirectional Q v
      (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) =
      ∑ i, v i * primeResidueMap Q (MvPolynomial.pderiv i p) := by
  calc
    _ = ∑ i, v i * primeLocalPartial Q i
        (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) := by
      change (Derivation.coeFnAddMonoidHom (∑ i, v i • primeLocalPartial Q i)) _ = _
      rw [map_sum, Finset.sum_apply]
      rfl
    _ = _ := by simp only [primeLocalPartial_polynomial]; rfl

theorem primeLocalDirectional_maximalIdeal_eq_zero
    (v : ι → Q.ResidueField) (hv : v ∈ polynomialTangent (primeResidueMap Q) Q)
    (x : IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    primeLocalDirectional Q v x = 0 := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj Q.primeCompl (x : Localization.AtPrime Q)
  have hamem : algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) a ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [← hs]
    exact Ideal.mul_mem_right _ _ x.2
  have haQ : a ∈ Q :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q a).mp hamem
  have hDa : primeLocalDirectional Q v
      (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) a) = 0 := by
    rw [primeLocalDirectional_polynomial]
    have hh := congrFun hv (⟨a, haQ⟩ : Q)
    simpa only [polynomialJacobian, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
      mul_comm] using hh
  have hx0 : algebraMap (Localization.AtPrime Q) Q.ResidueField x = 0 := by
    change IsLocalRing.residue (Localization.AtPrime Q) x = 0
    exact (IsLocalRing.residue_eq_zero_iff (x : Localization.AtPrime Q)).mpr x.2
  have hs0 : algebraMap (MvPolynomial ι C) Q.ResidueField (s : MvPolynomial ι C) ≠ 0 := by
    intro hz
    exact s.2 (Ideal.algebraMap_residueField_eq_zero.mp hz)
  have hD := congrArg (primeLocalDirectional Q v) hs
  rw [Derivation.leibniz, hDa, Algebra.smul_def, Algebra.smul_def, hx0,
    zero_mul, zero_add, ← IsScalarTower.algebraMap_apply] at hD
  exact (mul_eq_zero.mp hD).resolve_left hs0

theorem primeNormalPairing_ker_eq_tangent :
    LinearMap.ker (primeNormalPairing Q) = polynomialTangent (primeResidueMap Q) Q := by
  apply le_antisymm (primeNormalPairing_ker_le_tangent Q)
  intro v hv
  change primeNormalPairing Q v = 0
  ext x
  obtain ⟨a, rfl⟩ := (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent_surjective x
  rw [primeNormalPairing_toCotangent]
  exact primeLocalDirectional_maximalIdeal_eq_zero Q v hv a

end PiExponent

end

end OAI
