import OAI.NumberTheory.DirichletL.CubicSieve.Gcd

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicQuotientCharacter (I : Ideal O) (hI : Admissible I) : MulChar (O ⧸ I) ℂ where
  toFun := CompletedGauss.cubicRow I hI.2
  map_one' := by simp [CompletedGauss.cubicRow]
  map_mul' x y := by simp only [CompletedGauss.cubicRow, map_mul, Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1]
    have hcop : ¬ IsCoprime I (Ideal.span {z}) := by
      simpa only [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq] using hx
    have hc := idealSymbol_cube_mask I z hI.2
    rw [ite_eq_right hcop] at hc
    exact (eq_zero_of_pow_eq_zero hc)

@[simp] lemma cubicQuotientCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    cubicQuotientCharacter I hI (Ideal.Quotient.mk I z) = cubicRow I z :=
  CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z

lemma cubicQuotientCharacter_cube (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicQuotientCharacter_mk, cubicRow,
    idealSymbol_cube_mask I z hI.2]
  have hu : IsUnit (Ideal.Quotient.mk I z) ↔ IsCoprime I (Ideal.span {z}) := by
    rw [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq]
  by_cases h : IsUnit (Ideal.Quotient.mk I z)
  · rw [ite_eq_left (hu.mp h), MulChar.one_apply h]
  · rw [ite_eq_right (fun hcop => h (hu.mpr hcop)), MulChar.map_nonunit _ h]

lemma cubicQuotientCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI (-1) = 1 := by
  have h3 := congrArg (fun χ : MulChar (O ⧸ I) ℂ => χ (-1)) (cubicQuotientCharacter_cube I hI)
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply (isUnit_neg_one)] at h3
  have h2 : cubicQuotientCharacter I hI (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  calc
    _ = cubicQuotientCharacter I hI (-1) ^ 2 * cubicQuotientCharacter I hI (-1) := by rw [h2, one_mul]
    _ = cubicQuotientCharacter I hI (-1) ^ 3 := by ring
    _ = 1 := h3

def quotientCharacterTransport {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]
  map_nonunit' x hx := MulChar.map_nonunit χ (fun h => hx (by simpa using h.map e.symm.toMonoidHom))

def principalCubicCharacter (I : Ideal O) (hI : Admissible I) :
    MulChar (O ⧸ Ideal.span {primaryGenerator I}) ℂ :=
  quotientCharacterTransport (Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1)
    (cubicQuotientCharacter I hI)

@[simp] lemma principalCubicCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    principalCubicCharacter I hI (Ideal.Quotient.mk _ z) = cubicRow I z := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (Ideal.Quotient.mk _ z)) = _
  rw [Ideal.quotEquivOfEq_mk, cubicQuotientCharacter_mk]

lemma principalCubicCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    principalCubicCharacter I hI (-1) = 1 := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (-1)) = 1
  rw [map_neg, map_one, cubicQuotientCharacter_neg_one]

lemma gaussTwo_eq_gaussSum (I : Ideal O) (hI : Admissible I) :
    let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
    let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
    gaussTwo I hI.2 = gaussSum (principalCubicCharacter I hI)
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (primaryGenerator I) hI.2) / (‖eisEmbedding (primaryGenerator I)‖ : ℂ) := by
  dsimp only [gaussTwo, gaussSum, principalCubicCharacter, quotientCharacterTransport, cubicQuotientCharacter]
  congr 1

lemma gaussSum_inverse_of_even {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (heven : χ (-1) = 1) :
    gaussSum χ⁻¹ ψ = star (gaussSum χ ψ) := by
  rw [star_gaussSum_eq]
  have hh : χ⁻¹ (-1) = 1 := by rw [← MulChar.star_apply', heven, star_one]
  have h := gaussSum_mulShift χ⁻¹ ψ (-1 : Rˣ)
  rw [Units.coe_neg_one, ← ψ.inv_mulShift, hh, one_mul] at h
  exact h.symm

lemma cubic_pair_cross_phase (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.mk _ (primaryGenerator J)) *
      principalCubicCharacter J hJ (Ideal.Quotient.mk _ (primaryGenerator I)) = 1 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  rw [← MulChar.star_apply', principalCubicCharacter_mk, principalCubicCharacter_mk]
  change star (idealKernel I J) * idealKernel J I = 1
  rw [← idealKernel_reciprocity I J hI.2 hJ.2]
  change star (cubicRow I (primaryGenerator J)) * cubicRow I (primaryGenerator J) = 1
  rw [cubicRow_common_mask I hI.2, (primaryGenerator_spec J hJ.2).1, ite_eq_left hcop]

def cubicPairGauss (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) : ℂ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.factor Ideal.mul_le_left x) *
      principalCubicCharacter J hJ (Ideal.Quotient.factor Ideal.mul_le_right x) *
      eisTraceProdChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates a b hI.2 hJ.2 x) /
      ((‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ))

theorem cubicPairGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    cubicPairGauss I J hI hJ = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator J}) := finite_quotient_span hJ.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator J}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) :=
    finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) := Fintype.ofFinite _
  have hc : IsCoprime (Ideal.span {primaryGenerator I}) (Ideal.span {primaryGenerator J}) := by
    rwa [(primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]
  dsimp only [cubicPairGauss]
  rw [gauss_sum_actual_O ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
    (primaryGenerator I) (primaryGenerator J) hI.2 hJ.2 hc,
    cubic_pair_cross_phase I J hI hJ hcop, one_mul,
    gaussSum_inverse_of_even _ _ (principalCubicCharacter_neg_one I hI),
    gaussTwo_eq_gaussSum I hI, gaussTwo_eq_gaussSum J hJ]
  have halg (a b : ℂ) (x y : ℝ) :
      star a * b / ((x : ℂ) * (y : ℂ)) = star (a / (x : ℂ)) * (b / (y : ℂ)) := by
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    ring
  exact halg _ _ _ _

end
end SevenEighths.CubicSieve

end OAI
