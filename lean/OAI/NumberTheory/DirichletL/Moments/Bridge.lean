import OAI.NumberTheory.DirichletL.Moments.FirstPoisson
import OAI.NumberTheory.DirichletL.Moments.Primitive

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson

def productCharacter (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) :
    MulChar (Residue (a * b)) ℂ where
  toFun x := χa ((principalCRT a b hcop x).1) * χb ((principalCRT a b hcop x).2)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul]; ring
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (principalCRT a b hcop x) := fun h =>
      hx ((isUnit_map_iff (principalCRT a b hcop) x).mp h)
    rw [Prod.isUnit_iff] at hn
    by_cases h : IsUnit (principalCRT a b hcop x).1
    · rw [χb.map_nonunit (fun hb => hn ⟨h, hb⟩), mul_zero]
    · rw [χa.map_nonunit h, zero_mul]

theorem productCharacter_apply (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : Residue (a * b)) :
    productCharacter a b hcop χa χb x =
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [productCharacter, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    principalCRT_mk, frequencyReduction_mk]

@[simp] theorem productCharacter_mk (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : O) :
    productCharacter a b hcop χa χb (Ideal.Quotient.mk _ x) =
      χa (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x) := by
  rw [productCharacter_apply, frequencyReduction_mk, frequencyReduction_mk]

theorem productCharacter_gauss (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    residueGauss (a * b) (mul_ne_zero ha hb) (productCharacter a b hcop χa χb) h =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  simpa only [residueGauss, tsum_fintype, productCharacter_apply] using
    coprime_character_fourier a b ha hb hcop χa χb h

theorem triple_pair_gauss (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (j : O) :
    residueGauss (r * (a * b)) (mul_ne_zero hr (mul_ne_zero ha hb))
      (productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹))
      (Ideal.Quotient.mk _ j) =
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
  let := finite_quotient_span hb
  rw [productCharacter_gauss r (a * b) hr (mul_ne_zero ha hb),
    frequencyReduction_mk, frequencyReduction_mk,
    productCharacter_mk, productCharacter_gauss a b ha hb, frequencyReduction_mk,
    frequencyReduction_mk, residueGauss_inverse, ← map_neg]
  simp only [map_mul, star_mul, MulChar.star_apply']
  ring

theorem triple_pair_poisson (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) =
      ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z)) := by
    simp only [χ, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hp := actual_radial_paper_poisson_trace W K hK (r * (a * b)) hm χ
  change (∑' z : O, χ (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) •
    ∑' j : O, (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) *
      paperRadialFourier W
        (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) at hp
  simp only [hχ] at hp
  rw [hp]
  have hcoeff (j : O) : (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) =
      residueGauss (r * (a * b)) hm χ (Ideal.Quotient.mk _ j) := by
    simp only [residueGauss, tsum_fintype]
  simp_rw [hcoeff]
  simp_rw [χ, triple_pair_gauss r a b hr ha hb hrab hab ξ χa χb]
  simp_rw [mul_assoc, tsum_mul_left]
  rw [Complex.real_smul]

theorem masked_triple_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι)
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, rowCoprimeMask P S z *
      (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
          residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  let row := fun z : O => ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
    star (χb (Ideal.Quotient.mk _ z))
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) = row z := by
    simp only [χ, row, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hsum : Summable (fun z : O => row z * W (‖eisEmbedding z‖ ^ 2 / K)) := by
    have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
      (Ideal.Quotient.mk (Ideal.span {r * (a * b)})) χ
    simpa only [hχ, scaledRadialTest_apply] using hs
  have hmul (x y : O) : row (x * y) = row x * row y := by
    simp only [row, map_mul, star_mul]
    ring
  rw [tsum_masked_radial_dilations P hinj S row hmul W K hsum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W
    (K / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hK)]
  ring

theorem normalized_triple_pair_poisson
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  have hnr : (‖eisEmbedding r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hr))
  have hna : (‖eisEmbedding a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))
  have hnb : (‖eisEmbedding b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))
  have hpoint (j : O) : residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
      residueGauss a ha χa (Ideal.Quotient.mk _ j) *
      star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) =
      ((‖eisEmbedding r‖ : ℂ) * (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ)) *
      (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    simp only [normalizedResidueGauss, CenteredMomentPrimitive.sqrt_absNorm,
      star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W K hK]
  simp_rw [hpoint, mul_assoc, tsum_mul_left, CenteredMomentPrimitive.sqrt_absNorm]
  simp only [map_mul, norm_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentBridge
end

end OAI
