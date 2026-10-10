import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusPolynomials
import OAI.NumberTheory.CubicMoment.Estimates.IdealMellinSeries
import OAI.NumberTheory.CubicMoment.Estimates.StructuredConvolution

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentOf_eq_of_associated {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associated a b) : idealExponentOf a = idealExponentOf b := by
  have he := congrArg Associates.factors (Associates.mk_eq_mk_iff_associated.mpr h)
  rw [Associates.factors_mk a ha,Associates.factors_mk b hb] at he
  exact congrArg Multiset.toFinsupp (WithTop.coe_inj.mp he)

lemma idealExponentOf_primaryGenerator (ν : EisensteinIdealExponent) :
    idealExponentOf (idealPrimaryGenerator ν) = ν := by
  have h := primaryNormalize_associated (idealExponentGenerator ν)
  have hne := h.ne_zero_iff.mp (idealExponentGenerator_ne_zero ν)
  exact (idealExponentOf_eq_of_associated hne (idealExponentGenerator_ne_zero ν) h.symm).trans
    (idealExponentOf_generator ν)

lemma idealPrimaryGenerator_injective : Function.Injective idealPrimaryGenerator :=
  Function.LeftInverse.injective idealExponentOf_primaryGenerator

/-- Primary element sums omit every ideal divisible by the prime over three. -/
def primaryElementBall (Y : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall Y).filter primary

@[simp] lemma mem_primaryElementBall {a : Eisenstein} {Y : ℝ} :
    a ∈ primaryElementBall Y ↔ primary a ∧ norm a ≤ Y := by
  simp only [primaryElementBall,Finset.mem_filter,mem_nonzeroNormBall]
  constructor
  · rintro ⟨⟨hN,_⟩,ha⟩
    exact ⟨ha,hN⟩
  · rintro ⟨ha,hN⟩
    exact ⟨⟨hN,primary_ne_zero ha⟩,ha⟩

/-- The corresponding finite ideal set, explicitly restricted to ideals
with a primary generator, hence prime to the ramified prime. -/
def primaryIdealBall (Y : ℝ) : Finset EisensteinIdealExponent :=
  (primaryElementBall Y).image idealExponentOf

@[simp] lemma mem_primaryIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ primaryIdealBall Y ↔ primary (idealPrimaryGenerator ν) ∧ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hN⟩ := mem_primaryElementBall.mp ha
    rw [idealPrimaryGenerator_at_element ha,idealExponentOf_norm (primary_ne_zero ha)]
    exact ⟨ha,hN⟩
  · rintro ⟨hν,hN⟩
    exact Finset.mem_image.mpr ⟨idealPrimaryGenerator ν,
      mem_primaryElementBall.mpr ⟨hν,(idealPrimaryGenerator_norm ν).trans_le hN⟩,
      idealExponentOf_primaryGenerator ν⟩

lemma primaryIdealBall_coprime_three {Y : ℝ} {ν : EisensteinIdealExponent}
    (hν : ν ∈ primaryIdealBall Y) : IsCoprime (idealPrimaryGenerator ν) 3 := by
  obtain ⟨k,hk⟩ := (mem_primaryIdealBall.mp hν).1
  refine ⟨1,-k,?_⟩
  linear_combination hk

/-- The primary ideal character polynomial with an arbitrary arithmetic
coefficient function. -/
def primaryIdealPolynomial (Y : ℝ) (A : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) : ℂ :=
  ∑ ν ∈ primaryIdealBall Y, idealCharacterCoeff A χ ν

theorem primaryIdealPolynomial_eq_elements (Y : ℝ) (A : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) :
    primaryIdealPolynomial Y A χ =
      ∑ a ∈ primaryElementBall Y, ((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*χ a := by
  unfold primaryIdealPolynomial primaryIdealBall
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    simp only [idealCharacterCoeff,idealPrimaryGenerator_at_element (mem_primaryElementBall.mp ha).1]
  · intro a ha b hb he
    have ha' := (mem_primaryElementBall.mp ha).1
    have hb' := (mem_primaryElementBall.mp hb).1
    have h := congrArg idealPrimaryGenerator he
    simpa only [idealPrimaryGenerator_at_element ha',idealPrimaryGenerator_at_element hb'] using h

/-- The short factor is the literal bounded Möbius polynomial over primary
elements. No complete ideal series or ramified Euler factor is inserted. -/
theorem shortIdealPolynomial_eq_moebius (F : ℝ) (χ : Eisenstein → ℂ) :
    primaryIdealPolynomial (Real.sqrt F) (shortIdealMoebius F) χ =
      ∑ a ∈ primaryElementBall (Real.sqrt F), (idealMoebius a : ℂ)*χ a := by
  rw [primaryIdealPolynomial_eq_elements]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨ha,hN⟩ := mem_primaryElementBall.mp ha
  rw [shortIdealMoebius_at_element F (primary_ne_zero ha),ite_eq_left hN]
  push_cast
  rfl

lemma logIdealPolynomial_eq_elements (Y : ℝ) (χ : Eisenstein → ℂ) :
    primaryIdealPolynomial Y idealLogNorm χ =
      ∑ a ∈ primaryElementBall Y, (Real.log (norm a) : ℂ)*χ a := by
  rw [primaryIdealPolynomial_eq_elements]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MvPowerSeries.coeff_apply,idealLogNorm,
    idealExponentOf_norm (primary_ne_zero (mem_primaryElementBall.mp ha).1)]

lemma zetaIdealPolynomial_eq_elements (Y : ℝ) (χ : Eisenstein → ℂ) :
    primaryIdealPolynomial Y idealZeta χ = ∑ a ∈ primaryElementBall Y, χ a := by
  rw [primaryIdealPolynomial_eq_elements]
  simp [MvPowerSeries.coeff_apply,idealZeta]

lemma primaryCharacter_prod {ι : Type*} (S : Finset ι) (f : ι → Eisenstein)
    (χ : Eisenstein → ℂ) (hχ1 : χ 1 = 1)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y)
    (hf : ∀ i ∈ S, primary (f i)) :
    χ (∏ i ∈ S, f i) = ∏ i ∈ S, χ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hχ1
  | @insert i S hi ih =>
    have hS : ∀ j ∈ S, primary (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,
      hχ _ _ (hf i (Finset.mem_insert_self _ _)) (primary_finset_prod S f hS),ih hS]

/-- Independent ideal factors are exactly the collected actual element
convolution. Each factor may have its own complex norm weight. -/
theorem primaryIdealPolynomial_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ι → ℝ) (A : ι → EisensteinArithmeticFunction) (w : ι → Eisenstein → ℂ)
    (χ : Eisenstein → ℂ) (hχ1 : χ 1 = 1)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y) :
    (∏ i, primaryIdealPolynomial (Y i) (A i) (fun a => w i a*χ a)) =
      ∑ b ∈ orderedConvolutionSupport (fun i => primaryElementBall (Y i)),
        orderedConvolution (fun i => primaryElementBall (Y i))
          (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i) : ℝ) : ℂ)*w i a) b * χ b := by
  simp_rw [primaryIdealPolynomial_eq_elements]
  rw [orderedConvolution_sum]
  have hprod := Finset.prod_univ_sum (fun i => primaryElementBall (Y i))
    (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i) : ℝ) : ℂ)*(w i a*χ a))
  rw [hprod]
  apply Finset.sum_congr rfl
  intro f hf
  have hp : ∀ i ∈ (Finset.univ : Finset ι), primary (f i) := by
    intro i _
    exact (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hf i)).1
  rw [primaryCharacter_prod Finset.univ f χ hχ1 hχ hp,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma primaryIdealBall_generator_mem {Y : ℝ} {ν : EisensteinIdealExponent}
    (hν : ν ∈ primaryIdealBall Y) : idealPrimaryGenerator ν ∈ primaryElementBall Y := by
  obtain ⟨hprim,hN⟩ := mem_primaryIdealBall.mp hν
  exact mem_primaryElementBall.mpr ⟨hprim,(idealPrimaryGenerator_norm ν).trans_le hN⟩

lemma primaryIdealBall_card_le {Y : ℝ} (hY : 0 ≤ Y) :
    ((primaryIdealBall Y).card : ℝ) ≤ 18*Y := by
  have h1 : (primaryIdealBall Y).card ≤ (primaryElementBall Y).card :=
    Finset.card_image_le
  have h2 : (primaryElementBall Y).card ≤ (nonzeroNormBall Y).card := Finset.card_filter_le _ _
  exact (Nat.cast_le.mpr (h1.trans h2)).trans (nonzeroNormBall_card_le hY)

lemma primaryIdealPolynomial_norm_le {Y M : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M)
    (A : EisensteinArithmeticFunction) (χ : Eisenstein → ℂ)
    (hA : ∀ ν ∈ primaryIdealBall Y, ‖idealCharacterCoeff A χ ν‖ ≤ M) :
    ‖primaryIdealPolynomial Y A χ‖ ≤ 18*Y*M := by
  unfold primaryIdealPolynomial
  calc
    _ ≤ ∑ ν ∈ primaryIdealBall Y, ‖idealCharacterCoeff A χ ν‖ := norm_sum_le _ _
    _ ≤ ∑ _ν ∈ primaryIdealBall Y, M := Finset.sum_le_sum hA
    _ = ((primaryIdealBall Y).card : ℝ)*M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (primaryIdealBall_card_le hY) hM

/-- The short Möbius polynomial has the actual half-length trivial bound. -/
theorem shortIdealPolynomial_norm_le (F : ℝ) (χ : Eisenstein → ℂ)
    (hχ : ∀ a ∈ primaryElementBall (Real.sqrt F), ‖χ a‖ ≤ 1) :
    ‖primaryIdealPolynomial (Real.sqrt F) (shortIdealMoebius F) χ‖ ≤ 18*Real.sqrt F := by
  simpa using primaryIdealPolynomial_norm_le (Real.sqrt_nonneg F) zero_le_one
    (shortIdealMoebius F) χ (fun ν hν => shortIdeal_characterCoeff_norm_le_one F χ ν
      (hχ _ (primaryIdealBall_generator_mem hν)))

/-- The full primary log polynomial has a uniform elementary norm bound. -/
theorem logIdealPolynomial_norm_le {Y : ℝ} (hY : 1 ≤ Y) (χ : Eisenstein → ℂ)
    (hχ : ∀ a ∈ primaryElementBall Y, ‖χ a‖ ≤ 1) :
    ‖primaryIdealPolynomial Y idealLogNorm χ‖ ≤ 18*Y*Real.log Y := by
  apply primaryIdealPolynomial_norm_le (by linarith) (Real.log_nonneg hY)
  intro ν hν
  exact (logIdeal_characterCoeff_norm_le χ ν (hχ _ (primaryIdealBall_generator_mem hν))).trans
    (Real.log_le_log (idealExponentNorm_pos ν) (mem_primaryIdealBall.mp hν).2)

lemma zetaIdealPolynomial_norm_le {Y : ℝ} (hY : 0 ≤ Y) (χ : Eisenstein → ℂ)
    (hχ : ∀ a ∈ primaryElementBall Y, ‖χ a‖ ≤ 1) :
    ‖primaryIdealPolynomial Y idealZeta χ‖ ≤ 18*Y := by
  simpa using primaryIdealPolynomial_norm_le hY zero_le_one idealZeta χ (fun ν hν => by
    rw [idealCharacterCoeff_zeta]
    exact hχ _ (primaryIdealBall_generator_mem hν))

end CubicFirstMoment

end

end OAI
