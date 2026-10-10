import OAI.NumberTheory.CubicMoment.Estimates.IdealVonMangoldt
import OAI.NumberTheory.CubicMoment.Estimates.PublishedHecke

namespace OAI

/-! The short ideal convolution identity evaluated on actual primary
character polynomials. All sums below are finite divisor sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Canonical primary generator on the ideals prime to three. We use it
only for exponent vectors below an actual primary principal ideal. -/
def idealPrimaryGenerator (ν : EisensteinIdealExponent) : Eisenstein :=
  primaryNormalize (idealExponentGenerator ν)

lemma idealExponentGenerator_dvd_of_le {ν κ : EisensteinIdealExponent} (h : ν ≤ κ) :
    idealExponentGenerator ν ∣ idealExponentGenerator κ := by
  refine ⟨idealExponentGenerator (κ-ν),?_⟩
  rw [← idealExponentGenerator_add,add_tsub_cancel_of_le h]

lemma idealPrimaryGenerator_primary {a : Eisenstein} (ha : primary a)
    {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a) :
    primary (idealPrimaryGenerator ν) := by
  apply primaryNormalize_primary
  exact unit_residue_of_dvd_primary ha ((idealExponentGenerator_dvd_of_le hν).trans
    (idealExponentOf_associated (primary_ne_zero ha)).dvd)

lemma idealPrimaryGenerator_at_element {a : Eisenstein} (ha : primary a) :
    idealPrimaryGenerator (idealExponentOf a) = a := by
  exact primary_associated_eq (idealPrimaryGenerator_primary ha le_rfl) ha
    ((primaryNormalize_associated _).symm.trans (idealExponentOf_associated (primary_ne_zero ha)))

lemma idealPrimaryGenerator_norm (ν : EisensteinIdealExponent) :
    norm (idealPrimaryGenerator ν) = idealExponentNorm ν := by
  rw [← normNat_cast]
  change (normNat (primaryNormalize (idealExponentGenerator ν)) : ℝ) =
    (normNat (idealExponentGenerator ν) : ℝ)
  rw [normNat_primaryNormalize]

lemma idealPrimaryGenerator_add {a : Eisenstein} (ha : primary a)
    {ν κ : EisensteinIdealExponent} (h : ν+κ ≤ idealExponentOf a) :
    idealPrimaryGenerator (ν+κ) = idealPrimaryGenerator ν * idealPrimaryGenerator κ := by
  have hν : ν ≤ idealExponentOf a := (le_add_of_nonneg_right zero_le).trans h
  have hκ : κ ≤ idealExponentOf a := (le_add_of_nonneg_left zero_le).trans h
  apply primary_associated_eq (idealPrimaryGenerator_primary ha h)
    (primary_mul (idealPrimaryGenerator_primary ha hν) (idealPrimaryGenerator_primary ha hκ))
  apply (primaryNormalize_associated (idealExponentGenerator (ν+κ))).symm.trans
  rw [idealExponentGenerator_add]
  exact (primaryNormalize_associated _).mul_mul (primaryNormalize_associated _)

/-- Real ideal coefficients evaluated against a character of primary
Eisenstein elements. -/
def idealCharacterCoeff (A : EisensteinArithmeticFunction) (χ : Eisenstein → ℂ)
    (ν : EisensteinIdealExponent) : ℂ :=
  ((MvPowerSeries.coeff ν A : ℝ) : ℂ)*χ (idealPrimaryGenerator ν)

lemma idealCharacterCoeff_mul {a : Eisenstein} (ha : primary a)
    (A B : EisensteinArithmeticFunction) (χ : Eisenstein → ℂ)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y)
    {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a) :
    idealCharacterCoeff (A*B) χ ν =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        idealCharacterCoeff A χ p.1 * idealCharacterCoeff B χ p.2 := by
  unfold idealCharacterCoeff
  rw [MvPowerSeries.coeff_mul,Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hle : p.1+p.2 ≤ idealExponentOf a := he.le.trans hν
  have h1 : p.1 ≤ idealExponentOf a := (le_add_of_nonneg_right zero_le).trans hle
  have h2 : p.2 ≤ idealExponentOf a := (le_add_of_nonneg_left zero_le).trans hle
  rw [← he,idealPrimaryGenerator_add ha hle,
    hχ _ _ (idealPrimaryGenerator_primary ha h1) (idealPrimaryGenerator_primary ha h2)]
  push_cast
  ring

lemma idealCharacterCoeff_add (A B : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) (ν : EisensteinIdealExponent) :
    idealCharacterCoeff (A+B) χ ν = idealCharacterCoeff A χ ν+idealCharacterCoeff B χ ν := by
  simp [idealCharacterCoeff,map_add,add_mul]

lemma idealCharacterCoeff_sub (A B : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) (ν : EisensteinIdealExponent) :
    idealCharacterCoeff (A-B) χ ν = idealCharacterCoeff A χ ν-idealCharacterCoeff B χ ν := by
  simp [idealCharacterCoeff,map_sub,sub_mul]

/-- The actual von Mangoldt character coefficient splits into a two-factor
and a four-factor ideal convolution throughout the sharp norm range. -/
theorem shortMoebius_character_identity {F : ℝ} (hF : 0 ≤ F)
    {a : Eisenstein} (ha : primary a) (hNa : norm a ≤ F)
    (χ : Eisenstein → ℂ)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y) :
    ((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt : ℝ) : ℂ)*χ a =
      2 * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (idealExponentOf a),
        idealCharacterCoeff (shortIdealMoebius F) χ p.1 * idealCharacterCoeff idealLogNorm χ p.2) -
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (idealExponentOf a),
        idealCharacterCoeff (shortIdealMoebius F*shortIdealMoebius F*idealZeta) χ p.1 *
          idealCharacterCoeff idealLogNorm χ p.2) := by
  have hid := short_moebius_identity hF (idealExponentOf a)
    ((idealExponentOf_norm (primary_ne_zero ha)).trans_le hNa)
  have halg :
      (2*shortIdealMoebius F-shortIdealMoebius F*shortIdealMoebius F*idealZeta)*idealLogNorm =
      shortIdealMoebius F*idealLogNorm + shortIdealMoebius F*idealLogNorm -
        (shortIdealMoebius F*shortIdealMoebius F*idealZeta)*idealLogNorm := by ring
  have hlhs : ((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt : ℝ) : ℂ)*χ a =
      idealCharacterCoeff idealVonMangoldt χ (idealExponentOf a) := by
    simp only [idealCharacterCoeff,idealPrimaryGenerator_at_element ha]
  rw [hlhs]
  rw [show idealCharacterCoeff idealVonMangoldt χ (idealExponentOf a) =
    idealCharacterCoeff ((2*shortIdealMoebius F-shortIdealMoebius F*shortIdealMoebius F*idealZeta)*
      idealLogNorm) χ (idealExponentOf a) by unfold idealCharacterCoeff; rw [hid]]
  rw [halg,idealCharacterCoeff_sub,idealCharacterCoeff_add,
    idealCharacterCoeff_mul ha _ _ χ hχ le_rfl,idealCharacterCoeff_mul ha _ _ χ hχ le_rfl]
  ring

/-- Four actual ideal factors, with no convolution coefficient left hidden.
The antidiagonal constraints encode their exact product, before Mellin
separation of a norm weight. -/
lemma idealCharacterCoeff_four {a : Eisenstein} (ha : primary a)
    (A B C D : EisensteinArithmeticFunction) (χ : Eisenstein → ℂ)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y)
    {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a) :
    idealCharacterCoeff (A*B*C*D) χ ν =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        (∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
          (∑ r ∈ Finset.HasAntidiagonal.antidiagonal q.1,
            idealCharacterCoeff A χ r.1*idealCharacterCoeff B χ r.2)*
          idealCharacterCoeff C χ q.2)*idealCharacterCoeff D χ p.2 := by
  rw [idealCharacterCoeff_mul ha _ _ χ hχ hν]
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 : p.1 ≤ idealExponentOf a :=
    (le_add_of_nonneg_right zero_le).trans
      ((Finset.HasAntidiagonal.mem_antidiagonal.mp hp).le.trans hν)
  rw [idealCharacterCoeff_mul ha _ _ χ hχ hp1]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq1 : q.1 ≤ idealExponentOf a :=
    (le_add_of_nonneg_right zero_le).trans
      ((Finset.HasAntidiagonal.mem_antidiagonal.mp hq).le.trans hp1)
  rw [idealCharacterCoeff_mul ha _ _ χ hχ hq1]

lemma idealCharacterCoeff_zeta (χ : Eisenstein → ℂ) (ν : EisensteinIdealExponent) :
    idealCharacterCoeff idealZeta χ ν = χ (idealPrimaryGenerator ν) := by
  simp [idealCharacterCoeff,MvPowerSeries.coeff_apply,idealZeta]

lemma idealCharacterCoeff_log (χ : Eisenstein → ℂ) (ν : EisensteinIdealExponent) :
    idealCharacterCoeff idealLogNorm χ ν =
      (Real.log (idealExponentNorm ν) : ℂ)*χ (idealPrimaryGenerator ν) := by
  rfl

/-- Every nonzero short Möbius factor has the required half-length and
squarefree ideal support. These are derived support conditions. -/
lemma shortIdeal_characterCoeff_support {F : ℝ} {χ : Eisenstein → ℂ}
    {ν : EisensteinIdealExponent}
    (h : idealCharacterCoeff (shortIdealMoebius F) χ ν ≠ 0) :
    idealExponentNorm ν ≤ Real.sqrt F ∧ ∀ p, ν p ≤ 1 := by
  have hN : idealExponentNorm ν ≤ Real.sqrt F := by
    by_contra hn
    exact h (by simp [idealCharacterCoeff,MvPowerSeries.coeff_apply,shortIdealMoebius,hn])
  refine ⟨hN,?_⟩
  intro p
  by_contra hp
  have hzero := idealMoebiusSeries_repeated (ν := ν) (p := p) (by omega)
  exact h (by simp [idealCharacterCoeff,MvPowerSeries.coeff_apply,shortIdealMoebius,hN,hzero])

lemma shortIdeal_characterCoeff_norm_le_one (F : ℝ) (χ : Eisenstein → ℂ)
    (ν : EisensteinIdealExponent) (hχ : ‖χ (idealPrimaryGenerator ν)‖ ≤ 1) :
    ‖idealCharacterCoeff (shortIdealMoebius F) χ ν‖ ≤ 1 := by
  rw [idealCharacterCoeff,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |MvPowerSeries.coeff ν (shortIdealMoebius F)| * 1 :=
      mul_le_mul_of_nonneg_left hχ (abs_nonneg _)
    _ ≤ 1 := by simpa using shortIdealMoebius_abs_le_one F ν

lemma logIdeal_characterCoeff_norm_le (χ : Eisenstein → ℂ)
    (ν : EisensteinIdealExponent) (hχ : ‖χ (idealPrimaryGenerator ν)‖ ≤ 1) :
    ‖idealCharacterCoeff idealLogNorm χ ν‖ ≤ Real.log (idealExponentNorm ν) := by
  have hlog : 0 ≤ Real.log (idealExponentNorm ν) := Real.log_nonneg (idealExponentNorm_ge_one ν)
  rw [idealCharacterCoeff_log,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  simpa using mul_le_mul_of_nonneg_left hχ hlog

/-- Evaluation at the actual mixed cubic character used in the exceptional
moments; its multiplicativity is already proved arithmetically. -/
theorem shortMoebius_mixedCubic_identity {F : ℝ} (hF : 0 ≤ F)
    {a q₁ q₂ : Eisenstein} (ha : primary a) (hNa : norm a ≤ F)
    (h₁ : primary q₁) (h₂ : primary q₂) :
    ((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt : ℝ) : ℂ)*mixedCubic q₁ q₂ a =
      2 * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (idealExponentOf a),
        idealCharacterCoeff (shortIdealMoebius F) (mixedCubic q₁ q₂) p.1 *
        idealCharacterCoeff idealLogNorm (mixedCubic q₁ q₂) p.2) -
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (idealExponentOf a),
        (∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
          (∑ r ∈ Finset.HasAntidiagonal.antidiagonal q.1,
            idealCharacterCoeff (shortIdealMoebius F) (mixedCubic q₁ q₂) r.1*
            idealCharacterCoeff (shortIdealMoebius F) (mixedCubic q₁ q₂) r.2)*
          idealCharacterCoeff idealZeta (mixedCubic q₁ q₂) q.2)*
        idealCharacterCoeff idealLogNorm (mixedCubic q₁ q₂) p.2) := by
  have hm : ∀ x y, primary x → primary y →
      mixedCubic q₁ q₂ (x*y) = mixedCubic q₁ q₂ x*mixedCubic q₁ q₂ y :=
    fun x y _ _ => mixedCubic_mul h₁ h₂ x y
  rw [shortMoebius_character_identity hF ha hNa (mixedCubic q₁ q₂) hm]
  congr 1
  have hfour := idealCharacterCoeff_four ha (shortIdealMoebius F) (shortIdealMoebius F)
    idealZeta idealLogNorm (mixedCubic q₁ q₂) hm le_rfl
  rw [idealCharacterCoeff_mul ha _ _ (mixedCubic q₁ q₂) hm le_rfl] at hfour
  exact hfour

/-- The two-factor Type I term furnished by the short inverse. -/
def shortTypeITwo (F : ℝ) (χ : Eisenstein → ℂ) (ν : EisensteinIdealExponent) : ℂ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
    idealCharacterCoeff (shortIdealMoebius F) χ p.1 * idealCharacterCoeff idealLogNorm χ p.2

/-- The four-factor Type I term, keeping both short Möbius factors explicit. -/
def shortTypeIFour (F : ℝ) (χ : Eisenstein → ℂ) (ν : EisensteinIdealExponent) : ℂ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
      (∑ r ∈ Finset.HasAntidiagonal.antidiagonal q.1,
        idealCharacterCoeff (shortIdealMoebius F) χ r.1*
        idealCharacterCoeff (shortIdealMoebius F) χ r.2)*
      idealCharacterCoeff idealZeta χ q.2)*idealCharacterCoeff idealLogNorm χ p.2

lemma shortMoebius_character_identity_expanded {F : ℝ} (hF : 0 ≤ F)
    {a : Eisenstein} (ha : primary a) (hNa : norm a ≤ F)
    (χ : Eisenstein → ℂ)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y) :
    ((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt : ℝ) : ℂ)*χ a =
      2*shortTypeITwo F χ (idealExponentOf a)-shortTypeIFour F χ (idealExponentOf a) := by
  rw [shortMoebius_character_identity hF ha hNa χ hχ]
  unfold shortTypeITwo shortTypeIFour
  congr 1
  have hfour := idealCharacterCoeff_four ha (shortIdealMoebius F) (shortIdealMoebius F)
    idealZeta idealLogNorm χ hχ le_rfl
  rw [idealCharacterCoeff_mul ha _ _ χ hχ le_rfl] at hfour
  exact hfour

/-- Exact finite weighted Type I decomposition on actual primary elements.
No separation of the product norm, dyadic partition, or analytic bound is
assumed here; those operations apply to this proved identity. -/
theorem shortMoebius_weighted_finite_sum {F : ℝ} (hF : 0 ≤ F)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ norm a ≤ F)
    (W : ℝ → ℂ) (χ : Eisenstein → ℂ)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y) :
    (∑ a ∈ S, W (norm a)*((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt : ℝ) : ℂ)*χ a) =
      2*(∑ a ∈ S, W (norm a)*shortTypeITwo F χ (idealExponentOf a)) -
        ∑ a ∈ S, W (norm a)*shortTypeIFour F χ (idealExponentOf a) := by
  calc
    _ = ∑ a ∈ S, W (norm a)*(2*shortTypeITwo F χ (idealExponentOf a)-
        shortTypeIFour F χ (idealExponentOf a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_assoc,shortMoebius_character_identity_expanded hF (hS a ha).1 (hS a ha).2 χ hχ]
    _ = _ := by
      simp only [mul_sub,Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

end CubicFirstMoment

end

end OAI
