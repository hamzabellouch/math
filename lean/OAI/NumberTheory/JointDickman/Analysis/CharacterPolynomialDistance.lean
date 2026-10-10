import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceDivergence
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDistanceComparison
import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge

namespace OAI

/-! # Nonprincipal prime agreement at polynomial frequency heights -/
namespace JointDickman
open Complex Filter Finset PublishedInputs
open scoped Topology

theorem character_LFunction_sublog_polynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (A : ℝ) (hA : 1 ≤ A)
    {η : ℝ} (hη : 0 < η) : ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, |t| ≤ X^A →
      ‖χ.LFunction (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ η*Real.log X := by
  let B : ℝ := 2+2*A/η
  have hA0 : 0 < A := by linarith
  have hB : 2 ≤ B := by
    dsimp [B]
    linarith [div_pos (mul_pos (by norm_num : (0:ℝ)<2) hA0) hη]
  have hB0 : 0 < B := by linarith
  have hcoef : 1/B ≤ η/(2*A) := by
    apply (div_le_iff₀ hB0).mpr
    have he : (η/(2*A))*B = η/A+1 := by dsimp [B]; field_simp
    rw [he]
    linarith [div_pos hη hA0]
  obtain ⟨C,_,hlarge⟩ := character_LFunction_logarithmic_bound hB χ hχ
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hlarge
  filter_upwards [character_LFunction_uniform_sublog χ hχ hη,
    eventually_ge_atTop (max T₀ (Real.exp 1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*C/η))]
    with X hbase hX hXC
  intro t ht
  by_cases hsmall : |t| ≤ X
  · exact hbase t hsmall
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hXT : T₀ ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog0 : 0 < Real.log X := by linarith
  have ht0 : 0 < |t| := by linarith
  have hσ1 : 1 ≤ 1+1/Real.log X := by linarith [one_div_pos.mpr hlog0]
  have hσ2 : 1+1/Real.log X ≤ 2 := by
    have := (div_le_one hlog0).mpr hlog1
    linarith
  have hb := hT₀ |t| (by linarith) t (1+1/Real.log X) rfl hσ1 hσ2
  have hCbound : C ≤ (η/2)*Real.log X := by
    have hh := (div_le_iff₀ hη).mp hXC
    nlinarith
  have hlt : Real.log |t| ≤ A*Real.log X := by
    have hh := Real.log_le_log ht0 ht
    rwa [Real.log_rpow hX0] at hh
  calc
    _ ≤ (1/B)*Real.log |t|+C := hb
    _ ≤ (1/B)*(A*Real.log X)+C :=
      add_le_add (mul_le_mul_of_nonneg_left hlt (by positivity)) le_rfl
    _ ≤ (η/(2*A))*(A*Real.log X)+(η/2)*Real.log X :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (by positivity)) hCbound
    _ = _ := by field_simp; ring

theorem character_distance_polynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, |t| ≤ X^A →
      R ≤ primeDistanceSquared (characterArithmetic χ) X t := by
  obtain ⟨C,hC⟩ := characterDistance_ge_log_sub_L
  filter_upwards [character_LFunction_sublog_polynomial χ hχ A hA
    (Real.exp_pos (-(R+C+1))),eventually_ge_atTop (max 2 (Real.exp 1))]
    with X hbound hX
  intro t ht
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog : 0 < Real.log X := by linarith
  have hs : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hn : 0 < ‖χ.LFunction (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ := by
    apply norm_pos_iff.mpr
    rw [χ.LFunction_eq_LSeries hs]
    exact χ.LSeries_ne_zero_of_one_lt_re hs
  have hl := Real.log_le_log hn (hbound t ht)
  rw [Real.log_mul (Real.exp_pos _).ne' hlog.ne',Real.log_exp] at hl
  have hd := hC q χ X hX t
  linarith

theorem character_agreement_distance_polynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (P : Finset ℕ) (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ P → (p:ℝ) ≤ X^c → f p = χ p) →
      ∀ t : ℝ, |t| ≤ X^A → R ≤ primeDistanceSquared f X t := by
  let M : ℝ := -Real.log c+1+∑ p ∈ P, 1/(p:ℝ)
  have htail := (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).eventually
    (eventually_le_nhds (lt_add_one (-Real.log c)))
  filter_upwards [character_distance_polynomial χ hχ A hA (R+2*M),htail]
    with X hX htailX
  intro f hf heq t ht
  have hg := characterArithmetic_norm_le_one χ
  have hh := primeDistanceSquared_lower_of_agree f (characterArithmetic χ) hf hg P X (X^c) t (by
    intro p hp hpP hpX
    rw [heq p hp hpP hpX,characterArithmetic_prime χ hp])
  have hd := hX t ht
  dsimp only [M] at hd
  linarith

end JointDickman

end OAI
