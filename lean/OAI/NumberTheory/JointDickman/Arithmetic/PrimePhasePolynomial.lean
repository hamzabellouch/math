import OAI.NumberTheory.JointDickman.Arithmetic.PrimePhaseDivergence

namespace OAI

/-! # Prime-phase separation up to a fixed power of the cutoff -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

theorem zeta_uniform_sublog_polynomial (A : ℝ) (hA : 1 ≤ A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ X^A →
      ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ η*Real.log X := by
  let B : ℝ := 2+2*A/η
  have hA0 : 0 < A := by linarith
  have hB : 2 ≤ B := by dsimp [B]; linarith [div_pos (mul_pos (by norm_num : (0:ℝ)<2) hA0) hη]
  have hB0 : 0 < B := by linarith
  have hcoef : 1/B ≤ η/(2*A) := by
    apply (div_le_iff₀ hB0).mpr
    have he : (η/(2*A))*B = η/A+1 := by dsimp [B]; field_simp
    rw [he]
    linarith [div_pos hη hA0]
  obtain ⟨C,hC,hlarge⟩ := zeta_logarithmic_bound hB
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hlarge
  filter_upwards [zeta_uniform_sublog hη,eventually_ge_atTop (max T₀ (Real.exp 1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*C/η))]
    with X hbase hX hXC
  intro t htlo ht
  by_cases hsmall : |t| ≤ 2*X
  · exact hbase t htlo hsmall
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hXT : T₀ ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog0 : 0 < Real.log X := by linarith
  have ht0 : 0 < |t| := by linarith
  have hσ1 : 1 < 1+1/Real.log X := by linarith [one_div_pos.mpr hlog0]
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

theorem prime_cosine_defect_polynomial (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ X^A →
      R ≤ ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1-Real.cos (t*Real.log (p:ℝ)))/(p:ℝ) := by
  obtain ⟨C,hC⟩ := characterDistance_ge_log_sub_L
  let η := Real.exp (-(R+C+1))
  filter_upwards [zeta_uniform_sublog_polynomial A hA (Real.exp_pos (-(R+C+1))),
    eventually_ge_atTop (max 2 (Real.exp 1))] with X hbound hX
  intro t htlo ht
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog : 0 < Real.log X := by linarith
  have hs : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hn : 0 < ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  have hl := Real.log_le_log hn (hbound t htlo ht)
  rw [Real.log_mul (Real.exp_pos _).ne' hlog.ne',Real.log_exp] at hl
  have hd := hC 1 (1 : DirichletCharacter ℂ 1) X hX t
  rw [DirichletCharacter.LFunction_modOne_eq,principalDistance_eq_cosine] at hd
  linarith

end JointDickman

end OAI
