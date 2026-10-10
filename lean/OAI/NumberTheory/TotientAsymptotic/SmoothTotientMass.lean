import OAI.NumberTheory.TotientAsymptotic.BootstrapRealCount
import OAI.NumberTheory.TotientAsymptotic.SmoothCofactorTail

namespace OAI

/-! The finite-set consequence of Ford, *The distribution of totients*,
Lemma 4.3 (2013 revision), proved from the counting bootstrap and Rankin tail. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma smooth_mass_log_budget : ∀ᶠ b : ℝ in atTop,
    0 < b ∧ 32 ≤ Real.log b ∧ Real.log (100*b)+4 ≤ b := by
  have hl := Real.isLittleO_log_id_atTop.bound (show (0:ℝ)<1/2 by norm_num)
  filter_upwards [hl,eventually_ge_atTop (2*(Real.log 100+4)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (32:ℝ)),
    eventually_gt_atTop (1:ℝ)] with b hb hbC hlog hb1
  have hb0 : 0 < b := by linarith
  have hh : Real.log b ≤ b/2 := by
    have ht := (le_abs_self (Real.log b)).trans (by
      simpa only [Real.norm_eq_abs,abs_of_pos hb0,id_eq] using hb)
    linarith
  refine ⟨hb0,hlog,?_⟩
  rw [Real.log_mul (by norm_num : (100:ℝ)≠0) hb0.ne']
  linarith

lemma smooth_mass_exponential {b : ℝ} (hb : 0 < b) (hlog : 32 ≤ Real.log b) :
    b*Real.exp (9*(Real.log (2*b))^2) ≤ Real.exp (10*(Real.log b)^2) := by
  have h2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have h2' : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hs : (Real.log (2*b))^2 ≤ (Real.log b+1)^2 := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hb.ne']
    nlinarith
  have he : Real.log b+9*(Real.log (2*b))^2 ≤ 10*(Real.log b)^2 := by nlinarith
  calc
    _ = Real.exp (Real.log b+9*(Real.log (2*b))^2) := by rw [Real.exp_add,Real.exp_log hb]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem smooth_totient_reciprocal_mass : ∃ C : ℝ,0 < C ∧ ∀ᶠ y : ℕ in atTop,
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ largestPrimeFactor v ≤ y) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (B y))^2) := by
  classical
  obtain ⟨C,hC,hglobal⟩ := bootstrap_envelope_bound
  obtain ⟨D,hD,hmertens⟩ := mertensProductInput
  refine ⟨1+8*C+D^4,by positivity,?_⟩
  have hB : Tendsto (fun y : ℕ => B y) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [hB.eventually smooth_mass_log_budget,hB.eventually (eventually_ge_atTop (2:ℝ)),
    eventually_ge_atTop (4:ℕ)] with y hbudget hby hy
  obtain ⟨hb,hlogb,hsmall⟩ := hbudget
  have hyl : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let Z := 100*B y*Real.log y
  let T := Real.exp Z
  let J := countingDyadicIndex T
  have hT4 : 4 ≤ T := by
    have hz : 3 ≤ Z := by
      have hylog : 1 ≤ Real.log (y:ℝ) := by
        have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ) ≤ y by exact_mod_cast hy)
        rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
        norm_num only [Nat.cast_ofNat] at hh
        linarith [Real.log_two_gt_d9]
      dsimp [Z]
      nlinarith
    exact le_trans (by linarith : 4 ≤ Z+1) (Real.add_one_le_exp Z)
  obtain ⟨hJ,hTJ,hheight⟩ := counting_dyadic_index_bounds hT4
  have hBT : B T = B y+Real.log (100*B y) := by
    change Real.log (Real.log (Real.exp (100*B y*Real.log y))) = _
    rw [Real.log_exp,Real.log_mul (by positivity : 100*B y ≠ 0) hyl.ne']
    change Real.log (100*B y)+B y=B y+Real.log (100*B y)
    ring
  have hh : bootstrapHeight J ≤ 2*B y := by
    rw [hBT] at hheight
    linarith
  have hlogJ : 1+Real.log (J:ℝ) ≤ bootstrapHeight J := by
    have hp : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    have hj := Real.log_le_log hp (show (J:ℝ) ≤ (J:ℝ)+1 by linarith)
    dsimp [bootstrapHeight]
    linarith
  have hE : dyadicTotientEnvelope J ≤ C*Real.exp (9*(Real.log (2*B y))^2) := by
    have hH := bootstrapHeight_one_le J
    have hlog := Real.log_le_log (by linarith) hh
    have hnon : 0 ≤ Real.log (bootstrapHeight J) := Real.log_nonneg hH
    have hp : Real.exp (9*(Real.log (bootstrapHeight J))^2) ≤ Real.exp (9*(Real.log (2*B y))^2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact (hglobal J).trans (mul_le_mul_of_nonneg_left hp hC.le)
  intro Q hQ
  let A := Q.filter (fun v : ℕ => (v:ℝ) ≤ T)
  let E := Q.filter (fun v : ℕ => ¬(v:ℝ) ≤ T)
  have hA := dyadic_totient_reciprocal_mass hJ A (by
    intro v hv
    obtain ⟨hv,hvT⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,hvT.trans hTJ⟩)
  have hA' : (∑ v ∈ A,(v:ℝ)⁻¹) ≤ (1+8*C)*Real.exp (10*(Real.log (B y))^2) := by
    have hJlog : 0 ≤ 1+Real.log (J:ℝ) := by
      have ht := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ)
      linarith
    have hp := mul_le_mul hE (hlogJ.trans hh) hJlog (by positivity : 0 ≤ C*Real.exp (9*(Real.log (2*B y))^2))
    have hexp := smooth_mass_exponential hb hlogb
    have hone : 1 ≤ Real.exp (10*(Real.log (B y))^2) := Real.one_le_exp (by positivity)
    nlinarith
  have hE' : (∑ v ∈ E,(v:ℝ)⁻¹) ≤ D^4 := by
    have hr := smooth_cofactor_rankin (show 2 ≤ y by omega) Z E (by
      intro v hv
      obtain ⟨hv,hvT⟩ := Finset.mem_filter.mp hv
      have hv0 := isTotient_pos (hQ v hv).1
      refine ⟨hv0,(hQ v hv).2,?_⟩
      exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hv0)).mpr (lt_of_not_ge hvT))
    have hrec : (∑ v ∈ E,(v:ℝ)⁻¹) ≤ ∑ v ∈ E,(v.totient:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro v hv
      have hp := isTotient_pos (hQ v (Finset.mem_filter.mp hv).1).1
      exact inv_anti₀ (by exact_mod_cast Nat.totient_pos.mpr hp) (Nat.cast_le.mpr (Nat.totient_le v))
    have hprod := hmertens y (by omega)
    have hprod0 : 0 ≤ primeEulerProduct y := le_of_lt (by
      apply Finset.prod_pos
      intro p hp
      have hp1 : (1:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
      exact div_pos (by linarith) (by linarith))
    have hbound := hr.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprod0 hprod 4) (by positivity))
    have hid : Real.exp (-Z/(4*Real.log y))*(D*Real.log y)^4 = D^4*Real.exp (-21*B y) := by
      have hz : -Z/(4*Real.log y)= -25*B y := by dsimp [Z]; field_simp; ring
      have hpow : (Real.log (y:ℝ))^4=Real.exp (4*B y) := by
        simpa only [Nat.cast_ofNat,B,Real.exp_log hyl] using (Real.exp_nat_mul (B y) 4).symm
      rw [hz,mul_pow,hpow]
      rw [mul_left_comm,← Real.exp_add]
      congr 1
      congr 1
      ring
    rw [hid] at hbound
    exact hrec.trans (hbound.trans (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith))))
  have hsum : (∑ v ∈ Q,(v:ℝ)⁻¹)=(∑ v ∈ A,(v:ℝ)⁻¹)+(∑ v ∈ E,(v:ℝ)⁻¹) := by
    exact (Finset.sum_filter_add_sum_filter_not Q (fun v : ℕ => (v:ℝ) ≤ T) (fun v => (v:ℝ)⁻¹)).symm
  rw [hsum]
  have hone : 1 ≤ Real.exp (10*(Real.log (B y))^2) := Real.one_le_exp (by positivity)
  nlinarith [show 0 ≤ D^4 by positivity]

end TotientAsymptotic

end

end OAI
