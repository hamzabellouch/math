import Mathlib
import OAI.Probability.SKGap.Localization.CondSubConst

namespace OAI

namespace SKGap.GaussianHistory
open Real Filter
open scoped Topology
noncomputable section

def gridSteps (n : ℕ) : ℕ := (n+1)^4
def gridStep (T : ℝ) (n : ℕ) : ℝ := T/(gridSteps n:ℝ)

lemma gridSteps_pos (n : ℕ) : 0<gridSteps n := by unfold gridSteps; positivity
lemma gridStep_nonneg {T : ℝ} (hT : 0≤T) (n : ℕ) : 0≤gridStep T n := by
  unfold gridStep
  positivity
lemma grid_total (T : ℝ) (n : ℕ) : (gridSteps n:ℝ)*gridStep T n=T := by
  unfold gridStep
  field_simp [show (gridSteps n:ℝ)≠0 from (Nat.cast_pos.mpr (gridSteps_pos n)).ne']
lemma gridStep_eq (T : ℝ) (n : ℕ) : gridStep T n=T*((n:ℝ)+1)⁻¹^4 := by
  simp only [gridStep,gridSteps,Nat.cast_pow,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,inv_pow]

lemma inv_succ_tendsto : Tendsto (fun n : ℕ=>((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
  apply Tendsto.inv_tendsto_atTop
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

lemma gridStep_tendsto (T : ℝ) : Tendsto (gridStep T) atTop (𝓝 0) := by
  change Tendsto (fun n=>gridStep T n) atTop (𝓝 0)
  simpa only [gridStep_eq,zero_pow (by decide : 4≠0),mul_zero] using
    (tendsto_const_nhds.mul (inv_succ_tendsto.pow 4) :
      Tendsto (fun n : ℕ=>T*((n:ℝ)+1)⁻¹^4) atTop (𝓝 (T*0^4)))

lemma nat_mul_gridStep_tendsto (T : ℝ) :
    Tendsto (fun n : ℕ=>(n:ℝ)*gridStep T n) atTop (𝓝 0) := by
  have H:=(((tendsto_const_nhds (x:=(1:ℝ))).sub inv_succ_tendsto).mul
    (inv_succ_tendsto.pow 3)).const_mul T
  have he (n : ℕ) : (n:ℝ)*gridStep T n=T*(1-((n:ℝ)+1)⁻¹)*((n:ℝ)+1)⁻¹^3 := by
    rw [gridStep_eq]
    field_simp [show (n:ℝ)+1≠0 by positivity]
    ring
  simpa only [he,sub_zero,zero_pow (by decide : 3≠0),mul_zero,mul_assoc] using H

lemma nat_sq_mul_gridStep_tendsto (T : ℝ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^2*gridStep T n) atTop (𝓝 0) := by
  have H:=((((tendsto_const_nhds (x:=(1:ℝ))).sub inv_succ_tendsto).pow 2).mul
    (inv_succ_tendsto.pow 2)).const_mul T
  have he (n : ℕ) : (n:ℝ)^2*gridStep T n=T*(1-((n:ℝ)+1)⁻¹)^2*((n:ℝ)+1)⁻¹^2 := by
    rw [gridStep_eq]
    field_simp [show (n:ℝ)+1≠0 by positivity]
    ring
  simpa only [he,sub_zero,zero_pow (by decide : 2≠0),mul_zero,mul_assoc] using H

lemma nat_inv_tendsto : Tendsto (fun n : ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_natCast_atTop_atTop.inv_tendsto_atTop

lemma sqrt_div_nat_tendsto :
    Tendsto (fun n : ℕ=>sqrt (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have H := (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  apply H.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hs : 0<sqrt (n:ℝ) := sqrt_pos.mpr hp
  change (sqrt (n:ℝ))⁻¹ = sqrt (n:ℝ)/(n:ℝ)
  field_simp [hp.ne',hs.ne']
  nlinarith [sq_sqrt hp.le]

lemma localizationLoss_tendsto (T W A a b : ℝ) (hb : b≠0) :
    Tendsto (fun n=>localizationLoss n (gridStep T n) W A a b T) atTop
      (𝓝 (exp (4*T/a)*T*W/b)) := by
  have h1 := (nat_sq_mul_gridStep_tendsto T).const_mul (16*T)
  have h2 := ((tendsto_const_nhds (x:=W)).add ((sqrt_div_nat_tendsto.const_mul (2*A)).add
    (nat_inv_tendsto.const_mul (4/a)))).const_mul T
  have h3 := (nat_mul_gridStep_tendsto T).const_mul (64*T)
  have H := (h1.add ((h2.add h3).const_mul (exp (4*T/a)/b))).add
    (nat_inv_tendsto.const_mul (1/b))
  have H' : Tendsto (fun n : ℕ=>16*T*((n:ℝ)^2*gridStep T n)+
      exp (4*T/a)/b*(T*(W+(2*A*(sqrt (n:ℝ)/(n:ℝ))+4/a*(n:ℝ)⁻¹))+
        64*T*((n:ℝ)*gridStep T n))+1/b*(n:ℝ)⁻¹) atTop
      (𝓝 (exp (4*T/a)*T*W/b)) := by convert H using 1; ring_nf
  apply H'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  unfold localizationLoss
  field_simp
  ring

lemma localizationCost_tendsto (A a b D L T : ℝ) :
    Tendsto (fun n=>localizationCost n A a b D L T) atTop (𝓝 (D*T+L)) := by
  have H := (tendsto_const_nhds (x:=D*T+L)).add (sqrt_div_nat_tendsto.const_mul (exp (4*T/a)*T*A/b))
  convert H using 1
  · ext n
    unfold localizationCost
    ring
  · ring_nf

theorem localization_numeric_choice (D L T a b : ℝ) (hT : 0<T) (hb : 0<b) :
    ∃W : ℝ,0<W ∧ ∀A : ℝ,∀ᶠ n : ℕ in atTop,
      0<n ∧ 4*(n:ℝ)*gridStep T n≤1 ∧ D*gridStep T n≤1/2 ∧
      localizationLoss n (gridStep T n) W A a b T≤exp (-2*D*T)/2 ∧
      localizationCost n A a b D L T≤D*T+L+1 := by
  let W:=exp (-2*D*T)*b/(4*exp (4*T/a)*T)
  have hW : 0<W := by dsimp [W]; positivity
  refine ⟨W,hW,?_⟩
  intro A
  have hw : exp (4*T/a)*T*W/b=exp (-2*D*T)/4 := by
    dsimp [W]
    field_simp
  have hl:=localizationLoss_tendsto T W A a b hb.ne'
  rw [hw] at hl
  have ht:=((nat_mul_gridStep_tendsto T).const_mul 4).eventually_lt_const (by norm_num : (4:ℝ)*0<1)
  have hd:=((gridStep_tendsto T).const_mul D).eventually_lt_const (by norm_num : D*(0:ℝ)<1/2)
  have hloss:=hl.eventually_lt_const (show exp (-2*D*T)/4<exp (-2*D*T)/2 by nlinarith [exp_pos (-2*D*T)])
  have hcost:=(localizationCost_tendsto A a b D L T).eventually_lt_const
    (show D*T+L<D*T+L+1 by linarith)
  filter_upwards [eventually_ge_atTop 1,ht,hd,hloss,hcost] with n hn ht hd hl hc
  exact ⟨by omega,by simpa only [mul_assoc] using ht.le,hd.le,hl.le,hc.le⟩

lemma nat_pow_exp_tendsto {a : ℝ} (ha : 0<a) (k : ℕ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^k*exp (-a*(n:ℝ))) atTop (𝓝 0) := by
  have H := (tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  have H' := H.const_mul (a^k)⁻¹
  convert H' using 1
  · ext n
    dsimp
    rw [mul_pow]
    field_simp
  · simp

lemma grid_polynomial_exp_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun n : ℕ=>((gridSteps n:ℝ)+1)*exp (-a*(n:ℝ))) atTop (𝓝 0) := by
  have H := ((((nat_pow_exp_tendsto ha 4).add ((nat_pow_exp_tendsto ha 3).const_mul 4)).add
    ((nat_pow_exp_tendsto ha 2).const_mul 6)).add ((nat_pow_exp_tendsto ha 1).const_mul 4)).add
      ((nat_pow_exp_tendsto ha 0).const_mul 2)
  convert H using 1
  · ext n
    simp only [gridSteps,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    ring
  · ring_nf

lemma grid_exp_absorb {a : ℝ} (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop,((gridSteps n:ℝ)+1)*exp (-a*(n:ℝ))≤exp (-(a/2)*(n:ℝ)) := by
  have H := (grid_polynomial_exp_tendsto (half_pos ha)).eventually_lt_const zero_lt_one
  filter_upwards [H] with n hn
  have he : exp (-a*(n:ℝ))= exp (-(a/2)*(n:ℝ))*exp (-(a/2)*(n:ℝ)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he,← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hn.le (exp_pos _).le).trans_eq (one_mul _)

lemma constant_exp_absorb (C : ℝ) {a : ℝ} (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop,C*exp (-a*(n:ℝ))≤exp (-(a/2)*(n:ℝ)) := by
  have H : Tendsto (fun n : ℕ=>C*exp (-(a/2)*(n:ℝ))) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul,mul_zero] using (nat_pow_exp_tendsto (half_pos ha) 0).const_mul C
  filter_upwards [H.eventually_lt_const zero_lt_one] with n hn
  have he : exp (-a*(n:ℝ))= exp (-(a/2)*(n:ℝ))*exp (-(a/2)*(n:ℝ)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he,← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hn.le (exp_pos _).le).trans_eq (one_mul _)

end
end SKGap.GaussianHistory

end OAI
