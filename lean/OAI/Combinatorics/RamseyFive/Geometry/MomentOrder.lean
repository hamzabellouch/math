import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.RadialOffException
import OAI.Combinatorics.RamseyFive.Geometry.DyadCount

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Filter Asymptotics ParameterHierarchy
open scoped Topology

noncomputable def momentOrder (σ P : ℝ) : ℕ := 2*⌈5000*σ/P⌉₊
noncomputable def residualOrder (σ : ℝ) : ℕ := ⌈1000*Real.log σ⌉₊+1

lemma momentOrder_bounds {σ P : ℝ} (hσ : 1≤σ) (hP : 1≤P) :
    Even (momentOrder σ P) ∧ 0 < momentOrder σ P ∧
      10000*σ/P≤(momentOrder σ P:ℝ) ∧ (momentOrder σ P:ℝ)≤10000*σ/P+2 ∧
      (momentOrder σ P:ℝ)≤10002*σ := by
  have hσ0 : 0<σ := by linarith
  have hP0 : 0<P := by linarith
  have hlo := Nat.le_ceil (5000*σ/P)
  have hhi := Nat.ceil_lt_add_one (by positivity : 0≤5000*σ/P)
  have hn : 0<⌈5000*σ/P⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hdiv : 5000*σ/P≤5000*σ := div_le_self (by positivity) hP
  have heq : 10000*σ/P = 2*(5000*σ/P) := by ring
  unfold momentOrder
  push_cast
  rw [heq]
  refine ⟨even_two_mul _,by omega,?_,?_,?_⟩ <;> linarith

lemma residualOrder_bound {σ : ℝ} (hσ : 1≤σ) :
    0<residualOrder σ ∧ (residualOrder σ:ℝ)≤1000*Real.log σ+2 ∧
      (residualOrder σ:ℝ)≤1002*σ ∧
      (19/20:ℝ)^(residualOrder σ-1)≤σ^(-50:ℝ) := by
  have hσ0 : 0<σ := by linarith
  have hlog := Real.log_nonneg hσ
  have hhi := Nat.ceil_lt_add_one (show 0≤1000*Real.log σ by positivity)
  have hlo := Nat.le_ceil (1000*Real.log σ)
  have he : (19/20:ℝ)≤Real.exp (-(1/20:ℝ)) := by linarith [Real.add_one_le_exp (-(1/20:ℝ))]
  refine ⟨by unfold residualOrder; omega,?_,?_,?_⟩
  · unfold residualOrder
    push_cast
    linarith
  · have hl := Real.log_le_sub_one_of_pos hσ0
    unfold residualOrder
    push_cast
    linarith
  · simp only [residualOrder,Nat.add_sub_cancel]
    calc
      _ ≤ (Real.exp (-(1/20:ℝ)))^⌈1000*Real.log σ⌉₊ := pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp ((⌈1000*Real.log σ⌉₊:ℝ)*(-(1/20:ℝ))) := (Real.exp_nat_mul ..).symm
      _ ≤ Real.exp (Real.log σ*(-50)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := (Real.rpow_def_of_pos hσ0 _).symm

theorem eventually_moment_orders {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ D : ℝ,∀ R : ℕ,Range η σ D R →
      Even (momentOrder σ (P η σ D R)) ∧ 0 < momentOrder σ (P η σ D R) ∧
      10000*σ/P η σ D R≤(momentOrder σ (P η σ D R):ℝ) ∧
      (momentOrder σ (P η σ D R):ℝ)≤10000*σ/P η σ D R+2 ∧
      (momentOrder σ (P η σ D R):ℝ)≤10002*σ ∧
      200≤R/2 ∧ 0<residualOrder σ ∧ residualOrder σ≤(R/2-5000)/(2*200) ∧
      (momentOrder σ (P η σ D R):ℝ)*(residualOrder σ:ℝ)*
        (19/20:ℝ)^(residualOrder σ-1)<1/2 := by
  have hb : 0<ParameterHierarchy.beta η := beta_pos hη
  have hlog := (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero
  have ht : Tendsto (fun σ : ℝ => (1000000*Real.log σ+2000)/σ^(ParameterHierarchy.beta η)) atTop (𝓝 0) := by
    simpa only [add_div,mul_div_assoc,mul_zero,zero_add] using
      (hlog.const_mul 1000000).add ((tendsto_const_nhds (x:=(2000:ℝ))).div_atTop (tendsto_rpow_atTop hb))
  have hp : Tendsto (fun σ : ℝ => (10002*1002:ℝ)*σ^(-48:ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<48)).const_mul (10002*1002)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const (by norm_num : (0:ℝ)<1),
    hp.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (50000:ℝ))]
    with σ hσ ht hp hRlo
  intro D R hr
  have hσ0 : 0<σ := by linarith
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow hσ (by linarith : 0≤10*ParameterHierarchy.beta η)).trans
      (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  obtain ⟨heven,hpos,hplo,hphi,hps⟩ := momentOrder_bounds hσ hP
  obtain ⟨hhpos,hhlog,hhs,hpow⟩ := residualOrder_bound hσ
  have hsize : 1000*(residualOrder σ:ℝ)≤(R:ℝ) := by
    have hlog' := (div_le_iff₀ (Real.rpow_pos_of_pos hσ0 _)).mp ht.le
    nlinarith [hr.rlo]
  have hR : 50000≤R := by exact_mod_cast hRlo.trans hr.rlo
  have hsN : 1000*residualOrder σ≤R := by exact_mod_cast hsize
  have hsizeN : residualOrder σ≤(R/2-5000)/(2*200) := by omega
  refine ⟨heven,hpos,hplo,hphi,hps,by omega,hhpos,hsizeN,?_⟩
  apply lt_of_le_of_lt _ hp
  calc
    _ ≤ (10002*σ)*(1002*σ)*σ^(-50:ℝ) :=
      mul_le_mul (mul_le_mul hps hhs (Nat.cast_nonneg _) (by positivity)) hpow
        (pow_nonneg (by norm_num) _) (by positivity)
    _ = (10002*1002:ℝ)*σ^(-48:ℝ) := by
      rw [show (10002*σ)*(1002*σ)=(10002*1002:ℝ)*σ^(2:ℝ) by rw [Real.rpow_two]; ring,
        mul_assoc,←Real.rpow_add hσ0]
      norm_num

end

open Filter ParameterHierarchy
open scoped Topology

lemma pencilAlphabet_le {q k : ℕ} (hq : 1≤q) :
    (pencilAlphabet q k:ℝ)≤(k:ℝ)*(q:ℝ)^(k-1) := by
  unfold pencilAlphabet
  simp only [Nat.cast_sum,Nat.cast_pow]
  calc
    _ ≤ ∑ i∈Finset.range k,(q:ℝ)^(k-1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_right₀ (by exact_mod_cast hq)
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

lemma exp_geometryScale {q : ℕ} {σ g n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g)) :
    geometryScale q n=Real.exp (2*σ-g) := by
  rw [geometryScale,hq,hn,←Real.exp_nat_mul,←Real.exp_sub]
  congr 1
  norm_num
  ring

lemma exp_radialScale {q : ℕ} {σ g n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g)) :
    (q:ℝ)^4/n^2=Real.exp (-2*g) := by
  rw [hq,hn,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_sub]
  congr 1
  norm_num
  ring

noncomputable def localTruncConstant : ℝ := 24*2^(200:ℕ)*8^(4900:ℕ)
lemma localTruncConstant_pos : 0<localTruncConstant := by
  exact mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _))
    (pow_pos (by norm_num) _)

lemma high_local_radial_numeric {q m : ℕ} {σ g n χ P M : ℝ}
    (hσ : 1≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hP : 0≤P) (hM : 0≤M) (hMhi : M≤8*Real.exp (-g))
    (hm : (m:ℝ)≤Real.exp (3*σ)) :
    (pencilAlphabet q 3:ℝ)*P^5000*
      (M^4900*(2^200*((Nat.clog 2 m:ℝ)+1)*((q:ℝ)^4/n^2*Real.exp χ))) ≤
      geometryScale q n*(localTruncConstant*σ*P^5000*Real.exp (χ-4901*g)) := by
  have hq1 : 1≤q := by
    have h := hq▸Real.one_le_exp_iff.mpr (show 0≤σ by linarith)
    exact_mod_cast h
  have hQ := pencilAlphabet_le (k:=3) hq1
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hQ
  have hq2 : (q:ℝ)^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul]; norm_num
  rw [hq2] at hQ
  have hdy := dyad_count_le hσ hm
  rw [exp_radialScale hq hn]
  calc
    _ ≤ (3*Real.exp (2*σ))*P^5000*
      ((8*Real.exp (-g))^4900*(2^200*(8*σ)*(Real.exp (-2*g)*Real.exp χ))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hQ (pow_nonneg hP _)) _ (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hM hMhi _) _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdy (pow_nonneg (by norm_num) _)) (by positivity)
    _ = _ := by
      rw [exp_geometryScale hq hn,mul_pow,←Real.exp_nat_mul]
      simp only [Nat.cast_ofNat]
      rw [show (3*Real.exp (2*σ))*P^5000*(8^(4900:ℕ)*Real.exp (4900*(-g))*
          (2^(200:ℕ)*(8*σ)*(Real.exp (-2*g)*Real.exp χ))) =
        (24*2^(200:ℕ)*8^(4900:ℕ))*σ*P^5000*
          (Real.exp (2*σ)*Real.exp (4900*(-g))*Real.exp (-2*g)*Real.exp χ) by
            rw [show (24:ℝ)=3*8 by norm_num]; ac_rfl]
      rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
      unfold localTruncConstant
      rw [show Real.exp (2*σ-g)*((24*2^(200:ℕ)*8^(4900:ℕ))*σ*P^5000*Real.exp (χ-4901*g)) =
        (24*2^(200:ℕ)*8^(4900:ℕ))*σ*P^5000*(Real.exp (2*σ-g)*Real.exp (χ-4901*g)) by ac_rfl]
      rw [←Real.exp_add]
      congr 2
      ring

theorem eventually_local_trunc_scalar {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ D R g : ℝ,Range η σ D R → P η σ D R/10000≤g →
      localTruncConstant*σ*(P η σ D R)^5000*
        Real.exp (P η σ D R/100-4901*g)≤1 := by
  have hab := eventually_power_absorption hη hη' localTruncConstant 5001 (1/10)
    localTruncConstant_pos (by norm_num) (by norm_num)
  have hs := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hs] with σ hσ hab hs
  intro D R g hr hg
  have hp := (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  have hP0 : 0≤P η σ D R := (Real.rpow_nonneg (by linarith) _).trans hp
  have hPσ : P η σ D R≤σ := by
    have hh := hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hc : localTruncConstant*σ*(P η σ D R)^5000≤Real.exp (P η σ D R/10) := by
    calc
      _ ≤ localTruncConstant*σ*σ^5000 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hP0 hPσ _) (mul_nonneg localTruncConstant_pos.le (by linarith))
      _ = localTruncConstant*σ^(5001:ℕ) := by rw [show σ^(5001:ℕ)=σ^5000*σ from pow_succ σ 5000]; ac_rfl
      _ ≤ _ := by
        have hh := hab D R hr
        rw [show σ^(5001:ℝ)=σ^(5001:ℕ) from Real.rpow_natCast σ 5001] at hh
        simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using hh
  calc
    _ ≤ Real.exp (P η σ D R/10)*Real.exp (P η σ D R/100-4901*g) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (P η σ D R/10+(P η σ D R/100-4901*g)) := (Real.exp_add ..).symm
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

end SharpRamseyFive.ScoreGeometry

end

end OAI
