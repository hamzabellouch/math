import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.MomentOrder
import OAI.Combinatorics.RamseyFive.Iteration.CellScoreProcedure

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma eventually_exception_decay {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (C : ℝ) (hC : 0<C) :
    ∀ᶠ σ : ℝ in atTop,∀ D R : ℝ,Range η σ D R →
      C*σ*Real.exp (-P η σ D R/20000)≤Real.exp (-L η σ D/1000) := by
  have habs := eventually_power_absorption hη hη' C 1 (1/40000) hC (by norm_num) (by norm_num)
  have hlarge := (tendsto_rpow_atTop (beta_pos hη)).eventually (eventually_ge_atTop (40:ℝ))
  filter_upwards [eventually_ge_atTop (1:ℝ),habs,hlarge] with σ hσ habs hlarge
  intro D R hr
  have hb := finite_bounds hη hη' hσ hr
  have hL : 0<L η σ D := by dsimp [L];exact mul_pos hb.1 (Real.rpow_pos_of_pos (by linarith only [hσ]) _)
  have hR : 40≤R := hlarge.trans hr.rlo
  have hLP : 40*L η σ D≤P η σ D R := by dsimp [P];nlinarith only [hL,hR]
  have hc : C*σ≤Real.exp (P η σ D R/40000) := by
    simpa only [Real.rpow_one,one_mul,one_div,mul_comm (40000⁻¹:ℝ),div_eq_mul_inv] using habs D R hr
  calc
    _ ≤ Real.exp (P η σ D R/40000)*Real.exp (-P η σ D R/20000) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (-P η σ D R/40000) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hLP])

theorem eventually_exception_payment {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (A B M : ℝ) (hA : 0≤A) (hB : 0≤B) (hM : 0<M) :
    ∀ᶠ σ : ℝ in atTop,∀ (D R g χ : ℝ) (m : ℕ),Range η σ D R →
      P η σ D R/10000≤g → P η σ D R/100≤χ → (m:ℝ)≤Real.exp (3*σ) →
      ((Nat.clog 2 m:ℝ)+1)*(A*Real.exp (-(4/5:ℝ)*g)+B*Real.exp (-χ))≤
        Real.exp (-L η σ D/1000)/M := by
  have hC : 0<8*M*(1+A+B) := by positivity
  have he := eventually_exception_decay hη hη' (8*M*(1+A+B)) hC
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with σ hσ he
  intro D R g χ m hr hg hχ hm
  have hb := finite_bounds hη hη' hσ hr
  have hL : 0<L η σ D := by dsimp [L];exact mul_pos hb.1 (Real.rpow_pos_of_pos (by linarith only [hσ]) _)
  have hP : 0<P η σ D R := mul_pos hL hb.2.1
  have h1 : Real.exp (-(4/5:ℝ)*g)≤Real.exp (-P η σ D R/20000) :=
    Real.exp_le_exp.mpr (by linarith only [hg,hP])
  have h2 : Real.exp (-χ)≤Real.exp (-P η σ D R/20000) :=
    Real.exp_le_exp.mpr (by linarith only [hχ,hP])
  have hsum : A*Real.exp (-(4/5:ℝ)*g)+B*Real.exp (-χ)≤
      (1+A+B)*Real.exp (-P η σ D R/20000) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_left h2 hB)
    nlinarith only [hh,Real.exp_pos (-P η σ D R/20000)]
  apply (le_div_iff₀ hM).mpr
  calc
    _ ≤ (8*σ)*((1+A+B)*Real.exp (-P η σ D R/20000))*M :=
      mul_le_mul_of_nonneg_right (mul_le_mul (dyad_count_le hσ hm) hsum (by positivity) (by linarith only [hσ])) hM.le
    _ = (8*M*(1+A+B))*σ*Real.exp (-P η σ D R/20000) := by ring
    _ ≤ _ := he D R hr

theorem eventually_exception_payment_wide {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (A B M : ℝ) (hA : 0≤A) (hB : 0≤B) (hM : 0<M) :
    ∀ᶠ σ : ℝ in atTop,∀ (D R g χ : ℝ) (m : ℕ),Range η σ D R →
      P η σ D R/10000≤g → P η σ D R/200≤χ → (m:ℝ)≤Real.exp (3*σ) →
      ((Nat.clog 2 m:ℝ)+1)*(A*Real.exp (-(4/5:ℝ)*g)+B*Real.exp (-χ))≤
        Real.exp (-L η σ D/1000)/M := by
  have hC : 0<8*M*(1+A+B) := by positivity
  have he := eventually_exception_decay hη hη' (8*M*(1+A+B)) hC
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with σ hσ he
  intro D R g χ m hr hg hχ hm
  have hb := finite_bounds hη hη' hσ hr
  have hL : 0<L η σ D := by dsimp [L];exact mul_pos hb.1 (Real.rpow_pos_of_pos (by linarith only [hσ]) _)
  have hP : 0<P η σ D R := mul_pos hL hb.2.1
  have h1 : Real.exp (-(4/5:ℝ)*g)≤Real.exp (-P η σ D R/20000) :=
    Real.exp_le_exp.mpr (by linarith only [hg,hP])
  have h2 : Real.exp (-χ)≤Real.exp (-P η σ D R/20000) :=
    Real.exp_le_exp.mpr (by linarith only [hχ,hP])
  have hsum : A*Real.exp (-(4/5:ℝ)*g)+B*Real.exp (-χ)≤
      (1+A+B)*Real.exp (-P η σ D R/20000) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_left h2 hB)
    nlinarith only [hh,Real.exp_pos (-P η σ D R/20000)]
  apply (le_div_iff₀ hM).mpr
  calc
    _ ≤ (8*σ)*((1+A+B)*Real.exp (-P η σ D R/20000))*M :=
      mul_le_mul_of_nonneg_right (mul_le_mul (dyad_count_le hσ hm) hsum (by positivity) (by linarith only [hσ])) hM.le
    _ = (8*M*(1+A+B))*σ*Real.exp (-P η σ D R/20000) := by ring
    _ ≤ _ := he D R hr

end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreScalars
lemma regular_training_payment_half {L P : ℝ} (hL : 10000000000≤L) (hLP : 100*L≤P) :
    200000*Real.exp (-2*(L/100))+Real.exp (-P/2)≤Real.exp (-L/1000)/2 := by
  have h₁ := exp_sub_le_scaled (a:=L/1000) (b:=2*(L/100)) (C:=800000) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤800000),hL])
  have h₂ := exp_sub_le_scaled (a:=L/1000) (b:=P/2) (C:=4) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤4),hL,hLP])
  simp only [neg_div,neg_mul] at *
  linarith only [h₁,h₂]

lemma ambient_three_payment {σ : ℝ} (hσ : 100≤σ) :
    2*Real.exp (3*σ)*(Real.exp σ)^(-(50:ℝ))≤1/2 := by
  rw [←Real.exp_mul, mul_assoc,←Real.exp_add]
  have h := exp_sub_le_scaled (a:=0) (b:=47*σ) (C:=4) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤4),hσ])
  simp only [neg_zero,Real.exp_zero] at h
  have he : 3*σ+σ*(-50)=-(47*σ) := by ring
  rw [he]
  linarith only [h]

lemma strong_exception_payment {q n E a P : ℝ} (_hq : 0≤q) (hn : 0<n) (hE : 0≤E)
    (ha : Real.exp (-P)≤a) (hnq : q^2≤4*n*Real.exp (4*P))
    (hcount : E*a^2≤333024*q^2) (hbig : (1332096:ℝ)≤Real.exp P) :
    E≤n*Real.exp (7*P) := by
  have ha0 : 0≤a := (Real.exp_pos _).le.trans ha
  have hsq : Real.exp (-2*P)≤a^2 := by
    calc
      Real.exp (-2*P)=(Real.exp (-P))^2 := by rw [←Real.exp_nat_mul];congr 1;ring
      _≤a^2 := pow_le_pow_left₀ (Real.exp_nonneg (-P)) ha 2
  have hh : E*Real.exp (-2*P)≤333024*q^2 :=
    (mul_le_mul_of_nonneg_left hsq hE).trans hcount
  have hcancel : (E*Real.exp (-2*P))*Real.exp (2*P)=E := by
    rw [mul_assoc,←Real.exp_add];simp
  calc
    E=(E*Real.exp (-2*P))*Real.exp (2*P) := hcancel.symm
    _≤(333024*q^2)*Real.exp (2*P) := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
    _≤(333024*(4*n*Real.exp (4*P)))*Real.exp (2*P) := by gcongr
    _=1332096*n*Real.exp (6*P) := by
      rw [show (333024*(4*n*Real.exp (4*P)))*Real.exp (2*P)=1332096*n*(Real.exp (4*P)*Real.exp (2*P)) by ring,
        ←Real.exp_add];congr 2;ring
    _≤Real.exp P*n*Real.exp (6*P) := by gcongr
    _=n*Real.exp (7*P) := by rw [mul_assoc,mul_left_comm (Real.exp P),←Real.exp_add];congr 2;ring
end SharpRamseyFive.ScoreScalars

namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_plane_ambient_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
      let Q := P η σ D R
      let a := 1/(100*(momentOrder σ Q:ℝ))
      100000000≤Q/10000 ∧ Q/10000<σ/2-4*Q ∧
      20*Q≤σ/2-4*Q ∧ Real.exp (-Q)≤a ∧ a≤2 ∧ (1332096:ℝ)≤Real.exp Q := by
  have hh := eventually_hierarchy hη hη' 0 (1/100) 1000000000000 (by norm_num) (by norm_num)
  have ha := eventually_power_absorption hη hη' 1000200 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hc := eventually_power_absorption hη hη' 1332096 0 1 (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hh,ha,hc] with σ hσ hh ha hc
  intro D R hr
  have hh := hh D R 0 0 hr (by simp) (by positivity)
  have ha := ha D R hr
  have hc := hc D R hr
  dsimp only
  have hL : 0≤L η σ D := by linarith only [hh.1]
  have hLP : L η σ D≤P η σ D R := by linarith only [hh.2.2.2.2.2,hL]
  have hP : 1≤P η σ D R := by linarith only [hh.1,hLP]
  have hp := momentOrder_bounds hσ hP
  have hp0 : (0:ℝ)< momentOrder σ (P η σ D R) := Nat.cast_pos.mpr hp.2.1
  have hp1 : (1:ℝ)≤ momentOrder σ (P η σ D R) := by exact_mod_cast hp.2.1
  refine ⟨by linarith only [hh.1,hLP],by linarith only [hh.2.1,hP],by linarith only [hh.2.1,hP],?_,?_,?_⟩
  · rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ))
    calc
      _≤100*(10002*σ) := mul_le_mul_of_nonneg_left hp.2.2.2.2 (by norm_num)
      _=1000200*σ := by ring
      _≤_ := by simpa only [Real.rpow_one,one_mul] using ha
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ))).mpr
    linarith only [hp1]
  · simpa only [Real.rpow_zero,mul_one,one_mul] using hc
end SharpRamseyFive.ScoreGeometry

end OAI
