import Mathlib
import OAI.Probability.CoordinateSweeps.SparseDimension

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators
open Filter Asymptotics
namespace CoordinateSweeps.SparseScalar
-- A concrete permissible choice in source04/06. R is still chosen last.
def theta : ℝ := 1/1600
def K0 : ℝ := 100000
def B0 : ℕ := 12800
def xi : ℝ := 1/2048000000
def rho : ℝ := 1/32768000000
def q : ℕ := 65536000000
lemma constants : 0 < theta ∧ theta < 1 ∧ 1 ≤ K0 ∧ 1 ≤ B0 ∧
    0 < xi ∧ xi=theta/(100*B0) ∧ xi≤1/(4*B0) ∧ rho=xi/16 ∧ 2*q*rho=4 := by
  norm_num [theta,K0,B0,xi,rho,q]
lemma pow_two_exp (k : ℕ) : (2:ℝ)^k=Real.exp ((k:ℝ)*Real.log 2) := by
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
lemma exp_rpow (x y : ℝ) : (Real.exp x)^y=Real.exp (x*y) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
lemma rpow_exp (s x : ℝ) (hs : 0 < s) : s^x=Real.exp (x*Real.log s) := by
  rw [Real.rpow_def_of_pos hs,mul_comm]
lemma eventually_power_gt (ε C : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, C < s^ε := (tendsto_rpow_atTop hε).eventually (eventually_gt_atTop C)
lemma eventually_log_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧ Real.log s ≤ s^ε := by
  have hh := (isLittleO_log_rpow_rpow_atTop 1 hε).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with s hs h1
  simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg h1.le),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),one_mul] using And.intro h1 hs

/- All scalar scale requirements for the sparse proof can be imposed before
R and the finite real perturbation interval are fixed. -/
lemma eventually_sparse_requirements :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧
      Real.log s ≤ s^(theta/4) ∧ 2 ≤ s^(theta/4) ∧
      (B0+1 : ℝ) ≤ s^(theta/2) ∧
      4/s^(1/(4*(B0:ℝ))) ≤ theta/(64*B0) ∧
      Real.log (2*(B0:ℝ)+1)+Real.log 2 ≤ xi*Real.log s ∧
      Real.log 2 ≤ xi*Real.log s/8 := by
  have h1 := eventually_log_le_power (theta/4) (by norm_num [theta])
  have h2 := eventually_power_gt (theta/4) 2 (by norm_num [theta])
  have h3 := eventually_power_gt (theta/2) (B0+1) (by norm_num [theta])
  have h4 := eventually_power_gt (1/(4*B0)) (256*B0/theta) (by norm_num [B0])
  have ht : Tendsto (fun s : ℝ => xi*Real.log s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num [xi] : 0 < xi)).mpr Real.tendsto_log_atTop
  have h5 := ht.eventually (eventually_ge_atTop (Real.log (2*(B0:ℝ)+1)+Real.log 2))
  have h6 := ht.eventually (eventually_ge_atTop (8*Real.log 2))
  filter_upwards [h1,h2,h3,h4,h5,h6] with s hs h₂ h₃ h₄ h₅ h₆
  refine ⟨hs.1,hs.2,h₂.le,h₃.le,?_,h₅,by linarith⟩
  have hp : 0 < s^(1/(4*(B0:ℝ))) := Real.rpow_pos_of_pos (by linarith [hs.1]) _
  apply (div_le_iff₀ hp).mpr
  have hc : 0 < theta/(64*(B0:ℝ)) := by norm_num [theta,B0]
  have hh := mul_le_mul_of_nonneg_left h₄.le hc.le
  norm_num [theta,B0] at hh ⊢
  nlinarith

/- Arithmetic behind the many-coordinate HS bound, with its full literal
prefactor. The inputs are scalar size bounds derived from the allowed grid. -/
lemma many_HS_bound (s t b h : ℝ) (k : ℕ) (hs : 1 < s) (ht : 0 ≤ t)
    (hts : t ≤ s^(-theta/2)) (hh : h ≤ K0*k)
    (hb : 0 ≤ b)
    (habsorb : 3*Real.log 2+2*b*(K0+1+Real.log 4) ≤ theta*Real.log s/8) :
    ((2:ℝ)^k*Real.exp (b*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*t^((k:ℝ)/2)) ≤ s^(-theta*k/8) := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp := Real.rpow_le_rpow ht hts (by positivity : 0 ≤ (k:ℝ)/2)
  rw [rpow_exp s _ (by linarith),exp_rpow] at hp
  have he : b*(h+k)+Real.log 4*k*b ≤ b*(K0+1+Real.log 4)*k := by
    have hh' := mul_le_mul_of_nonneg_left hh hb
    nlinarith
  have he' := Real.exp_le_exp.mpr he
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^k*Real.exp (b*(h+k)+Real.log 4*k*b))
    (mul_le_mul_of_nonneg_left he' (by positivity)) 2
  apply (mul_le_mul hpow (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity) (by positivity)).trans
  rw [pow_two_exp,← Real.exp_add,← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add,rpow_exp s _ (by linarith)]
  apply Real.exp_le_exp.mpr
  have ha := mul_le_mul_of_nonneg_right habsorb hk
  push_cast
  nlinarith
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.SparseScalar
lemma prob_power_bound {s t E : ℝ} {k : ℕ} (hs : 1 < s) (ht : 0 ≤ t)
    (hts : t ≤ s^(-theta/2)) (hE : (k:ℝ)/(8*B0) ≤ E) :
    t^E ≤ Real.exp (-theta*k*Real.log s/(16*B0)) := by
  have hEp : 0 ≤ E := (by positivity : 0 ≤ (k:ℝ)/(8*B0)).trans hE
  have hh := Real.rpow_le_rpow ht hts hEp
  rw [rpow_exp s (-theta/2) (by linarith),exp_rpow] at hh
  apply hh.trans (Real.exp_le_exp.mpr ?_)
  have hp : 0 ≤ theta*Real.log s/2 := by
    have hl := Real.log_pos hs
    norm_num [theta]
    positivity
  have ha := mul_le_mul_of_nonneg_left hE hp
  norm_num [B0] at ha ⊢
  nlinarith

/- Scalar absorption of the literal coverage/occupancy union estimate. -/
lemma fewGood_bound {b k : ℕ} (hb : 1 ≤ b) (hB : b ≤ B0) (hk : 1 ≤ k)
    {s v u t : ℝ} (hs : 1 < s) (hv : 0 ≤ v) (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hvs : v ≤ s^(-theta/2)) (hus : u ≤ s^(-theta/2)) (hts : t ≤ s^(-theta/2))
    (C : Fin b → ℝ) (hC0 : ∀ j, 0 ≤ C j)
    (hC : ∀ j, C j ≤ Real.exp (theta*k*Real.log s/(32*B0)))
    (habs : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log s) :
    (2:ℝ)^k*v^((k:ℝ)/8)+∑ j : Fin b,
      ((2:ℝ)^k*u^((k:ℝ)/(8*b))+C j*2^k*t^((k:ℝ)/(8*b))) ≤ s^(-xi*k) := by
  have hbpos : (0:ℝ)<b := by exact_mod_cast hb
  have hB' : (b:ℝ)≤B0 := by exact_mod_cast hB
  have hkpos : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)≤k := by positivity
  have hL := Real.log_pos hs
  have hE : (k:ℝ)/(8*B0) ≤ (k:ℝ)/(8*b) :=
    div_le_div_of_nonneg_left hk0 (by positivity) (by nlinarith)
  have hE' : (k:ℝ)/(8*B0) ≤ (k:ℝ)/8 :=
    div_le_div_of_nonneg_left hk0 (by norm_num) (by norm_num [B0])
  let D := Real.exp (-theta*k*Real.log s/(32*B0))
  have hD : 0 ≤ D := (Real.exp_pos _).le
  have hpow : Real.exp (-theta*k*Real.log s/(16*B0)) ≤ D := by
    apply Real.exp_le_exp.mpr
    dsimp [theta,B0]
    nlinarith [mul_nonneg hk0 hL.le]
  have hv' : v^((k:ℝ)/8) ≤ D := (prob_power_bound hs hv hvs hE').trans hpow
  have hu' : u^((k:ℝ)/(8*b)) ≤ D := (prob_power_bound hs hu hus hE).trans hpow
  have ht' := prob_power_bound hs ht hts hE
  have hc' (j : Fin b) : C j*t^((k:ℝ)/(8*b)) ≤ D := by
    apply (mul_le_mul (hC j) ht' (Real.rpow_nonneg ht _) ((hC0 j).trans (hC j))).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
  calc
    _ ≤ (2:ℝ)^k*D+∑ _j : Fin b, (2*(2:ℝ)^k*D) := by
      apply add_le_add (mul_le_mul_of_nonneg_left hv' (by positivity))
      apply Finset.sum_le_sum
      intro j _
      have h1 := mul_le_mul_of_nonneg_left hu' (by positivity : 0 ≤ (2:ℝ)^k)
      have h2 := mul_le_mul_of_nonneg_left (hc' j) (by positivity : 0 ≤ (2:ℝ)^k)
      nlinarith
    _ = (1+2*(b:ℝ))*(2:ℝ)^k*D := by simp; ring
    _ ≤ (1+2*(B0:ℝ))*(2:ℝ)^k*D := by gcongr
    _ = Real.exp (Real.log (1+2*(B0:ℝ))+(k:ℝ)*Real.log 2-theta*k*Real.log s/(32*B0)) := by
      rw [pow_two_exp,show 1+2*(B0:ℝ)=Real.exp (Real.log (1+2*(B0:ℝ))) by
        rw [Real.exp_log (by norm_num [B0])],← Real.exp_add,← Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring
    _ ≤ s^(-xi*k) := by
      rw [rpow_exp _ _ (by linarith)]
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul_of_nonneg_right habs hk0
      have hlog : 0 ≤ Real.log (1+2*(B0:ℝ)) := Real.log_nonneg (by norm_num [B0])
      have hx := mul_le_mul_of_nonneg_right hkpos hlog
      norm_num [theta,xi,B0] at ha hx hlog ⊢
      nlinarith [mul_nonneg hk0 hL.le]
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.Grid
lemma size_pos (G : Grid) : 0 < G.size := by unfold size; positivity
lemma log_size (G : Grid) : Real.log G.size = ∑ j, (G.bits j : ℝ)*Real.log 2 := by
  simp only [size,Nat.cast_prod,Nat.cast_pow,Nat.cast_ofNat]
  rw [Real.log_prod (fun j _ => by positivity)]
  simp only [Real.log_pow]
lemma log_size_lower (G : Grid) {r : ℕ} (hG : G.Allowed r) :
    (G.b : ℝ)*((r : ℝ)*Real.log 2) ≤ Real.log G.size := by
  rw [G.log_size]
  calc
    _ = ∑ _ : Fin G.b, (r : ℝ)*Real.log 2 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (hG j).1) (Real.log_nonneg (by norm_num)))
lemma log_size_upper (G : Grid) {r : ℕ} (hG : G.Allowed r) :
    Real.log G.size ≤ 2*(G.b : ℝ)*((r : ℝ)*Real.log 2) := by
  rw [G.log_size]
  calc
    _ ≤ ∑ _ : Fin G.b, (2*r : ℝ)*Real.log 2 := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast (hG j).2) (Real.log_nonneg (by norm_num)))
    _ = _ := by simp; ring

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid
open SparseScalar
lemma log_coordinate (G : Grid) (j : Fin G.b) :
    Real.log (2^G.bits j : ℝ)=(G.bits j:ℝ)*Real.log 2 := by rw [Real.log_pow]
lemma log_size_pos_of_allowed (G : Grid) {r : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r) :
    0 < Real.log G.size := by
  have hb : 0 < (G.b:ℝ) := by exact_mod_cast G.positive
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  exact lt_of_lt_of_le (by positivity : 0 < (G.b:ℝ)*((r:ℝ)*Real.log 2)) (G.log_size_lower hG)
lemma coordinate_log_many (G : Grid) {r : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r)
    (hb : B0 ≤ G.b) (j : Fin G.b) :
    Real.log (2^G.bits j : ℝ) ≤ (theta/4)*Real.log G.size := by
  rw [G.log_coordinate]
  have hbits : (G.bits j:ℝ) ≤ 2*r := by exact_mod_cast (hG j).2
  have hb' : (B0:ℝ)≤G.b := by exact_mod_cast hb
  have hr' : 0 ≤ (r:ℝ)*Real.log 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hbits (by positivity : 0 ≤ Real.log 2)
  have h2 := mul_le_mul_of_nonneg_right hb' hr'
  have h3 := G.log_size_lower hG
  have hth : 0 ≤ theta/4 := by norm_num [theta]
  have h4 := mul_le_mul_of_nonneg_left h3 hth
  norm_num [theta,B0] at h2 h4 ⊢
  nlinarith
lemma coordinate_log_bounded (G : Grid) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (j : Fin G.b) :
    Real.log G.size/(2*(B0:ℝ)) ≤ Real.log (2^G.bits j : ℝ) := by
  rw [G.log_coordinate]
  have hb' : (G.b:ℝ)≤B0 := by exact_mod_cast hb
  have hr' : 0 ≤ (r:ℝ)*Real.log 2 := by positivity
  have hbits : (r:ℝ) ≤ G.bits j := by exact_mod_cast (hG j).1
  have h1 := mul_le_mul_of_nonneg_right hbits (by positivity : 0 ≤ Real.log 2)
  have h2 := mul_le_mul_of_nonneg_right hb' hr'
  have h3 := G.log_size_upper hG
  apply (div_le_iff₀ (by norm_num [B0] : 0 < 2*(B0:ℝ))).mpr
  norm_num [B0] at h2 ⊢
  nlinarith
lemma coordinate_size_many (G : Grid) {r : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r)
    (hb : B0 ≤ G.b) (j : Fin G.b) :
    (2^G.bits j:ℝ) ≤ (G.size:ℝ)^(theta/4) := by
  rw [rpow_exp _ _ (by exact_mod_cast G.size_pos)]
  rw [← Real.exp_log (by positivity : 0 < (2^G.bits j:ℝ))]
  exact Real.exp_le_exp.mpr (G.coordinate_log_many hr hG hb j)
lemma coordinate_size_bounded (G : Grid) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (j : Fin G.b) :
    (G.size:ℝ)^(1/(2*(B0:ℝ))) ≤ (2^G.bits j:ℝ) := by
  rw [rpow_exp _ _ (by exact_mod_cast G.size_pos)]
  rw [← Real.exp_log (by positivity : 0 < (2^G.bits j:ℝ))]
  apply Real.exp_le_exp.mpr
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using G.coordinate_log_bounded hG hb j
lemma card_line_mul (G : Grid) (j : Fin G.b) :
    2^G.bits j*Fintype.card (G.Line j)=G.size := by
  have he := Fintype.card_congr (Equiv.piSplitAt j (fun t => Cube (G.bits t)))
  simpa only [Fintype.card_prod,G.card_slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using he.symm
lemma card_line_le (G : Grid) (j : Fin G.b) : Fintype.card (G.Line j) ≤ G.size := by
  rw [← G.card_line_mul j]
  exact Nat.le_mul_of_pos_left _ (by positivity)
end CoordinateSweeps.Grid

namespace CoordinateSweeps.SparseScalar
lemma sparse_fraction {s u : ℝ} (hs : 1 < s) (hu : 0 ≤ u)
    (huS : u ≤ s^(1-theta)) (h2 : 2 ≤ s^(theta/4)) :
    2*u/(s*s^(-xi)) ≤ s^(-theta/2) := by
  have hs0 : 0 < s := by linarith
  apply (div_le_iff₀ (mul_pos hs0 (Real.rpow_pos_of_pos hs0 _))).mpr
  calc
    2*u ≤ s^(theta/4)*s^(1-theta) := mul_le_mul h2 huS hu (Real.rpow_nonneg hs0.le _)
    _ ≤ s^(-theta/2)*(s*s^(-xi)) := by
      rw [rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0]
      conv_rhs => arg 2; arg 1; rw [← Real.exp_log hs0]
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hl := Real.log_pos hs
      norm_num [theta,xi]
      linarith
lemma sparse_line_mass {s m : ℝ} (hs : 1 < s)
    (hm : s^(1/(2*(B0:ℝ))) ≤ m) : s^(1/(4*(B0:ℝ))) ≤ m*s^(-xi) := by
  have hs0 : 0 < s := by linarith
  calc
    _ ≤ s^(1/(2*(B0:ℝ)))*s^(-xi) := by
      rw [rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hl := Real.log_pos hs
      norm_num [B0,xi]
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hs0.le _)

lemma logarithm_count {s : ℝ} (hs : 2 ≤ s) {n : ℕ} (hn : (n : ℝ) ≤ s) :
    Real.log (n+1 : ℕ) ≤ 2*Real.log s := by
  have hs0 : 0 < s := by linarith
  have h1 : (n+1 : ℝ) ≤ 2*s := by linarith
  have hh := Real.log_le_log (by positivity : 0 < (n+1 : ℝ)) h1
  rw [Real.log_mul (by norm_num) hs0.ne'] at hh
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hs
  push_cast
  linarith
lemma occupancy_count {s m : ℝ} {n k : ℕ} (hs : 2 ≤ s) (hn : (n : ℝ) ≤ s)
    (hm : s^(1/(2*(B0:ℝ))) ≤ m)
    (habs : 4/s^(1/(4*(B0:ℝ))) ≤ theta/(64*B0)) :
    ((n+1:ℕ):ℝ)^⌊2*k/(m*s^(-xi))⌋₊ ≤ Real.exp (theta*k*Real.log s/(32*B0)) := by
  have hs1 : 1<s := by linarith
  have hs0 : 0<s := by linarith
  have hmη := sparse_line_mass hs1 hm
  have hp : 0 < s^(1/(4*(B0:ℝ))) := Real.rpow_pos_of_pos hs0 _
  have hmpos := hp.trans_le hmη
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 2*(k:ℝ)/(m*s^(-xi)))
  have hlog := logarithm_count hs hn
  have hlog0 : 0 ≤ Real.log (n+1:ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hL := Real.log_pos hs1
  have hh := mul_le_mul hfloor hlog hlog0 (by positivity : 0 ≤ 2*(k:ℝ)/(m*s^(-xi)))
  have hdiv := (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) hp hmη).trans habs
  have hh' := mul_le_mul_of_nonneg_right hdiv (mul_nonneg (Nat.cast_nonneg k) hL.le)
  have heq : (2*(k:ℝ)/(m*s^(-xi)))*(2*Real.log s)=(4/(m*s^(-xi)))*((k:ℝ)*Real.log s) := by ring
  rw [heq] at hh
  rw [show ((n+1:ℕ):ℝ)^⌊2*k/(m*s^(-xi))⌋₊=
      Real.exp ((⌊2*k/(m*s^(-xi))⌋₊:ℝ)*Real.log (n+1:ℕ)) by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]]
  apply Real.exp_le_exp.mpr
  have ht : 0 ≤ theta := by norm_num [theta]
  have hkL := mul_nonneg (Nat.cast_nonneg k) hL.le
  push_cast at hh
  norm_num [B0,theta] at hh' ⊢
  nlinarith
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.SparseScalar
lemma sparse_vertex_fraction {s t B : ℝ} (hs : 1 < s) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (htS : t ≤ s^(1-theta)) (hBS : B ≤ s^(theta/2)) :
    t*B/s ≤ s^(-theta/2) := by
  have hs0 : 0<s := by linarith
  apply (div_le_iff₀ hs0).mpr
  calc
    _ ≤ s^(1-theta)*s^(theta/2) := mul_le_mul htS hBS hB (ht.trans htS)
    _ = s^(-theta/2)*s := by
      rw [rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0]
      conv_rhs => arg 2; rw [← Real.exp_log hs0]
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
end CoordinateSweeps.SparseScalar
namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
/- Uniform bounded-axis source04:eq12, with all sparse geometry now discharged. -/
theorem sparse_fewGood_bound (hf : H.Feasible) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hs : (2:ℝ) ≤ G.size)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (h2 : 2 ≤ (G.size:ℝ)^(theta/4)) (hB : (B0+1:ℝ) ≤ (G.size:ℝ)^(theta/2))
    (hcount : 4/(G.size:ℝ)^(1/(4*(B0:ℝ))) ≤ theta/(64*B0))
    (habs : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log G.size) :
    Coverage.probability G.endpointWeight (fun v : Fin k → G.Slot × G.Slot =>
      ((H.goodSet (fun i => (v i).1) (fun i => (v i).2) ((G.size:ℝ)^(-xi))).card:ℝ)<k/2) ≤
      (G.size:ℝ)^(-xi*k) := by
  have hs1 : (1:ℝ)<G.size := by linarith
  have hs0 : (0:ℝ)<G.size := by linarith
  have hη : 0 < (G.size:ℝ)^(-xi) := Real.rpow_pos_of_pos hs0 _
  have hn : (G.size:ℝ)^(-theta/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs1.le (by norm_num [theta])
  have hhS : (h:ℝ) ≤ (G.size:ℝ)^(1-theta) := by push_cast at hsp; linarith
  have hkS : (k:ℝ) ≤ (G.size:ℝ)^(1-theta) := by push_cast at hsp; linarith
  have hhr := sparse_fraction hs1 (Nat.cast_nonneg h) hhS h2
  have hkr := sparse_fraction hs1 (Nat.cast_nonneg k) hkS h2
  have hvr : ((k+h:ℕ):ℝ)*G.vertexSharingRate ≤ (G.size:ℝ)^(-theta/2) := by
    have hbs : ((G.b+1:ℕ):ℝ)≤(B0+1:ℝ) := by exact_mod_cast Nat.add_le_add_right hb 1
    have hvS : ((k+h:ℕ):ℝ)≤(G.size:ℝ)^(1-theta) := by simpa only [Nat.add_comm k h] using hsp
    have hh := sparse_vertex_fraction hs1 (Nat.cast_nonneg (k+h)) (Nat.cast_nonneg (G.b+1)) hvS (hbs.trans hB)
    simpa only [Grid.vertexSharingRate,mul_div_assoc] using hh
  have hle := H.probability_fewGood_le hf hη (hhr.trans hn) (hkr.trans hn) (hvr.trans hn)
  apply hle.trans
  apply fewGood_bound G.positive hb hk hs1
    (mul_nonneg (Nat.cast_nonneg _) G.vertexSharingRate_nonneg) (by positivity) (by positivity)
    hvr hhr hkr _ (fun _ => by positivity) _ habs
  intro j
  apply occupancy_count hs (by exact_mod_cast G.card_line_le j)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using G.coordinate_size_bounded hG hb j) hcount
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.SparseScalar
def uniformRate : ℝ := Real.log ((2 : ℕ) : ℝ) + (B0 : ℝ) *
  (K0 + 1 + Real.log ((4 : ℕ) : ℝ) +
    Real.log (((16 : ℕ) : ℝ) * Real.exp ((2 : ℕ) : ℝ)) +
    Real.log (1 + ((16 : ℕ) : ℝ) * Real.exp ((2 : ℕ) : ℝ)))
lemma uniformRate_nonneg : 0 ≤ uniformRate := by
  unfold uniformRate
  have he : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have h1 : 0 ≤ Real.log (16*Real.exp 2) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log (1+16*Real.exp 2) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  norm_num [B0,K0]
  positivity
lemma eventually_prefactor_small : ∀ᶠ s : ℝ in atTop,
    uniformRate ≤ xi*Real.log s/16 := by
  have ht : Tendsto (fun s : ℝ => xi*Real.log s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num [xi] : 0 < xi)).mpr Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (16*uniformRate))] with s hs
  linarith
end CoordinateSweeps.SparseScalar
namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k : ℕ}
lemma uniformSparsePrefactor_le (hb : G.b ≤ B0) (hh : (h:ℝ) ≤ K0*k) :
    uniformSparsePrefactor G h k ≤ Real.exp (uniformRate*k) := by
  have hK : 0 ≤ K0 := by norm_num [K0]
  have he : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have h1 : 0 ≤ Real.log (16*Real.exp 2) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log (1+16*Real.exp 2) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have hb' : (G.b:ℝ)≤B0 := by exact_mod_cast hb
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg G.b)
  have hB := mul_le_mul_of_nonneg_right hb'
    (show 0 ≤ K0+1+Real.log 4+Real.log (16*Real.exp 2)+Real.log (1+16*Real.exp 2) by positivity)
  have hBk := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg k)
  unfold uniformSparsePrefactor
  rw [pow_two_exp,show (16*Real.exp 2)^(G.b*k)=Real.exp ((G.b*k:ℕ)*Real.log (16*Real.exp 2)) by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)],
    show (1+16*Real.exp 2)^(G.b*k)=Real.exp ((G.b*k:ℕ)*Real.log (1+16*Real.exp 2)) by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)],
    ← Real.exp_add,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold uniformRate
  push_cast
  nlinarith

/- Quantitative uniform-law HS-square contraction with fixed slack for the
later finite real perturbation step. -/
theorem sparse_uniform_HS_bound (H : G.Holes h) (hf : H.Feasible) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hh : (h:ℝ) ≤ K0*k) (hs : (2:ℝ) ≤ G.size)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (h2 : 2 ≤ (G.size:ℝ)^(theta/4)) (hB : (B0+1:ℝ) ≤ (G.size:ℝ)^(theta/2))
    (hcount : 4/(G.size:ℝ)^(1/(4*(B0:ℝ))) ≤ theta/(64*B0))
    (habs : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log G.size)
    (hη : (G.size:ℝ)^(-xi) ≤ 1/8)
    (hpref : uniformRate ≤ xi*Real.log G.size/16) (hlog2 : Real.log 2 ≤ xi*Real.log G.size/8) :
    H.placementHSsq (k := k) (fun _ => FiniteLaw.uniform _) ≤ (G.size:ℝ)^(-xi*k/4) := by
  have hs0 : (0:ℝ)<G.size := by linarith
  have hs1 : (1:ℝ)<G.size := by linarith
  have hL := Real.log_pos hs1
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)≤k := by positivity
  have hxi : 0 < xi := by norm_num [xi]
  have hhS := H.placementHSsq_uniform_le_fewGood (k := k) (Real.rpow_nonneg hs0.le _) hη
  have hfew := H.sparse_fewGood_bound hf hG hb hk hs hsp h2 hB hcount habs
  have hpref' := uniformSparsePrefactor_le (G := G) (k := k) hb hh
  have hprob : 0 ≤ Coverage.probability G.endpointWeight (fun v : Fin k → G.Slot × G.Slot =>
      ((H.goodSet (fun i => (v i).1) (fun i => (v i).2) ((G.size:ℝ)^(-xi))).card:ℝ)<k/2) :=
    by
      unfold Coverage.probability
      apply Finset.sum_nonneg
      intro v hv
      split_ifs
      · exact Coverage.productMass_nonneg _ G.endpointWeight_nonneg v
      · exact le_rfl
  have hp0 : 0 ≤ uniformSparsePrefactor G h k := by unfold uniformSparsePrefactor; positivity
  have hpp := pow_le_pow_left₀ hp0 hpref' 2
  apply hhS.trans ((mul_le_mul hpp (add_le_add (le_refl (((G.size:ℝ)^(-xi))^((k:ℝ)/2))) hfew)
    (add_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hs0.le _) _) hprob)
    (sq_nonneg _)).trans ?_)
  rw [rpow_exp (G.size:ℝ) (-xi) hs0,exp_rpow,rpow_exp (G.size:ℝ) (-xi*k) hs0,
    ← Real.exp_nat_mul,rpow_exp (G.size:ℝ) (-xi*k/4) hs0]
  have heq : (-xi*Real.log G.size)*((k:ℝ)/2)=-xi*k*Real.log G.size/2 := by ring
  rw [heq]
  have hsmall : Real.exp (-xi*k*Real.log G.size) ≤ Real.exp (-xi*k*Real.log G.size/2) := by
    apply Real.exp_le_exp.mpr
    have hpos := mul_nonneg (mul_nonneg hxi.le hk0) hL.le
    linarith
  have hsumm : Real.exp (-xi*k*Real.log G.size/2)+Real.exp (-xi*k*Real.log G.size) ≤
      2*Real.exp (-xi*k*Real.log G.size/2) := by linarith
  apply (mul_le_mul_of_nonneg_left hsumm (Real.exp_pos _).le).trans
  rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],
    ← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)]
  have h1 := mul_le_mul_of_nonneg_right hpref hk0
  have h2 := mul_le_mul_of_nonneg_right hlog2 hk0
  have h3 := mul_le_mul_of_nonneg_right hk' (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  push_cast
  nlinarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
open SparseScalar
lemma b_le_log_size {G : Grid} {r : ℕ} (hG : G.Allowed r)
    (hrL : 1 ≤ (r:ℝ)*Real.log 2) : (G.b:ℝ) ≤ Real.log G.size := by
  exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hrL).trans (G.log_size_lower hG)
lemma sparse_lineSharing (G : Grid) {r h k : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r)
    (hb : B0 ≤ G.b) (hrL : 1 ≤ (r:ℝ)*Real.log 2)
    (hlog : Real.log G.size ≤ (G.size:ℝ)^(theta/4))
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta)) :
    ((k+h:ℕ):ℝ)*G.lineSharingRate ≤ (G.size:ℝ)^(-theta/2) := by
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hb' := (b_le_log_size hG hrL).trans hlog
  have hrate : G.lineSharingRate ≤ (G.b:ℝ)*(G.size:ℝ)^(theta/4)/(G.size:ℝ) := by
    unfold lineSharingRate
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hs0.le
    calc
      _ ≤ ∑ _j : Fin G.b, (G.size:ℝ)^(theta/4) :=
        Finset.sum_le_sum (fun j _ => G.coordinate_size_many hr hG hb j)
      _ = _ := by simp
  have hp := mul_le_mul hsp hrate G.lineSharingRate_nonneg (Real.rpow_nonneg hs0.le _)
  have hb'' := mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hs0.le (theta/4))
  have hb''' := div_le_div_of_nonneg_right hb'' hs0.le
  calc
    ((k+h:ℕ):ℝ)*G.lineSharingRate = ((h+k:ℕ):ℝ)*G.lineSharingRate := by rw [Nat.add_comm]
    _ ≤ (G.size:ℝ)^(1-theta)*((G.b:ℝ)*(G.size:ℝ)^(theta/4)/(G.size:ℝ)) := hp
    _ ≤ (G.size:ℝ)^(1-theta)*((G.size:ℝ)^(theta/4)*(G.size:ℝ)^(theta/4)/(G.size:ℝ)) :=
      mul_le_mul_of_nonneg_left hb''' (Real.rpow_nonneg hs0.le _)
    _ = (G.size:ℝ)^(-theta/2) := by
      rw [← Real.rpow_add hs0,div_eq_mul_inv,← Real.rpow_neg_one,← Real.rpow_add hs0,← Real.rpow_add hs0]
      congr 1
      ring
lemma sparse_many_absorb (G : Grid) {r : ℕ} (hG : G.Allowed r)
    (hrL : 3*Real.log 2+2*(K0+1+Real.log 4) ≤ theta*((r:ℝ)*Real.log 2)/8) :
    3*Real.log 2+2*(G.b:ℝ)*(K0+1+Real.log 4) ≤ theta*Real.log G.size/8 := by
  have hb : (1:ℝ)≤G.b := by exact_mod_cast G.positive
  have hb0 : (0:ℝ)≤G.b := by positivity
  have h1 := mul_le_mul_of_nonneg_left hrL hb0
  have h2 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 3*Real.log 2)
  have h3 := mul_le_mul_of_nonneg_left (G.log_size_lower hG) (by norm_num [theta] : 0 ≤ theta/8)
  nlinarith
end CoordinateSweeps.Grid
namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k : ℕ}
/- Literal many-coordinate real-law HS-square bound, with all grid and
forest-counting conditions derived from source sparse size assumptions. -/
theorem sparse_many_HS_bound (H : G.Holes h) (hf : H.Feasible) {r : ℕ}
    (hr : 1 ≤ r) (hG : G.Allowed r) (hb : B0 ≤ G.b)
    (hrL : 1 ≤ (r:ℝ)*Real.log 2)
    (hrA : 3*Real.log 2+2*(K0+1+Real.log 4) ≤ theta*((r:ℝ)*Real.log 2)/8)
    (hh : (h:ℝ) ≤ K0*k)
    (hlog : Real.log G.size ≤ (G.size:ℝ)^(theta/4))
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    H.placementHSsq (k := k) (fun j => lineLaw (G.bits j) z hz hz') ≤
      (G.size:ℝ)^(-theta*k/8) := by
  have hL := G.log_size_pos_of_allowed hr hG
  have hs : (1:ℝ)<G.size := (Real.log_pos_iff (by exact_mod_cast G.size_pos.le)).mp hL
  have ht := G.sparse_lineSharing hr hG hb hrL hlog hsp
  have ht0 : 0 ≤ ((k+h:ℕ):ℝ)*G.lineSharingRate := mul_nonneg (Nat.cast_nonneg _) G.lineSharingRate_nonneg
  have hsmall : ((k+h:ℕ):ℝ)*G.lineSharingRate ≤ 1 := ht.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hs.le (by norm_num [theta]))
  exact (H.placementHSsq_le hf hz hz' hlo hhi hsmall).trans
    (many_HS_bound _ _ _ _ k hs ht0 ht hh (Nat.cast_nonneg _) (G.sparse_many_absorb hG hrA))
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
/- Every choice mass is a real polynomial. No conditional law is extended to complex z. -/
lemma continuous_choiceWeight (G : Grid) (ω : G.Choices) : Continuous (fun z : ℝ => G.choiceWeight z ω) := by
  unfold choiceWeight
  fun_prop
/- Event-level l1 distance, independent of the representation and therefore
suitable for a single bounded-grid perturbation interval. -/
def eventDistance (G : Grid) (E : Finset G.Choices) (z : ℝ) : ℝ :=
  ∑ ω ∈ E, |G.choiceWeight z ω/(∑ v ∈ E, G.choiceWeight z v)-
    G.choiceWeight 0 ω/(∑ v ∈ E, G.choiceWeight 0 v)|
lemma eventMass_zero_pos (G : Grid) (E : Finset G.Choices) (hE : E.Nonempty) :
    0 < ∑ ω ∈ E, G.choiceWeight 0 ω := by
  exact Finset.sum_pos (fun _ _ => G.choiceWeight_pos le_rfl (by norm_num) _) hE
lemma continuousAt_eventDistance_zero (G : Grid) (E : Finset G.Choices) (hE : E.Nonempty) :
    ContinuousAt (G.eventDistance E) 0 := by
  unfold eventDistance
  apply tendsto_finsetSum
  intro ω hω
  apply ContinuousAt.abs
  apply ContinuousAt.sub _ continuousAt_const
  apply ContinuousAt.div (G.continuous_choiceWeight ω).continuousAt
  · exact (continuous_finsetSum _ (fun v _ => G.continuous_choiceWeight v)).continuousAt
  · exact (G.eventMass_zero_pos E hE).ne'
@[simp] lemma eventDistance_zero (G : Grid) (E : Finset G.Choices) : G.eventDistance E 0=0 := by
  simp [eventDistance]
lemma eventually_eventDistance_small (G : Grid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in nhds (0:ℝ), ∀ E : Finset G.Choices, E.Nonempty → G.eventDistance E z < ε := by
  have hE : ∀ E : Finset G.Choices, ∀ᶠ z in nhds (0:ℝ), E.Nonempty → G.eventDistance E z < ε := by
    intro E
    by_cases hn : E.Nonempty
    · have hh := (G.continuousAt_eventDistance_zero E hn).eventually (gt_mem_nhds (by simpa using hε : G.eventDistance E 0<ε))
      filter_upwards [hh] with z hz
      exact fun _ => hz
    · exact Filter.Eventually.of_forall (fun _ h => (hn h).elim)
  exact Filter.eventually_all.mpr hE
end CoordinateSweeps.Grid
namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h : ℕ}
def event (H : G.Holes h) : Finset G.Choices := Finset.univ.filter H.Compatible
lemma event_nonempty (H : G.Holes h) (hf : H.Feasible) : H.event.Nonempty := by
  obtain ⟨ω,hω⟩ := hf
  exact ⟨ω,by simpa [event] using hω⟩
lemma probability_eq_eventMass (H : G.Holes h) (z : ℝ) :
    H.probability z=∑ ω ∈ H.event, G.choiceWeight z ω := by
  exact (Finset.sum_subtype H.event (by simp [event]) (fun ω => G.choiceWeight z ω)).symm
lemma eventDistance_eq (H : G.Holes h) (z : ℝ) :
    G.eventDistance H.event z=
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        |G.choiceWeight z ω.val/H.probability z-G.choiceWeight 0 ω.val/H.probability 0| := by
  simp only [Grid.eventDistance,← H.probability_eq_eventMass]
  exact Finset.sum_subtype H.event (by simp [event]) _
/- Uniform in every irreducible: real event-distance controls the conditional
operator difference. This avoids choosing a topology on equivalence classes
of irreducible models. -/
theorem conditionalAverage_difference_le (H : G.Holes h) (hf : H.Feasible)
    (z : ℝ) (ρ : UnitaryIrrep H.stabilizer) :
    ‖H.conditionalAverage hf z ρ-H.conditionalAverage hf 0 ρ‖ ≤ G.eventDistance H.event z := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  rw [H.conditionalAverage_eq_sum,H.conditionalAverage_eq_sum,← Finset.sum_sub_distrib,H.eventDistance_eq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ω hω
  rw [← sub_smul,← Complex.ofReal_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (matrix_unitary_norm_le _ (ρ.unitary _))
theorem conditionalAverage_perturb_bound (H : G.Holes h) (hf : H.Feasible)
    (z : ℝ) (ρ : UnitaryIrrep H.stabilizer) :
    ‖H.conditionalAverage hf z ρ‖ ≤ ‖H.conditionalAverage hf 0 ρ‖+G.eventDistance H.event z := by
  have hh := H.conditionalAverage_difference_le hf z ρ
  have ht := norm_le_insert (H.conditionalAverage hf 0 ρ) (H.conditionalAverage hf z ρ)
  rw [norm_sub_rev] at ht
  linarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
/- Literal finite parameter space of bounded ordered grids; no model of
irreducibles or of conditioned complex measures is involved. -/
def BoundedCode (B r : ℕ) := Σ b : Fin (B+1),
  Subtype (fun _ : Fin b.val → Fin (2*r+1) => 0 < b.val)
instance (B r : ℕ) : Finite (BoundedCode B r) := by unfold BoundedCode; infer_instance
def BoundedCode.grid {B r : ℕ} (x : BoundedCode B r) : Grid where
  b := x.1.val
  positive := x.2.property
  bits j := (x.2.val j).val
def boundedCode (G : Grid) (B r : ℕ) (hb : G.b ≤ B) (hbits : ∀ j, G.bits j ≤ 2*r) : BoundedCode B r :=
  ⟨⟨G.b,by omega⟩,⟨(fun j => ⟨G.bits j,by have hh := hbits j; omega⟩),G.positive⟩⟩
@[simp] lemma boundedCode_grid (G : Grid) (B r : ℕ) (hb : G.b ≤ B) (hbits : ∀ j, G.bits j ≤ 2*r) :
    (G.boundedCode B r hb hbits).grid=G := by cases G; rfl
/- Uniform finite real perturbation for all nonempty events on every bounded
allowed grid. Quantifiers include all feasible path events, uniformly in h. -/
theorem bounded_event_interval (B r : ℕ) (ε : Grid → ℝ) (hε : ∀ G, 0 < ε G) :
    ∃ zStar : ℝ, 0 < zStar ∧ zStar ≤ 1/2 ∧
      ∀ G : Grid, G.b ≤ B → (∀ j, G.bits j ≤ 2*r) →
      ∀ z ∈ Set.Icc 0 zStar, ∀ E : Finset G.Choices, E.Nonempty → G.eventDistance E z < ε G := by
  let : Fintype (BoundedCode B r) := Fintype.ofFinite _
  have hall : ∀ᶠ z in nhds (0:ℝ), ∀ x : BoundedCode B r,
      ∀ E : Finset x.grid.Choices, E.Nonempty → x.grid.eventDistance E z < ε x.grid := by
    exact Filter.eventually_all.mpr (fun x => x.grid.eventually_eventDistance_small (hε x.grid))
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨min (δ/2) (1/2),lt_min (by linarith) (by norm_num),min_le_right _ _,?_⟩
  intro G hb hbits z hz E hE
  have hdist : dist z (0:ℝ)<δ := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hz.1]
    have hh := hz.2.trans (min_le_left (δ/2) (1/2))
    linarith
  have hh := hd hdist (G.boundedCode B r hb hbits)
  cases G
  exact hh E hE
end CoordinateSweeps.Grid
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
