import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Real

def logMeshLength (T : ℝ) : ℝ := -Real.log (1-T)
def logMeshCount (T h : ℝ) : ℕ := ⌈logMeshLength T/h⌉₊
def logMeshStep (T h : ℝ) : ℝ := logMeshLength T/(logMeshCount T h:ℝ)
def logMeshNode (T h : ℝ) (j : ℕ) : ℝ := 1-Real.exp (-(j:ℝ)*logMeshStep T h)

lemma logMeshLength_pos {T : ℝ} (hT0 : 0<T) (hT1 : T<1) : 0<logMeshLength T := by
  dsimp [logMeshLength]
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

lemma logMeshCount_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    0<logMeshCount T h := by
  have hp := div_pos (logMeshLength_pos hT0 hT1) hh
  have he := Nat.le_ceil (logMeshLength T/h)
  have hc : (0:ℝ)<logMeshCount T h := hp.trans_le he
  exact_mod_cast hc

lemma logMeshCount_bound {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    (logMeshCount T h:ℝ)<logMeshLength T/h+1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos (logMeshLength_pos hT0 hT1) hh))

lemma logMeshStep_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    0<logMeshStep T h :=
  div_pos (logMeshLength_pos hT0 hT1) (by exact_mod_cast logMeshCount_pos hT0 hT1 hh)

lemma logMeshStep_le {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    logMeshStep T h≤h := by
  have hN : (0:ℝ)<logMeshCount T h := by exact_mod_cast logMeshCount_pos hT0 hT1 hh
  apply (div_le_iff₀ hN).mpr
  have he := (div_le_iff₀ hh).mp (Nat.le_ceil (logMeshLength T/h))
  change logMeshLength T≤(logMeshCount T h:ℝ)*h at he
  nlinarith

lemma logMeshStep_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) : h/2≤logMeshStep T h := by
  have hN : (0:ℝ)<logMeshCount T h := by exact_mod_cast logMeshCount_pos hT0 hT1 hh
  have he : (logMeshCount T h:ℝ)<(logMeshLength T+h)/h := by
    simpa only [add_div,div_self (ne_of_gt hh)] using logMeshCount_bound hT0 hT1 hh
  have hN' := (lt_div_iff₀ hh).mp he
  apply (le_div_iff₀ hN).mpr
  nlinarith

@[simp] lemma logMeshNode_zero (T h : ℝ) : logMeshNode T h 0=0 := by
  simp [logMeshNode]

lemma logMeshNode_last {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    logMeshNode T h (logMeshCount T h)=T := by
  have hN : (logMeshCount T h:ℝ)≠0 := by
    exact_mod_cast ne_of_gt (logMeshCount_pos hT0 hT1 hh)
  dsimp [logMeshNode,logMeshStep,logMeshLength]
  rw [neg_mul, mul_div_cancel₀ _ hN,neg_neg,Real.exp_log (by linarith : 0<1-T)]
  ring

lemma logMeshNode_sub {T h : ℝ} (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j=
      (1-logMeshNode T h j)*(1-Real.exp (-logMeshStep T h)) := by
  have he : -((j+1:ℕ):ℝ)*logMeshStep T h=
      -(j:ℝ)*logMeshStep T h+(-logMeshStep T h) := by push_cast; ring
  simp only [logMeshNode,he,Real.exp_add]
  ring

lemma logMeshNode_strictMono {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    StrictMono (logMeshNode T h) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hs := logMeshStep_pos hT0 hT1 hh
  have he : Real.exp (-logMeshStep T h)<1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hp : 0<1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using Real.exp_pos (-(j:ℝ)*logMeshStep T h)
  have hd : 0<logMeshNode T h (j+1)-logMeshNode T h j := by
    rw [logMeshNode_sub]
    exact mul_pos hp (by linarith)
  linarith

lemma logMeshNode_mem {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    {j : ℕ} (hj : j≤logMeshCount T h) : logMeshNode T h j∈Set.Icc 0 T := by
  have hm := (logMeshNode_strictMono hT0 hT1 hh).monotone
  constructor
  · simpa only [logMeshNode_zero] using hm (Nat.zero_le j)
  · simpa only [logMeshNode_last hT0 hT1 hh] using hm hj

lemma logMeshCell_upper {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j≤h*(1-logMeshNode T h j) := by
  have hb : 1-Real.exp (-logMeshStep T h)≤h := by
    have hx := Real.add_one_le_exp (-logMeshStep T h)
    have hs := logMeshStep_le hT0 hT1 hh
    linarith
  have hp : 0≤1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos (-(j:ℝ)*logMeshStep T h)).le
  rw [logMeshNode_sub,mul_comm h]
  exact mul_le_mul_of_nonneg_left hb hp

lemma logMeshCell_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hsmall : h≤Real.log 2) (j : ℕ) :
    h/4*(1-logMeshNode T h j)≤logMeshNode T h (j+1)-logMeshNode T h j := by
  have hs0 := logMeshStep_pos hT0 hT1 hh
  have hs := logMeshStep_le hT0 hT1 hh
  have hs' := logMeshStep_lower hT0 hT1 hh hL
  have he : Real.exp (logMeshStep T h)≤2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr (hs.trans hsmall)
  have he' : (1:ℝ)/2≤Real.exp (-logMeshStep T h) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (Real.exp_pos _) he)
  have hw : logMeshStep T h*Real.exp (-logMeshStep T h)≤1-Real.exp (-logMeshStep T h) := by
    have hx := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (logMeshStep T h))
      (Real.exp_pos (-logMeshStep T h)).le
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hx
    nlinarith
  have hb : h/4≤1-Real.exp (-logMeshStep T h) := by
    have hx := mul_le_mul_of_nonneg_left he' hs0.le
    nlinarith
  have hp : 0≤1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos (-(j:ℝ)*logMeshStep T h)).le
  rw [logMeshNode_sub,mul_comm (h/4)]
  exact mul_le_mul_of_nonneg_left hb hp
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature

lemma logMeshCell_upper_right {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hsmall : h≤Real.log 2) (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j≤2*h*(1-logMeshNode T h (j+1)) := by
  have hs := logMeshStep_le hT0 hT1 hh
  have he : Real.exp (logMeshStep T h)≤2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr (hs.trans hsmall)
  have hid : (1-logMeshNode T h (j+1))*Real.exp (logMeshStep T h)=1-logMeshNode T h j := by
    simp only [logMeshNode,sub_sub_cancel,←Real.exp_add]
    congr 1
    push_cast
    ring
  have hn : 0≤1-logMeshNode T h (j+1) := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos _).le
  have hb := mul_le_mul_of_nonneg_left he hn
  rw [hid] at hb
  calc
    _ ≤ h*(1-logMeshNode T h j) := logMeshCell_upper hT0 hT1 hh j
    _ ≤ h*((1-logMeshNode T h (j+1))*2) := mul_le_mul_of_nonneg_left hb hh.le
    _ = _ := by ring

lemma cell_singularity_cancel {a b t h : ℝ} (ha : 0≤a) (hat : a≤t) (htb : t≤b)
    (hb : b<1) (hh : 0≤h) (hcell : b-a≤h*(1-b)) (n : ℕ) :
    (t-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*n+2)≤h^(n+1) := by
  have hb0 : 0≤b := ha.trans (hat.trans htb)
  have hp : 0<1-b^2 := by nlinarith
  have hlen : t-a≤h*(1-b^2) := by
    have he : 1-b≤1-b^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he hh
    linarith
  have hr : (t-a)*(1-b^2)⁻¹≤h := by
    rw [←div_eq_mul_inv,div_le_iff₀ hp]
    exact hlen
  rw [show 2*n+2=2*(n+1) by omega,pow_mul,inv_pow,Real.sq_sqrt hp.le,←mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hat) (inv_nonneg.mpr hp.le)) hr _

lemma cell_taylor_budget {a b t h A : ℝ} (ha : 0≤a) (hat : a≤t) (htb : t≤b)
    (hb : b<1) (hh : 0≤h) (hcell : b-a≤h*(1-b)) (hA : 0≤A) (n : ℕ) :
    ((t-a)^(n+1)/(n.factorial:ℝ))^2*(A*((Real.sqrt (1-b^2))⁻¹)^(2*n+2))^2≤
      (A*h^(n+1))^2 := by
  have hfac : (1:ℝ)≤n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfp : (0:ℝ)<n.factorial := by positivity
  have hd : (t-a)^(n+1)/(n.factorial:ℝ)≤(t-a)^(n+1) := by
    rw [div_le_iff₀ hfp]
    exact le_mul_of_one_le_right (pow_nonneg (sub_nonneg.mpr hat) _) hfac
  have hB := cell_singularity_cancel ha hat htb hb hh hcell n
  have hR : 0≤((Real.sqrt (1-b^2))⁻¹)^(2*n+2) := by positivity
  have he : ((t-a)^(n+1)/(n.factorial:ℝ))*(A*((Real.sqrt (1-b^2))⁻¹)^(2*n+2))≤
      A*h^(n+1) := by
    calc
      _ ≤ (t-a)^(n+1)*(A*((Real.sqrt (1-b^2))⁻¹)^(2*n+2)) :=
        mul_le_mul_of_nonneg_right hd (mul_nonneg hA hR)
      _ = A*((t-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*n+2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB hA
  rw [←mul_pow]
  apply pow_le_pow_left₀ _ he 2
  positivity
end LogConcaveSampling.Quadrature

end

end

end

end OAI
