import OAI.NumberTheory.ShortEgyptian.Density

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma greedy_step (A C : ℕ) (hA : 0 < A) (hAC : A < C) :
    let z := quotient C A
    let r := residue C A z
    2 ≤ z ∧ z ≤ C ∧ r < A ∧
      (A:ℚ)/C = 1/(z:ℚ)+(r:ℚ)/(C*z) ∧
      (r:ℝ)/(C*z) ≤ ((A:ℝ)/C)^2 ∧ (r:ℝ)/(C*z) ≤ 1/2 := by
  dsimp
  let z := quotient C A
  let r := residue C A z
  change 2 ≤ z ∧ z ≤ C ∧ r < A ∧
    (A:ℚ)/C = 1/(z:ℚ)+(r:ℚ)/(C*z) ∧
      (r:ℝ)/(C*z) ≤ ((A:ℝ)/C)^2 ∧ (r:ℝ)/(C*z) ≤ 1/2
  have hC : 0 < C := hA.trans hAC
  have hz := quotient_spec hC hA
  have hr := residue_spec hC hA
  change 0 < z ∧ C ≤ A*z ∧ A*z < C+A at hz
  change r < A ∧ C+r=A*z at hr
  have hz2 : 2 ≤ z := by nlinarith
  have hzC : z ≤ C := by
    change ⌈(C:ℚ)/(A:ℚ)⌉₊ ≤ C
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast hA : (0:ℚ)<A)).mpr
    have ha1 : (1:ℚ) ≤ A := by exact_mod_cast hA
    nlinarith [show (0:ℚ)≤C by positivity]
  have hCq : (C:ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hzq : (z:ℚ) ≠ 0 := by exact_mod_cast hz.1.ne'
  have hCr : (0:ℝ)<C := by exact_mod_cast hC
  have hzr : (0:ℝ)<z := by exact_mod_cast hz.1
  have har : (0:ℝ)<A := by exact_mod_cast hA
  have hrR : (r:ℝ) < A := by exact_mod_cast hr.1
  have hACR : (A:ℝ)<C := by exact_mod_cast hAC
  have hzr2 : (2:ℝ)≤z := by exact_mod_cast hz2
  have hvR : (C:ℝ)≤A*z := by exact_mod_cast hz.2.1
  refine ⟨hz2,hzC,hr.1,?_,?_,?_⟩
  · have hre : (C:ℚ)+r=A*z := by exact_mod_cast hr.2
    field_simp
    nlinarith
  · have h1 : 1/(z:ℝ) ≤ (A:ℝ)/C := by
      apply (div_le_div_iff₀ hzr hCr).mpr
      simpa using hvR
    calc
      (r:ℝ)/(C*z) ≤ (A:ℝ)/(C*z) := div_le_div_of_nonneg_right hrR.le (mul_nonneg hCr.le hzr.le)
      _ = ((A:ℝ)/C)*(1/(z:ℝ)) := by ring
      _ ≤ ((A:ℝ)/C)*((A:ℝ)/C) := mul_le_mul_of_nonneg_left h1 (div_nonneg har.le hCr.le)
      _ = _ := by ring
  · apply (div_le_iff₀ (mul_pos hCr hzr)).mpr
    nlinarith

def Prepared (a b : ℕ) (T : ℝ) (k : ℕ) : Prop :=
  ∃ ns : List ℕ, ∃ A C : ℕ, (∀ n ∈ ns, 2 ≤ n) ∧ ns.length ≤ k ∧
    A ≤ a ∧ A < C ∧ (a:ℚ)/b = unitSum ns+(A:ℚ)/C ∧
    (A=0 ∨ T ≤ (C:ℝ) ∧ (C:ℝ)<T^2)

lemma prepared_of_large (A C : ℕ) (hAC : A < C) (T : ℝ) (k : ℕ)
    (hClo : T ≤ C) (hChi : (C:ℝ)<T^2) : Prepared A C T k := by
  exact ⟨[],A,C,by simp,by simp,le_rfl,hAC,by simp,Or.inr ⟨hClo,hChi⟩⟩

lemma prepared_zero (C : ℕ) (hC : 0<C) (T : ℝ) (k : ℕ) : Prepared 0 C T k := by
  exact ⟨[],0,C,by simp,by simp,le_rfl,hC,by simp,Or.inl rfl⟩

lemma prepared_cons (A C : ℕ) (hA : 0<A) (hAC : A<C) (T : ℝ) (k : ℕ)
    (h : Prepared (residue C A (quotient C A)) (C*quotient C A) T k) :
    Prepared A C T (k+1) := by
  obtain ⟨xs,B,D,hxs,hlen,hB,hBD,heq,hstop⟩ := h
  have hs := greedy_step A C hA hAC
  dsimp at hs
  refine ⟨quotient C A :: xs,B,D,?_,by simpa only [List.length_cons] using Nat.succ_le_succ hlen,
    hB.trans hs.2.2.1.le,hBD,?_,hstop⟩
  · intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hs.1
    · exact hxs n hn
  · rw [unitSum_cons]
    rw [Nat.cast_mul] at heq
    linarith [hs.2.2.2.1]

lemma prepare_aux (k : ℕ) (A C : ℕ) (hAC : A<C) (T v : ℝ) (hT : 1<T)
    (hv : 0<v) (hsize : (C:ℝ)<T^2) (hsmall : (A:ℝ)/C ≤ Real.exp (-v))
    (hcap : T ≤ Real.exp ((2:ℝ)^k*v)) : Prepared A C T k := by
  induction k generalizing A C v with
  | zero =>
    by_cases hA0 : A=0
    · subst A; exact prepared_zero C hAC T 0
    have hA : 0<A := Nat.pos_of_ne_zero hA0
    have hC : (0:ℝ)<C := by exact_mod_cast hA.trans hAC
    have h1 : (1:ℝ)≤A := by exact_mod_cast hA
    have hE : Real.exp (-v)=1/Real.exp v := by simp only [Real.exp_neg,one_div]
    rw [hE] at hsmall
    simp only [pow_zero,one_mul] at hcap
    have hprod := (div_le_div_iff₀ hC (Real.exp_pos v)).mp hsmall
    have hx : Real.exp v ≤ (C:ℝ) := by nlinarith [Real.exp_pos v]
    exact prepared_of_large A C hAC T 0 (hcap.trans hx) hsize
  | succ k ih =>
    by_cases hA0 : A=0
    · subst A; exact prepared_zero C hAC T (k+1)
    have hA : 0<A := Nat.pos_of_ne_zero hA0
    by_cases hCT : T ≤ (C:ℝ)
    · exact prepared_of_large A C hAC T (k+1) hCT hsize
    have hCT' : (C:ℝ)<T := lt_of_not_ge hCT
    have hC : 0<C := hA.trans hAC
    have hCR : (0:ℝ)<C := by exact_mod_cast hC
    let z := quotient C A
    let r := residue C A z
    have hs := greedy_step A C hA hAC
    change 2 ≤ z ∧ z ≤ C ∧ r < A ∧ _ at hs
    have hz : 0<z := by omega
    have hrCz : r<C*z := by nlinarith [hs.2.2.1]
    have hnextsize : ((C*z:ℕ):ℝ)<T^2 := by
      push_cast
      have hh : (z:ℝ)≤C := by exact_mod_cast hs.2.1
      nlinarith
    have hnextsmall : (r:ℝ)/(C*z:ℕ) ≤ Real.exp (-(2*v)) := by
      rw [Nat.cast_mul]
      apply hs.2.2.2.2.1.trans
      calc
        ((A:ℝ)/C)^2 ≤ (Real.exp (-v))^2 := pow_le_pow_left₀ (by positivity) hsmall 2
        _ = _ := by rw [pow_two,←Real.exp_add]; congr 1; ring
    have hnextcap : T ≤ Real.exp ((2:ℝ)^k*(2*v)) := by
      simpa only [pow_succ,mul_assoc] using hcap
    exact prepared_cons A C hA hAC T k (ih r (C*z) hrCz (2*v) (by positivity) hnextsize hnextsmall hnextcap)

lemma prepare_denominator (a b : ℕ) (ha : 0<a) (hab : a<b) (T : ℝ)
    (hT : 1<T) (hbT : (b:ℝ)<T) (k : ℕ)
    (hcap : T ≤ Real.exp ((2:ℝ)^k*Real.log 2)) : Prepared a b T (k+1) := by
  let z := quotient b a
  let r := residue b a z
  have hs := greedy_step a b ha hab
  change 2 ≤ z ∧ z ≤ b ∧ r < a ∧ _ at hs
  have hb : 0<b := ha.trans hab
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hz : 0<z := by omega
  have hr : r<b*z := by nlinarith [hs.2.2.1]
  have hsize : ((b*z:ℕ):ℝ)<T^2 := by
    push_cast
    have hh : (z:ℝ)≤b := by exact_mod_cast hs.2.1
    nlinarith
  have hsmall : (r:ℝ)/(b*z:ℕ) ≤ Real.exp (-Real.log 2) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),Nat.cast_mul]
    simpa only [one_div] using hs.2.2.2.2.2
  exact prepared_cons a b ha hab T k (prepare_aux k r (b*z) hr T (Real.log 2) hT
    (Real.log_pos (by norm_num)) hsize hsmall hcap)

noncomputable def greedySteps (S : ℝ) : ℕ :=
  ⌈Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2⌉₊

noncomputable def greedyConstant : ℝ := (dimC:ℝ)/(Real.log 2)^2+1/Real.log 2+2

lemma greedyConstant_pos : 0<greedyConstant := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  dsimp [greedyConstant]
  have hD : (0:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
  positivity

lemma greedy_power_cap (S : ℝ) (hS : 0<S) :
    Real.exp ((dimC:ℝ)*S) ≤ Real.exp ((2:ℝ)^greedySteps S*Real.log 2) := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hD : (0:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
  have hx : 0 < (dimC:ℝ)*S/Real.log 2 := div_pos (mul_pos hD hS) h₂
  have hh := (div_le_iff₀ h₂).mp (Nat.le_ceil (Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2))
  change Real.log ((dimC:ℝ)*S/Real.log 2) ≤ (greedySteps S:ℝ)*Real.log 2 at hh
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log hx,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] at he
  exact Real.exp_le_exp.mpr ((div_le_iff₀ h₂).mp he)

lemma greedy_length_bound (S : ℝ) (hS : 1≤S) (hlog : 1≤Real.log S) :
    ((greedySteps S+1:ℕ):ℝ) ≤ greedyConstant*Real.log S := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h₂' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hD : (1:ℝ)≤dimC := by norm_num [dimC,dimX,dimM]
  have hSp : 0<S := lt_of_lt_of_le (by norm_num) hS
  have hD' : 0<(dimC:ℝ) := by linarith
  have hx : 1≤(dimC:ℝ)/Real.log 2 := (le_div_iff₀ h₂).mpr (by nlinarith)
  have hprod : 1≤(dimC:ℝ)*S/Real.log 2 := by
    rw [mul_div_right_comm]
    nlinarith
  have ht : 0 ≤ Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2 :=
    div_nonneg (Real.log_nonneg hprod) h₂.le
  have hh := Nat.ceil_lt_add_one ht
  change (greedySteps S:ℝ) < Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2+1 at hh
  have heq : Real.log ((dimC:ℝ)*S/Real.log 2) = Real.log ((dimC:ℝ)/Real.log 2)+Real.log S := by
    rw [mul_div_right_comm,Real.log_mul (div_pos hD' h₂).ne' hSp.ne']
  have hL : Real.log ((dimC:ℝ)/Real.log 2) ≤ (dimC:ℝ)/Real.log 2 :=
    (Real.log_le_sub_one_of_pos (div_pos hD' h₂)).trans (by linarith)
  have hcoef : 0 ≤ (dimC:ℝ)/(Real.log 2)^2+2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hlog hcoef
  have hd := div_le_div_of_nonneg_right hL h₂.le
  rw [heq,add_div] at hh
  dsimp [greedyConstant]
  push_cast
  have heq' : (dimC:ℝ)/(Real.log 2)/Real.log 2 = (dimC:ℝ)/(Real.log 2)^2 := by ring
  rw [heq'] at hd
  simp only [div_eq_mul_inv] at hh hb hd ⊢
  nlinarith

end ShortEgyptian

end OAI
