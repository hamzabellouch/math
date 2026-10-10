import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WindowMulBounded

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryLocalAdditive
open OrdinaryCorrelations OrdinarySharpWindow OrdinaryChainScales Finset Filter MeasureTheory

def phase (x : ℝ) : ℂ := Complex.exp ((2*Real.pi*x:ℝ)*Complex.I)
lemma norm_phase (x : ℝ) : ‖phase x‖=1 := by simp [phase,Complex.norm_exp]
lemma phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma phase_int (n : ℤ) : phase n=1 := by
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨n,?_⟩
  push_cast
  ring
lemma phase_sub_le (x y : ℝ) : ‖phase x-phase y‖ ≤ 2*Real.pi*|x-y| := by
  have he : phase x-phase y=phase y*(phase (x-y)-1) := by
    rw [mul_sub,mul_one,← phase_add]
    congr 1
    congr 1
    ring
  rw [he,norm_mul,norm_phase,one_mul]
  have hh := @Real.norm_exp_I_mul_ofReal_sub_one_le (2*Real.pi*(x-y))
  rw [mul_comm Complex.I] at hh
  simpa only [phase,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0 < (2:ℝ)*Real.pi)] using hh

lemma phase_rational_mod (a : ℤ) {q : ℕ} (hq : 0 < q) (n : ℕ) :
    phase ((a:ℝ)/q*n)=phase ((a:ℝ)/q*(n%q:ℕ)) := by
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hn : (n:ℝ)=(n%q:ℕ)+(q:ℝ)*(n/q:ℕ) := by exact_mod_cast (Nat.mod_add_div n q).symm
  have he : (a:ℝ)/q*n=(a:ℝ)/q*(n%q:ℕ)+(a:ℝ)*(n/q:ℕ) := by
    calc
      _ = (a:ℝ)/q*((n%q:ℕ)+(q:ℝ)*(n/q:ℕ)) := congrArg (fun z : ℝ=>(a:ℝ)/q*z) hn
      _ = _ := by field_simp
  rw [he,phase_add]
  have hi : (a:ℝ)*(n/q:ℕ)=((a*(n/q:ℕ):ℤ):ℝ) := by push_cast; rfl
  rw [hi,phase_int,mul_one]

theorem rational_windowSmall {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (a : ℤ) {q : ℕ} (hq : 0 < q) :
    WindowSmall (fun n=>f n*phase ((a:ℝ)/q*n)) := by
  have hs := periodic_windowSmall hf hm hNP hq (fun b=>phase ((a:ℝ)/q*b))
  apply windowSmall_congr_pos _ hs
  intro n hn
  rw [phase_rational_mod a hq n]

lemma phase_inside_window {D x u α β : ℝ} (hu : x-u ∈ Set.Ioc 0 D) :
    ‖phase (α*u)-phase ((α-β)*x)*phase (β*u)‖ ≤ 2*Real.pi*|α-β| *D := by
  rw [← phase_add]
  have he : α*u-((α-β)*x+β*u)=(α-β)*(u-x) := by ring
  have hb : |u-x| ≤ D := by rw [abs_sub_comm,abs_of_pos hu.1]; exact hu.2
  have hh := phase_sub_le (α*u) ((α-β)*x+β*u)
  rw [he,abs_mul] at hh
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*Real.pi*|α-β|)])

lemma sharp_phase_pointwise {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {D : ℝ} (hD : 0 ≤ D) (α β x : ℝ) :
    ‖sharpWindow s (fun n=>a n*phase (α*u n)) u D x‖ ≤
      ‖sharpWindow s (fun n=>a n*phase (β*u n)) u D x‖+
        (2*Real.pi*|α-β| *D)*(∑n∈s,‖a n‖*box D (x-u n)) := by
  let A := sharpWindow s (fun n=>a n*phase (α*u n)) u D x
  let B := phase ((α-β)*x)*sharpWindow s (fun n=>a n*phase (β*u n)) u D x
  have hB : ‖B‖=‖sharpWindow s (fun n=>a n*phase (β*u n)) u D x‖ := by
    dsimp only [B]; rw [norm_mul,norm_phase,one_mul]
  have he : A-B=∑n∈s,a n*(phase (α*u n)-phase ((α-β)*x)*phase (β*u n))*(box D (x-u n):ℂ) := by
    dsimp only [A,B,sharpWindow]
    rw [mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    ring
  have herr : ‖A-B‖ ≤ (2*Real.pi*|α-β| *D)*(∑n∈s,‖a n‖*box D (x-u n)) := by
    rw [he,mul_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    by_cases hh : x-u n ∈ Set.Ioc 0 D
    · rw [OrdinarySharpWindow.box,Set.indicator_of_mem hh,Complex.ofReal_one,mul_one,mul_one,norm_mul]
      rw [mul_comm ‖a n‖]
      exact mul_le_mul (phase_inside_window (α:=α) (β:=β) hh) le_rfl
        (norm_nonneg (a n)) (mul_nonneg (by positivity) hD)
    · simp only [OrdinarySharpWindow.box,Set.indicator_of_notMem hh,Complex.ofReal_zero,mul_zero,norm_zero,le_refl]
  have htri := norm_sub_le A B
  have ht : ‖A‖ ≤ ‖B‖+‖A-B‖ := by
    have h := norm_add_le B (A-B)
    have heq : B+(A-B)=A := by abel
    rw [heq] at h
    exact h
  exact ht.trans (by rw [hB]; exact _root_.add_le_add le_rfl herr)

lemma sharp_phase_l1 {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {D : ℝ} (hD : 0 ≤ D) (α β : ℝ) :
    (∫x : ℝ,‖sharpWindow s (fun n=>a n*phase (α*u n)) u D x‖) ≤
      (∫x : ℝ,‖sharpWindow s (fun n=>a n*phase (β*u n)) u D x‖)+
        2*Real.pi*|α-β| *D^2*(∑n∈s,‖a n‖) := by
  have hi (n : ι) : Integrable (fun x : ℝ=>‖a n‖*box D (x-u n)) :=
    ((box_integrable D).comp_sub_right (u n)).const_mul _
  have hs := integrable_finsetSum s (fun n hn=>hi n)
  have ha := (sharpWindow_integrable s (fun n=>a n*phase (α*u n)) u D).norm
  have hb := (sharpWindow_integrable s (fun n=>a n*phase (β*u n)) u D).norm
  calc
    _ ≤ ∫x : ℝ,‖sharpWindow s (fun n=>a n*phase (β*u n)) u D x‖+
        (2*Real.pi*|α-β| *D)*(∑n∈s,‖a n‖*box D (x-u n)) :=
      integral_mono ha (hb.add (hs.const_mul _)) (sharp_phase_pointwise s a u hD α β)
    _ = _ := by
      rw [integral_add hb (hs.const_mul _),MeasureTheory.integral_const_mul,integral_finsetSum s (fun n hn=>hi n)]
      have he (n : ι) : (∫x : ℝ,‖a n‖*box D (x-u n))=‖a n‖*D := by
        rw [MeasureTheory.integral_const_mul,integral_sub_right_eq_self,box_integral hD]
      simp_rw [he]
      rw [← sum_mul]
      ring

end OrdinaryLocalAdditive

end

end OAI
