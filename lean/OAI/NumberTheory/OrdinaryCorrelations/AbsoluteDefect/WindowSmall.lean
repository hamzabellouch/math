import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FrozenBandBound

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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinarySharpWindow Finset Filter MeasureTheory

def WindowSmall (a : ℕ→ℂ) : Prop :=
  ∀ε : ℝ,0 < ε → ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
    (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) a (fun n=>(n:ℝ)) D x‖) < ε*D*X

lemma windowSmall_of_nonpretentious {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f) : WindowSmall f := by
  intro ε hε
  have he : characterModulation f (1:DirichletCharacter ℂ 1)=f := by
    funext n
    have hn : (n:ZMod 1)=1 := Subsingleton.elim _ _
    simp [characterModulation,hn]
  simpa only [he] using dyadic_character_fixed_window_small hf hm hNP
    (by decide : 0 < (1:ℕ)) (1:DirichletCharacter ℂ 1) hε

lemma windowSmall_congr_pos {a b : ℕ→ℂ} (h : ∀n : ℕ,0 < n → a n=b n)
    (ha : WindowSmall a) : WindowSmall b := by
  intro ε hε
  obtain ⟨D0,hD0,hL⟩ := ha ε hε
  refine ⟨D0,hD0,?_⟩
  intro D hD
  filter_upwards [hL D hD] with X hLX
  convert hLX using 1
  congr 1
  funext x
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [h n (lt_of_le_of_lt (Nat.zero_le X) (mem_Ioc.mp hn).1)]

lemma windowSmall_zero : WindowSmall (fun _ : ℕ=>(0:ℂ)) := by
  intro ε hε
  refine ⟨1,by decide,?_⟩
  intro D hD
  filter_upwards [eventually_ge_atTop (1:ℕ)] with X hX
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one (by simpa using hD)
  have hXp : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  simp only [sharpWindow,zero_mul,sum_const_zero,norm_zero,integral_zero]
  positivity

lemma sharpWindow_add {ι : Type*} (s : Finset ι) (a b : ι→ℂ) (u : ι→ℝ) (D x : ℝ) :
    sharpWindow s (fun n=>a n+b n) u D x=sharpWindow s a u D x+sharpWindow s b u D x := by
  simp only [sharpWindow,add_mul,sum_add_distrib]
lemma sharpWindow_const_mul {ι : Type*} (s : Finset ι) (c : ℂ) (a : ι→ℂ) (u : ι→ℝ) (D x : ℝ) :
    sharpWindow s (fun n=>c*a n) u D x=c*sharpWindow s a u D x := by
  simp only [sharpWindow,mul_sum,mul_assoc]

lemma sharpWindow_add_l1 {ι : Type*} (s : Finset ι) (a b : ι→ℂ) (u : ι→ℝ) (D : ℝ) :
    (∫x : ℝ,‖sharpWindow s (fun n=>a n+b n) u D x‖) ≤
      (∫x : ℝ,‖sharpWindow s a u D x‖)+(∫x : ℝ,‖sharpWindow s b u D x‖) := by
  rw [← integral_add (sharpWindow_integrable s a u D).norm (sharpWindow_integrable s b u D).norm]
  apply integral_mono (sharpWindow_integrable s _ u D).norm
    ((sharpWindow_integrable s a u D).norm.add (sharpWindow_integrable s b u D).norm)
  intro x
  dsimp only
  rw [sharpWindow_add]
  exact norm_add_le _ _

lemma windowSmall_add {a b : ℕ→ℂ} (ha : WindowSmall a) (hb : WindowSmall b) :
    WindowSmall (fun n=>a n+b n) := by
  intro ε hε
  obtain ⟨A,hA,hLA⟩ := ha (ε/2) (by positivity)
  obtain ⟨B,hB,hLB⟩ := hb (ε/2) (by positivity)
  refine ⟨max A B,lt_max_of_lt_left hA,?_⟩
  intro D hD
  have hAD : (A:ℝ) ≤ D := (by exact_mod_cast le_max_left A B : (A:ℝ) ≤ max A B).trans hD
  have hBD : (B:ℝ) ≤ D := (by exact_mod_cast le_max_right A B : (B:ℝ) ≤ max A B).trans hD
  filter_upwards [hLA D hAD,hLB D hBD] with X hAX hBX
  have hh := sharpWindow_add_l1 (Ioc X (2*X)) a b (fun n=>(n:ℝ)) D
  linarith only [hh,hAX,hBX]

lemma windowSmall_const_mul (c : ℂ) {a : ℕ→ℂ} (ha : WindowSmall a) :
    WindowSmall (fun n=>c*a n) := by
  intro ε hε
  let C : ℝ := ‖c‖+1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨D0,hD0,hL⟩ := ha (ε/C) (div_pos hε hC)
  refine ⟨D0,hD0,?_⟩
  intro D hD
  have hDp : 0 < D := (by exact_mod_cast hD0 : (0:ℝ) < D0).trans_le hD
  filter_upwards [hL D hD,eventually_ge_atTop (1:ℕ)] with X hLX hXp
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  simp_rw [sharpWindow_const_mul,norm_mul]
  rw [MeasureTheory.integral_const_mul]
  have hI : 0 ≤ ∫x : ℝ,‖sharpWindow (Ioc X (2*X)) a (fun n=>(n:ℝ)) D x‖ := integral_nonneg (fun x=>norm_nonneg _)
  have hh := mul_lt_mul_of_pos_left hLX hC
  have he : C*(ε/C*D*X)=ε*D*X := by field_simp
  rw [he] at hh
  have hb : ‖c‖*(∫x : ℝ,‖sharpWindow (Ioc X (2*X)) a (fun n=>(n:ℝ)) D x‖) ≤
      C*(∫x : ℝ,‖sharpWindow (Ioc X (2*X)) a (fun n=>(n:ℝ)) D x‖) := by
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hI
  exact hb.trans_lt hh

lemma windowSmall_finsetSum {ι : Type*} (s : Finset ι) (a : ι→ℕ→ℂ)
    (ha : ∀i∈s,WindowSmall (a i)) : WindowSmall (fun n=>∑i∈s,a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using windowSmall_zero
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact windowSmall_add (ha i (mem_insert_self i s)) (ih (fun j hj=>ha j (mem_insert_of_mem hj)))

end OrdinaryChainScales

end

end OAI
