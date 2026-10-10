import Mathlib

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

namespace OrdinaryUniformWidth
open Filter

def ExpBound (b : ℕ) (F : ℕ→ℝ) : Prop := ∃ c : ℕ, ∀m, F m≤(2:ℝ)^(b*m+c)
def WideBound (b : ℕ) (F : ℕ→ℝ) : Prop := ∃ c : ℕ, ∀m, F m≤(2:ℝ)^(2^(b*m+c):ℕ)

lemma ExpBound.mono {b : ℕ} {F G : ℕ→ℝ} (h : ExpBound b F)
    (hFG : ∀m,G m≤F m) : ExpBound b G := by
  obtain ⟨c,hc⟩ := h
  exact ⟨c,fun m=>(hFG m).trans (hc m)⟩

lemma WideBound.mono {b : ℕ} {F G : ℕ→ℝ} (h : WideBound b F)
    (hFG : ∀m,G m≤F m) : WideBound b G := by
  obtain ⟨c,hc⟩ := h
  exact ⟨c,fun m=>(hFG m).trans (hc m)⟩

lemma ExpBound.weaken {b d : ℕ} {F : ℕ→ℝ} (h : ExpBound b F) (hbd : b≤d) : ExpBound d F := by
  obtain ⟨c,hc⟩ := h
  refine ⟨c,fun m=>(hc m).trans ?_⟩
  exact pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (Nat.mul_le_mul_right m hbd) c)

lemma WideBound.weaken {b d : ℕ} {F : ℕ→ℝ} (h : WideBound b F) (hbd : b≤d) : WideBound d F := by
  obtain ⟨c,hc⟩ := h
  refine ⟨c,fun m=>(hc m).trans ?_⟩
  apply pow_le_pow_right₀ (by norm_num)
  exact Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_right m hbd) c)

lemma expBound_const (b : ℕ) (C : ℝ) : ExpBound b (fun _=>C) := by
  obtain ⟨c,hc⟩ := exists_nat_ge C
  refine ⟨c,fun m=>hc.trans ?_⟩
  have he : (c:ℝ)≤(2:ℝ)^c := by exact_mod_cast (Nat.lt_two_pow_self (n := c)).le
  exact he.trans (pow_le_pow_right₀ (by norm_num) (by omega))

lemma expBound_id : ExpBound 1 (fun m=>(m:ℝ)) := by
  refine ⟨0,?_⟩
  intro m
  simpa only [one_mul,add_zero,Nat.cast_pow,Nat.cast_ofNat] using
    (show (m:ℝ)≤((2^m:ℕ):ℝ) by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le)

lemma ExpBound.add {b : ℕ} {F G : ℕ→ℝ} (hF : ExpBound b F) (hG : ExpBound b G) :
    ExpBound b (fun m=>F m+G m) := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨d,hd⟩ := hG
  refine ⟨c+d+1,?_⟩
  intro m
  have h1 := (hc m).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : b*m+c≤b*m+(c+d)))
  have h2 := (hd m).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : b*m+d≤b*m+(c+d)))
  have he : b*m+(c+d+1)=(b*m+(c+d))+1 := by omega
  rw [he,pow_succ]
  linarith only [h1,h2]

lemma ExpBound.mul {b d : ℕ} {F G : ℕ→ℝ} (hF : ExpBound b F) (hG : ExpBound d G)
    (hG0 : ∀m,0≤G m) : ExpBound (b+d) (fun m=>F m*G m) := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨e,he⟩ := hG
  refine ⟨c+e,?_⟩
  intro m
  have hh := mul_le_mul (hc m) (he m) (hG0 m) (by positivity)
  rw [←pow_add] at hh
  convert hh using 1
  congr 1
  ring

lemma ExpBound.toWide {b : ℕ} {F : ℕ→ℝ} (hF : ExpBound b F) : WideBound b F := by
  obtain ⟨c,hc⟩ := hF
  exact ⟨c,fun m=>(hc m).trans (pow_le_pow_right₀ (by norm_num) ((Nat.lt_two_pow_self (n := _)).le))⟩

lemma wideBound_const (b : ℕ) (C : ℝ) : WideBound b (fun _=>C) := (expBound_const b C).toWide

lemma WideBound.mul {b : ℕ} {F G : ℕ→ℝ} (hF : WideBound b F) (hG : WideBound b G)
    (hG0 : ∀m,0≤G m) : WideBound b (fun m=>F m*G m) := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨d,hd⟩ := hG
  refine ⟨c+d+1,?_⟩
  intro m
  have h1 := (hc m).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
    (Nat.pow_le_pow_right (by omega) (by omega : b*m+c≤b*m+(c+d))))
  have h2 := (hd m).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
    (Nat.pow_le_pow_right (by omega) (by omega : b*m+d≤b*m+(c+d))))
  have hh := mul_le_mul h1 h2 (hG0 m) (by positivity)
  rw [←pow_add] at hh
  change F m*G m≤_
  apply hh.trans_eq
  congr 1
  rw [show b*m+(c+d+1)=b*m+(c+d)+1 by omega,pow_succ]
  omega

lemma WideBound.add {b : ℕ} {F G : ℕ→ℝ} (hF : WideBound b F) (hG : WideBound b G) :
    WideBound b (fun m=>F m+G m) := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨d,hd⟩ := hG
  refine ⟨c+d+1,?_⟩
  intro m
  let e := b*m+(c+d)
  have h1 := (hc m).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
    (Nat.pow_le_pow_right (by omega) (by dsimp [e];omega : b*m+c≤e)))
  have h2 := (hd m).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
    (Nat.pow_le_pow_right (by omega) (by dsimp [e];omega : b*m+d≤e)))
  have he0 : 1≤(2:ℕ)^e := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤(2:ℝ)^(2^e:ℕ)+(2:ℝ)^(2^e:ℕ) := add_le_add h1 h2
    _ =(2:ℝ)^(2^e+1:ℕ) := by rw [pow_succ];ring
    _ ≤(2:ℝ)^(2*2^e:ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = _ := by congr 1;rw [show b*m+(c+d+1)=e+1 by dsimp [e];omega,pow_succ];omega

lemma WideBound.ceil {b : ℕ} {F : ℕ→ℝ} (hF : WideBound b F) :
    WideBound b (fun m=>(Nat.ceil (F m):ℝ)) := by
  obtain ⟨c,hc⟩ := hF
  refine ⟨c,?_⟩
  intro m
  have hh : Nat.ceil (F m)≤2^(2^(b*m+c)) := Nat.ceil_le.mpr (by exact_mod_cast hc m)
  change (Nat.ceil (F m):ℝ)≤_
  exact_mod_cast hh

lemma ExpBound.pow_two {b : ℕ} {F : ℕ→ℕ} (hF : ExpBound b (fun m=>(F m:ℝ))) :
    WideBound b (fun m=>(2:ℝ)^(F m)) := by
  obtain ⟨c,hc⟩ := hF
  refine ⟨c,?_⟩
  intro m
  apply pow_le_pow_right₀ (by norm_num)
  have hh := hc m
  dsimp only at hh
  exact_mod_cast hh

end OrdinaryUniformWidth

end

end OAI
