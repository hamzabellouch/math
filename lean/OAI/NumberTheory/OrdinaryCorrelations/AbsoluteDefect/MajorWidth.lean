import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.QuadraticGeometricLimit
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpLogGate
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ExpBound
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeStart

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
open OrdinaryMellinModulus OrdinaryGaussianWindow OrdinarySharpWindow

def majorWidth (A c k v m : ℕ) : ℝ := 2*sharpLogGate A c k (30*m+v)
def primeEnd (t m : ℕ) : ℕ := 2^(primeStart m+primeSpan t m)
def approxBound (A c k v t m : ℕ) : ℕ :=
  1+2*primeEnd t m+Nat.ceil (2*Real.pi*majorWidth A c k v m*(2:ℝ)^(2*m))
def shortWidth (A c k v t m : ℕ) : ℕ :=
  1+Nat.ceil ((2:ℝ)^(2*m)*majorWidth A c k v m)+
    Nat.ceil (8*(approxBound A c k v t m:ℝ)*primeEnd t m*
      (primeSpan t m+1:ℕ)^2*(2:ℝ)^(4*m))
def longGate (A c k v t m : ℕ) : ℝ := (2:ℝ)^(2*m)*shortWidth A c k v t m

lemma majorWidth_pos (A c k v m : ℕ) : 0 < majorWidth A c k v m :=
  mul_pos (by norm_num) (sharpLogGate_pos _ _ _ _)
lemma primeEnd_pos (t m : ℕ) : 0<primeEnd t m := by unfold primeEnd;positivity
lemma approxBound_pos (A c k v t m : ℕ) : 0<approxBound A c k v t m := by unfold approxBound;omega
lemma shortWidth_pos (A c k v t m : ℕ) : 0<shortWidth A c k v t m := by unfold shortWidth;omega

lemma expBound_affine (a c : ℝ) : ExpBound 1 (fun m=>a*(m:ℝ)+c) := by
  have hp := (expBound_const 0 a).mul expBound_id (fun m=>Nat.cast_nonneg m)
  exact hp.add (expBound_const 1 c)

lemma pow_wide (b c : ℕ) : WideBound b (fun m=>(2:ℝ)^(2^(b*m+c):ℕ)) := ⟨c,fun _=>le_rfl⟩

lemma majorWidth_wide (A c k v : ℕ) : WideBound 1740 (majorWidth A c k v) := by
  let C : ℝ := 2*16*8*(bumpMoment+1)/bumpMass
  have hP : ExpBound 1 (fun m=>((2*(30*m+v+k)+2+c+1:ℕ):ℝ)) := by
    have hh := expBound_affine 60 (2*((v:ℝ)+k)+2+c+1)
    convert hh using 1
    funext m
    push_cast
    ring
  have hE : WideBound 1740 (fun m=>(2:ℝ)^(2^(29*(2*(30*m+v+k)+2+3)+A):ℕ)) := by
    have hh := pow_wide 1740 (29*(2*(v+k)+5)+A)
    convert hh using 1
    funext m
    congr 2
    ring
  have hB : ExpBound 30 (fun m=>(2:ℝ)^(30*m+v)) := ⟨v,fun _=>le_rfl⟩
  have hh := (((wideBound_const 1740 C).mul (hP.toWide.weaken (by omega))
    (fun m=>by positivity)).mul hE (fun m=>by positivity)).mul
      (hB.toWide.weaken (by omega)) (fun m=>by positivity)
  apply hh.mono
  intro m
  apply le_of_eq
  unfold majorWidth sharpLogGate
  push_cast
  have hpow : (1/2:ℝ)^(30*m+v)=((2:ℝ)^(30*m+v))⁻¹ := by simp [inv_pow]
  rw [hpow]
  dsimp [C]
  field_simp

lemma primeEnd_wide (t : ℕ) : WideBound 3 (fun m=>(primeEnd t m:ℝ)) := by
  have hr : ExpBound 1 (fun m=>(primeStart m:ℝ)) := by
    simpa only [primeStart,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using expBound_affine 8 2
  have hp : ExpBound 2 (fun m=>(2:ℝ)^(2*m+t)) := ⟨t,fun _=>le_rfl⟩
  have hh := hr.mul hp (fun m=>by positivity)
  have he : ExpBound 3 (fun m=>((primeStart m+primeSpan t m:ℕ):ℝ)) := by
    simpa only [prime_extent,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh
  simpa only [primeEnd,Nat.cast_pow,Nat.cast_ofNat] using he.pow_two

lemma primeSpan_wide (t : ℕ) : WideBound 3 (fun m=>(primeSpan t m:ℝ)) := by
  have he := primeEnd_wide t
  apply he.mono
  intro m
  have hh : primeSpan t m≤2^(primeStart m+primeSpan t m) :=
    (Nat.le_add_left _ _).trans (Nat.lt_two_pow_self (n := _)).le
  exact_mod_cast hh

lemma approxBound_wide (A c k v t : ℕ) : WideBound 1740 (fun m=>(approxBound A c k v t m:ℝ)) := by
  have hK := (primeEnd_wide t).weaken (by norm_num : 3≤(1740:ℕ))
  have h2K := (wideBound_const 1740 2).mul hK (fun m=>Nat.cast_nonneg _)
  have hH := majorWidth_wide A c k v
  have hpow : WideBound 1740 (fun m=>(2:ℝ)^(2*m)) :=
    (show ExpBound 2 (fun m=>(2:ℝ)^(2*m)) from ⟨0,by intro m;simp⟩).toWide.weaken (by norm_num)
  have hN := (((wideBound_const 1740 (2*Real.pi)).mul hH (fun m=>(majorWidth_pos _ _ _ _ _).le)).mul hpow (fun m=>by positivity)).ceil
  have hh := ((wideBound_const 1740 1).add h2K).add hN
  simpa only [approxBound,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hh

lemma shortWidth_wide (A c k v t : ℕ) : WideBound 1740 (fun m=>(shortWidth A c k v t m:ℝ)) := by
  have hN := approxBound_wide A c k v t
  have hK := (primeEnd_wide t).weaken (by norm_num : 3≤(1740:ℕ))
  have hR := (primeSpan_wide t).weaken (by norm_num : 3≤(1740:ℕ))
  have hR1 := hR.add (wideBound_const 1740 1)
  have hR2 := hR1.mul hR1 (fun m=>by positivity)
  have hH := majorWidth_wide A c k v
  have hp2 : WideBound 1740 (fun m=>(2:ℝ)^(2*m)) :=
    (show ExpBound 2 (fun m=>(2:ℝ)^(2*m)) from ⟨0,by intro m;simp⟩).toWide.weaken (by norm_num)
  have hp4 : WideBound 1740 (fun m=>(2:ℝ)^(4*m)) :=
    (show ExpBound 4 (fun m=>(2:ℝ)^(4*m)) from ⟨0,by intro m;simp⟩).toWide.weaken (by norm_num)
  have hterm := (((((wideBound_const 1740 8).mul hN (fun m=>Nat.cast_nonneg _)).mul hK (fun m=>Nat.cast_nonneg _)).mul hR2 (fun m=>by positivity)).mul hp4 (fun m=>by positivity)).ceil
  have hfirst := (hp2.mul hH (fun m=>(majorWidth_pos _ _ _ _ _).le)).ceil
  have hh := ((wideBound_const 1740 1).add hfirst).add hterm
  simpa only [shortWidth,Nat.cast_add,Nat.cast_one,pow_two] using hh

lemma longGate_wide (A c k v t : ℕ) : WideBound 1800 (longGate A c k v t) := by
  have hs := shortWidth_wide A c k v t
  have hp2 : WideBound 1740 (fun m=>(2:ℝ)^(2*m)) :=
    (show ExpBound 2 (fun m=>(2:ℝ)^(2*m)) from ⟨0,by intro m;simp⟩).toWide.weaken (by norm_num)
  exact (hp2.mul hs (fun m=>Nat.cast_nonneg _)).weaken (by norm_num)

end OrdinaryUniformWidth

end

end OAI
