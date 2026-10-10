import Mathlib
import OAI.Probability.Contingency.DenseWeightBounds

namespace OAI

/-! Dense Dyadic. -/

noncomputable section


open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid Contingency.FiniteChain
variable {a c q K : ℕ} (D : BinProblem a c q K)
attribute [local instance] tableFintype tableNonempty
local instance : DecidableRel (@Adj q K) := Classical.decRel _

def exponent (v : Vertex q K) : ℕ :=
  (⌊binExponent D.e (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths D.d (realCorner v)⌋:ℤ).toNat

theorem floor_nonneg (v : Vertex q K) :
    0≤(⌊binExponent D.e (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths D.d (realCorner v)⌋:ℤ) := by
  exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) (penalty_nonneg _ _ _ _ _ _))

theorem weight_exponent (v : Vertex q K) : D.weight v=1/(2:ℝ)^D.exponent v := by
  change (2:ℝ)^(-(⌊binExponent D.e _ _ D.widths D.d (realCorner v)⌋:ℝ))=_
  rw [← Int.toNat_of_nonneg (D.floor_nonneg v)]
  simp only [Int.cast_natCast,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,one_div,exponent]

theorem exponent_bound (d : ℕ) (hD : D.d=d) (hK : (K:ℝ)=4*D.d^8) (v : Vertex q K) :
    D.exponent v≤8*d^5 := by
  apply Int.toNat_le.mpr
  have hh := Int.floor_le (binExponent D.e (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths D.d (realCorner v))
  have hb := mul_le_mul_of_nonneg_left (D.corner_penalty_bound hK v) (show 0≤D.d^4 by positivity)
  have hle : (⌊binExponent D.e (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths D.d (realCorner v)⌋:ℝ)≤8*(d:ℝ)^5 := by
    unfold binExponent at hh ⊢
    rw [hD] at hh hb ⊢
    nlinarith only [hh,hb,show 0≤(d:ℝ)^5 by positivity]
  exact_mod_cast hle

theorem neighbor_bound (d : ℕ) (hD : D.d=d) (v : Vertex q K) :
    (Finset.univ.filter (Adj v)).card≤2^Nat.clog 2 (8*d) := by
  classical
  have he : (Finset.univ.filter (Adj v)).card=Nat.card {w : Vertex q K // Adj v w} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [he]
  have hq : q≤d := by
    have hq' := D.hq
    rw [hD] at hq'
    exact_mod_cast hq'
  exact (neighbor_card v).trans ((by omega : 2*q≤8*d).trans (Nat.le_pow_clog (by norm_num) (8*d)))

def bitKernel (d : ℕ) (hD : D.d=d) (v : Vertex q K) : DyadicLaw (Vertex q K) := by
  classical
  exact (DyadicLaw.neighborProposal Adj v (Nat.clog 2 (8*d)) (adj_irrefl v) (D.neighbor_bound d hD v)).accept D.exponent (8*d^5) v

theorem bitKernel_bits (d : ℕ) (hD : D.d=d) (v : Vertex q K) :
    (D.bitKernel d hD v).bits=Nat.clog 2 (8*d)+8*d^5 := rfl

theorem bitKernel_law (d : ℕ) (hD : D.d=d) (hK : (K:ℝ)=4*D.d^8)
    (hp0 : 0≤proposalRate (8*d)) (hp : proposalRate (8*d)≤1/(8*D.d)) (v : Vertex q K) :
    (D.bitKernel d hD v).toLaw=(D.chain (proposalRate (8*d)) hp0 hp).transition v := by
  classical
  apply DyadicLaw.accepted_neighbor_kernel Adj D.exponent (8*d^5) (Nat.clog 2 (8*d)) (D.exponent_bound d hD hK) v
  intro w hvw
  change (if v=w then _ else _) = _
  rw [ite_eq_right hvw]
  change proposalRate (8*d)*edgeWeight D.weight v w/D.weight v=_
  simp only [edgeWeight,D.weight_exponent,proposalRate]

def bitOffsets (h d : ℕ) : DyadicLaw (Offsets D.w) :=
  DyadicLaw.pi (fun i => offsetLaw (D.w i) (D.hw i) (Nat.clog 2 (D.w i+1)+4*(h+d)))

theorem bitOffsets_law (h d : ℕ) : (D.bitOffsets h d).toLaw=D.implementedOffsets h d := by
  exact DyadicLaw.toLaw_pi _

def bitTrial (h d : ℕ) (hD : D.d=d) (t : ℕ) : DyadicLaw (Option (Tables D.R D.P)) := by
  classical
  let walk := DyadicLaw.walk (D.bitKernel d hD) (Nat.clog 2 (8*d)+8*d^5) (D.bitKernel_bits d hD) (fun _ => ⟨0,D.Kpos⟩) t
  exact (walk.bind (fun v => (D.bitOffsets h d).map (fun β => (v,β))) (D.bitOffsets h d).bits
    (fun _ => DyadicLaw.map_bits _ _)).map D.decode

theorem bitTrial_law (h d : ℕ) (hD : D.d=d) (hK : (K:ℝ)=4*D.d^8)
    (hp0 : 0≤proposalRate (8*d)) (hp : proposalRate (8*d)≤1/(8*D.d)) (t : ℕ) :
    (D.bitTrial h d hD t).toLaw=D.implementedTrial (proposalRate (8*d)) hp0 hp h d t := by
  classical
  have hw : (DyadicLaw.walk (D.bitKernel d hD) (Nat.clog 2 (8*d)+8*d^5) (D.bitKernel_bits d hD)
      (fun _ => ⟨0,D.Kpos⟩) t).toLaw=(D.chain (proposalRate (8*d)) hp0 hp).walk (fun _ => ⟨0,D.Kpos⟩) t := by
    induction t with
    | zero => exact DyadicLaw.toLaw_pure _ _
    | succ t ih =>
      simp only [DyadicLaw.walk,DyadicLaw.toLaw_bind,Chain.walk]
      rw [ih]
      congr 1
      funext x
      exact D.bitKernel_law d hD hK hp0 hp x
  simp only [bitTrial,DyadicLaw.toLaw_map,DyadicLaw.toLaw_bind,D.bitOffsets_law]
  rw [hw]
  congr 1
  apply Law.ext; funext s
  rcases s with ⟨v,β⟩
  simp only [Law.bind,Law.map,Law.pure,Law.prod]
  simp [Prod.mk.injEq,ite_and,Finset.sum_ite_irrel,mul_ite]

def bitDraw (h d : ℕ) (hD : D.d=d) (fallback : Tables D.R D.P) : DyadicLaw (Tables D.R D.P) := by
  classical
  exact stoppedLaw (D.bitTrial h d hD (d^50*(h+1)^2)) fallback (d^4*(h+1))

theorem bitDraw_tv (d : ℕ) (hd : 14≤d) (hD : D.d=d) (hK : (K:ℝ)=4*D.d^8)
    (h : ℕ) (hh : 1≤h) (fallback : Tables D.R D.P) :
    (D.bitDraw h d hD fallback).toLaw.tv (Law.uniform (Tables D.R D.P))≤(2:ℝ)^(-(h:ℤ)) := by
  classical
  have hb := binProposal_bounds d (by omega)
  have hp : proposalRate (8*d)≤1/(8*D.d) := by simpa only [hD] using hb.2
  have hp0 : 0≤proposalRate (8*d) := by unfold proposalRate; positivity
  rw [bitDraw,stoppedLaw_toLaw,D.bitTrial_law h d hD hK hp0 hp]
  exact D.draw_tv d hd hD hK _ hp0 hp (by simpa only [hD] using hb.1) h hh fallback

end
end Contingency.Dense.BinProblem

 

 

namespace Contingency
namespace Schedule
 
def h (d b k : ℕ) := d^4*(k+b)^2
def T (d b k : ℕ) := d^200*(k+b)^2
def Jo (d k : ℕ) := d^4*(k+1)
def Q (d : ℕ) := Nat.clog 2 (8*d)+8*d^5
def qs (d : ℕ) := Nat.clog 2 (32*d^2)
def rmax (d b k : ℕ) := b+1+4*(h d b k+d)
def H (d b k : ℕ) := d^50*(h d b k+1)^2
def JD (d b k : ℕ) := d^4*(h d b k+1)
def R1 (d b k : ℕ) := H d b k*Q d+d*rmax d b k
def RD (d b k : ℕ) := JD d b k*R1 d b k
def RT (d b k : ℕ) := T d b k*(RD d b k+qs d)+RD d b k
def R (d b k : ℕ) := Jo d k*RT d b k

theorem clog_self_bound (x : ℕ) : Nat.clog 2 x≤x :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=x)).le

theorem qs_bound (d : ℕ) : qs d≤2*d+5 := by
  apply Nat.clog_le_of_le_pow
  calc
    32*d^2 ≤ 32*(2^d)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=d)).le 2)
    _ = 2^(2*d+5) := by rw [← pow_mul,Nat.mul_comm d 2,pow_add]; norm_num; ring

 

theorem bounds (d b k : ℕ) (hd : 14≤d) (hb : d≤b) (hk : 1≤k) :
    let q := d+b+k+2
    h d b k≤q^6 ∧ h d b k+1≤q^7 ∧ Q d≤q^6 ∧ rmax d b k≤q^7 ∧
    H d b k≤q^64 ∧ R1 d b k≤q^71 ∧ RD d b k≤q^82 ∧
    RT d b k≤q^285 ∧ R d b k≤q^290 ∧ R d b k≤q^300 := by
  dsimp only
  set q := d+b+k+2
  have hq : 31≤q := by dsimp [q]; omega
  have hq0 : 0<q := by omega
  have hdq : d≤q := by dsimp [q]; omega
  have hbq : b+1≤q := by dsimp [q]; omega
  have hkq : k+1≤q := by dsimp [q]; omega
  have htq : k+b≤q := by dsimp [q]; omega
  have hp (a b : ℕ) (hab : a≤b) : q^a≤q^b := Nat.pow_le_pow_right hq0 hab
  have hq6 : q≤q^6 := by simpa using hp 1 6 (by omega)
  have hh : h d b k≤q^6 := by
    calc
      _ ≤ q^4*q^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hdq _) (Nat.pow_le_pow_left htq _)
      _ = _ := by rw [← pow_add]
  have hh1 : h d b k+1≤q^7 := by
    calc
      _ ≤ q^6+q^6 := Nat.add_le_add hh (le_trans (by omega) hq6)
      _ = 2*q^6 := by omega
      _ ≤ q*q^6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' q 6).symm
  have hQ : Q d≤q^6 := by
    have hlog := clog_self_bound (8*d)
    calc
      _ ≤ 8*q+8*q^5 := Nat.add_le_add (hlog.trans (Nat.mul_le_mul_left _ hdq)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdq _))
      _ ≤ 16*q^5 := by have hh := Nat.mul_le_mul_left 8 (show q≤q^5 by simpa using hp 1 5 (by omega)); omega
      _ ≤ q*q^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' q 5).symm
  have hr : rmax d b k≤q^7 := by
    calc
      _ ≤ q^6+4*(q^6+q^6) := Nat.add_le_add (hbq.trans hq6) (Nat.mul_le_mul_left _ (Nat.add_le_add hh (hdq.trans hq6)))
      _ = 9*q^6 := by omega
      _ ≤ q*q^6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' q 6).symm
  have hH : H d b k≤q^64 := by
    calc
      _ ≤ q^50*(q^7)^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hdq _) (Nat.pow_le_pow_left hh1 _)
      _ = _ := by rw [← pow_mul,← pow_add]
  have hR1 : R1 d b k≤q^71 := by
    calc
      _ ≤ q^64*q^6+q*q^7 := Nat.add_le_add (Nat.mul_le_mul hH hQ) (Nat.mul_le_mul hdq hr)
      _ = q^70+q^8 := by rw [← pow_add,← pow_succ']
      _ ≤ q^70+q^70 := Nat.add_le_add_left (hp 8 70 (by omega)) _
      _ = 2*q^70 := by omega
      _ ≤ q*q^70 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' q 70).symm
  have hRD : RD d b k≤q^82 := by
    calc
      _ ≤ (q^4*q^7)*q^71 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hdq _) hh1) hR1
      _ = _ := by rw [← pow_add,← pow_add]
  have hqs : qs d≤q^2 := by
    have hh := qs_bound d
    have hmul : 2*q+5≤q^2 := by nlinarith
    omega
  have hT : T d b k≤q^202 := by
    calc
      _ ≤ q^200*q^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hdq _) (Nat.pow_le_pow_left htq _)
      _ = _ := by rw [← pow_add]
  have hRT : RT d b k≤q^285 := by
    calc
      _ ≤ q^202*(q^82+q^82)+q^82 := Nat.add_le_add (Nat.mul_le_mul hT (Nat.add_le_add hRD (hqs.trans (hp 2 82 (by omega))))) hRD
      _ = 2*q^284+q^82 := by
        simp only [Nat.mul_add, ← pow_add, Nat.reduceAdd, two_mul]
      _ ≤ 2*q^284+q^284 := Nat.add_le_add_left (hp 82 284 (by decide)) _
      _ = 3*q^284 := (Nat.succ_mul 2 (q^284)).symm
      _ ≤ q*q^284 := Nat.mul_le_mul_right (q^284) (le_trans (by decide : 3 ≤ 31) hq)
      _ = q^285 := by simpa only [Nat.reduceAdd] using (pow_succ' q 284).symm
  have hR : R d b k≤q^290 := by
    calc
      _ ≤ (q^4*q)*q^285 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hdq _) hkq) hRT
      _ = q^290 := by simp only [← pow_succ, ← pow_add, Nat.reduceAdd]
  exact ⟨hh,hh1,hQ,hr,hH,hR1,hRD,hRT,hR,hR.trans (hp 290 300 (by decide))⟩

end Schedule
end Contingency

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid
variable {a c q K : ℕ} (D : BinProblem a c q K)
attribute [local instance] tableFintype tableNonempty

theorem bitTrial_bits (h d : ℕ) (hD : D.d=d) (t : ℕ) :
    (D.bitTrial h d hD t).bits=t*(Nat.clog 2 (8*d)+8*d^5)+
      ∑ i : Fin q,(Nat.clog 2 (D.w i+1)+4*(h+d)) := by
  classical
  simp only [bitTrial,DyadicLaw.map_bits,DyadicLaw.bind,DyadicLaw.walk_bits,bitOffsets,
    DyadicLaw.pi,offsetLaw,DyadicLaw.map_bits,bitWordLaw]

theorem bitOffsets_bound (d b h : ℕ) (hw : ∀ i,D.w i≤2^b) :
    (∑ i : Fin q,(Nat.clog 2 (D.w i+1)+4*(h+d)))≤q*(b+1+4*(h+d)) := by
  calc
    _ ≤ ∑ _ : Fin q,(b+1+4*(h+d)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Nat.add_le_add_right
      apply Nat.clog_le_of_le_pow
      have hh := hw i
      rw [pow_succ]
      have hp : 1≤2^b := one_le_pow₀ (by omega)
      omega
    _ = _ := by simp

theorem bitTrial_bound (d b k : ℕ) (hD : D.d=d) (hw : ∀ i,D.w i≤2^b) :
    (D.bitTrial (Schedule.h d b k) d hD (Schedule.H d b k)).bits≤Schedule.R1 d b k := by
  rw [D.bitTrial_bits]
  have hq : q≤d := by have hh := D.hq; rw [hD] at hh; exact_mod_cast hh
  exact Nat.add_le_add_left ((D.bitOffsets_bound d b (Schedule.h d b k) hw).trans (Nat.mul_le_mul_right _ hq)) _

theorem bitDraw_bound (d b k : ℕ) (hD : D.d=d) (hw : ∀ i,D.w i≤2^b)
    (fallback : Tables D.R D.P) :
    (D.bitDraw (Schedule.h d b k) d hD fallback).bits≤Schedule.RD d b k := by
  change (D.bitTrial _ _ _ _).bits*Schedule.JD d b k≤_
  rw [Schedule.RD,Nat.mul_comm (Schedule.JD d b k)]
  exact Nat.mul_le_mul_right _ (D.bitTrial_bound d b k hD hw)

 

def reservedDraw (d b k : ℕ) (hD : D.d=d) (hw : ∀ i,D.w i≤2^b)
    (fallback : Tables D.R D.P) : DyadicLaw (Tables D.R D.P) :=
  (D.bitDraw (Schedule.h d b k) d hD fallback).pad (Schedule.RD d b k) (D.bitDraw_bound d b k hD hw fallback)

theorem reservedDraw_bits (d b k : ℕ) (hD : D.d=d) (hw : ∀ i,D.w i≤2^b)
    (fallback : Tables D.R D.P) : (D.reservedDraw d b k hD hw fallback).bits=Schedule.RD d b k := rfl

theorem reservedDraw_tv (d b k : ℕ) (hd : 14≤d) (hk : 1≤k)
    (hD : D.d=d) (hK : (K:ℝ)=4*D.d^8) (hw : ∀ i,D.w i≤2^b)
    (fallback : Tables D.R D.P) :
    (D.reservedDraw d b k hD hw fallback).toLaw.tv (Law.uniform (Tables D.R D.P))≤
      (2:ℝ)^(-(Schedule.h d b k:ℤ)) := by
  rw [reservedDraw,DyadicLaw.toLaw_pad]
  apply D.bitDraw_tv d hd hD hK _ _ fallback
  unfold Schedule.h
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

end
end Contingency.Dense.BinProblem

 

 

open scoped BigOperators
namespace Contingency.Dense
noncomputable section

lemma floor_width_bounds (s B : ℕ) (hB : 0 < B) (hs : 2*B ≤ s) :
    0  <  s / B ∧ (s : ℝ) / (2 * B)  ≤  (s / B : ℕ) ∧ ((s / B : ℕ) : ℝ)  ≤  (s : ℝ) / B := by
  have hw : 0 < s/B := Nat.div_pos (by omega) hB
  have hlo : s ≤ 2*B*(s/B) := by
    have hh := Nat.lt_mul_div_succ s hB
    have he := Nat.mul_le_mul_left B (show s/B+1 ≤ 2*(s/B) by omega)
    nlinarith only [hh,he]
  have hhi := Nat.mul_div_le s B
  have hBp : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨hw,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*B)).mpr
    have hh : (s:ℝ) ≤ 2*B*(s/B:ℕ) := by exact_mod_cast hlo
    nlinarith only [hh]
  · apply (le_div_iff₀ hBp).mpr
    have hh : (B:ℝ)*(s/B:ℕ) ≤ s := by exact_mod_cast hhi
    nlinarith only [hh]

variable {a c : ℕ} (d : ℕ) (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ)
    (hd : 14 ≤ d) (ha : a+1 ≤ d) (hc : c+1 ≤ d) (hac : (a+1)*(c+1) ≤ d)
    (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j) (heq : (∑ i,R i)=∑ j,P j)

abbrev sortedR := fun i => R (marginOrder R i)
abbrev sortedP := fun j => P (marginOrder P j)

def literalWidth (i : Fin (a*c)) : ℕ :=
  min (sortedR R ((finProdFinEquiv.symm i).1.castSucc))
    (sortedP P ((finProdFinEquiv.symm i).2.castSucc))/(d^8)

include hd in
theorem padding_scale : 2*d^8 ≤ d^12 := by
  have hh : 2 ≤ d^4 := (by norm_num : 2 ≤ 14^4).trans (Nat.pow_le_pow_left hd _)
  nlinarith only [Nat.mul_le_mul_left (d^8) hh,show d^12=d^8*d^4 by ring]

abbrev literalProblem : BinProblem a c (a*c) (4*d^8) where
  e := finProdFinEquiv.symm
  R := sortedR R
  P := sortedP P
  w := literalWidth d R P
  d := d
  hd := by exact_mod_cast (show 4 ≤ d by omega)
  hq := by exact_mod_cast (Nat.mul_le_mul (Nat.le_add_right a 1) (Nat.le_add_right c 1)).trans hac
  ha := by exact_mod_cast ha
  hc := by exact_mod_cast hc
  hK := by
    push_cast
    have hp : (0:ℝ) < (d:ℝ)^8 := by positivity
    linarith
  hR i := (pow_pos (by omega : 0 < d) 12).trans_le (hR _)
  hP j := (pow_pos (by omega : 0 < d) 12).trans_le (hP _)
  heq := by rw [(marginOrder R).sum_comp R,(marginOrder P).sum_comp P]; exact heq
  hRmax := marginOrder_max R
  hPmax := marginOrder_max P
  hw i := (floor_width_bounds _ (d^8) (by positivity) ((padding_scale d hd).trans (le_min (hR _) (hP _)))).1
  hwlo i := by
    have hh := (floor_width_bounds
      (min (sortedR R (finProdFinEquiv.symm i).1.castSucc) (sortedP P (finProdFinEquiv.symm i).2.castSucc))
      (d^8) (by positivity) ((padding_scale d hd).trans (le_min (hR _) (hP _)))).2.1
    simpa only [scale,literalWidth,Nat.cast_min,Nat.cast_pow] using hh
  hwhi i := by
    have hh := (floor_width_bounds
      (min (sortedR R (finProdFinEquiv.symm i).1.castSucc) (sortedP P (finProdFinEquiv.symm i).2.castSucc))
      (d^8) (by positivity) ((padding_scale d hd).trans (le_min (hR _) (hP _)))).2.2
    simpa only [scale,literalWidth,Nat.cast_min,Nat.cast_pow] using hh

theorem literalWidth_bound (_hd : 14 ≤ d) (b : ℕ) (hRb : ∀ i,R i ≤ 2^b) (i : Fin (a*c)) : literalWidth d R P i ≤ 2^b := by
  exact (Nat.div_le_self _ _).trans ((min_le_left _ _).trans (hRb _))

attribute [local instance] BinProblem.tableFintype

def literalDraw (b k : ℕ) (hRb : ∀ i,R i ≤ 2^b) (fallback : Tables R P) : DyadicLaw (Tables R P) := by
  classical
  let e := permuteTableEquiv R P (marginOrder R) (marginOrder P)
  let D := literalProblem d R P hd ha hc hac hR hP heq
  exact (D.reservedDraw d b k rfl (literalWidth_bound d R P hd b hRb) (e fallback)).map e.symm

theorem literalDraw_bits (b k : ℕ) (hRb : ∀ i,R i ≤ 2^b) (fallback : Tables R P) :
    (literalDraw d R P hd ha hc hac hR hP heq b k hRb fallback).bits=Schedule.RD d b k := by
  classical
  simp only [literalDraw,DyadicLaw.map_bits,BinProblem.reservedDraw_bits]

theorem literalDraw_tv (b k : ℕ) (hk : 1 ≤ k) (hRb : ∀ i,R i ≤ 2^b) (fallback : Tables R P) :
    letI := tables_nonempty R P heq
    (literalDraw d R P hd ha hc hac hR hP heq b k hRb fallback).toLaw.tv (Law.uniform (Tables R P)) ≤ 
      (2:ℝ)^(-(Schedule.h d b k:ℤ)) := by
  classical
  let := tables_nonempty R P heq
  let e := permuteTableEquiv R P (marginOrder R) (marginOrder P)
  let D := literalProblem d R P hd ha hc hac hR hP heq
  let := tables_nonempty D.R D.P D.heq
  have hK : ((4*d^8:ℕ):ℝ)=4*D.d^8 := by simp [D]
  have hh := D.reservedDraw_tv d b k hd hk rfl hK (literalWidth_bound d R P hd b hRb) (e fallback)
  change ((D.reservedDraw d b k rfl _ (e fallback)).map e.symm).toLaw.tv _ ≤ _
  rw [DyadicLaw.toLaw_map,← Law.uniform_map_equiv e.symm]
  exact (Law.tv_map e.symm _ _).trans hh

end
end Contingency.Dense

 

 

open scoped BigOperators

namespace Contingency
namespace PaddedGraph

variable {m n : ℕ}

 
def IsLarge (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (s : Cell m n) : Prop :=
  U ≤ r s.1 ∧ U ≤ c s.2

def IsSmall (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (s : Cell m n) : Prop :=
  ¬IsLarge U r c s

instance (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (s : Cell m n) :
    Decidable (IsLarge U r c s) := inferInstanceAs (Decidable (_ ∧ _))
instance (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (s : Cell m n) :
    Decidable (IsSmall U r c s) := inferInstanceAs (Decidable (¬_))

 

structure State (m n : ℕ) where
  x : Cell m n → ℤ
  q : Cell m n → ℤ
  deriving DecidableEq

def rowSum (x : Cell m n → ℤ) (i : Fin m) : ℤ := ∑ j, x (i,j)
def colSum (x : Cell m n → ℤ) (j : Fin n) : ℤ := ∑ i, x (i,j)

def Feasible (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (X : State m n) : Prop :=
  (∀ s, 0 ≤ X.x s ∧ X.x s ≤ U ∧ 0 ≤ X.q s ∧ X.q s ≤ U) ∧
  (∀ s, IsLarge U r c s → X.x s = 0 ∧ X.q s = 0) ∧
  (∀ i, rowSum X.x i ≤ r i ∧ ((∀ j, ¬IsLarge U r c (i,j)) → rowSum X.x i = r i)) ∧
  (∀ j, colSum X.q j ≤ c j ∧ ((∀ i, ¬IsLarge U r c (i,j)) → colSum X.q j = c j))

def Transversal (X : State m n) : Prop := X.q = X.x

def unit (s : Cell m n) : Cell m n → ℤ := fun v => if v = s then 1 else 0

def DefectAt (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) : Prop :=
  IsSmall U r c s ∧ IsSmall U r c t ∧ s ≠ t ∧
    X.q = fun v => X.x v - unit t v + unit s v

def receiver (s t : Cell m n) : Cell m n := (t.1,s.2)

 
noncomputable def repair (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) : State m n :=
  let x' := fun w => X.x w - unit t w + if IsSmall U r c (receiver s t) then unit (receiver s t) w else 0
  ⟨x',x'⟩

@[simp] theorem repair_transversal (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) : Transversal (repair U r c s t X) := rfl

@[simp] theorem rowSum_unit (s : Cell m n) (i : Fin m) :
    rowSum (unit s) i = if i = s.1 then 1 else 0 := by
  classical
  rcases s with ⟨a,b⟩
  unfold rowSum unit
  by_cases hi : i = a
  · subst i; simp
  · simp [hi]

@[simp] theorem colSum_unit (s : Cell m n) (j : Fin n) :
    colSum (unit s) j = if j = s.2 then 1 else 0 := by
  classical
  rcases s with ⟨a,b⟩
  unfold colSum unit
  by_cases hj : j = b
  · subst j; simp
  · simp [hj]

theorem rowSum_sub_add (x y z : Cell m n → ℤ) (i : Fin m) :
    rowSum (fun v => x v-y v+z v) i = rowSum x i-rowSum y i+rowSum z i := by
  simp [rowSum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem colSum_sub_add (x y z : Cell m n → ℤ) (j : Fin n) :
    colSum (fun v => x v-y v+z v) j = colSum x j-colSum y j+colSum z j := by
  simp [colSum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem donor_positive (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hx : Feasible U r c X) (hd : DefectAt U r c s t X) :
    1 ≤ X.x t := by
  have h := congrFun hd.2.2.2 t
  have hq := (hx.1 t).2.2.1
  change X.q t = X.x t - (if t = t then 1 else 0) + (if t = s then 1 else 0) at h
  simp [Ne.symm hd.2.2.1] at h
  omega

theorem repair_nonneg (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hx : Feasible U r c X) (hd : DefectAt U r c s t X) :
    ∀ w, 0 ≤ (repair U r c s t X).x w := by
  intro w
  have h0 := (hx.1 w).1
  have ht := donor_positive U r c s t X hx hd
  dsimp [repair,unit]
  by_cases hw : w = t
  · subst w; split_ifs <;> omega
  · simp only [ite_eq_right hw,sub_zero]
    split_ifs <;> omega

theorem repair_support (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hx : Feasible U r c X) (hd : DefectAt U r c s t X) :
    ∀ w, IsLarge U r c w → (repair U r c s t X).x w = 0 := by
  intro w hw
  have hwt : w ≠ t := by intro he; exact hd.2.1 (he ▸ hw)
  have hx0 := (hx.2.1 w hw).1
  dsimp [repair,unit]
  rw [hx0,ite_eq_right hwt]
  by_cases hv : IsSmall U r c (receiver s t)
  · rw [ite_eq_left hv]
    have hwv : w ≠ receiver s t := by intro he; exact hv (he ▸ hw)
    rw [ite_eq_right hwv]
    ring
  · rw [ite_eq_right hv]
    ring

theorem repair_rowSum (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (i : Fin m) :
    rowSum (repair U r c s t X).x i = rowSum X.x i -
      if IsLarge U r c (receiver s t) ∧ i = t.1 then 1 else 0 := by
  by_cases hv : IsSmall U r c (receiver s t)
  · change rowSum (fun w => X.x w - unit t w + if IsSmall U r c (receiver s t) then unit (receiver s t) w else 0) i = _
    simp only [ite_eq_left hv,rowSum_sub_add,rowSum_unit]
    have hv' : ¬IsLarge U r c (receiver s t) := hv
    have hnot : ¬(IsLarge U r c (receiver s t) ∧ i = t.1) := fun h => hv' h.1
    rw [ite_eq_right hnot]
    dsimp [receiver]
    omega
  · have hv' : IsLarge U r c (receiver s t) := Classical.not_not.mp hv
    simp only [repair,ite_eq_right hv]
    change rowSum (fun w => X.x w-unit t w+0) i = _
    rw [rowSum_sub_add,rowSum_unit]
    simp [rowSum,hv']

theorem repair_q_identity (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X) :
    (repair U r c s t X).q = fun w => X.q w - unit s w +
      if IsSmall U r c (receiver s t) then unit (receiver s t) w else 0 := by
  funext w
  have h := congrFun hd.2.2.2 w
  dsimp [repair]
  rw [h]
  ring

theorem repair_colSum (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X) (j : Fin n) :
    colSum (repair U r c s t X).q j = colSum X.q j -
      if IsLarge U r c (receiver s t) ∧ j = s.2 then 1 else 0 := by
  rw [repair_q_identity U r c s t X hd]
  by_cases hv : IsSmall U r c (receiver s t)
  · simp only [ite_eq_left hv,colSum_sub_add,colSum_unit]
    have hv' : ¬IsLarge U r c (receiver s t) := hv
    have hnot : ¬(IsLarge U r c (receiver s t) ∧ j = s.2) := fun h => hv' h.1
    rw [ite_eq_right hnot]
    dsimp [receiver]
    omega
  · have hv' : IsLarge U r c (receiver s t) := Classical.not_not.mp hv
    simp only [ite_eq_right hv]
    rw [colSum_sub_add,colSum_unit]
    simp [colSum,hv']

theorem coordinate_le_rowSum (x : Cell m n → ℤ) (hx : ∀ v, 0 ≤ x v) (s : Cell m n) :
    x s ≤ rowSum x s.1 := by
  apply Finset.single_le_sum (fun j _ => hx (s.1,j)) (Finset.mem_univ s.2)

theorem coordinate_le_colSum (x : Cell m n → ℤ) (hx : ∀ v, 0 ≤ x v) (s : Cell m n) :
    x s ≤ colSum x s.2 := by
  apply Finset.single_le_sum (fun i _ => hx (i,s.2)) (Finset.mem_univ s.1)

 

theorem repair_feasible (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hx : Feasible U r c X) (hd : DefectAt U r c s t X) :
    Feasible U r c (repair U r c s t X) := by
  have hnn := repair_nonneg U r c s t X hx hd
  have hsup := repair_support U r c s t X hx hd
  have hr (i) : rowSum (repair U r c s t X).x i ≤ r i ∧
      ((∀ j, ¬IsLarge U r c (i,j)) → rowSum (repair U r c s t X).x i = r i) := by
    rw [repair_rowSum]
    constructor
    · have h := (hx.2.2.1 i).1
      split_ifs <;> omega
    · intro hi
      have h := (hx.2.2.1 i).2 hi
      have hn : ¬(IsLarge U r c (receiver s t) ∧ i = t.1) := by
        rintro ⟨hl, rfl⟩
        exact hi s.2 hl
      rw [ite_eq_right hn,h]
      omega
  have hc (j) : colSum (repair U r c s t X).q j ≤ c j ∧
      ((∀ i, ¬IsLarge U r c (i,j)) → colSum (repair U r c s t X).q j = c j) := by
    rw [repair_colSum U r c s t X hd]
    constructor
    · have h := (hx.2.2.2 j).1
      split_ifs <;> omega
    · intro hj
      have h := (hx.2.2.2 j).2 hj
      have hn : ¬(IsLarge U r c (receiver s t) ∧ j = s.2) := by
        rintro ⟨hl, rfl⟩
        exact hj t.1 hl
      rw [ite_eq_right hn,h]
      omega
  have hcap (w) : (repair U r c s t X).x w ≤ U := by
    by_cases hw : IsLarge U r c w
    · rw [hsup w hw]; positivity
    · have hw' : ¬(U ≤ r w.1 ∧ U ≤ c w.2) := hw
      have h1 := coordinate_le_rowSum _ hnn w
      have h2 := coordinate_le_colSum _ hnn w
      have h3 := (hr w.1).1
      have h4 := (hc w.2).1
      change colSum (repair U r c s t X).x w.2 ≤ c w.2 at h4
      omega
  exact ⟨fun w => ⟨hnn w,hcap w,hnn w,hcap w⟩,
    fun w hw => ⟨hsup w hw,hsup w hw⟩,hr,hc⟩

 
theorem repair_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X Y : State m n)
    (hX : DefectAt U r c s t X) (hY : DefectAt U r c s t Y)
    (he : repair U r c s t X = repair U r c s t Y) : X = Y := by
  have hx : X.x = Y.x := by
    funext w
    have h := congrArg (fun Z : State m n => Z.x w) he
    dsimp [repair] at h
    linarith
  have hq : X.q = Y.q := by rw [hX.2.2.2,hY.2.2.2,hx]
  cases X; cases Y
  simp_all

 

def Before (s t : Cell m n) : Prop := s.1 < t.1 ∨ s.1 = t.1 ∧ s.2 < t.2

theorem before_ne (s t : Cell m n) (h : Before s t) : s ≠ t := by
  intro he
  subst t
  rcases h with h | h
  · exact (lt_irrefl _ h)
  · exact (lt_irrefl _ h.2)

theorem before_trans (s t v : Cell m n) (hst : Before s t) (htv : Before t v) : Before s v := by
  rcases hst with hst | ⟨hst,hst'⟩ <;> rcases htv with htv | ⟨htv,htv'⟩
  · exact Or.inl (lt_trans hst htv)
  · exact Or.inl (htv ▸ hst)
  · exact Or.inl (hst ▸ htv)
  · exact Or.inr ⟨hst.trans htv,lt_trans hst' htv'⟩

theorem receiver_order (s t : Cell m n) (hst : Before s t) :
    receiver s t = s ∨ Before s (receiver s t) := by
  rcases hst with hst | ⟨hst,_⟩
  · exact Or.inr (Or.inl hst)
  · exact Or.inl (Prod.ext hst.symm rfl)

theorem repair_prefix (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X)
    (hst : Before s t) (w : Cell m n) (hws : Before w s) :
    (repair U r c s t X).x w = X.x w ∧ (repair U r c s t X).q w = X.q w := by
  have hwt := before_ne w t (before_trans w s t hws hst)
  have hws' := before_ne w s hws
  have hwv : w ≠ receiver s t := by
    rcases receiver_order s t hst with he | he
    · rwa [he]
    · exact before_ne w _ (before_trans w s _ hws he)
  constructor
  · simp [repair,unit,hwt,hwv]
  · rw [repair_q_identity U r c s t X hd]
    simp [unit,hws',hwv]

theorem repair_special (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X) (l : ℤ)
    (hl : X.x s = l-1) :
    (repair U r c s t X).x s = if t.1 = s.1 then l else l-1 := by
  have hst := hd.2.2.1
  by_cases hi : t.1=s.1
  · have hv : receiver s t = s := Prod.ext hi rfl
    simp [repair,unit,hst,hi,hv,hd.1,hl]
  · have hv : s ≠ receiver s t := by
      intro he
      exact hi (congrArg Prod.fst he).symm
    simp [repair,unit,hst,hi,hv,hl]

end PaddedGraph
end Contingency

end

end OAI
