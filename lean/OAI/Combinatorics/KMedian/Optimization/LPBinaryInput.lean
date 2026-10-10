import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ApproximateFractional
import OAI.Combinatorics.KMedian.Compression.RationalScaling
import OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight
import OAI.Combinatorics.KMedian.Optimization.LPListFacts
import OAI.Combinatorics.KMedian.Optimization.SubgradientTrajectoryHeight

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

structure Input where
  n : ℕ
  m : ℕ
  k : ℕ
  npos : 0 < n
  mpos : 0 < m
  kpos : 0 < k
  kle : k ≤ n
  distance : Fin m → Fin n → ℚ

namespace Input
instance (I : Input) : NeZero I.n := ⟨I.npos.ne'⟩
instance (I : Input) : NeZero I.m := ⟨I.mpos.ne'⟩
def rows (I : Input) : Rows := List.ofFn (fun j => List.ofFn (I.distance j))
def raw (I : Input) : Rows × ℕ := (I.rows,I.k)
abbrev encode (I : Input) := encodePair ers Nat.bits I.raw

 theorem bounds (I : Input) : I.n ≤ I.encode.length ∧ I.m ≤ I.encode.length ∧ I.k ≤ I.encode.length ∧
    ∀ j i, HasHeight (I.distance j i) I.encode.length := by
  let L := I.encode.length
  have henc : L=2*(ers I.rows).length+1+I.k.bits.length := by
    simp only [L,raw,encodePair_length]
  have hm := EncodedList.length_le er I.rows
  change I.rows.length ≤ (ers I.rows).length at hm
  simp only [rows,List.length_ofFn] at hm
  change I.m ≤ (ers I.rows).length at hm
  have hrow (j : Fin I.m) : (er (List.ofFn (I.distance j))).length  ≤  (ers I.rows).length :=
    EncodedList.member_length er I.rows _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hn := EncodedList.length_le Ratio.encode (List.ofFn (I.distance ⟨0,I.mpos⟩))
  change (List.ofFn (I.distance ⟨0,I.mpos⟩)).length ≤ (er (List.ofFn (I.distance ⟨0,I.mpos⟩))).length at hn
  simp only [List.length_ofFn] at hn
  have hnL : I.n ≤ L := by have hh := hrow ⟨0,I.mpos⟩; omega
  refine ⟨hnL,by omega,I.kle.trans hnL,?_⟩
  intro j i
  have hh := EncodedList.member_length Ratio.encode (List.ofFn (I.distance j)) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  change (Ratio.encode (I.distance j i)).length ≤ (er (List.ofFn (I.distance j))).length at hh
  have hrow := hrow j
  exact (Ratio.height_length _).mono (by omega)

def vector (I : Input) (r : ℕ) (t : ℕ) : Vector ℚ I.n :=
  ProjectedSubgradient.trajectory (I.k:ℚ) (TruncatedLP.rate (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k))
    (fun y => TruncatedLP.gradient I.distance y (TruncatedLP.penalty r I.k))
    (ProjectedSubgradient.initial (I.k:ℚ)) t

def iterate (I : Input) (r : ℕ) (t : ℕ) : Row := List.ofFn (ProjectedSubgradient.point (I.vector r t))
end Input

def gradientBound (r L : ℕ) := L*(L*(4*r*(L+1)))^2
def baseBound (r L : ℕ) := 2*r*gradientBound r L*L
def stepsBound (r L : ℕ) := 8*r^2*gradientBound r L*L^2
def exponentBound (r L : ℕ) := baseBound r L+L*(L*L)+L+1
def heightBound (r L : ℕ) := exponentBound r L*(stepsBound r L+1)

 theorem penalty_bound (I : Input) (r : ℕ) : TruncatedLP.penalty r I.k  ≤  4*r*(I.encode.length+1) := by
  unfold TruncatedLP.penalty
  gcongr
  exact I.bounds.2.2.1
 theorem grad_bound (I : Input) (r : ℕ) :
    TruncatedLP.gradSize (n:=I.n) (m:=I.m) (TruncatedLP.penalty r I.k)  ≤  gradientBound r I.encode.length := by
  unfold TruncatedLP.gradSize gradientBound
  gcongr
  · exact I.bounds.1
  · exact I.bounds.2.1
  · exact penalty_bound I r
 theorem steps_bound (I : Input) (r : ℕ) :
    TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)  ≤  stepsBound r I.encode.length := by
  unfold TruncatedLP.steps stepsBound
  gcongr
  · exact grad_bound I r
  · exact I.bounds.2.2.1

 theorem iterate_height (I : Input) (r : ℕ) (hr : 0 < r) (t : ℕ)
    (ht : t ≤ TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)) (i : Fin I.n) :
    HasHeight (ProjectedSubgradient.point (I.vector r t) i) (heightBound r I.encode.length) := by
  let L := I.encode.length
  let q := fun p : Fin I.m × Fin I.n => I.distance p.1 p.2
  let R := RationalScaling.denominator q
  have hR : 0 < R := RationalScaling.denominator_pos q
  have hd : ∀ j i, RationalGrid.At R (I.distance j i) := by
    intro j i
    refine ⟨RationalScaling.numerator q (j,i),?_⟩
    rw [RationalScaling.numerator_cast,mul_div_cancel_right₀]
    exact_mod_cast hR.ne'
  have hRbound : R ≤ (2:ℤ)^(L*(L*L)) := by
    have hh := RationalScaling.denominator_bound q L (fun p => (I.bounds.2.2.2 p.1 p.2).2)
    simp only [Fintype.card_prod,Fintype.card_fin] at hh
    apply hh.trans
    apply pow_le_pow_right₀ (by norm_num)
    gcongr
    · exact I.bounds.2.1
    · exact I.bounds.1
  have hbn : TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*(I.n:ℤ) ≤ baseBound r L := by
    unfold TruncatedLP.rateDen
    have hg := grad_bound I r
    have hn := I.bounds.1
    dsimp only [baseBound]
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left (2*r) hg) hn
  have hnat : (baseBound r L:ℤ) ≤ (2:ℤ)^(baseBound r L) := by exact_mod_cast (Nat.lt_two_pow_self (n:=baseBound r L)).le
  have hbase : TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*R*(I.n:ℤ) ≤ (2:ℤ)^(exponentBound r L) := by
    calc
      _ = (TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*(I.n:ℤ))*R := by ring
      _  ≤  (2:ℤ)^(baseBound r L)*(2:ℤ)^(L*(L*L)) := mul_le_mul (hbn.trans hnat) hRbound hR.le (by positivity)
      _ = (2:ℤ)^(baseBound r L+L*(L*L)) := (pow_add ..).symm
      _  ≤  _ := pow_le_pow_right₀ (by norm_num) (by unfold exponentBound; omega)
  have hk : (I.k:ℤ) ≤ (2:ℤ)^(exponentBound r L) := by
    have hkL : (I.k:ℤ) ≤ L := by exact_mod_cast I.bounds.2.2.1
    have hL : (L:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast (Nat.lt_two_pow_self (n:=L)).le
    exact (hkL.trans hL).trans (pow_le_pow_right₀ (by norm_num) (by unfold exponentBound; omega))
  have hh := TruncatedLP.trajectory_height I.distance r I.k (TruncatedLP.penalty r I.k) hr I.kpos
    (TruncatedLP.penalty_pos r I.k hr) R hR hd (exponentBound r L) hbase hk t i
  apply hh.mono
  unfold heightBound
  exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (ht.trans (steps_bound I r)))

 theorem iterate_size (I : Input) (r : ℕ) (hr : 0 < r) (t : ℕ)
    (ht : t ≤ TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)) :
    (er (I.iterate r t)).length  ≤  I.encode.length*(2*(3*heightBound r I.encode.length+10)+1) := by
  have hh := EncodedList.length_bound Ratio.encode (I.iterate r t) (3*heightBound r I.encode.length+10) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact Ratio.length_height (iterate_height I r hr t ht i))
  simp only [Input.iterate,List.length_ofFn] at hh
  exact hh.trans (Nat.mul_le_mul_right _ I.bounds.1)

noncomputable def stepsPolynomial (r : ℕ) : Polynomial ℕ := 8*C r^2*(X*(X*(4*C r*(X+1)))^2)*X^2
noncomputable def heightPolynomial (r : ℕ) : Polynomial ℕ :=
  (2*C r*(X*(X*(4*C r*(X+1)))^2)*X+X*(X*X)+X+1)*(stepsPolynomial r+1)
 theorem stepsPolynomial_eval (r L : ℕ) : (stepsPolynomial r).eval L=stepsBound r L := by
  simp only [stepsPolynomial,stepsBound,gradientBound,eval_add,eval_mul,eval_pow,eval_ofNat,eval_C,eval_X,eval_one]
 theorem heightPolynomial_eval (r L : ℕ) : (heightPolynomial r).eval L=heightBound r L := by
  simp only [heightPolynomial,heightBound,exponentBound,baseBound,gradientBound,eval_add,eval_mul,eval_pow,eval_ofNat,eval_C,eval_X,eval_one,stepsPolynomial_eval]
end MetricKMedian.LPBinary
end

end OAI
