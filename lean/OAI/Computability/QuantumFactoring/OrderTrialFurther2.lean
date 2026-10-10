import Mathlib
import OAI.Computability.QuantumFactoring.OrderTrialFurther

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma largeQ (B : ℕ) (hB : 2 ≤ B) : 65*B ≤ B^16 := by
  have h : 65 ≤ B^15 := by
    calc
      65 ≤ (2:ℕ)^15 := by norm_num
      _ ≤ B^15 := Nat.pow_le_pow_left hB 15
  calc
    _ ≤ B^15*B := Nat.mul_le_mul_right B h
    _ = B^16 := (pow_succ B 15).symm

/-- The literal majorant-sum estimate at the standing Q=B^16. -/
lemma majorantSum_bounds {B d : ℕ} (hB : 2 ≤ B) (hd : 0 < d) (hdB : d < B) (j : ℕ) :
    1/(128*(d:ℝ)) ≤ (majorantSum (B^16) B d j:ℝ) ∧
      (majorantSum (B^16) B d j:ℝ) ≤ 2 := by
  have hQ : 0 < B^16 := pow_pos (by omega) _
  refine ⟨majorantSum_lower hQ hB hd hdB.le j, (majorantSum_upper hQ hB hd hdB.le j).trans ?_⟩
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hQ' : (0:ℝ) < (B^16:ℕ) := Nat.cast_pos.mpr hQ
  have h65 : (65:ℝ)*d ≤ (B^16:ℕ) := by
    exact_mod_cast (Nat.mul_le_mul_left 65 hdB.le).trans (largeQ B hB)
  have h₁ : 1/(2*(d:ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*d)).mpr
    linarith
  have h₂ : 65*(d:ℝ)/(2*(B^16:ℕ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(B^16:ℕ))).mpr
    linarith
  linarith

/-- Integer numerator retained by upward rounding at an integer argument. -/
noncomputable def roundedNumerator (D : ℕ) (p : ℚ[X]) (u : ℕ) : ℤ :=
  ∑ q ∈ Finset.range 5, ⌈(D:ℚ)*p.coeff q⌉*(u:ℤ)^q

lemma roundedValue_numerator (D : ℕ) (p : ℚ[X]) (u : ℕ) :
    roundedValue D p u = (roundedNumerator D p u:ℚ)/D := by
  simp only [roundedValue, roundedNumerator, roundCoeff, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  ring

noncomputable def majorantNumerator (Q B d j u : ℕ) : ℤ :=
  roundedNumerator (Q*B^8) (selectedMass d (binErrorRat Q d j) u) u+64*(B:ℤ)^8

lemma majorant_numerator {Q B : ℕ} (hQ : 0 < Q) (hB : 0 < B) (d j u : ℕ) :
    majorant Q B d j u = (majorantNumerator Q B d j u:ℚ)/(Q*B^8) := by
  simp only [majorant, majorantNumerator, roundedValue_numerator, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow]
  have hQ' : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hB' : (B:ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

lemma majorantSum_numerator {Q B : ℕ} (hQ : 0 < Q) (hB : 0 < B) (d j : ℕ) :
    majorantSum Q B d j =
      ((∑ u ∈ Finset.range d, majorantNumerator Q B d j u : ℤ):ℚ)/(2*(Q*B^8)) := by
  simp only [majorantSum, majorant_numerator hQ hB, Int.cast_sum, ← Finset.sum_div]
  ring

/-- Dyadic means an integer over a nonnegative integral power of two. -/
def IsDyadic (x : ℚ) : Prop := ∃ k : ℕ, ∃ z : ℤ, x = (z:ℚ)/2^k

lemma majorant_dyadic (n d j u : ℕ) :
    IsDyadic (majorant ((2^n)^16) (2^n) d j u) := by
  refine ⟨n*24, majorantNumerator ((2^n)^16) (2^n) d j u, ?_⟩
  rw [majorant_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_add, ← pow_mul]

lemma majorantSum_dyadic (n d j : ℕ) :
    IsDyadic (majorantSum ((2^n)^16) (2^n) d j) := by
  refine ⟨n*24+1, ∑ u ∈ Finset.range d, majorantNumerator ((2^n)^16) (2^n) d j u, ?_⟩
  rw [majorantSum_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_add, ← pow_mul, pow_succ]
  ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Five closed power-sum formulas, not an enumeration up to the endpoint. -/
def powerSumValue (q : ℕ) (M : ℚ) : ℚ :=
  match q with
  | 0 => M
  | 1 => M*(M-1)/2
  | 2 => M*(M-1)*(2*M-1)/6
  | 3 => (M*(M-1)/2)^2
  | 4 => M*(M-1)*(2*M-1)*(3*M^2-3*M-1)/30
  | _ => 0

lemma powerSumValue_correct (q : ℕ) (hq : q ≤ 4) (M : ℕ) :
    powerSumValue q M = ∑ u ∈ Finset.range M, (u:ℚ)^q := by
  induction M with
  | zero => interval_cases q <;> norm_num [powerSumValue]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    interval_cases q <;> simp only [powerSumValue] <;> ring

lemma powerSumValue_sub {lo hi : ℕ} (h : lo ≤ hi) {q : ℕ} (hq : q ≤ 4) :
    powerSumValue q hi-powerSumValue q lo = ∑ u ∈ Finset.Ico lo hi, (u:ℚ)^q := by
  rw [Finset.sum_Ico_eq_sub _ h, powerSumValue_correct q hq, powerSumValue_correct q hq]

/-- Constant-length arithmetic formula for summing a degree-four expression. -/
def fiveTermSum (a : ℕ → ℚ) (lo hi : ℕ) : ℚ :=
  if lo ≤ hi then ∑ q ∈ Finset.range 5, a q*(powerSumValue q hi-powerSumValue q lo) else 0

lemma fiveTermSum_correct (a : ℕ → ℚ) (lo hi : ℕ) :
    fiveTermSum a lo hi = ∑ u ∈ Finset.Ico lo hi, ∑ q ∈ Finset.range 5, a q*(u:ℚ)^q := by
  unfold fiveTermSum
  split_ifs with h
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [powerSumValue_sub h (by simp only [Finset.mem_range] at hq; omega), Finset.mul_sum]
  · simp [Finset.Ico_eq_empty (by omega : ¬ lo < hi)]

/-- Clipped natural endpoints for the intersection of two rational intervals. -/
def intervalLo (a c : ℚ) : ℕ := max ⌈a⌉.toNat ⌈c⌉.toNat

def intervalHi (d : ℕ) (b e : ℚ) : ℕ := min d (min ⌈b⌉.toNat ⌈e⌉.toNat)

lemma interval_mem_iff (d u : ℕ) (a b c e : ℚ) :
    u ∈ Finset.Ico (intervalLo a c) (intervalHi d b e) ↔
      u < d ∧ a ≤ (u:ℚ) ∧ (u:ℚ) < b ∧ c ≤ (u:ℚ) ∧ (u:ℚ) < e := by
  simp only [Finset.mem_Ico, intervalLo, intervalHi, max_le_iff, lt_min_iff,
    Int.toNat_le, Int.lt_toNat, Int.ceil_le, Int.lt_ceil, Int.cast_natCast]
  tauto

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma quarterIndex_eq (x : ℚ) (q : ℤ) :
    quarterIndex x=q ↔ (q:ℚ)/4 ≤ x ∧ x < ((q:ℚ)+1)/4 := by
  unfold quarterIndex
  rw [Int.floor_eq_iff]
  constructor <;> rintro ⟨hl,hu⟩ <;> constructor <;> linarith

lemma shiftedQuarter_eq {d : ℕ} (hd : 0 < d) (u : ℕ) (η : ℚ) (q : ℤ) :
    quarterIndex ((u:ℚ)/d+η)=q ↔
      (d:ℚ)*((q:ℚ)/4-η) ≤ u ∧ (u:ℚ) < d*(((q:ℚ)+1)/4-η) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  rw [quarterIndex_eq, ← sub_le_iff_le_add, ← lt_sub_iff_add_lt,
    le_div_iff₀ hd', div_lt_iff₀ hd']
  simp only [mul_comm]

/-- Exactly 32 possible quarter pairs. -/
noncomputable def quarterPairs : Finset (ℤ × ℤ) := (Finset.Ico 0 4) ×ˢ (Finset.Ico (-2) 6)

def pieceLabel (d : ℕ) (η : ℚ) (u : ℕ) : ℤ × ℤ :=
  (quarterIndex ((u:ℚ)/d), quarterIndex ((u:ℚ)/d+η))

lemma pieceLabel_mem {d : ℕ} (hd : 0 < d) {η : ℚ} (hη : |η| ≤ 1/2)
    {u : ℕ} (hu : u < d) : pieceLabel d η u ∈ quarterPairs := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hu₀ : (0:ℚ) ≤ (u:ℚ)/d := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hu₁ : (u:ℚ)/d < 1 := (div_lt_one hd').mpr (by exact_mod_cast hu)
  rcases abs_le.mp hη with ⟨hη₀,hη₁⟩
  simp only [pieceLabel, quarterPairs, Finset.mem_product, Finset.mem_Ico,
    quarterIndex, Int.le_floor, Int.floor_lt, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
  constructor <;> constructor <;> linarith

lemma quarterPairs_card : quarterPairs.card=32 := by norm_num [quarterPairs]

def pieceLo (d : ℕ) (η : ℚ) (q : ℤ × ℤ) : ℕ :=
  intervalLo ((d:ℚ)*(q.1:ℚ)/4) ((d:ℚ)*((q.2:ℚ)/4-η))

def pieceHi (d : ℕ) (η : ℚ) (q : ℤ × ℤ) : ℕ :=
  intervalHi d ((d:ℚ)*((q.1:ℚ)+1)/4) ((d:ℚ)*(((q.2:ℚ)+1)/4-η))

lemma piece_fiber {d : ℕ} (hd : 0 < d) (η : ℚ) (q : ℤ × ℤ) :
    (Finset.range d).filter (fun u => pieceLabel d η u=q) =
      Finset.Ico (pieceLo d η q) (pieceHi d η q) := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_range, pieceLo, pieceHi, interval_mem_iff]
  rw [Prod.ext_iff]
  simp only [pieceLabel]
  have h₀ := shiftedQuarter_eq hd u 0 q.1
  simp only [add_zero, sub_zero] at h₀
  rw [h₀, shiftedQuarter_eq hd u η q.2]
  simp only [mul_div_assoc]
  tauto

/-- Each piece sum is computed with five closed power sums plus its length. -/
noncomputable def packedPieceSum (Q B d j : ℕ) (q : ℤ × ℤ) : ℚ :=
  let η := binErrorRat Q d j
  let lo := pieceLo d η q
  let hi := pieceHi d η q
  fiveTermSum (fun k => roundCoeff (Q*B^8) ((massPiece d η q.1 q.2).coeff k)) lo hi +
    ((hi-lo:ℕ):ℚ)*(64/(Q:ℚ))

lemma packedPieceSum_correct {Q B d : ℕ} (hd : 0 < d) (j : ℕ) (q : ℤ × ℤ) :
    packedPieceSum Q B d j q =
      ∑ u ∈ (Finset.range d).filter (fun u => pieceLabel d (binErrorRat Q d j) u=q),
        majorant Q B d j u := by
  let η := binErrorRat Q d j
  have hf := piece_fiber hd η q
  have he : ∀ u ∈ (Finset.range d).filter (fun u => pieceLabel d η u=q),
      majorant Q B d j u = roundedValue (Q*B^8) (massPiece d η q.1 q.2) u+64/(Q:ℚ) := by
    intro u hu
    have h := (Finset.mem_filter.mp hu).2
    have h₀ := congrArg Prod.fst h
    have h₁ := congrArg Prod.snd h
    simp only [pieceLabel] at h₀ h₁
    simp only [majorant, selectedMass, h₀, h₁, η]
  change packedPieceSum Q B d j q = ∑ u ∈ (Finset.range d).filter (fun u => pieceLabel d η u=q), _
  rw [Finset.sum_congr rfl he, hf, Finset.sum_add_distrib]
  simp only [packedPieceSum, fiveTermSum_correct, roundedValue, η,
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- Exact constant-piece evaluation: no traversal of the d residues. -/
noncomputable def packedMajorantSum (Q B d j : ℕ) : ℚ :=
  (∑ q ∈ quarterPairs, packedPieceSum Q B d j q)/2

lemma packedMajorantSum_correct {Q B d : ℕ} (hd : 0 < d) (j : ℕ) :
    packedMajorantSum Q B d j = majorantSum Q B d j := by
  unfold packedMajorantSum majorantSum
  congr 1
  simp only [packedPieceSum_correct hd]
  apply Finset.sum_fiberwise_of_maps_to
  intro u hu
  apply pieceLabel_mem hd
  · have h := binError_bound (Q:=Q) (j:=j) hd
    rw [← binErrorRat_cast] at h
    have h' : ((|binErrorRat Q d j|:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := by simpa using h
    exact Rat.cast_le.mp h'
  · exact Finset.mem_range.mp hu

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Exact prescribed per-numerator mass, with the manuscript's ceiling. -/
def prescribedMass (d : ℕ) : ℚ := 1/(2:ℚ)^(Nat.clog 2 d+10)

lemma prescribedMass_pos (d : ℕ) : 0 < prescribedMass d := by
  unfold prescribedMass
  positivity

lemma prescribedMass_upper {d : ℕ} (hd : 0 < d) :
    prescribedMass d ≤ 1/(1024*(d:ℚ)) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) d
  have h' : (d:ℚ) ≤ (2:ℚ)^(Nat.clog 2 d) := by exact_mod_cast h
  unfold prescribedMass
  rw [pow_add, show (2:ℚ)^10=1024 by norm_num]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

lemma prescribedMass_lower {d : ℕ} (hd : 0 < d) :
    1/(2048*(d:ℚ)) ≤ prescribedMass d := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hp : (2:ℕ)^(Nat.clog 2 d) ≤ 2*d := by
    by_cases h : d=1
    · simp [h]
    · have hd₁ : 1 < d := by omega
      have hc := Nat.clog_pos (by norm_num : 1 < 2) hd₁
      have hlt := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hd₁
      calc
        _ = 2^(Nat.clog 2 d-1)*2 := by rw [← pow_succ]; congr 1; omega
        _ ≤ d*2 := Nat.mul_le_mul_right 2 hlt.le
        _ = 2*d := by omega
  have hp' : (2:ℚ)^Nat.clog 2 d ≤ 2*d := by exact_mod_cast hp
  unfold prescribedMass
  rw [pow_add, show (2:ℚ)^10=1024 by norm_num]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

/-- Downward dyadic ratio rounding, as in (mode-coefficient). -/
def modeCoeff (n : ℕ) (lam S : ℚ) : ℚ :=
  (⌊(2:ℚ)^(10*n)*(lam/S)⌋:ℤ)/(2:ℚ)^(10*n)

def modeRemainder (n : ℕ) (lam S : ℚ) : ℚ := lam-modeCoeff n lam S*S

lemma modeCoeff_basic (n : ℕ) {lam S : ℚ} (hlam : 0 ≤ lam) (hS : 0 < S) :
    0 ≤ modeCoeff n lam S ∧ modeCoeff n lam S ≤ lam/S ∧
      lam/S-modeCoeff n lam S ≤ 1/(2:ℚ)^(10*n) := by
  have hD : (0:ℚ) < 2^(10*n) := by positivity
  have hx : 0 ≤ (2:ℚ)^(10*n)*(lam/S) := mul_nonneg hD.le (div_nonneg hlam hS.le)
  have hf := Int.floor_le ((2:ℚ)^(10*n)*(lam/S))
  have hu := (Int.lt_floor_add_one ((2:ℚ)^(10*n)*(lam/S))).le
  have hfn : (0:ℚ) ≤ (⌊(2:ℚ)^(10*n)*(lam/S)⌋:ℤ) := by
    exact_mod_cast (Int.floor_nonneg.mpr hx)
  unfold modeCoeff
  refine ⟨div_nonneg hfn hD.le, ?_, ?_⟩
  · apply (div_le_iff₀ hD).mpr
    nlinarith
  · apply (mul_le_mul_iff_right₀ hD).mp
    rw [mul_sub, mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
    linarith

lemma modeRemainder_basic (n : ℕ) {lam S : ℚ} (hlam : 0 ≤ lam) (hS : 0 < S) :
    0 ≤ modeRemainder n lam S ∧ modeRemainder n lam S ≤ S/(2:ℚ)^(10*n) := by
  have h := modeCoeff_basic n hlam hS
  have he : modeRemainder n lam S = (lam/S-modeCoeff n lam S)*S := by
    unfold modeRemainder
    rw [sub_mul, div_mul_cancel₀ _ hS.ne']
  rw [he]
  refine ⟨mul_nonneg (sub_nonneg.mpr h.2.1) hS.le, ?_⟩
  calc
    _ ≤ (1/(2:ℚ)^(10*n))*S := mul_le_mul_of_nonneg_right h.2.2 hS.le
    _ = _ := by ring

lemma modeCoeff_bounds (n : ℕ) {d : ℕ} (hd : 0 < d) {S : ℚ}
    (hSl : 1/(128*(d:ℚ)) ≤ S) (hSu : S ≤ 2) :
    0 ≤ modeCoeff n (prescribedMass d) S ∧ modeCoeff n (prescribedMass d) S ≤ 1/8 ∧
      0 ≤ modeRemainder n (prescribedMass d) S ∧
      modeRemainder n (prescribedMass d) S ≤ 2/(2:ℚ)^(10*n) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hSl
  have hc := modeCoeff_basic n (prescribedMass_pos d).le hS
  have hr := modeRemainder_basic n (prescribedMass_pos d).le hS
  refine ⟨hc.1, hc.2.1.trans ?_, hr.1, hr.2.trans ?_⟩
  · apply (div_le_iff₀ hS).mpr
    have hl := prescribedMass_upper hd
    have he : 1/(1024*(d:ℚ)) = (1/8)*(1/(128*(d:ℚ))) := by ring
    rw [he] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hSl (by norm_num))
  · exact div_le_div_of_nonneg_right hSu (by positivity)

lemma sum_residue_permutation {α : Type*} [AddCommMonoid α] {d j : ℕ}
    (hd : 0 < d) (hj : Nat.Coprime j d) (f : ℕ → α) :
    (∑ t ∈ Finset.range d, f ((j*t)%d)) = ∑ u ∈ Finset.range d, f u := by
  let g : Fin d → Fin d := fun t => ⟨(j*t.val)%d, Nat.mod_lt _ hd⟩
  have hi : Function.Injective g := by
    intro a b hab
    apply Fin.ext
    have he : Nat.ModEq d (j*a.val) (j*b.val) := congrArg Fin.val hab
    have h := he.cancel_left_of_coprime hj.symm
    change a.val % d = b.val % d at h
    simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h
  have hb : Function.Bijective g := ⟨hi, Finite.surjective_of_injective hi⟩
  have h := (Equiv.ofBijective g hb).sum_comp (fun u : Fin d => f u.val)
  change (∑ t : Fin d, f ((j*t.val)%d)) = ∑ u : Fin d, f u.val at h
  rw [Fin.sum_univ_eq_sum_range (fun t => f ((j*t)%d)) d,
    Fin.sum_univ_eq_sum_range f d] at h
  exact h

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma IsDyadic.intCast (z : ℤ) : IsDyadic (z:ℚ) := ⟨0,z,by simp⟩

lemma IsDyadic.add {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x+y) := by
  obtain ⟨k,a,rfl⟩ := hx
  obtain ⟨l,b,rfl⟩ := hy
  refine ⟨k+l,a*2^l+b*2^k,?_⟩
  push_cast
  rw [pow_add]
  field_simp

lemma IsDyadic.neg {x : ℚ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨k,a,rfl⟩ := hx
  exact ⟨k,-a,by push_cast; ring⟩

lemma IsDyadic.sub {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x-y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

lemma IsDyadic.mul {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x*y) := by
  obtain ⟨k,a,rfl⟩ := hx
  obtain ⟨l,b,rfl⟩ := hy
  refine ⟨k+l,a*b,?_⟩
  push_cast
  rw [pow_add]
  ring

lemma prescribedMass_dyadic (d : ℕ) : IsDyadic (prescribedMass d) :=
  ⟨Nat.clog 2 d+10,1,by simp [prescribedMass]⟩

lemma modeCoeff_dyadic (n : ℕ) (lam S : ℚ) : IsDyadic (modeCoeff n lam S) :=
  ⟨10*n,⌊(2:ℚ)^(10*n)*(lam/S)⌋,rfl⟩

lemma modeRemainder_dyadic (n : ℕ) {lam S : ℚ}
    (hlam : IsDyadic lam) (hS : IsDyadic S) : IsDyadic (modeRemainder n lam S) :=
  hlam.sub ((modeCoeff_dyadic n lam S).mul hS)

/-- The three actual branches, including mode selection and uniform-label masses. -/
noncomputable def firstModeMass (n Q B d j : ℕ) : ℝ :=
  (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ)/2 *
    ∑ t ∈ Finset.range d, residueProbability Q d j t

noncomputable def secondModeMass (n Q B d j : ℕ) : ℝ :=
  (1/4) * ∑ t ∈ Finset.range d,
    (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t) *
      (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ))

noncomputable def thirdModeMass (n Q B d j : ℕ) : ℝ :=
  (1/4) * (1/(B:ℝ)^2) * (4*(B:ℝ)^2 *
    (modeRemainder n (prescribedMass d) (majorantSum Q B d j):ℝ))

/-- Exact cancellation, not an estimate: Mode 2 fills precisely U-P. -/
lemma first_second_mass {n Q B d j : ℕ} (hB : 0 < B) (hd : 0 < d)
    (hj : Nat.Coprime j d) :
    firstModeMass n Q B d j + secondModeMass n Q B d j =
      (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ) *
      (majorantSum Q B d j:ℝ) := by
  have hB' : (B:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  let c : ℝ := modeCoeff n (prescribedMass d) (majorantSum Q B d j)
  have hs : ∀ t, (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t)*c) =
      2*c*((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t) := by
    intro t
    field_simp
  unfold firstModeMass secondModeMass
  change c/2*(∑ t ∈ Finset.range d, residueProbability Q d j t) +
    1/4*(∑ t ∈ Finset.range d, (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t)*c)) =
        c*(majorantSum Q B d j:ℝ)
  simp_rw [hs]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_residue_permutation hd hj (fun u => (majorant Q B d j u:ℝ))]
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  ring

lemma third_mode_mass {n Q B d j : ℕ} (hB : 0 < B) :
    thirdModeMass n Q B d j =
      (modeRemainder n (prescribedMass d) (majorantSum Q B d j):ℝ) := by
  have hB' : (B:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  unfold thirdModeMass
  field_simp

/-- The exact mass per reduced label, including the d=1, j=0 boundary case. -/
lemma three_mode_mass {n Q B d j : ℕ} (hB : 0 < B) (hd : 0 < d)
    (hj : Nat.Coprime j d) :
    firstModeMass n Q B d j + secondModeMass n Q B d j + thirdModeMass n Q B d j =
      (prescribedMass d:ℝ) := by
  rw [first_second_mass hB hd hj, third_mode_mass hB]
  simp only [modeRemainder, Rat.cast_sub, Rat.cast_mul]
  ring

lemma largeQ_cube (B : ℕ) (hB : 2 ≤ B) : 256*B^3 ≤ B^16 := by
  have h : 256 ≤ B^13 := (by norm_num : 256 ≤ (2:ℕ)^13).trans (Nat.pow_le_pow_left hB 13)
  calc
    _ ≤ B^13*B^3 := Nat.mul_le_mul_right (B^3) h
    _ = _ := by rw [← pow_add]

/-- The artificial discrepancy is a valid probability even at false labels. -/
lemma discrepancy_retention_bounds {B d t : ℕ} (hB : 2 ≤ B) (hd : 0 < d)
    (hdB : d < B) (ht : t < d) (j : ℕ) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    0 ≤ 2*(B:ℝ)^3*((majorant (B^16) B d j ((j*t)%d):ℝ)-
      residueProbability (B^16) d j t)*c ∧
    2*(B:ℝ)^3*((majorant (B^16) B d j ((j*t)%d):ℝ)-
      residueProbability (B^16) d j t)*c ≤ 1 := by
  have hB₀ : 0 < B := by omega
  have hQ₀ : 0 < B^16 := pow_pos hB₀ _
  have hBQ : B ≤ B^16 := (by omega : B ≤ 65*B).trans (largeQ B hB)
  have he := majorant_probability_error hB hd hdB.le (hdB.le.trans hBQ) ht j
  have he₀ : 0 ≤ (majorant (B^16) B d j ((j*t)%d):ℝ)-residueProbability (B^16) d j t :=
    (by positivity : (0:ℝ) ≤ 32/(B^16:ℕ)).trans he.1
  have hq : (256:ℝ)*(B:ℝ)^3 ≤ (B:ℝ)^16 := by exact_mod_cast largeQ_cube B hB
  have hq₀ : (0:ℝ) < (B:ℝ)^16 := by positivity
  have he₁ : (majorant (B^16) B d j ((j*t)%d):ℝ)-residueProbability (B^16) d j t ≤
      128/(B:ℝ)^16 := by
    refine he.2.trans ?_
    simp only [Nat.cast_pow]
    exact div_le_div_of_nonneg_right (by norm_num) hq₀.le
  constructor
  · positivity
  calc
    _ ≤ 2*(B:ℝ)^3*(128/(B:ℝ)^16)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left he₁ (by positivity)) hc₁ hc₀ (by positivity)
    _ = 256*(B:ℝ)^3/(B:ℝ)^16 := by ring
    _ ≤ 1 := (div_le_one hq₀).mpr hq

lemma remainder_retention_bounds {n : ℕ} (hn : 1 ≤ n) {rho : ℝ}
    (hr₀ : 0 ≤ rho) (hr₁ : rho ≤ 2/(2:ℝ)^(10*n)) :
    0 ≤ 4*((2:ℝ)^n)^2*rho ∧ 4*((2:ℝ)^n)^2*rho ≤ 1 := by
  have h : (8:ℝ) ≤ 2^(8*n) := by
    calc
      _ ≤ (2:ℝ)^8 := by norm_num
      _ ≤ 2^(8*n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : (2:ℝ)^(10*n) = ((2:ℝ)^n)^2*2^(8*n) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  constructor
  · positivity
  calc
    _ ≤ 4*((2:ℝ)^n)^2*(2/(2:ℝ)^(10*n)) :=
      mul_le_mul_of_nonneg_left hr₁ (by positivity)
    _ = 8/(2:ℝ)^(8*n) := by
      rw [he]
      field_simp
      norm_num
    _ ≤ 1 := (div_le_one (by positivity)).mpr h

end ExactQuantumFactoring.OrderTrial



end

end OAI
