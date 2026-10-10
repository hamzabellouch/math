import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialState
import OAI.Combinatorics.KMedianRecovery.Recovery.BoundedMinimizingExtreme

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

abbrev BoundRow (m n : ℕ) := Fin m ⊕ (Bool × Fin n)

def boundedMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (BoundRow m n) (Fin n) ℤ
  | .inl r,j => A r j
  | .inr (s,i),j => if j=i then if s then 1 else -1 else 0

def boundedBounds {m n : ℕ} (b : Fin m → ℤ) (B : ℕ) : BoundRow m n → ℤ
  | .inl r => b r
  | .inr _ => B

def integerRow {n : ℕ} (a : Fin n → ℤ) (b : ℤ) : Row n := ⟨fun j => a j,b⟩

def boundedRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : List (Row n) :=
  List.ofFn (fun r => integerRow (A r) (b r)) ++
  List.ofFn (fun i => integerRow (boundedMatrix A (.inr (true,i))) B) ++
  List.ofFn (fun i => integerRow (boundedMatrix A (.inr (false,i))) B)

lemma boundedRows_all {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ)
    (P : Row n → Prop) : (∀ q∈boundedRows A b B, P q) ↔
      ∀ r, P (integerRow (boundedMatrix A r) (boundedBounds b B r)) := by
  constructor
  · intro h r
    apply h
    simp only [boundedRows,List.mem_append,List.mem_ofFn]
    cases r with
    | inl r => exact Or.inl (Or.inl ⟨r,rfl⟩)
    | inr p =>
      rcases p with ⟨s,i⟩
      cases s
      · exact Or.inr ⟨i,rfl⟩
      · exact Or.inl (Or.inr ⟨i,rfl⟩)
  · intro h q hq
    simp only [boundedRows,List.mem_append,List.mem_ofFn] at hq
    rcases hq with ((⟨r,rfl⟩ | ⟨i,rfl⟩) | ⟨i,rfl⟩)
    · exact h (.inl r)
    · exact h (.inr (true,i))
    · exact h (.inr (false,i))

lemma bounded_region {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (B : ℕ) (x : Fin n → ℝ) :
    x∈region (fun r j => (boundedMatrix A r j:ℝ)) (fun r => (boundedBounds b B r:ℝ)) ↔
      (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  have he (s : Bool) (i : Fin n) :
      (∑ j, (boundedMatrix A (.inr (s,i)) j:ℝ)*x j)=if s then x i else -x i := by
    cases s <;> simp [boundedMatrix]
  constructor
  · intro hh
    refine ⟨fun r => hh (.inl r),fun i => abs_le.mpr ?_⟩
    have hp := hh (.inr (true,i))
    have hm := hh (.inr (false,i))
    rw [he] at hp hm
    exact ⟨by
      have hh : -x i≤(B:ℝ) := by simpa [boundedBounds] using hm
      linarith,by simpa [boundedBounds] using hp⟩
  · rintro ⟨ha,hb⟩ r
    cases r with
    | inl r => exact ha r
    | inr p =>
      rcases p with ⟨s,i⟩
      rw [he]
      cases s
      · change -x i≤(B:ℝ)
        linarith [(abs_le.mp (hb i)).1]
      · exact (abs_le.mp (hb i)).2

lemma rows_real_region {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ)
    (x : Fin n → ℝ) : (∀ q∈boundedRows A b B, q.RealHolds x) ↔
      x∈region (fun r j => (boundedMatrix A r j:ℝ)) (fun r => (boundedBounds b B r:ℝ)) := by
  rw [boundedRows_all]
  simp only [integerRow,Row.RealHolds,Row.realValue,Rat.cast_intCast,region,Set.mem_ofPred_eq]

lemma bounded_data_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (B H : ℕ) (hBH : B+1≤H) (hA : ∀ r j, |A r j|≤(H:ℤ)) (hb : ∀ r, |b r|≤(H:ℤ)) :
    (∀ r j, |boundedMatrix A r j|≤(H:ℤ)) ∧ (∀ r, |boundedBounds (n:=n) b B r|≤(H:ℤ)) := by
  have hH : (1:ℤ)≤H := by exact_mod_cast (show 1≤H by omega)
  constructor
  · intro r j
    cases r with
    | inl r => exact hA r j
    | inr p =>
      rcases p with ⟨s,i⟩
      simp only [boundedMatrix]
      split_ifs <;> simp only [abs_one,abs_neg,abs_zero] <;> omega
  · intro r
    cases r with
    | inl r => exact hb r
    | inr p =>
      change |(B:ℤ)|≤(H:ℤ)
      simpa only [Int.natCast_nonneg,abs_of_nonneg] using
        (show (B:ℤ)≤(H:ℤ) by exact_mod_cast (show B≤H by omega))

def gapDenominator (m n H : ℕ) : ℕ :=
  (n+1).factorial*((m+2*n+2*(n+1))*H^2)^(n+1)

def gapEpsilon (m n H : ℕ) : ℚ := 1/(2*(gapDenominator m n H:ℚ))

def precisionLog (m n H : ℕ) : ℕ := Nat.log2 (2*gapDenominator m n H*H)+1

def radiusLog (n B : ℕ) : ℕ := Nat.log2 (n*(B+1))+1

def integerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : Bool :=
  (weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B))
    ((n:ℚ)*(B+1)) (precisionLog m n H) (radiusLog n B)).isSome

lemma gapDenominator_pos (m n H : ℕ) (hH : 1≤H) : 0<gapDenominator m n H := by
  unfold gapDenominator
  apply Nat.mul_pos (Nat.factorial_pos _)
  apply pow_pos
  exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

lemma gapEpsilon_bounds (m n H : ℕ) (hH : 1≤H) :
    0<gapEpsilon m n H ∧ gapEpsilon m n H≤1 ∧
      gapEpsilon m n H<1/(gapDenominator m n H:ℚ) := by
  have hQ : (1:ℚ)≤gapDenominator m n H := by exact_mod_cast gapDenominator_pos m n H hH
  have hpos : (0:ℚ)<gapDenominator m n H := by linarith
  refine ⟨by exact div_pos (by norm_num) (mul_pos (by norm_num) hpos),?_,?_⟩
  · exact (div_le_one (by positivity)).mpr (by nlinarith)
  · apply one_div_lt_one_div_of_lt hpos
    nlinarith

lemma gapDenominator_cast (m n B H : ℕ) (hBH : B+1≤H) :
    ((Fintype.card (Option (Fin n))).factorial *
      ((Fintype.card (SlackRow (BoundRow m n) (Fin n)):ℤ)*(max (H:ℤ) (B+1))^2)^
        (Fintype.card (Option (Fin n))) : ℤ)=(gapDenominator m n H:ℤ) := by
  have hh : max (H:ℤ) (B+1)=H := max_eq_left (by exact_mod_cast hBH)
  simp only [Fintype.card_option,Fintype.card_fin,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_bool,SlackRow,BoundRow,hh,gapDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]

lemma precisionLog_bound (m n H : ℕ) (hH : 1≤H) :
    (H:ℚ)/gapEpsilon m n H≤(2:ℚ)^(precisionLog m n H) := by
  have hh : (2*gapDenominator m n H*H:ℕ)<2^(precisionLog m n H) := Nat.lt_log2_self
  have hcast : (2:ℚ)*(gapDenominator m n H)*H≤(2:ℚ)^(precisionLog m n H) := by exact_mod_cast hh.le
  have hQ : (gapDenominator m n H:ℚ)≠0 := by exact_mod_cast (gapDenominator_pos m n H hH).ne'
  convert hcast using 1
  dsimp only [gapEpsilon]
  field_simp

lemma radiusLog_bound (n B : ℕ) : (n:ℚ)*(B+1)≤(2:ℚ)^(radiusLog n B) := by
  exact_mod_cast (Nat.lt_log2_self (n:=n*(B+1))).le

theorem integerDecide_correct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (B H : ℕ) (hn : 2≤n) (hBH : B+1≤H) (hA : ∀ r j, |A r j|≤(H:ℤ)) (hb : ∀ r, |b r|≤(H:ℤ)) :
    integerDecide A b B H=true ↔
      ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  have hH : 1≤H := by omega
  have heps := gapEpsilon_bounds m n H hH
  have hdata := bounded_data_bound A b B H hBH hA hb
  constructor
  · intro hyes
    obtain ⟨c,hc⟩ := Option.isSome_iff_exists.mp hyes
    have hrows := weakSolve_sound _ _ _ _ c hc
    have ha : ∀ r, (∑ j, (boundedMatrix A r j:ℝ)*(c j:ℝ))≤
        (boundedBounds b B r:ℝ)+(gapEpsilon m n H:ℝ) := by
      have hall : ∀ q∈boundedRows A b B, (relaxedRow (gapEpsilon m n H) q).Holds c := by
        intro q hq
        exact hrows _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
      have hh := (boundedRows_all A b B _).mp hall
      intro r
      have ht := (Row.realHolds_cast _ c).mpr (hh r)
      simpa only [relaxedRow,integerRow,Row.RealHolds,Row.realValue,Rat.cast_intCast,Rat.cast_add] using ht
    have hcbox : ∀ j, -((B+1:ℕ):ℝ)≤(c j:ℝ) ∧ (c j:ℝ)≤((B+1:ℕ):ℝ) := by
      intro j
      have hp := ha (.inr (true,j))
      have hm := ha (.inr (false,j))
      simp only [boundedMatrix,boundedBounds] at hp hm
      simp at hp hm
      have hepr : (gapEpsilon m n H:ℝ)≤1 := by exact_mod_cast heps.2.1
      push_cast
      constructor <;> linarith
    obtain ⟨y,hy,_⟩ := approximate_implies_feasible (boundedMatrix A) (boundedBounds b B)
      (B+1) H (by positivity) (by exact_mod_cast hH) hdata.1 hdata.2 (gapEpsilon m n H:ℝ)
      (by exact_mod_cast heps.1.le) (by exact_mod_cast (heps.2.1.trans (by exact_mod_cast hH : (1:ℚ)≤H)))
      (by
        rw [gapDenominator_cast m n B H hBH]
        have hh := (Rat.cast_lt (K:=ℝ)).mpr heps.2.2
        simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Int.cast_natCast] using hh) (fun j => (c j:ℝ))
      (by simpa only [Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_natCast,Int.cast_one] using hcbox) ha
    exact ⟨y,(bounded_region A b B y).mp hy⟩
  · rintro ⟨x,hx,hbox⟩
    have hcoeff : ∀ q∈boundedRows A b B, ∀ j, |q.coeff j|≤(H:ℚ) := by
      refine (boundedRows_all A b B (fun q => ∀ j, |q.coeff j|≤(H:ℚ))).mpr ?_
      intro r j
      change |((boundedMatrix A r j:ℤ):ℚ)|≤(H:ℚ)
      exact_mod_cast hdata.1 r j
    obtain ⟨c,hc⟩ := weakSolve_complete (boundedRows A b B) hn B H (gapEpsilon m n H)
      (by positivity) (by exact_mod_cast hH) heps.1 heps.2.1 (precisionLog m n H) (radiusLog n B)
      (radiusLog_bound n B) (precisionLog_bound m n H hH) hcoeff x
      ((rows_real_region A b B x).mpr ((bounded_region A b B x).mpr ⟨hx,hbox⟩))
      (by exact_mod_cast hbox)
    exact Option.isSome_iff_exists.mpr ⟨c,hc⟩

end MetricKMedianRecovery.Ellipsoid

end OAI
