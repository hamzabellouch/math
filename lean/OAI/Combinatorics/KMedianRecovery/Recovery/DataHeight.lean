import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BoundRow

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

def dataHeight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : ℕ :=
  B+1+∑ r, ((b r).natAbs+∑ j, (A r j).natAbs)

lemma dataHeight_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    B+1≤dataHeight A b B ∧ (∀ r j, |A r j|≤(dataHeight A b B:ℤ)) ∧
      (∀ r, |b r|≤(dataHeight A b B:ℤ)) := by
  have hr (r : Fin m) : (b r).natAbs+∑ j, (A r j).natAbs≤dataHeight A b B := by
    have hh := Finset.single_le_sum (f:=fun r => (b r).natAbs+∑ j, (A r j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    exact hh.trans (Nat.le_add_left _ _)
  refine ⟨Nat.le_add_right _ _,?_,?_⟩
  · intro r j
    have hj := Finset.single_le_sum (f:=fun j => (A r j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hh : (A r j).natAbs≤dataHeight A b B := hj.trans ((Nat.le_add_left _ _).trans (hr r))
    rw [←Int.natCast_natAbs]
    exact_mod_cast hh
  · intro r
    have hh : (b r).natAbs≤dataHeight A b B := (Nat.le_add_right _ _).trans (hr r)
    rw [←Int.natCast_natAbs]
    exact_mod_cast hh

def padMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin (n+2)) ℤ :=
  fun r => Fin.append (A r) (fun _ : Fin 2 => 0)

lemma padMatrix_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (r : Fin m) (y : Fin (n+2) → ℝ) :
    (∑ j, (padMatrix A r j:ℝ)*y j)=∑ j, (A r j:ℝ)*y (Fin.castAdd 2 j) := by
  rw [Fin.sum_univ_add]
  simp [padMatrix]

lemma pad_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    (∃ y : Fin (n+2) → ℝ, (∀ r, (∑ j, (padMatrix A r j:ℝ)*y j)≤(b r:ℝ)) ∧
      (∀ j, |y j|≤(B:ℝ))) ↔
    ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  constructor
  · rintro ⟨y,hy,hbox⟩
    refine ⟨fun i => y (Fin.castAdd 2 i),?_,fun i => hbox _⟩
    intro r
    simpa only [padMatrix_sum] using hy r
  · rintro ⟨x,hx,hbox⟩
    refine ⟨Fin.append x (fun _ : Fin 2 => 0),?_,?_⟩
    · intro r
      simpa only [padMatrix_sum,Fin.append_left] using hx r
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [Fin.append_left] using hbox i
      · simp

def boundedIntegerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : Bool :=
  integerDecide (padMatrix A) b B (dataHeight (padMatrix A) b B)

theorem boundedIntegerDecide_correct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    boundedIntegerDecide A b B=true ↔
      ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  have hh := dataHeight_bounds (padMatrix A) b B
  exact (integerDecide_correct (padMatrix A) b B _ (by omega) hh.1 hh.2.1 hh.2.2).trans
    (pad_feasible A b B)

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped BigOperators
variable {J R V : Type*} [Fintype J] [DecidableEq J] [Fintype R] [Fintype V] [DecidableEq V]

def rowDenominator (q : J → ℚ) : ℤ := ∏ i, ((q i).den:ℤ)
def rowNumerator (q : J → ℚ) (i : J) : ℤ :=
  (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ)

omit [DecidableEq J] in
lemma rowDenominator_pos (q : J → ℚ) : 0 < rowDenominator q := by
  apply Finset.prod_pos
  intro i _
  exact_mod_cast (q i).den_pos

lemma rowNumerator_cast (q : J → ℚ) (i : J) :
    (rowNumerator q i:ℝ)=(rowDenominator q:ℝ)*(q i:ℝ) := by
  have hh : rowDenominator q = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den:ℤ)) (Finset.mem_univ i)).symm
  rw [hh,Rat.cast_def]
  unfold rowNumerator
  push_cast
  have hn : ((q i).den:ℝ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  field_simp

end MetricKMedianRecovery.PolytopeCertificate
namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

def rowEntries {n : ℕ} (q : Row n) : Option (Fin n) → ℚ := Option.elim' q.bound q.coeff

def clearedMatrix {n : ℕ} (rows : List (Row n)) : Matrix (Fin rows.length) (Fin n) ℤ :=
  fun r j => rowNumerator (rowEntries rows[r]) (some j)

def clearedBounds {n : ℕ} (rows : List (Row n)) : Fin rows.length → ℤ :=
  fun r => rowNumerator (rowEntries rows[r]) none

lemma clearRow_holds {n : ℕ} (q : Row n) (x : Fin n → ℝ) :
    (∑ j, (rowNumerator (rowEntries q) (some j):ℝ)*x j)≤
      (rowNumerator (rowEntries q) none:ℝ) ↔ q.RealHolds x := by
  simp only [rowNumerator_cast,mul_assoc,←Finset.mul_sum]
  have hp : (0:ℝ)<(rowDenominator (rowEntries q):ℝ) := by exact_mod_cast rowDenominator_pos (rowEntries q)
  exact mul_le_mul_iff_right₀ hp

lemma clearedRows_holds {n : ℕ} (rows : List (Row n)) (x : Fin n → ℝ) :
    (∀ r, (∑ j, (clearedMatrix rows r j:ℝ)*x j)≤(clearedBounds rows r:ℝ)) ↔
      ∀ q∈rows, q.RealHolds x := by
  simp only [clearedMatrix,clearedBounds,clearRow_holds]
  constructor
  · intro h q hq
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hq
    have hh : rows[i].RealHolds x := h ⟨i,hi⟩
    rwa [he] at hh
  · intro h i
    exact h _ (List.getElem_mem _)

def boundedRationalDecide {n : ℕ} (rows : List (Row n)) (B : ℕ) : Bool :=
  boundedIntegerDecide (clearedMatrix rows) (clearedBounds rows) B

theorem boundedRationalDecide_correct {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    boundedRationalDecide rows B=true ↔
      ∃ x : Fin n → ℝ, (∀ q∈rows, q.RealHolds x) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  rw [boundedRationalDecide,boundedIntegerDecide_correct]
  exact exists_congr (fun x => and_congr_left (fun _ => clearedRows_holds rows x))

end MetricKMedianRecovery.Ellipsoid

end OAI
