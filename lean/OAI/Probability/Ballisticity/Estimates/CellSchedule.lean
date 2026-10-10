import Mathlib
import OAI.Probability.Ballisticity.Estimates.Cell

namespace OAI

section

open scoped BigOperators
namespace DirectionalTransience

def cellWidth (w m i : ℕ) : ℕ := 16^(m-i)*w

def cellOpportunity (v w m i : ℕ) : ℕ :=
  if i < m then v-2*cellWidth w m i else v+w

lemma cellWidth_zero (w m : ℕ) : cellWidth w m 0=16^m*w := by simp [cellWidth]
lemma cellWidth_last (w m : ℕ) : cellWidth w m m=w := by simp [cellWidth]
lemma cellWidth_antitone (w m : ℕ) : Antitone (cellWidth w m) := by
  intro i j hij
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hij m)
lemma cellWidth_pos {w : ℕ} (hw : 0 < w) (m i : ℕ) : 0 < cellWidth w m i := by
  unfold cellWidth; positivity
lemma cellWidth_min (w m i : ℕ) : w ≤ cellWidth w m i := by
  unfold cellWidth
  have h : 1 ≤ 16^(m-i) := one_le_pow₀ (by norm_num)
  simpa only [one_mul] using Nat.mul_le_mul_right w h
lemma cellWidth_step (w m i : ℕ) (hi : i < m) :
    cellWidth w m i=16*cellWidth w m (i+1) := by
  have he : m-i=(m-(i+1))+1 := by omega
  unfold cellWidth
  rw [he,pow_succ]
  ring
lemma cellWidth_shift (w m i j : ℕ) (hij : i+j ≤ m) :
    cellWidth w m i=16^j*cellWidth w m (i+j) := by
  have he : m-i=j+(m-(i+j)) := by omega
  unfold cellWidth
  rw [he,pow_add]
  ring
lemma cellOpportunity_last (v w m : ℕ) : cellOpportunity v w m m=v+w := by
  simp [cellOpportunity]
lemma cellOpportunity_le_end (v w m i : ℕ) : cellOpportunity v w m i ≤ v+w := by
  unfold cellOpportunity
  split
  · omega
  · rfl
lemma cellOpportunity_monotone (v w m : ℕ) : Monotone (cellOpportunity v w m) := by
  intro i j hij
  by_cases hj : j < m
  · have hi : i < m := lt_of_le_of_lt hij hj
    simp only [cellOpportunity,ite_eq_left hi,ite_eq_left hj]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 (cellWidth_antitone w m hij)) v
  · simp only [cellOpportunity,ite_eq_right hj]
    exact cellOpportunity_le_end v w m i

lemma cell_seed_endpoint (v w m i : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hi : i < m) :
    cellOpportunity v w m i+cellWidth w m i=v-cellWidth w m i := by
  have hw := Nat.mul_le_mul_left 2 (cellWidth_antitone w m (Nat.zero_le i))
  simp only [cellOpportunity,ite_eq_left hi]
  omega

lemma cell_seed_before_next (v w m i : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hi : i < m) :
    cellOpportunity v w m i+cellWidth w m i ≤ cellOpportunity v w m (i+1) := by
  rw [cell_seed_endpoint v w m i hv hi]
  by_cases hn : i+1 < m
  · simp only [cellOpportunity,ite_eq_left hn]
    apply Nat.sub_le_sub_left
    rw [cellWidth_step w m i hi]
    omega
  · simp only [cellOpportunity,ite_eq_right hn]
    omega

lemma cell_step_length (v w m i : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hi : i < m) :
    cellOpportunity v w m (i+1)-cellOpportunity v w m i ≤ 3*cellWidth w m i := by
  have hw := Nat.mul_le_mul_left 2 (cellWidth_antitone w m (Nat.zero_le i))
  have hmin := cellWidth_min w m i
  have hend := cellOpportunity_le_end v w m (i+1)
  simp only [cellOpportunity,ite_eq_left hi]
  split <;> omega

def cellEarlyHeight (v w m i s : ℕ) : ℕ :=
  cellOpportunity v w m (i+min s (m-i))-(cellOpportunity v w m i+cellWidth w m i)

def cellLateHeight (v w m i s j : ℕ) : ℕ :=
  if i+s+j < m then
    cellOpportunity v w m (i+s+j+1)-cellOpportunity v w m (i+s+j) else 0

lemma cellEarly_endpoint (v w m i s : ℕ) (hv : 2*cellWidth w m 0 ≤ v)
    (hi : i < m) (hs : 0 < s) :
    cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s=
      cellOpportunity v w m (i+min s (m-i)) := by
  unfold cellEarlyHeight
  have hmin : 1 ≤ min s (m-i) := by omega
  have hh := cellOpportunity_monotone v w m (show i+1 ≤ i+min s (m-i) by omega)
  have ht := cell_seed_before_next v w m i hv hi
  omega

lemma cellEarlyHeight_bound (v w m i s : ℕ) (hv : 2*cellWidth w m 0 ≤ v)
    (hi : i < m) : cellEarlyHeight v w m i s ≤ 3*cellWidth w m i := by
  unfold cellEarlyHeight
  rw [cell_seed_endpoint v w m i hv hi]
  have hmin := cellWidth_min w m i
  have hh := cellOpportunity_le_end v w m (i+min s (m-i))
  have hw := Nat.mul_le_mul_left 2 (cellWidth_antitone w m (Nat.zero_le i))
  omega

lemma cellLateHeight_bound (v w m i s j : ℕ) (hv : 2*cellWidth w m 0 ≤ v) :
    cellLateHeight v w m i s j*16^(s+j) ≤ 3*cellWidth w m i := by
  unfold cellLateHeight
  split
  · rename_i h
    have hh := Nat.mul_le_mul_right (16^(s+j)) (cell_step_length v w m (i+s+j) hv h)
    have he := cellWidth_shift w m i (s+j) (by omega)
    calc
      _ ≤ 3*cellWidth w m (i+(s+j))*16^(s+j)  := by simpa only [Nat.add_assoc] using hh
      _ = 3*cellWidth w m i := by rw [he]; ring
  · simp

lemma cellLate_endpoint (v w m i s n : ℕ) (_ : 2*cellWidth w m 0 ≤ v)
    (hn : i+s+n ≤ m) :
    cellOpportunity v w m (i+s)+(∑ j∈Finset.range n,cellLateHeight v w m i s j)=
      cellOpportunity v w m (i+s+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hin : i+s+n < m := by omega
    have hp := ih (by omega)
    rw [Finset.sum_range_succ,←Nat.add_assoc,hp]
    simp only [cellLateHeight,ite_eq_left hin]
    have hh := cellOpportunity_monotone v w m (show i+s+n ≤ i+s+n+1 by omega)
    have he : i+s+(n+1)=i+s+n+1 := by omega
    rw [he]
    omega

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def cellRadius {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (C : ℝ) (w m i : ℕ) : ℝ :=
  fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) ((cellWidth w m i:ℝ)/C)

lemma cellRadius_pos {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (C : ℝ) (w m i : ℕ) : 0 < cellRadius ν e f C w m i := fluctuationRadius_pos _ _ _

noncomputable def cellRestart {d k : ℕ} (e : Direction d) (a : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (v w m i : ℕ)
    (ω : Environment d) : LayerTupleProfile (k:=k) e (a+cellOpportunity v w m i) :=
  fullTupleProfile e a (cellOpportunity v w m i) (π ω) ω

lemma cellRestart_measurable {d k : ℕ} (e : Direction d) (a : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (v w m i : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+cellOpportunity v w m i))) _
      (cellRestart e a π v w m i) := fullTupleProfile_measurable e a _ π hπ

noncomputable def scheduledCellFailure {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (v w m s i n : ℕ) : Set (Environment d) :=
  if i < m ∧ 0 < n ∧ n ≤ m-i then
    consumedCellFailure
      (cellSeedMass e f (a+cellOpportunity v w m i) (c*cellRadius ν e f C w m i)
        (cellWidth w m i) (cellRestart e a π v w m i))
      (cellEarlyMass e f hef (a+cellOpportunity v w m i) (c*cellRadius ν e f C w m i)
        (cellWidth w m i) (cellEarlyHeight v w m i s) (cellRestart e a π v w m i))
      (cellLateMass e f hef (a+cellOpportunity v w m i) c (cellRadius ν e f C w m i)
        hc (cellRadius_pos ν e f C w m i) (cellWidth w m i) (cellEarlyHeight v w m i s) s
        (cellLateHeight v w m i s) (cellRestart e a π v w m i)) g₀ g₁ (A*k) s (m-i) n
  else ∅

def cellFiltration {d : ℕ} (e : Direction d) (a : ℝ) (v w m : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Environment d)) where
  seq i := rowSigma (BelowHeight (realPosition (step e)) (a+cellOpportunity v w m i))
  mono' i j hij := by
    have hh : (cellOpportunity v w m i : ℝ) ≤ cellOpportunity v w m j :=
      by exact_mod_cast cellOpportunity_monotone v w m hij
    apply rowSigma_mono
    intro x hx
    change dot (realPosition x) (realPosition (step e)) < a+cellOpportunity v w m i at hx
    change dot (realPosition x) (realPosition (step e)) < a+cellOpportunity v w m j
    linarith only [hx,hh]
  le' _ := rowSigma_le _

lemma scheduledCellFailure_measurable {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (v w m s : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hs : 0 < s) (i n : ℕ) :
    MeasurableSet[cellFiltration e a v w m (i+n)]
      (scheduledCellFailure ν e f hef a C c g₀ g₁ A hc π v w m s i n) := by
  unfold scheduledCellFailure
  split
  · rename_i h
    rcases h with ⟨hi,hn,hnm⟩
    change MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+cellOpportunity v w m (i+n)))] _
    apply actual_cell_failure_measurable e f hef _ c _ hc _ _ _ s (m-i) n _ _
      (cellRestart_measurable e a π hπ v w m i) g₀ g₁ A (a+cellOpportunity v w m (i+n))
    · intro _
      have hh := (cell_seed_before_next v w m i hv hi).trans
        (cellOpportunity_monotone v w m (show i+1 ≤ i+n by omega))
      have hh' : (cellOpportunity v w m i:ℝ)+cellWidth w m i ≤ cellOpportunity v w m (i+n) :=
        by exact_mod_cast hh
      linarith only [hh']
    · intro h
      have hmin : min s (m-i) ≤ n := by rcases h with h|⟨h,_⟩ <;> omega
      have hh := cellOpportunity_monotone v w m (show i+min s (m-i) ≤ i+n by omega)
      rw [←cellEarly_endpoint v w m i s hv hi hs] at hh
      have hh' : (cellOpportunity v w m i:ℝ)+cellWidth w m i+cellEarlyHeight v w m i s ≤
          cellOpportunity v w m (i+n) := by exact_mod_cast hh
      linarith only [hh']
    · intro hsn hnm'
      have hmin : min s (m-i)=s := min_eq_left (by omega)
      have hearly := cellEarly_endpoint v w m i s hv hi hs
      rw [hmin] at hearly
      have hlate := cellLate_endpoint v w m i s (n-s) hv (by omega)
      have heq : i+s+(n-s)=i+n := by omega
      rw [heq,←hearly] at hlate
      have hh : (cellOpportunity v w m i:ℝ)+cellWidth w m i+cellEarlyHeight v w m i s+
          ((∑ j∈Finset.range (n-s),cellLateHeight v w m i s j):ℕ)=cellOpportunity v w m (i+n) :=
        by exact_mod_cast hlate
      linarith only [hh]
  · exact @MeasurableSet.empty _ (cellFiltration e a v w m (i+n))

end DirectionalTransience

end

end OAI
