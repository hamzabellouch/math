import OAI.Combinatorics.LowSpaceSubsetSum.Search.MainGuard
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedModulusExecution

namespace OAI

/-! # Executed input descriptor and main-branch guard

An indexed tail scan computes the maximum original input word. Two doubling
cursors then compute the input bit length and the guard's ceiling logarithm.
The original input is read-only throughout.
-/

namespace LowSpaceSubsetSum.WordInputDescriptor

variable {n : ℕ}

def maximumLoop (I : Instance n) : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | 0, _, top, work, peak => ((top,work+1),max peak 12)
  | fuel+1, cursor, top, work, peak =>
      if h : cursor < n then
        maximumLoop I fuel (cursor+1) (max top (I.values ⟨cursor,h⟩))
          (work+6) (max peak 12)
      else ((top,work+1),max peak 12)

theorem maximumLoop_upper (I : Instance n) (fuel cursor top work peak M : ℕ)
    (htop : top ≤ M) (hI : ∀ i, I.values i ≤ M) :
    (maximumLoop I fuel cursor top work peak).1.1 ≤ M := by
  induction fuel generalizing cursor top work peak with
  | zero => exact htop
  | succ fuel ih =>
    rw [maximumLoop]
    split
    · exact ih _ _ _ _ (max_le htop (hI _))
    · exact htop

theorem maximumLoop_lower (I : Instance n) (fuel cursor top work peak : ℕ)
    (hbound : cursor+fuel ≤ n) :
    top ≤ (maximumLoop I fuel cursor top work peak).1.1 ∧
      ∀ i : Fin n, cursor ≤ i.val → i.val < cursor+fuel →
        I.values i ≤ (maximumLoop I fuel cursor top work peak).1.1 := by
  induction fuel generalizing cursor top work peak with
  | zero => exact ⟨le_rfl,fun i hi hj => by omega⟩
  | succ fuel ih =>
    have hc : cursor < n := by omega
    simp only [maximumLoop, dite_eq_left hc]
    have h := ih (cursor+1) (max top (I.values ⟨cursor,hc⟩))
      (work+6) (max peak 12) (by omega)
    refine ⟨(le_max_left _ _).trans h.1,?_⟩
    intro i hi hj
    by_cases he : i.val = cursor
    · have hfin : i = ⟨cursor,hc⟩ := Fin.ext he
      subst i
      exact (le_max_right _ _).trans h.1
    · exact h.2 i (by omega) (by omega)

theorem maximumLoop_work (I : Instance n) (fuel cursor top work peak : ℕ)
    (hbound : cursor+fuel ≤ n) :
    (maximumLoop I fuel cursor top work peak).1.2 = work+6*fuel+1 := by
  induction fuel generalizing cursor top work peak with
  | zero => simp only [maximumLoop,Nat.mul_zero,Nat.add_zero]
  | succ fuel ih =>
    have hc : cursor < n := by omega
    simp only [maximumLoop,dite_eq_left hc]
    rw [ih _ _ _ _ (by omega)]
    omega

theorem maximumLoop_cells (I : Instance n) (fuel cursor top work peak : ℕ) :
    (maximumLoop I fuel cursor top work peak).2 ≤ max peak 12 := by
  induction fuel generalizing cursor top work peak with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [maximumLoop]
    split
    · simpa only [max_assoc,max_self] using ih (cursor+1) _ (work+6) (max peak 12)
    · exact le_rfl

def maximum (I : Instance n) : (ℕ × ℕ) × ℕ := maximumLoop I n 0 I.target 0 0

theorem maximum_value (I : Instance n) : (maximum I).1.1 = inputMaximum I := by
  apply le_antisymm
  · exact maximumLoop_upper I n 0 I.target 0 0 _ (le_max_left _ _) (fun i =>
      (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _))
  · have h := maximumLoop_lower I n 0 I.target 0 0 (by omega)
    apply max_le h.1
    exact Finset.sup_le (fun i _ => h.2 i (Nat.zero_le _) (by simp))

theorem maximum_work (I : Instance n) : (maximum I).1.2 = 6*n+1 := by
  simpa only [maximum,Nat.zero_add] using maximumLoop_work I n 0 I.target 0 0 (by omega)

theorem maximum_cells (I : Instance n) : (maximum I).2 ≤ 12 := by
  simpa only [maximum,Nat.zero_max] using maximumLoop_cells I n 0 I.target 0 0

structure Result where
  maximum : ℕ
  bits : ℕ
  scale : ℕ
  guardWidth : ℕ
  guard : Bool
  work : ℕ
  cells : ℕ

def run (T : ℕ) (I : Instance n) : Result :=
  let top := maximum I
  let bits := WordSeedModulusExecution.run (1+top.1.1)
  let b := max 1 bits.width
  let u := n+b+2
  let guardBits := WordSeedModulusExecution.run u
  ⟨top.1.1,b,u,guardBits.width,
    decide (T ≤ n ∧ guardBits.width ≤ n/1000000000),
    top.1.2+bits.work+guardBits.work+18,max top.2 40⟩

theorem run_maximum (T : ℕ) (I : Instance n) : (run T I).maximum = inputMaximum I := by
  exact maximum_value I

theorem run_bits (T : ℕ) (I : Instance n) : (run T I).bits = inputBits I := by
  simp only [run,maximum_value,WordSeedModulusExecution.run_width,inputBits]

theorem run_scale (T : ℕ) (I : Instance n) : (run T I).scale = inputScale I := by
  change n+(run T I).bits+2 = inputScale I
  rw [run_bits,inputScale]

theorem run_guardWidth (T : ℕ) (I : Instance n) :
    (run T I).guardWidth = Nat.clog 2 (inputScale I) := by
  change (WordSeedModulusExecution.run (run T I).scale).width = _
  rw [WordSeedModulusExecution.run_width,run_scale]

theorem run_guard (T : ℕ) (I : Instance n) :
    (run T I).guard = mainGuard T n (inputScale I) := by
  change decide (T ≤ n ∧ (run T I).guardWidth ≤ n/1000000000) = _
  rw [run_guardWidth]
  rfl

theorem run_work_exact (T : ℕ) (I : Instance n) :
    (run T I).work = 6*n+5*Nat.clog 2 (1+inputMaximum I)+
      5*Nat.clog 2 (inputScale I)+21 := by
  change (maximum I).1.2+(WordSeedModulusExecution.run (1+(maximum I).1.1)).work+
    (WordSeedModulusExecution.run (run T I).scale).work+18 = _
  rw [maximum_work,maximum_value,run_scale,WordSeedModulusExecution.run_work,
    WordSeedModulusExecution.run_work]
  omega

theorem run_work (T : ℕ) (I : Instance n) : (run T I).work ≤ 100*inputScale I := by
  have hb : Nat.clog 2 (1+inputMaximum I) ≤ inputBits I := le_max_right _ _
  have hu : Nat.clog 2 (inputScale I) ≤ inputScale I :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hp := inputBits_pos I
  rw [run_work_exact]
  unfold inputScale at hu ⊢
  omega

theorem run_cells_small (T : ℕ) (I : Instance n) : (run T I).cells = 40 := by
  exact max_eq_right ((maximum_cells I).trans (by decide))

theorem run_cells (T : ℕ) (I : Instance n) : (run T I).cells ≤ 100*inputScale I := by
  rw [run_cells_small]
  unfold inputScale
  omega

end LowSpaceSubsetSum.WordInputDescriptor

end OAI
