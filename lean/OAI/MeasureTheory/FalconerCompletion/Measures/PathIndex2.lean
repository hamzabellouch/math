import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.AmbientGridCell2
import OAI.MeasureTheory.FalconerCompletion.Recursion.CellPath

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory
variable {d : ℕ}

def pathIndex : CellPath d → Fin d → ℕ
  | [] => fun _ => 0
  | b :: p => fun i => (if b i then 2^p.length else 0) + pathIndex p i

lemma pathIndex_lt (p : CellPath d) (i : Fin d) : pathIndex p i < 2^p.length := by
  induction p with
  | nil => simp [pathIndex]
  | cons b p ih =>
    simp only [pathIndex,List.length_cons,pow_succ]
    split <;> omega

lemma pathIndex_div_leading (b : Fin d → Bool) (p : CellPath d) (i : Fin d) :
    pathIndex (b::p) i / 2^p.length = if b i then 1 else 0 := by
  have hlt := pathIndex_lt p i
  have hpos : 0 < 2^p.length := by positivity
  simp only [pathIndex]
  split <;> simp [Nat.add_div_left,hpos, Nat.div_eq_of_lt hlt]

lemma pathIndex_injective {p q : CellPath d} (hlen : p.length = q.length)
    (he : pathIndex p = pathIndex q) : p = q := by
  induction p generalizing q with
  | nil => simpa using hlen.symm
  | cons b p ih =>
    cases q with
    | nil => simp at hlen
    | cons c q =>
      have hlen' : p.length = q.length := by simpa using hlen
      have hbc : b = c := by
        funext i
        have hh := congrArg (fun f : Fin d → ℕ => f i / 2^p.length) he
        rw [pathIndex_div_leading,hlen',pathIndex_div_leading] at hh
        cases hb : b i <;> cases hc : c i <;> simp [hb,hc] at hh ⊢
      subst c
      have ht : pathIndex p = pathIndex q := by
        funext i
        have hh := congrFun he i
        simp only [pathIndex,hlen'] at hh
        omega
      rw [ih hlen' ht]

lemma exists_pathIndex (N : ℕ) (a : Fin d → ℕ) (ha : ∀ i, a i < 2^N) :
    ∃ p : CellPath d, p.length = N ∧ pathIndex p = a := by
  induction N generalizing a with
  | zero =>
    refine ⟨[],rfl,?_⟩
    funext i
    have := ha i
    simp only [pow_zero] at this
    simp only [pathIndex]
    omega
  | succ N ih =>
    let b : Fin d → Bool := fun i => decide (2^N ≤ a i)
    let r : Fin d → ℕ := fun i => if 2^N ≤ a i then a i-2^N else a i
    have hr : ∀ i, r i < 2^N := by
      intro i
      have hh := ha i
      rw [pow_succ] at hh
      dsimp [r]
      split <;> omega
    obtain ⟨p,hp,he⟩ := ih r hr
    refine ⟨b::p,by simp [hp],?_⟩
    funext i
    by_cases h : 2^N ≤ a i <;> simp [pathIndex,hp,he,b,r,h]

lemma pathIndex_take {p : CellPath d} {a : ℕ} (ha : a ≤ p.length) (i : Fin d) :
    pathIndex p i / 2^(p.length-a) = pathIndex (p.take a) i := by
  induction p generalizing a with
  | nil => simp at ha; simp [ha,pathIndex]
  | cons b p ih =>
    cases a with
    | zero => simpa only [Nat.sub_zero,List.take_zero,pathIndex] using
        Nat.div_eq_of_lt (pathIndex_lt (b::p) i)
    | succ a =>
      have ha' : a ≤ p.length := by simpa using ha
      have hp : 2^p.length = 2^a*2^(p.length-a) := by rw [← pow_add,Nat.add_sub_of_le ha']
      have hpos : 0 < 2^(p.length-a) := by positivity
      simp only [List.length_cons,Nat.add_sub_add_right,List.take_succ_cons,pathIndex,
        List.length_take,Nat.min_eq_left ha']
      split
      · rw [hp,Nat.mul_comm (2^a),Nat.mul_add_div hpos,ih ha']
      · simp only [zero_add,ih ha']

noncomputable def treeCell (p : CellPath d) : Set (EuclideanSpace ℝ (Fin d)) :=
  ambientGridCell p.length (fun i => (pathIndex p i : ℤ))

lemma measurableSet_treeCell (p : CellPath d) : MeasurableSet (treeCell p) :=
  measurableSet_ambientGridCell _ _

lemma treeCell_disjoint {p q : CellPath d} (hlen : p.length = q.length) (hpq : p ≠ q) :
    Disjoint (treeCell p) (treeCell q) := by
  unfold treeCell
  rw [hlen]
  apply ambientGridCell_disjoint
  intro he
  apply hpq
  apply pathIndex_injective hlen
  funext i
  have hh := congrFun he i
  exact_mod_cast hh

lemma treeCell_subset_take (p : CellPath d) (a : ℕ) : treeCell p ⊆ treeCell (p.take a) := by
  by_cases ha : a ≤ p.length
  · have hh := ambientGridCell_subset_ancestor (d := d) ha
      (fun i => (pathIndex p i : ℤ))
    convert hh using 1
    · rfl
    · rw [treeCell,List.length_take,Nat.min_eq_left ha]
      congr 1
      funext i
      rw [← pathIndex_take ha i]
      norm_cast
  · rw [List.take_of_length_le (by omega)]

lemma treeCell_cover_root (N : ℕ) :
    (⋃ p ∈ dyadicPaths (d := d) N, treeCell p) = treeCell [] := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨p,hp,hx⟩ := Set.mem_iUnion₂.mp hx
    simpa only [List.take_zero] using treeCell_subset_take p 0 hx
  · intro x hx
    have hx' : ∀ i, 0 ≤ x i ∧ x i < 1 := by simpa [treeCell,ambientGridCell,pathIndex] using hx
    let a : Fin d → ℕ := fun i => (⌊(2:ℝ)^N*x i⌋).toNat
    have hlo (i : Fin d) : 0 ≤ ⌊(2:ℝ)^N*x i⌋ := Int.floor_nonneg.mpr (mul_nonneg (by positivity) (hx' i).1)
    have hcast (i : Fin d) : (a i : ℤ) = ⌊(2:ℝ)^N*x i⌋ := Int.toNat_of_nonneg (hlo i)
    have ha (i : Fin d) : a i < 2^N := by
      have hilt : ⌊(2:ℝ)^N*x i⌋ < (2:ℤ)^N := by
        apply Int.floor_lt.mpr
        have hh := mul_lt_mul_of_pos_left (hx' i).2 (by positivity : 0 < (2:ℝ)^N)
        simpa only [mul_one,Int.cast_pow,Int.cast_ofNat] using hh
      rw [← hcast i] at hilt
      exact_mod_cast hilt
    obtain ⟨p,hp,he⟩ := exists_pathIndex N a ha
    refine Set.mem_iUnion₂.mpr ⟨p,(mem_dyadicPaths N p).mpr hp,?_⟩
    apply mem_ambientGridCell_iff.mpr
    intro i
    simpa only [hp,he] using (hcast i).symm

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
