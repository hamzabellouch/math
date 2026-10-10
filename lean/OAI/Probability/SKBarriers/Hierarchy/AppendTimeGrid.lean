import Mathlib
import OAI.Probability.SKBarriers.Scalar.PartitionOverlapIndex

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def appendTimeGrid (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ) :
    Fin (a+b+1) → ℝ := Fin.append (m:=a) (n:=b+1) (fun i : Fin a => q i.castSucc) p

theorem appendTimeGrid_right (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (j : Fin (b+1)) : appendTimeGrid a b q p (j.natAdd a)=p j := by
  exact Fin.append_right _ _ _

theorem appendTimeGrid_left (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hr : q (Fin.last a)=p 0) (i : Fin (a+1)) : appendTimeGrid a b q p ⟨i,by omega⟩=q i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [show (⟨(Fin.last a).val,by omega⟩:Fin (a+b+1))=(0:Fin (b+1)).natAdd a by ext; simp,
      appendTimeGrid_right,hr]
  · change appendTimeGrid a b q p (j.castAdd (b+1))=q j.castSucc
    exact Fin.append_left _ _ _

theorem appendTimeGrid_left_start (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hr : q (Fin.last a)=p 0) (i : Fin a) :
    appendTimeGrid a b q p (i.castAdd b).castSucc=q i.castSucc :=
  appendTimeGrid_left a b q p hr i.castSucc

theorem appendTimeGrid_left_end (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hr : q (Fin.last a)=p 0) (i : Fin a) :
    appendTimeGrid a b q p (i.castAdd b).succ=q i.succ :=
  appendTimeGrid_left a b q p hr i.succ

theorem appendTimeGrid_right_start (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (j : Fin b) : appendTimeGrid a b q p (j.natAdd a).castSucc=p j.castSucc :=
  appendTimeGrid_right a b q p j.castSucc

theorem appendTimeGrid_right_end (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (j : Fin b) : appendTimeGrid a b q p (j.natAdd a).succ=p j.succ := by
  rw [show (j.natAdd a).succ=j.succ.natAdd a by ext; simp; omega]
  exact appendTimeGrid_right a b q p j.succ

theorem appendTimeGrid_monotone (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hr : q (Fin.last a)=p 0) :
    Monotone (appendTimeGrid a b q p) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i
    rw [appendTimeGrid_left_start a b q p hr,appendTimeGrid_left_end a b q p hr]
    exact hq (Fin.castSucc_le_succ i)
  · intro j
    rw [appendTimeGrid_right_start,appendTimeGrid_right_end]
    exact hp (Fin.castSucc_le_succ j)

theorem timeGridCoefficients_append (a b : ℕ) (β : ℝ)
    (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ) (hr : q (Fin.last a)=p 0) :
    timeGridCoefficients (a+b) β (appendTimeGrid a b q p)=
      Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp only [timeGridCoefficients,Fin.append_left,
      appendTimeGrid_left_start a b q p hr,appendTimeGrid_left_end a b q p hr]
  · intro j
    simp only [timeGridCoefficients,Fin.append_right,appendTimeGrid_right_start,appendTimeGrid_right_end]

theorem appendTimeGrid_models {α : ℝ → ℝ} (a b : ℕ)
    (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ) (hr : q (Fin.last a)=p 0)
    (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hl : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i) :
    ∀ i : Fin (a+b), ∀ z∈Ico (appendTimeGrid a b q p i.castSucc)
      (appendTimeGrid a b q p i.succ), α z=Fin.append m l i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i z hz
    rw [appendTimeGrid_left_start a b q p hr,appendTimeGrid_left_end a b q p hr] at hz
    simpa only [Fin.append_left] using hm i z hz
  · intro j z hz
    rw [appendTimeGrid_right_start,appendTimeGrid_right_end] at hz
    simpa only [Fin.append_right] using hl j z hz

theorem scalarCDFOverlap_eq_two_partitions_index (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hq0 : q 0=0) (hp1 : p (Fin.last b)=1)
    (hr : q (Fin.last a)=p 0) (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hl : ∀ i, l i∈Icc (0:ℝ) 1)
    (hmodelq : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hmodelp : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i)
    (j : Fin (b+1)) :
    scalarCDFOverlap β α (p j)=
      scalarMomentSquare (a+b) (Fin.append m l)
        (Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p))
        scalarSpinTerminal scalarMagnetization (j.natAdd a) 0 := by
  have h0 : appendTimeGrid a b q p 0=0 := by
    have H := appendTimeGrid_left a b q p hr 0
    simpa only [Fin.val_zero,Fin.mk_zero,hq0] using H
  have h1 : appendTimeGrid a b q p (Fin.last (a+b))=1 := by
    have H := appendTimeGrid_right a b q p (Fin.last b)
    rw [show (Fin.last b).natAdd a=Fin.last (a+b) by ext; simp] at H
    exact H.trans hp1
  have hml (i : Fin (a+b)) : Fin.append m l i∈Icc (0:ℝ) 1 := by
    refine Fin.addCases ?_ ?_ i
    · intro i; simpa only [Fin.append_left] using hm i
    · intro j; simpa only [Fin.append_right] using hl j
  have H := scalarCDFOverlap_eq_partition_index β hα hαm (a+b) (appendTimeGrid a b q p)
    (appendTimeGrid_monotone a b q p hq hp hr) h0 h1 (Fin.append m l) hml
    (appendTimeGrid_models a b q p hr m l hmodelq hmodelp) (j.natAdd a)
  rwa [appendTimeGrid_right,timeGridCoefficients_append a b β q p hr] at H

end SK.Analytic

end
end

end OAI
