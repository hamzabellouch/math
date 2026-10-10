import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileParents

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def refinedOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (gate : FirstOriginalOuter ι→Prop) : Finset (FirstOriginalOuter ι) :=
  (originalOuterCell p pool Q k).filter gate

def refinedSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) : Finset (OriginalIndex ι) :=
  (sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k).filter
      (fun x=>gate x.1 ∧ firstOriginalWeight p β cutoff x.1 x.2≠0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedSource_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) :
    refinedSource p pool Q labels β cutoff Y k gate⊆sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k :=
  Finset.filter_subset _ _

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_weight_frequency (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (x : OriginalIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2≠0) :
    x.2.2∈reopenedPhysicalCutoff p x.1.1 x.2.1 (cutoff x.1.1 x.1.2.1 x.2.1) x.1.2.2 := by
  by_contra hh
  exact hx (by simp [firstOriginalWeight,hh])

theorem refined_source_radius (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ysource Ychild : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop)
    (hn : ∀I∈labels,I≠0)
    (hcut : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤Ychild) :
    refinedSource p pool Q labels β cutoff Ysource k gate⊆
      firstGlobalRetainedSource p (refinedOuter p pool Q k gate) (fun _=>labels) (fun x=>x.1) Ychild := by
  intro x hx
  obtain ⟨hxcell,hgate,hweight⟩ := Finset.mem_filter.mp hx
  have hxold := original_cell_subset p pool Q labels Ysource k hxcell
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxold
  have hm := (mem_firstRetainedSource p labels x.1.1 Ysource x.2).mp hf
  have houter : x.1∈refinedOuter p pool Q k gate := Finset.mem_filter.mpr ⟨ho,hgate⟩
  have hE := firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hn x.2.1 hm.1)
  apply Finset.mem_sigma.mpr
  refine ⟨houter,(mem_firstRetainedSource p labels x.1.1 Ychild x.2).mpr ⟨hm.1,?_⟩⟩
  apply Finset.mem_erase.mpr
  refine ⟨(Finset.mem_erase.mp hm.2).1,?_⟩
  apply (mem_childFrequencyBall _ hE Ychild x.2.2).mpr
  exact ((mem_childFrequencyBall _ hE _ x.2.2).mp
    (original_weight_frequency p β cutoff x hweight)).trans (hcut x.1 houter x.2.1 hm.1)

def labelGate (j : ℕ) (x : FirstOriginalOuter ι) : Prop :=
  InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedOuter_label (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (j : ℕ) :
    refinedOuter p pool Q k (labelGate p j)=
      (InverseFirstGlobalCaps.outerCell p pool Q k).filter
        (fun x=>InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j) := by
  rw [refinedOuter,originalOuterCell_eq_caps]
  ext x
  simp [labelGate]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
