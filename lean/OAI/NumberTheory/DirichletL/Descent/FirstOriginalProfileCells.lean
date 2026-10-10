import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileIdentity
import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsLive

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def originalNorms (x : OriginalIndex ι) : Fin 6→ℝ :=
  sourceNorms (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) x

def originalOuterCell (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    Finset (FirstOriginalOuter ι) :=
  (firstOriginalOuter pool Q).filter (fun x=>∀i:Fin 5,
    dyadIndex (originalNorms p ⟨x,(1,1)⟩ i.castSucc)=k i.castSucc)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_outer (x : OriginalIndex ι) (i : Fin 5) :
    originalNorms p ⟨x.1,(1,1)⟩ i.castSucc=originalNorms p x i.castSucc := by
  unfold originalNorms sourceNorms
  fin_cases i <;> simp [Fin.castSucc,leftNorm,rightNorm,commonNorm,activeNorm]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem original_cell_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex) :
    sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k ⊆
    firstGlobalRetainedSource p (originalOuterCell p pool Q k) (fun _=>labels) (fun x=>x.1) Y := by
  intro x hx
  obtain ⟨hxs,hk⟩ := Finset.mem_filter.mp hx
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxs
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_filter.mpr ⟨ho,?_⟩,hf⟩
  intro i
  rw [originalNorms_outer p x i]
  exact congrFun hk i.castSucc

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_outer_cell_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k⊆firstOriginalOuter pool Q := Finset.filter_subset _ _

theorem original_outer_cell_ratios (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (x : FirstOriginalOuter ι) (hx : x∈originalOuterCell p pool Q k) (i : Fin 5) :
    originalNorms p ⟨x,(1,1)⟩ i.castSucc/dyadScale (k i.castSucc)∈Set.Icc 1 2 := by
  have hnorm : ∀j:Fin 6,1≤originalNorms p ⟨x,(1,1)⟩ j := by
    apply sourceNorms_ge_one
    · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
    · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
    · exact primeSubsetGenerator_ne_zero _ _
    · exact one_ne_zero
  have hh := dyadIndex_bounds _ (hnorm i.castSucc)
  rw [(Finset.mem_filter.mp hx).2 i] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
