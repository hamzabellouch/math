import OAI.Combinatorics.BalancedRyser.Local.AlignedFreeCoordinates
import OAI.Combinatorics.BalancedRyser.Local.InjectionAuxiliaryExposure

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def generatedOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) : Fin 4 → Bool → F :=
  ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x).1.1

def generatedPositions (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) : Fin 4 → Point F :=
  tuplePositionEquiv d hd σ (generatedOffsets d hd σ g hg c J hJ a x)

theorem generatedPositions_old_left (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) (i : Fin 4) (hi : i ∈ J) :
    generatedPositions d hd σ g hg c J hJ a x i =
      lineIntersection (d i, a i (σ i)) (g,c) :=
  alignedPartial_position_old_left d hd σ g hg c J a
    ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x) i hi

theorem generatedPositions_old_right (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) (i : Fin 4) (hi : i + 1 ∈ J) :
    generatedPositions d hd σ g hg c J hJ a x i =
      lineIntersection (d (i+1), a (i+1) (!(σ (i+1)))) (g,c) :=
  alignedPartial_position_old_right d hd σ g hg c J a
    ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x) i hi

theorem generatedPositions_free (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F)
    (i : {i : Fin 4 // i ∈ freePositions J}) :
    generatedPositions d hd σ g hg c J hJ a x i =
      ((linePointEquiv g c).symm (x i)).1 :=
  alignedPartial_generated_free d hd σ g hg c J hJ a x i

theorem generatedPositions_agree_old (d d' : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (hd' : ∀ i, d' i ≠ d' (i + 1))
    (σ : Fin 4 → Bool) (g : Direction F)
    (hg : ∀ i, d i ≠ g) (hg' : ∀ i, d' i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a a' : Fin 4 → Bool → F)
    (hdir : ∀ i ∈ J, d i = d' i) (hoff : ∀ i ∈ J, a i = a' i)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) :
    generatedPositions d hd σ g hg c J hJ a x =
      generatedPositions d' hd' σ g hg' c J hJ a' x := by
  funext i
  by_cases hi : i ∈ J
  · rw [generatedPositions_old_left d hd σ g hg c J hJ a x i hi,
      generatedPositions_old_left d' hd' σ g hg' c J hJ a' x i hi,
      hdir i hi, hoff i hi]
  · by_cases hn : i + 1 ∈ J
    · rw [generatedPositions_old_right d hd σ g hg c J hJ a x i hn,
        generatedPositions_old_right d' hd' σ g hg' c J hJ a' x i hn,
        hdir (i+1) hn, hoff (i+1) hn]
    · have hf : i ∈ freePositions J := by simp [freePositions, hi, hn]
      exact (generatedPositions_free d hd σ g hg c J hJ a x ⟨i,hf⟩).trans
        (generatedPositions_free d' hd' σ g hg' c J hJ a' x ⟨i,hf⟩).symm

theorem generatedOffsets_from_positions (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) (i : Fin 4) (s : Bool) :
    generatedOffsets d hd σ g hg c J hJ a x i s =
      if s = σ i then lineEval (d i) (generatedPositions d hd σ g hg c J hJ a x i)
      else lineEval (d i) (generatedPositions d hd σ g hg c J hJ a x (i-1)) := by
  have h := congrFun (congrFun
    ((tuplePositionEquiv d hd σ).symm_apply_apply
      (generatedOffsets d hd σ g hg c J hJ a x)) i) s
  simpa only [tuplePositionEquiv_symm_apply, generatedPositions] using h.symm

def generatedPointLaw (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    PMF (Fin 4 → Point F) :=
  (PMF.uniformOfFintype ({i : Fin 4 // i ∈ freePositions J} → F)).map
    (generatedPositions d hd σ g hg c J hJ a)

theorem generatedPointLaw_agree_old (d d' : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (hd' : ∀ i, d' i ≠ d' (i + 1))
    (σ : Fin 4 → Bool) (g : Direction F)
    (hg : ∀ i, d i ≠ g) (hg' : ∀ i, d' i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a a' : Fin 4 → Bool → F)
    (hdir : ∀ i ∈ J, d i = d' i) (hoff : ∀ i ∈ J, a i = a' i) :
    generatedPointLaw d hd σ g hg c J hJ a =
      generatedPointLaw d' hd' σ g hg' c J hJ a' := by
  unfold generatedPointLaw
  congr 1
  funext x
  exact generatedPositions_agree_old d d' hd hd' σ g hg hg' c J hJ a a' hdir hoff x

end
end Balanced.AlignedListProbability

end OAI
