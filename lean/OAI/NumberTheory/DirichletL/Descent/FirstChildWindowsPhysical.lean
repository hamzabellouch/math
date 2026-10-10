import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsCells

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadScale dyadScale_pos)
local notation "O" => ActualEisensteinCubic.O

def columnScales (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) : Fin 9→ℝ :=
  rawScales k l (X₁/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X₂/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

lemma columnScales_pos (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) :
    ∀i,0<columnScales k l X₁ X₂ i := by
  apply rawScales_pos
  · exact div_pos h₁ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos h₂ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma columnScales_left (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) :
    let s := columnScales k l X₁ X₂
    s 0*s 2*s 5*s 7=X₁ := by
  dsimp [columnScales,rawScales]
  exact mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (dyadScale_pos _).ne' (dyadScale_pos _).ne') (dyadScale_pos _).ne')

lemma columnScales_right (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) :
    let s := columnScales k l X₁ X₂
    s 1*s 2*s 5*s 8=X₂ := by
  dsimp [columnScales,rawScales]
  exact mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (dyadScale_pos _).ne' (dyadScale_pos _).ne') (dyadScale_pos _).ne')

lemma physical_scales_congr {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s t : Fin 9→ℝ)
    (hleft : s 0*s 2*s 5*s 7=t 0*t 2*t 5*t 7)
    (hright : s 1*s 2*s 5*s 8=t 1*t 2*t 5*t 8) :
    firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h t := by
  unfold firstFamilyPhysicalRows
  rw [hleft,hright]

theorem original_physical_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      ∑k∈sourceKeys (sourceNorms A₁ A₂ C R d h) S,∑l∈commonKeys p F,
        firstFamilyPhysicalRows p hg (sourceCell (sourceNorms A₁ A₂ C R d h) S k) F
          (fun x=>commonSelector p (selector x) l) C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s := by
  let G (x : κ) (j : FirstCommonIndex ι) := w x*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j*
    firstNormProfile (fun y=>W₁ (y/(s 0*s 2*s 5*s 7)))
      (fun y=>W₂ (y/(s 1*s 2*s 5*s 8))) Φ (fun _ _=>1) K
      (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j)
  have rows (T : Finset κ) (sel : κ → Finset ι → ℂ) :
      firstFamilyPhysicalRows p hg T F sel C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s =
        ∑ x ∈ T, ∑ j ∈ firstCommonIndices F, sel x j.2.1 * G x j := by
    unfold firstFamilyPhysicalRows firstBlockedPhysicalRows
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [G]
    ring
  have he := original_signed_partition p F S (sourceNorms A₁ A₂ C R d h) selector G
  simpa only [rows] using he

theorem original_physical_partition_raw {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      ∑k∈sourceKeys (sourceNorms A₁ A₂ C R d h) S,∑l∈commonKeys p F,
        firstFamilyPhysicalRows p hg (sourceCell (sourceNorms A₁ A₂ C R d h) S k) F
          (fun x=>commonSelector p (selector x) l) C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h
          (columnScales k l (s 0*s 2*s 5*s 7) (s 1*s 2*s 5*s 8)) := by
  rw [original_physical_partition p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply physical_scales_congr
  · exact (columnScales_left k l _ _).symm
  · exact (columnScales_right k l _ _).symm

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI
