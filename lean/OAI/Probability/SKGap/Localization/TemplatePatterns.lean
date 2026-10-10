import Mathlib
import OAI.Probability.SKGap.Localization.TemplateChaining

namespace OAI

section
noncomputable section
namespace SKGap
open scoped BigOperators

def wordPatternSet (m : ℕ) : ℕ→Finset (List (WordTemplateLetter m))
  | 0 => {[]}
  | L+1 => insert [] ((Finset.univ×ˢ wordPatternSet m L).image (fun p=>p.1::p.2))

@[simp] lemma mem_wordPatternSet {m L : ℕ} (F : List (WordTemplateLetter m)) :
    F∈wordPatternSet m L ↔ F.length ≤ L := by
  induction L generalizing F with
  | zero => simp [wordPatternSet]
  | succ L ih =>
    cases F with
    | nil => simp [wordPatternSet]
    | cons l F =>
      simp only [wordPatternSet,Finset.mem_insert,List.cons_ne_nil,Finset.mem_image,
        Finset.mem_product,Finset.mem_univ,true_and,Prod.exists,List.cons.injEq,false_or]
      constructor
      · rintro ⟨a,G,hG,ha,hFG⟩
        subst a G
        exact Nat.succ_le_succ ((ih F).mp hG)
      · intro h
        exact ⟨l,F,(ih F).mpr (Nat.le_of_succ_le_succ h),rfl,rfl⟩
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem all_generalTemplateWords_gaussian_chaining {m : ℕ} (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ F : List (WordTemplateLetter m),F.length ≤ L ∧ ∃ θ : WordParameter m (Fin n),
        C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      (wordPatternSet m L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  classical
  choose C hC htail using (fun F : List (WordTemplateLetter m)=>generalTemplateWord_gaussian_chaining f hR hj hA hD F)
  let G := wordPatternSet m L
  let T := 1+∑ F∈G,C F
  have hT : 0<T := by
    have hh : 0 ≤ ∑ F∈G,C F := Finset.sum_nonneg (fun F _=>(hC F).le)
    dsimp [T]
    linarith
  have hF (F : List (WordTemplateLetter m)) (hF : F∈G) : C F ≤ T := by
    have hh : C F ≤ ∑ F∈G,C F := Finset.single_le_sum (fun F _=>(hC F).le) hF
    dsimp [T]
    linarith
  refine ⟨T,hT,?_⟩
  intro n hn p
  let E : List (WordTemplateLetter m)→Set (MatrixCoordinates (Fin n)→ℝ) := fun F=>
    {g | ∃ θ : WordParameter m (Fin n),C F< matrixWordSeminorm p
      (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
        generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)) (WithLp.toLp 2 g))}
  apply (measure_mono (show _⊆⋃ F∈G,E F from ?_)).trans
    ((measure_biUnion_finset_le G E).trans ?_)
  · intro g hg
    obtain ⟨F,hFl,θ,hθ⟩ := hg
    have hFm : F∈G := (mem_wordPatternSet F).mpr hFl
    exact mem_iUnion.mpr ⟨F,mem_iUnion.mpr ⟨hFm,θ,lt_of_le_of_lt (hF F hFm) hθ⟩⟩
  · calc
      _ ≤ ∑ F∈G,ENNReal.ofReal (3*exp (-(n:ℝ))) := Finset.sum_le_sum (fun F _=>htail F n hn p)
      _ = _ := by simp [G]
end SKGap
end
end

end OAI
