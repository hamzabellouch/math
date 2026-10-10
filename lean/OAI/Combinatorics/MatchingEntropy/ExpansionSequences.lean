import OAI.Combinatorics.MatchingEntropy.EightVertex

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

inductive KleeConstruction : (n : ℕ) → LooplessGraph (KleeV n) (KleeE n) → Prop
  | base : KleeConstruction 0 (kleeGraph 0)
  | expand {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
      (previous : KleeConstruction n G) (v : KleeV n) :
      KleeConstruction (n+1) (triangleExpansion G (kleeColor n) v)

def coloredLaw {W : Type uW} {D : Type uD} [Fintype D] [DecidableEq W] [DecidableEq D]
    (G : LooplessGraph W D) (c : D → Fin 3) : G.Matching → ℝ :=
  fun M => ∑ i : Fin 3, if M.val = colorEdges c i then 1 / 3 else 0

section ColoredLaws
variable {W : Type uW} {D : Type uD} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]

omit [Fintype W] in
theorem colored_law_eq_fiber (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) :
    coloredLaw G c = fiberMass (uniformLaw (Fin 3)) (colorMatching G c hc) := by
  ext M
  unfold coloredLaw fiberMass
  apply Finset.sum_congr rfl
  intro i _
  have he : colorMatching G c hc i = M ↔ M.val = colorEdges c i := by
    rw [Subtype.ext_iff]
    exact eq_comm
  simp [he,uniformLaw]

omit [Fintype W] in
theorem colored_law_feasible (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) :
    coloredLaw G c ∈ G.feasibleLaws (fun _ => 1/3) := by
  rw [colored_law_eq_fiber G c hc]
  exact ⟨fiberMass_mem_simplex uniformLaw_simplex _,colored_uniform_mean G c hc⟩

omit [Fintype W] in
theorem colored_uniform_mem (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) :
    (fun _ => 1/3) ∈ G.polytope :=
  (G.mem_polytope_iff _).mpr ⟨_,colored_law_feasible G c hc⟩

omit [Fintype W] in
theorem colored_entropy_law (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W) :
    entropy (coloredLaw G c) = Real.log 3 := by
  rw [colored_law_eq_fiber G c hc,entropy_fiberMass_injective _ _
    (colorMatching_injective G c hc v),uniformLaw_entropy]
  norm_num

omit [Fintype W] in
theorem colored_law_expand (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W) :
    fiberMass (coloredLaw G c) (expandMatching G c v) =
      coloredLaw (triangleExpansion G c v) (expandedColor c) := by
  rw [colored_law_eq_fiber G c hc,
    colored_law_eq_fiber _ _ (cubicColoring_expansion G c hc v),fiberMass_comp]
  ext M
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.comp_apply,expanded_colorMatching G c hc v]

omit [Fintype W] in
theorem colored_unique_expansion (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W)
    (hu : G.feasibleLaws (fun _ => 1/3) = {coloredLaw G c}) :
    (triangleExpansion G c v).feasibleLaws (fun _ => 1/3) =
      {coloredLaw (triangleExpansion G c v) (expandedColor c)} := by
  apply Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr
    (colored_law_feasible _ _ (cubicColoring_expansion G c hc v)))
  intro p hp
  have he : triangleExtension G c hc v (fun _ => 1/3) = fun _ => 1/3 := by
    ext e
    cases e <;> rfl
  rw [← he] at hp
  obtain ⟨hp',hq⟩ := expanded_pull_feasible G c hc v (colored_uniform_mem G c hc) hp
  rw [hu,Set.mem_singleton_iff] at hq
  rw [hq,colored_law_expand G c hc v] at hp'
  exact Set.mem_singleton_iff.mpr hp'

omit [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D] in
theorem colored_triangle_expansion (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W) :
    triangleExtension G c hc v '' convexHull ℝ (Set.range (coloredVector c)) =
      convexHull ℝ (Set.range (coloredVector (expandedColor c))) := by
  rw [LinearMap.image_convexHull,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact triangleExtension_colored G c hc v i

theorem colored_minimal_expansion (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W)
    (hm : minimalFace G (fun _ => 1/3) = convexHull ℝ (Set.range (coloredVector c))) :
    minimalFace (triangleExpansion G c v) (fun _ => 1/3) =
      convexHull ℝ (Set.range (coloredVector (expandedColor c))) := by
  have hh := ((expansion_face G c hc v).2.2 _ (colored_uniform_mem G c hc)).1
  have he : triangleExtension G c hc v (fun _ => 1/3) = fun _ => 1/3 := by
    ext e
    cases e <;> rfl
  rw [he,hm,colored_triangle_expansion G c hc v] at hh
  exact hh
end ColoredLaws

theorem klee_generated_cubic {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) : CubicColoring G (kleeColor n) := by
  induction hG with
  | base => exact klee_cubic 0
  | expand _ v ih => exact cubicColoring_expansion _ _ ih v

theorem klee_generated_minimal {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) : minimalFace G (kleeUniform n) = kleeTriangle n := by
  induction hG with
  | base => exact klee_minimal 0
  | @expand n G prev v ih =>
    rw [kleeEDecEq_succ,kleeVDecEq_succ]
    exact colored_minimal_expansion G (kleeColor n) (klee_generated_cubic prev) v ih

theorem klee_generated_unique {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) : G.feasibleLaws (kleeUniform n) = {coloredLaw G (kleeColor n)} := by
  induction hG with
  | base => exact klee_unique_law 0
  | @expand n G prev v ih =>
    rw [kleeEDecEq_succ,kleeVDecEq_succ]
    exact colored_unique_expansion G (kleeColor n) (klee_generated_cubic prev) v ih

theorem klee_initial_expansion_simple (v : KleeV 0) :
    IsSimpleLabelled (triangleExpansion (kleeGraph 0) (kleeColor 0) v) := by
  fin_cases v
  · exact klee_simple_one
  · intro e f h
    rcases e with e | i <;> rcases f with f | j
    · fin_cases e <;> fin_cases f <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
    · fin_cases e <;> fin_cases j <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
    · fin_cases i <;> fin_cases f <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
    · fin_cases i <;> fin_cases j <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]

theorem klee_generated_simple {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) (hn : 1 ≤ n) : IsSimpleLabelled G := by
  induction hG with
  | base => omega
  | @expand n G prev v ih =>
    by_cases hz : n = 0
    · subst n
      cases prev
      exact klee_initial_expansion_simple v
    · exact simplicity_expansion G _ v (ih (by omega))

theorem klee_all_expansions (n : ℕ) (G : LooplessGraph (KleeV n) (KleeE n))
    (hG : KleeConstruction n G) :
    Fintype.card (KleeV n) = 2 * (n+1) ∧
    Fintype.card (KleeE n) = 3 * (n+1) ∧
    CubicColoring G (kleeColor n) ∧
    (n ≥ 1 → IsSimpleLabelled G) ∧
    kleeUniform n ∈ G.polytope ∧
    minimalFace G (kleeUniform n) = kleeTriangle n ∧
    faceDimension G (kleeUniform n) = 2 ∧
    Fintype.card (KleeE n) - faceDimension G (kleeUniform n) = 3 * (n+1) - 2 ∧
    G.feasibleLaws (kleeUniform n) = {coloredLaw G (kleeColor n)} ∧
    maxMatchingEntropy G (kleeUniform n) = Real.log 3 ∧
    entropy (kleeUniform n) = (n+1) * Real.log 3 ∧
    complementEntropy (kleeUniform n) = 2 * (n+1) * Real.log (3/2) := by
  have hc := klee_generated_cubic hG
  have hm : kleeUniform n ∈ G.polytope := colored_uniform_mem G (kleeColor n) hc
  have hd : faceDimension G (kleeUniform n) = 2 := by
    rw [faceDimension,klee_generated_minimal hG,kleeTriangle,affineSpan_convexHull,direction_affineSpan]
    exact (coloredVector_linearIndependent G _ hc (kleeRoot n)).affineIndependent.finrank_vectorSpan (by decide)
  refine ⟨klee_cardV n,klee_cardE n,hc,klee_generated_simple hG,hm,klee_generated_minimal hG,
    hd,by rw [klee_cardE,hd],klee_generated_unique hG,?_,klee_entropy_terms n⟩
  obtain ⟨p,hp,he⟩ := maxMatchingEntropy_attained G hm
  rw [klee_generated_unique hG,Set.mem_singleton_iff] at hp
  rw [← he,hp,colored_entropy_law G _ hc (kleeRoot n)]

end MatchingEntropyBounds.Refined

end

end OAI
