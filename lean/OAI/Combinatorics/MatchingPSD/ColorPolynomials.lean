import OAI.Combinatorics.MatchingPSD.PartialColorings

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorPolynomials
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma colorAverage_recurrence (z : V → C) (l : List (V × V)) (e : V × V)
    (he : e ∈ candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2))
    (M₀ : Pairing V) (h₀ : Pairing.ContainsList M₀ l) :
    ((candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)).card : ℝ) •
      colorAverage z (Pairing.edgeMonomial (e::l)) =
    (tableCoordinate z (z e.1,z e.2) -
      (∑ v ∈ Pairing.edgeSupport l,
        if z v = z e.1 ∧ z (M₀.1 v) = z e.2 then (1:ℝ) else 0) • 1) *
      colorAverage z (Pairing.edgeMonomial l) := by
  let S := candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)
  have hsum : (∑ f ∈ S, colorAverage z (Pairing.edgeMonomial (f::l))) =
      ((S.card : ℕ) : ℝ) • colorAverage z (Pairing.edgeMonomial (e::l)) := by
    calc
      _ = ∑ _f ∈ S, colorAverage z (Pairing.edgeMonomial (e::l)) := by
        apply Finset.sum_congr rfl
        intro f hf
        exact candidate_average_eq z l _ f e hf he
      _ = _ := by
        funext M
        simp [Pi.smul_apply]
  have hm : (∑ f ∈ S, Pairing.edgeMonomial (f::l)) =
      Pairing.edgeMonomial l * ∑ f ∈ S, Pairing.edgeCoord f := by
    simp only [Pairing.edgeMonomial_cons, ← Finset.sum_mul, mul_comm]
  rw [← hsum, ← map_sum, hm, monomial_candidate_identity z l _ M₀ h₀, mul_comm]
  apply colorAverage_mul_invariant
  intro p
  rw [map_sub, tableCoordinate_invariant, map_smul]
  rfl

lemma colorAverage_monomial_mem (z : V → C) (l : List (V × V)) :
    colorAverage z (Pairing.edgeMonomial l) ∈ lowDegree (tableCoordinate z) l.length := by
  induction l with
  | nil =>
    simpa only [Pairing.edgeMonomial, List.map_nil, List.prod_nil, colorAverage_one,
      List.length_nil] using one_mem_lowDegree (tableCoordinate z) 0
  | cons e l ih =>
    by_cases hc : ∃ M : Pairing V, Pairing.ContainsList M (e::l)
    · obtain ⟨M₀, hm⟩ := hc
      have h₀ : Pairing.ContainsList M₀ l := fun f hf => hm f (List.mem_cons_of_mem _ hf)
      have hEdge : M₀.1 e.1 = e.2 := hm e (List.mem_cons_self)
      by_cases hv : e.1 ∈ Pairing.edgeSupport l ∨ e.2 ∈ Pairing.edgeSupport l
      · rw [Pairing.redundant_edgeMonomial hEdge h₀ hv]
        exact lowDegree_mono _ (by simp) ih
      · have he : e ∈ candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2) := by
          apply (mem_candidateEdges _ _ _ _).mpr
          refine ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h), ?_, rfl, rfl⟩
          intro heq
          exact M₀.partner_ne e.1 (hEdge.trans heq.symm)
        let D := ((candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)).card : ℝ)
        have hD : D ≠ 0 := by
          apply Nat.cast_ne_zero.mpr
          exact Finset.card_ne_zero.mpr ⟨e, he⟩
        have hr := colorAverage_recurrence z l e he M₀ h₀
        have hlin : tableCoordinate z (z e.1,z e.2) -
            (∑ v ∈ Pairing.edgeSupport l,
              if z v = z e.1 ∧ z (M₀.1 v) = z e.2 then (1:ℝ) else 0) • 1 ∈
            lowDegree (tableCoordinate z) 1 :=
          (lowDegree (tableCoordinate z) 1).sub_mem (coord_mem_lowDegree _ _)
            ((lowDegree (tableCoordinate z) 1).smul_mem _ (one_mem_lowDegree _ _))
        have hmem := mul_mem_lowDegree (tableCoordinate z) hlin ih
        rw [← hr] at hmem
        change D • colorAverage z (Pairing.edgeMonomial (e::l)) ∈
          lowDegree (tableCoordinate z) (1+l.length) at hmem
        have hh := (lowDegree (tableCoordinate z) (1+l.length)).smul_mem D⁻¹ hmem
        simpa only [smul_smul, inv_mul_cancel₀ hD, one_smul, Nat.add_comm,
          List.length_cons] using hh
    · rw [Pairing.edgeMonomial_zero_of_unsatisfiable _ hc, map_zero]
      exact Submodule.zero_mem _

lemma colorAverage_lowDegree (z : V → C) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    colorAverage z f ∈ lowDegree (tableCoordinate z) d := by
  apply Submodule.span_induction (p := fun f _ => colorAverage z f ∈
    lowDegree (tableCoordinate z) d) _ _ _ _ hf
  · rintro f ⟨l, hl, rfl⟩
    exact lowDegree_mono _ hl (colorAverage_monomial_mem z l)
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add] using (lowDegree (tableCoordinate z) d).add_mem hf hg
  · intro c f _ hf
    simpa only [map_smul] using (lowDegree (tableCoordinate z) d).smul_mem c hf

end ColorPolynomials

section Substitution
variable {E : Type u_3} {I : Type u_4} {X : Type u_5} {Y : Type u_6}

lemma list_prod_mem_lowDegree (x : E → X → ℝ) (l : List I) (y : I → X → ℝ)
    (hy : ∀ i, y i ∈ lowDegree x 1) : (l.map y).prod ∈ lowDegree x l.length := by
  induction l with
  | nil => exact one_mem_lowDegree x 0
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm] using
      mul_mem_lowDegree x (hy i) ih

lemma lowDegree_substitute (x : E → X → ℝ) (y : I → X → ℝ)
    (hy : ∀ i, y i ∈ lowDegree x 1) (d : ℕ) : lowDegree y d ≤ lowDegree x d := by
  apply Submodule.span_le.mpr
  rintro f ⟨l, hl, rfl⟩
  exact lowDegree_mono x hl (list_prod_mem_lowDegree x l y hy)

lemma lowDegree_lift (x : E → X → ℝ) (d : ℕ) (f : X → ℝ)
    (hf : f ∈ lowDegree x d) :
    ∃ P ∈ lowDegree (fun e (v : E → ℝ) => v e) d,
      ∀ a, f a = P (fun e => x e a) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    refine ⟨(l.map (fun e (v : E → ℝ) => v e)).prod,
      Submodule.subset_span ⟨l, hl, rfl⟩, ?_⟩
    intro a
    induction l with
    | nil => rfl
    | cons e l ih =>
      simp only [List.map_cons, List.prod_cons, Pi.mul_apply]
      rw [ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) hl)]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨P, hP, hp⟩ := hf
    obtain ⟨Q, hQ, hq⟩ := hg
    exact ⟨P+Q, Submodule.add_mem _ hP hQ, fun a => by simp [hp a, hq a]⟩
  | smul c f _ hf =>
    obtain ⟨P, hP, hp⟩ := hf
    exact ⟨c • P, Submodule.smul_mem _ c hP, fun a => by simp [hp a]⟩

end Substitution
end MatchingSmoothing

end OAI
