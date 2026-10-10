import OAI.Analysis.KadisonKastler.InfiniteFactorProperInfiniteness
import OAI.Analysis.KadisonKastler.ProjectionSchroederBernstein

namespace OAI

/-! # Nonzero projections in separably acting type III factors

A nonfinite projection contains a proper isometry and hence countably
many orthogonal copies of a nonzero defect.  Factoriality supplies a
countable source partition under this defect.  It embeds the identity
into the original projection; concrete Schroeder--Bernstein gives the
required equivalence.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- A nonfinite projection in a separably acting factor is equivalent to
its identity.  The type III hypothesis is needed only to supply nonfiniteness. -/
theorem projection_equivalent_one_of_not_finite_of_projection_countability
    (hFamilies : HasCountableProjectionFamilies M) (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hInfinite : ¬ FiniteProjectionIn M p.val) :
    p.Equivalent (⟨1, IsStarProjection.one _⟩ : AlgebraProjection M) := by
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM c.val c.property (fun a ha =>
      congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  simp only [FiniteProjectionIn] at hInfinite
  push Not at hInfinite
  obtain ⟨w, hw, hpw, hproper⟩ := hInfinite
  let v : PartialIsometry M := ⟨p, w, hw⟩
  have hvp : v.target ≤ v.support := (v.target_le_iff_mul p).mpr hpw
  let d := AlgebraProjection.remainder v.target v.support hvp
  have hd : d.val ≠ 0 := by
    change p.val - w * star w ≠ 0
    exact sub_ne_zero.mpr hproper.symm
  obtain ⟨slot, hs, ht, ho⟩ := v.defect_copies hvp
  obtain ⟨a, ha, hao, hatotal⟩ :=
    exists_countable_source_partition_of_projection_countability hFamilies hf d hd
  let b (n : ℕ) := (slot n).compose (a n).adjoint (by
    rw [PartialIsometry.adjoint_target, hs]
    exact ha n)
  have hbs (n : ℕ) : (b n).support = (a n).target := rfl
  have hbt (n : ℕ) : (b n).target ≤ p :=
    ((slot n).compose_target_le _ _).trans (ht n)
  obtain ⟨B, _, hBs, hBt⟩ := PartialIsometry.traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact hao hij)
    (by
      intro i j hij
      exact projection_orthogonal_of_le (ho hij)
        ((slot i).compose_target_le _ _) ((slot j).compose_target_le _ _))
  let oneP : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  have hB1 : B.support = oneP := Subtype.ext (hatotal _ (fun n => by
    simpa only [hbs] using (hBs B.support).mp le_rfl n)).symm
  have hBp : B.target ≤ p := (hBt _).mpr hbt
  have hp1 : p ≤ oneP := by change 1 * p.val = p.val; exact one_mul _
  exact AlgebraProjection.equivalent_of_le_of_subequivalent hp1 ⟨B, hB1, hBp⟩

theorem projection_equivalent_one_of_not_finite [TopologicalSpace.SeparableSpace H]
    (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hInfinite : ¬ FiniteProjectionIn M p.val) :
    p.Equivalent (⟨1, IsStarProjection.one _⟩ : AlgebraProjection M) :=
  projection_equivalent_one_of_not_finite_of_projection_countability
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho) hM p hInfinite

/-- Every nonzero projection in the concrete type III factor is the range
of an isometry in the same algebra. -/
theorem TypeIIIFactor.exists_isometry_onto_projection_of_projection_countability
    (hM : TypeIIIFactor M) (hFamilies : HasCountableProjectionFamilies M)
    (p : Algebra M) (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ v : Algebra M, star v * v = 1 ∧ v * star v = p := by
  have hInfinite : ¬ FiniteProjectionIn M p := fun h => hne (hM.purelyInfinite p hp h)
  have he := projection_equivalent_one_of_not_finite_of_projection_countability
    hFamilies hM.factor ⟨p, hp⟩ hInfinite
  obtain ⟨v, hv, ht⟩ := AlgebraProjection.equivalent_symm he
  refine ⟨v.val, ?_, ?_⟩
  · exact v.initial.trans (congrArg Subtype.val hv)
  · exact congrArg Subtype.val ht

theorem TypeIIIFactor.exists_isometry_onto_projection [TopologicalSpace.SeparableSpace H]
    (hM : TypeIIIFactor M) (p : Algebra M) (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ v : Algebra M, star v * v = 1 ∧ v * star v = p :=
  hM.exists_isometry_onto_projection_of_projection_countability
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho) p hp hne

/-- The type III projection-comparison input is a theorem of the existing
concrete projection and partial-isometry development. -/
theorem publishedTypeIIIProjectionComparison : PublishedTypeIIIProjectionComparison.{u} := by
  intro H _ _ _ _ M hM p hp hne
  exact hM.exists_isometry_onto_projection p hp hne

end

end KadisonKastler

end OAI
