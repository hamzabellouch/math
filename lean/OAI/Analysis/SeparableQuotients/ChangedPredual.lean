import OAI.Analysis.SeparableQuotients.SeparableSubspaces

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

@[reducible] local instance crDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance crDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance crSubGroup (F : Submodule ℝ E) : NormedAddCommGroup F := inferInstance
@[reducible] local instance crSubSpace (F : Submodule ℝ E) : NormedSpace ℝ F := inferInstance
@[reducible] local instance crSubDualGroup (F : Submodule ℝ E) : NormedAddCommGroup (StrongDual ℝ F) := inferInstance
@[reducible] local instance crSubDualSpace (F : Submodule ℝ E) : NormedSpace ℝ (StrongDual ℝ F) := inferInstance

def restrict (F : Submodule ℝ E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ F :=
  ContinuousLinearMap.precomp ℝ F.subtypeL

lemma coordinate_restriction_countable (F : Submodule ℝ E) [SeparableSpace F] :
    Set.Countable {a | restrict F (coordinate a) ≠ 0} := by
  let s : Set Γ := ⋃ n : ℕ, {a | coordinate a (denseSeq F n : E) ≠ 0}
  have hs : s.Countable := countable_iUnion (fun n => support_countable (denseSeq F n : E))
  apply hs.mono
  intro a ha
  by_contra hn
  apply ha
  have hz : ∀ n, coordinate a (denseSeq F n : E) = 0 := by
    intro n
    by_contra h
    exact hn (mem_iUnion.mpr ⟨n,h⟩)
  apply DFunLike.coe_injective
  exact (denseRange_denseSeq F).equalizer (restrict F (coordinate a)).continuous continuous_const
    (funext hz)

/-- Restrictions of the coordinate predual to a separable subspace form a norm-separable set. -/
lemma predual_restriction_separable (F : Submodule ℝ E) [SeparableSpace F] :
    IsSeparable (restrict F '' (X₀ : Set (StrongDual ℝ E))) := by
  let s := {a | restrict F (coordinate a) ≠ 0}
  let Z := (Submodule.span ℝ ((fun a => restrict F (coordinate a)) '' s)).topologicalClosure
  have hZ : IsSeparable (Z : Set (StrongDual ℝ F)) :=
    ((coordinate_restriction_countable F).image _).isSeparable.span.closure
  apply hZ.mono
  rintro _ ⟨y,hy,rfl⟩
  have hc : IsClosed ((Z.comap (restrict F).toLinearMap) : Set (StrongDual ℝ E)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (restrict F).continuous
  have hin : Submodule.span ℝ (range coordinate) ≤ Z.comap (restrict F).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change restrict F (coordinate a) ∈ Z
    by_cases h : restrict F (coordinate a) = 0
    · rw [h]; exact Z.zero_mem
    · exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a,h,rfl⟩)
  exact (Submodule.topologicalClosure_minimal _ hin hc) hy

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

@[reducible] local instance atDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance atDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
local instance atXClosed : IsClosed (X₀ : Set (StrongDual ℝ E)) := norming.predual_isClosed
@[reducible] local instance atWGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance atWSpace : NormedSpace ℝ W := inferInstance

@[reducible] local instance atX0Group : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance atX0Space : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance atX0DualGroup : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance atX0DualSpace : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma eval0_isometry : Isometry (evalOn X₀) := norming.evaluationIsometry.isometry
lemma eval0_surjective : Function.Surjective (evalOn X₀) := evaluation_surjective

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

/-- The changed predual is the kernel of the perturbed quotient map. -/
def X : Submodule ℝ (StrongDual ℝ E) := (X₀.mkQL - B hCH).ker
instance X_isClosed : IsClosed (X hCH : Set (StrongDual ℝ E)) := (X₀.mkQL - B hCH).isClosed_ker
instance X_complete : CompleteSpace (X hCH) := (X_isClosed hCH).completeSpace_coe

lemma twist_data :
    (∃ R : E ≃L[ℝ] StrongDual ℝ (X hCH),
      ∀ (e : E) (x : X hCH), R e x = (x : StrongDual ℝ E) e) ∧
    ((X hCH).map (B hCH).toLinearMap).topologicalClosure =
      (X₀.map (B hCH).toLinearMap).topologicalClosure := by
  exact (twist X₀ eval0_isometry eval0_surjective (B hCH) (norm_B_le hCH) (B_adjoint hCH)
    (B_range_mem_predual_closure hCH)).2

@[reducible] local instance atXGroup : NormedAddCommGroup (X hCH) := inferInstance
@[reducible] local instance atXSpace : NormedSpace ℝ (X hCH) := inferInstance
@[reducible] local instance atXDualGroup : NormedAddCommGroup (StrongDual ℝ (X hCH)) := inferInstance
@[reducible] local instance atXDualSpace : NormedSpace ℝ (StrongDual ℝ (X hCH)) := inferInstance

def twistedIso : E ≃L[ℝ] StrongDual ℝ (X hCH) := (twist_data hCH).1.choose
@[simp] lemma twistedIso_apply (e : E) (x : X hCH) :
    twistedIso hCH e x = (x : StrongDual ℝ E) e := (twist_data hCH).1.choose_spec e x

lemma X_infinite : ¬ FiniteDimensional ℝ (X hCH) := by
  intro hh
  let := hh
  have : FiniteDimensional ℝ (StrongDual ℝ (X hCH)) := inferInstance
  exact infiniteDimensional (FiniteDimensional.of_injective (twistedIso hCH).toLinearMap (twistedIso hCH).injective)

lemma quotient_eq_B_on_X (x : X hCH) : X₀.mkQL x = B hCH x := by
  have h := x.property
  change X₀.mkQL x - B hCH x = 0 at h
  exact sub_eq_zero.mp h

lemma X_quotient_image : (X hCH).map X₀.mkQ = (X hCH).map (B hCH).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,hx,(quotient_eq_B_on_X hCH ⟨x,hx⟩).symm⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,hx,quotient_eq_B_on_X hCH ⟨x,hx⟩⟩

lemma path_mem_twisted_sum {f : Family} (P : InfinitePath f) :
    pathFunctional P ∈ ((X hCH) ⊔ X₀).topologicalClosure := by
  apply quotient_closure_lift X₀ (X hCH)
  rw [X_quotient_image, (twist_data hCH).2]
  let p : PathIndex f := ⟨P.raw,⟨P,rfl⟩⟩
  have he : pathFunctional p.repr = pathFunctional P := pathFunctional_eq_of_raw p.repr_raw
  have hm := pathCoset_mem_B_predual hCH f p
  apply Submodule.le_topologicalClosure _
  simpa only [pathCoset,he] using hm

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

@[reducible] local instance chDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance chDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance chSubGroup (F : Submodule ℝ E) : NormedAddCommGroup F := inferInstance
@[reducible] local instance chSubSpace (F : Submodule ℝ E) : NormedSpace ℝ F := inferInstance
@[reducible] local instance chSubDualGroup (F : Submodule ℝ E) : NormedAddCommGroup (StrongDual ℝ F) := inferInstance
@[reducible] local instance chSubDualSpace (F : Submodule ℝ E) : NormedSpace ℝ (StrongDual ℝ F) := inferInstance

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

/-- The branch obstruction for the changed predual, using the open quotient map. -/
lemma X_restriction_nonseparable (F : Submodule ℝ E) (hF : IsClosed (F : Set E))
    (hFi : ¬ FiniteDimensional ℝ F) [SeparableSpace F] :
    ¬ IsSeparable (restrict F '' (X hCH : Set (StrongDual ℝ E))) := by
  intro hsep
  let s := restrict F '' (X hCH : Set (StrongDual ℝ E)) ∪
    restrict F '' (X₀ : Set (StrongDual ℝ E))
  let Z := (Submodule.span ℝ s).topologicalClosure
  have hZ : IsSeparable (Z : Set (StrongDual ℝ F)) :=
    (hsep.union (predual_restriction_separable F)).span.closure
  have hin : X hCH ⊔ X₀ ≤ Z.comap (restrict F).toLinearMap := by
    apply sup_le
    · intro y hy
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl ⟨y,hy,rfl⟩))
    · intro y hy
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr ⟨y,hy,rfl⟩))
  have hc : IsClosed ((Z.comap (restrict F).toLinearMap) : Set (StrongDual ℝ E)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (restrict F).continuous
  have hp {f : Family} (P : InfinitePath f) : restrict F (pathFunctional P) ∈ Z :=
    (Submodule.topologicalClosure_minimal _ hin hc) (path_mem_twisted_sum hCH P)
  let R : BranchReduction F := Classical.choice (exists_branchReduction F hF hFi)
  let ψ : (ℕ → Bool) → StrongDual ℝ F := fun b =>
    restrict F (pathFunctional (TreeNode.branchPath (BlockApprox.blocks R) b))
  have hsψ : IsSeparable (range ψ) := hZ.mono (by
    rintro _ ⟨b,rfl⟩
    exact hp _)
  apply boolSeq_uncountable
  apply countable_of_separated_range ψ hsψ (1/(2004*(‖R.U‖+1))) (by positivity)
  intro b c hbc
  rw [dist_eq_norm]
  exact BlockApprox.restricted_separated R hbc

lemma X_no_separableQuotient : ¬ HasSeparableQuotient ℝ (X hCH) := by
  intro hsq
  obtain ⟨F,hF,hFi,hFs,hsep⟩ := separable_restriction_of_quotient
    (twistedIso hCH) (X hCH).subtypeL (twistedIso_apply hCH) hsq
  let := hFs.separableSpace
  apply X_restriction_nonseparable hCH F hF hFi
  apply hsep.mono
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

end SeparableQuotient.ActualSpace

end

end OAI
