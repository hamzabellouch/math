import OAI.Analysis.GroupDeterminants.TraceLog

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section SubTrace
variable {A : Type uA} [CStarAlgebra A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]

def subTrace (τ : A →L[ℝ] ℂ) : D →L[ℝ] ℂ :=
  τ.comp (D.toSubalgebra.toSubmodule.subtypeL.restrictScalars ℝ)

@[simp] lemma subTrace_apply (τ : A →L[ℝ] ℂ) (a : D) : subTrace D τ a = τ a := rfl

lemma subalgebra_log_coe (a : D) (ha : IsSelfAdjoint a) (hu : IsUnit a) :
    ((CFC.log a : D) : A) = CFC.log (a : A) := by
  exact D.subtype.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) Real.log a
    (Real.continuousOn_log.mono (fun x hx hzero =>
      (spectrum.zero_notMem_iff ℝ).mpr hu (by simpa only [Set.mem_singleton_iff.mp hzero] using hx)))
    continuous_subtype_val ha (ha.map D.subtype)

lemma subTrace_mul_comm (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a ∈ D, ∀ b ∈ D, τ (a * b) = τ (b * a)) (a b : D) :
    subTrace D τ (a * b) = subTrace D τ (b * a) := hτ a a.property b b.property

lemma subTrace_star (τ : A →L[ℝ] ℂ) (hτ : ∀ a, τ (star a) = star (τ a)) (a : D) :
    subTrace D τ (star a) = star (subTrace D τ a) := hτ a

lemma trace_log_shear_invariant_subalgebra (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a ∈ D, ∀ b ∈ D, τ (a * b) = τ (b * a))
    (hstar : ∀ a, τ (star a) = star (τ a))
    (B S T : D) (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : τ (S : A) = 0) (htT : τ (T : A) = 0) (x : ℝ) :
    τ (CFC.log (star ((1 + x • (S : A)) * (B : A) * (1 + x • (T : A))) *
      ((1 + x • (S : A)) * (B : A) * (1 + x • (T : A))))) =
      τ (CFC.log (star (B : A) * (B : A))) := by
  cases subsingleton_or_nontrivial D with
  | inl h =>
    have he : (1 + x • S) * B * (1 + x • T) = B := Subsingleton.elim _ _
    have he' := congrArg (fun a : D => (a : A)) he
    change (1 + x • (S : A)) * (B : A) * (1 + x • (T : A)) = (B : A) at he'
    rw [he']
  | inr h =>
    have H := trace_log_shear_invariant (subTrace D τ) (subTrace_mul_comm D τ hτ)
      (subTrace_star D τ hstar) B S T hB hS hT htS htT x
    have hM : IsUnit ((1 + x • S) * B * (1 + x • T)) :=
      (((nilpotentShearUnit S hS x).isUnit).mul hB).mul (nilpotentShearUnit T hT x).isUnit
    change τ ((CFC.log (star ((1 + x • S) * B * (1 + x • T)) *
      ((1 + x • S) * B * (1 + x • T))) : D) : A) =
      τ ((CFC.log (star B * B) : D) : A) at H
    rw [subalgebra_log_coe _ _ (IsSelfAdjoint.star_mul_self _) (hM.star.mul hM),
      subalgebra_log_coe _ _ (IsSelfAdjoint.star_mul_self _) (hB.star.mul hB)] at H
    exact H

end SubTrace

section ClosedTraceCalculus
variable {G : Type} [Group G] {n : ℕ}

instance closedGroupAlgebra_isClosed :
    IsClosed (closedGroupAlgebra (G := G) (n := n) : Set (Hilbert G n →L[ℂ] Hilbert G n)) :=
  StarSubalgebra.isClosed_topologicalClosure _

def closedRepresentation : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G) →+*
    closedGroupAlgebra (G := G) (n := n) :=
  complexRepresentation.codRestrict closedGroupAlgebra (fun A =>
    StarSubalgebra.le_topologicalClosure _ ⟨A, rfl⟩)

@[simp] theorem closedRepresentation_coe (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    (closedRepresentation A : Hilbert G n →L[ℂ] Hilbert G n) = complexOperator A := rfl

theorem groupTrace_log_shear_invariant (B S T : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G))
    (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : ∑ i, (S i i).coeff 1 = 0) (htT : ∑ i, (T i i).coeff 1 = 0) (x : ℝ) :
    groupTrace (CFC.log (star ((1 + x • complexOperator S) * complexOperator B *
      (1 + x • complexOperator T)) * ((1 + x • complexOperator S) * complexOperator B *
      (1 + x • complexOperator T)))) =
      groupTrace (CFC.log (star (complexOperator B) * complexOperator B)) := by
  let B' := closedRepresentation B
  let S' := closedRepresentation S
  let T' := closedRepresentation T
  have hu : IsUnit B' := hB.map closedRepresentation
  have hs : S' * S' = 0 := by simpa [S'] using congrArg closedRepresentation hS
  have ht : T' * T' = 0 := by simpa [T'] using congrArg closedRepresentation hT
  have hcyc : ∀ a ∈ closedGroupAlgebra (G := G) (n := n),
      ∀ b ∈ closedGroupAlgebra (G := G) (n := n),
      groupTraceCLM (a * b) = groupTraceCLM (b * a) := by
    intro a ha b hb
    simp only [groupTraceCLM_apply]
    exact groupTrace_closed_mul_comm ha hb
  have hstar : ∀ a : Hilbert G n →L[ℂ] Hilbert G n,
      groupTraceCLM (star a) = star (groupTraceCLM a) := by
    simp only [groupTraceCLM_apply]
    exact groupTrace_star
  have hts : groupTraceCLM (S' : Hilbert G n →L[ℂ] Hilbert G n) = 0 := by
    simpa only [S', closedRepresentation_coe, groupTraceCLM_apply, groupTrace_complex] using htS
  have htt : groupTraceCLM (T' : Hilbert G n →L[ℂ] Hilbert G n) = 0 := by
    simpa only [T', closedRepresentation_coe, groupTraceCLM_apply, groupTrace_complex] using htT
  have H := trace_log_shear_invariant_subalgebra closedGroupAlgebra
    (groupTraceCLM.restrictScalars ℝ) hcyc hstar B' S' T' hu hs ht hts htt x
  change groupTraceCLM _ = groupTraceCLM _ at H
  simp only [groupTraceCLM_apply, S', B', T', closedRepresentation_coe] at H
  convert H using 1
  rfl

end ClosedTraceCalculus

end GroupRingDeterminant

end

end OAI
