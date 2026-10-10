import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.SubchainView
import OAI.Combinatorics.IndependentSets.Reduction.AuxiliaryJointMeasurable

namespace OAI

namespace LargeIndependentSets
open MeasureTheory
open scoped Classical BigOperators NNReal
open PhaseTest ProductAveraging

noncomputable instance mixedTupleFintype {A B : Type*} [Fintype A] [Fintype B] (n i : ℕ) :
    Fintype (MixedTuple A B n i) := by
  classical
  unfold MixedTuple
  infer_instance

noncomputable def subchainBase {n : ℕ} (I : Finset (Fin (n+1))) (hI : I.Nonempty) : I :=
  ⟨I.min' hI, I.min'_mem hI⟩

lemma subchainBase_le {n : ℕ} (I : Finset (Fin (n+1))) (hI : I.Nonempty) (j : I) :
    (subchainBase I hI).val ≤ j.val := Finset.min'_le _ _ j.property

noncomputable def viewFunction {U V L R : Type} {n : ℕ}
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    {I : Finset (Fin (n+1))} (hI : I.Nonempty) (v : SubchainView U V L R n I)
    {m : ℕ} (t : I → Fin (m+1)) (θ : SubchainCoord L R n I → ℝ) : ℝ :=
  F ⟨(subchainBase I hI).val, v.question (subchainBase I hI)⟩
    (phase (fun j => v.projection (subchainBase I hI) j (subchainBase_le I hI j))
      (fun j => Coefficient.value (t j)) θ)

theorem canonical_subchain_rules (Lips : ℝ≥0) (s : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ J : ℕ, 1 ≤ J ∧
    ∀ (U V A B : Type) [Fintype A] [Fintype B] (n : ℕ),
    ∀ (F : ∀ q : LayerQuestion U V n, (LayerAnswer A B q → Circle) → ℝ),
    (∀ q, LipschitzWith Lips (F q)) → (∀ q x, |F q x| ≤ 1) →
    ∀ m : ℕ, 0 < m →
    ∃ rule : ∀ (I : Finset (Fin (n+1))), I.Nonempty ∧ I.card ≤ s →
      SubchainView U V A B n I → (I → Fin (m+1)) → Finset (SubchainCoord A B n I),
    ∀ I hI v,
      (∀ t, (rule I hI v t).card ≤ J ∧
        (∫ θ, (viewFunction F hI.1 v t θ -
          ProductAveraging.average rotationLaw (rule I hI v t) (viewFunction F hI.1 v t) θ)^2
          ∂Measure.pi (fun _ : SubchainCoord A B n I => rotationLaw)) < γ^2) ∧
      (Finset.univ.biUnion (rule I hI v)).card ≤ J*(m+1)^s := by
  obtain ⟨J,hJ,HJ⟩ := subchain_juntas Lips s hγ
  refine ⟨J,hJ,?_⟩
  intro U V A B _ _ n F hF hb m hm
  have H (I : Finset (Fin (n+1))) (hI : I.Nonempty ∧ I.card ≤ s)
      (v : SubchainView U V A B n I) :
      ∃ S : (I → Fin (m+1)) → Finset (SubchainCoord A B n I),
        (∀ t, (S t).card ≤ J ∧
          (∫ θ, (viewFunction F hI.1 v t θ -
            ProductAveraging.average rotationLaw (S t) (viewFunction F hI.1 v t) θ)^2
            ∂Measure.pi (fun _ : SubchainCoord A B n I => rotationLaw)) < γ^2) ∧
        (Finset.univ.biUnion S).card ≤ J*(m+1)^s := by
    let b := subchainBase I hI.1
    exact HJ I (by simpa using hI.2) (fun j => MixedTuple A B n j.val.val)
      (MixedTuple A B n b.val.val) (fun j => v.projection b j (subchainBase_le I hI.1 j))
      (F ⟨b.val,v.question b⟩) (hF ⟨b.val,v.question b⟩) (hb ⟨b.val,v.question b⟩) m hm
  choose rule hrule using H
  exact ⟨rule,hrule⟩

end LargeIndependentSets

end OAI
