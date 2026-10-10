import Mathlib
import OAI.Analysis.Commutator.WOTCompact

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma isClosed_vonNeumann (M : VonNeumannAlgebra H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM∈M} := by
  have he : {T : H →WOT[ℂ] H | T.toCLM∈M}=
      (commutant (Set.centralizer (M : Set (H →L[ℂ] H))) : Set (H →WOT[ℂ] H)) := by
    ext T
    change T.toCLM∈M.carrier ↔ ∀ a∈Set.centralizer (M : Set (H →L[ℂ] H)),ofCLM a*T=T*ofCLM a
    rw [←M.centralizer_centralizer']
    constructor
    · intro h a ha
      exact congrArg ofCLM (h a ha)
    · intro h a ha
      exact congrArg toCLM (h a ha)
  rw [he]
  exact isClosed_commutant _

abbrev AlgebraBall (M : VonNeumannAlgebra H) (C : ℝ) :=
  {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C}

lemma compact_algebraBall (M : VonNeumannAlgebra H) {C : ℝ} (hC : 0≤C) :
    CompactSpace (AlgebraBall M C) := by
  apply isCompact_iff_compactSpace.mp
  exact (isCompact_normBall hC).inter_left (isClosed_vonNeumann M)

theorem secondCountable_algebraBall [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) {C : ℝ} (hC : 0≤C) :
    SecondCountableTopology (AlgebraBall M C) := by
  classical
  let : CompactSpace (AlgebraBall M C) := compact_algebraBall M hC
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq H
  let f : AlgebraBall M C → (ℕ×ℕ → ℂ) := fun T ij => inner ℂ (v ij.1) (T.val (v ij.2))
  have hf : Continuous f := by
    apply continuous_pi
    intro ij
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val _ _
  have hi : Function.Injective f := by
    intro T S he
    apply Subtype.ext
    apply ContinuousLinearMapWOT.toCLM_injective
    apply ContinuousLinearMap.ext
    intro x
    have hcoeff (n m : ℕ) : inner ℂ (v n) (T.val.toCLM (v m))=
        inner ℂ (v n) (S.val.toCLM (v m)) := congrFun he (n,m)
    have hx (m : ℕ) : T.val.toCLM (v m)=S.val.toCLM (v m) :=
      hv.eq_of_inner_right ℂ (fun n => hcoeff n m)
    exact hv.induction_on x (isClosed_eq T.val.toCLM.continuous S.val.toCLM.continuous) hx
  exact (hf.isClosedEmbedding hi).isEmbedding.secondCountableTopology

end Kadison.WOTDistance

end

end
end

end OAI
