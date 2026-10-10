import OAI.Analysis.KadisonKastler.StateBicentralizerVonNeumann
import OAI.Analysis.KadisonKastler.ProductStateCentralizer

namespace OAI

/-! # Exact centralizer tests inside the state bicentralizer -/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateBicentralizerMember_commutes (ξ : H) {a : Algebra M}
    (ha : stateBicentralizerMember ξ a) (b : Algebra M)
    (hb : vectorStateCommutator ξ b=0) : a*b=b*a := by
  let x : BoundedSequence (Algebra M) := BoundedContinuousFunction.const ℕ b
  have hx : StateAsymptoticallyCentral ξ x := by
    change Tendsto (fun _ : ℕ => ‖vectorStateCommutator ξ b‖) atTop (𝓝 0)
    rw [hb,norm_zero]
    exact tendsto_const_nhds
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro η
  have ht := ha x hx η
  change Tendsto (fun _ : ℕ => (a*b-b*a).val η) atTop (𝓝 0) at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

theorem vectorStateCommutator_eq_zero_of_productStateCentralizes (ξ : H)
    (b : Algebra M) (hb : ProductStateCentralizes M ξ b.val) :
    vectorStateCommutator ξ b=0 := by
  ext c
  change inner ℂ ξ (((b*c-c*b).val) ξ)=0
  change productVectorState ξ (b.val*c.val-c.val*b.val)=0
  simp only [productVectorState,sub_apply,inner_sub_right,sub_eq_zero]
  exact hb c.val c.property

theorem stateBicentralizerMember_commutes_of_productStateCentralizes (ξ : H)
    {a : Algebra M} (ha : stateBicentralizerMember ξ a) (b : Algebra M)
    (hb : ProductStateCentralizes M ξ b.val) : a*b=b*a :=
  stateBicentralizerMember_commutes ξ ha b
    (vectorStateCommutator_eq_zero_of_productStateCentralizes ξ b hb)

end

end KadisonKastler

end OAI
