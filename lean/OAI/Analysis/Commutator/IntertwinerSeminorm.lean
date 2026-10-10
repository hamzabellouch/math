import Mathlib
import OAI.Analysis.Commutator.IntertwinerCompression

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma seminorm_le_of_ball (Q : VonNeumannAlgebra G) (Z : G →L[ℂ] G) (δ : ℝ)
    (hball : ∀ b∈Q,‖b‖≤1 → ‖Z*b-b*Z‖≤δ) : commutatorSeminorm Q Z≤δ := by
  apply csSup_le
  · exact ⟨0,0,Q.zero_mem,by simp,by simp⟩
  rintro r ⟨b,hb,hbn,rfl⟩
  exact hball b hb hbn

lemma faithful_norm (M : VonNeumannAlgebra H)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (hinj : Function.Injective ψ) (a : M) : ‖ψ a‖=‖a‖ :=
  NonUnitalStarAlgHom.norm_map ψ.toNonUnitalStarAlgHom hinj a

lemma seminorm_le (M : VonNeumannAlgebra H) (Q : VonNeumannAlgebra G)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (hinj : Function.Injective ψ)
    (hrange : ∀ b∈Q,∃ a : M,ψ a=b)
    (T : H →L[ℂ] G) (hcon : ‖T‖≤1)
    (hT : ∀ a : M,T.comp (a:H →L[ℂ] H)=(ψ a).comp T) (Y : H →L[ℂ] H) :
    commutatorSeminorm Q (transfer T Y)≤commutatorSeminorm M Y := by
  apply seminorm_le_of_ball
  intro b hb hbn
  obtain ⟨a,rfl⟩ := hrange b hb
  have han : ‖(a:H →L[ℂ] H)‖≤1 := by
    change ‖a‖≤1
    have hn : ‖ψ a‖=‖a‖ := faithful_norm M ψ hinj a
    rwa [hn] at hbn
  exact (transfer_commutator_norm_le (A:=M) (H:=H) (G:=G) M.toStarSubalgebra.subtype ψ T hT hcon Y a).trans
    (commutator_bound_unitball M Y a.property han)

end Kadison.IntertwinerCompression

end

end
end

end OAI
