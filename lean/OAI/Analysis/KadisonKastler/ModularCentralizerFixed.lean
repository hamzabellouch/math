import OAI.Analysis.KadisonKastler.ModularFixedVectors
import OAI.Analysis.KadisonKastler.ProductStateCentralizer

namespace OAI

/-! # From fixed centralizer vectors to fixed operators

Normalization and separation of the state vector upgrade the fixed-vector
identity to a fixed-operator identity.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem modularStrongGroup_centralizer_fixed (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hnormal : ∀ t, Conjugates (modularStrongGroup J Ω hsep hcyc t) M M)
    (x : H →L[ℂ] H) (hx : x ∈ M) (hcentral : ProductStateCentralizes M Ω x)
    (t : Multiplicative ℝ) :
    unitaryConj (modularStrongGroup J Ω hsep hcyc t) x = x := by
  let u := modularStrongGroup J Ω hsep hcyc t
  have hfix : (u : H →L[ℂ] H) Ω = Ω :=
    modularStrongGroup_fixes_state J Ω hsep hcyc t.toAdd
  have hstar : star (u : H →L[ℂ] H) Ω = Ω := by
    calc
      _ = star (u : H →L[ℂ] H) ((u : H →L[ℂ] H) Ω) := by rw [hfix]
      _ = Ω := congrArg (fun T : H →L[ℂ] H => T Ω) (Unitary.star_mul_self_of_mem u.property)
  have hmem : unitaryConj u x ∈ M := by
    change unitaryConj u x ∈ (M : Set (H →L[ℂ] H))
    rw [← hnormal t]
    exact Set.mem_image_of_mem _ hx
  have hvec : unitaryConj u x Ω = x Ω := by
    change (u : H →L[ℂ] H) (x (star (u : H →L[ℂ] H) Ω)) = _
    rw [hstar]
    exact modularStrongGroup_fixes_centralizer_vector J Ω hsep hcyc t.toAdd ⟨x, hx⟩
      (fun a => hcentral a.val a.property)
  have he : (⟨unitaryConj u x, hmem⟩ : Algebra M) = ⟨x, hx⟩ := hsep hvec
  exact congrArg (fun a : Algebra M => a.val) he

end

end KadisonKastler

end OAI
