import OAI.GroupTheory.BooneHigman.ActionEnvelope
import OAI.GroupTheory.BooneHigman.Diagrams

namespace OAI

noncomputable section

/-!
Intermediate simple overgroups, finite-presentation transport, and Boone–Higman equivalence.
-/

namespace FiniteAlgebraicEnvelopes
universe u

/-- A countable simple overgroup supplied by the action envelope. -/

theorem input_countable_simple_extension (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Countable H ∧ IsSimpleGroup H ∧
      ∃ f : G →* H, Function.Injective f := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := envelope G hG
  let := hfp
  let : Countable Γ := by
    obtain ⟨n,φ,hφ,_⟩ := hfp.out
    exact Function.Surjective.countable hφ
  let := hcount
  let := hinf
  let := hfaith
  refine ⟨TwistedBrinThompson.group (Γ:=Γ) (X:=X),inferInstance,inferInstance,
    inferInstance,(TwistedBrinThompson.embedding (X:=X)).comp f,?_⟩
  exact TwistedBrinThompson.embedding_injective.comp hf

/-- A finitely generated countable simple overgroup. -/

theorem input_finitely_generated_simple_extension (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Group.FG H ∧ Countable H ∧ IsSimpleGroup H ∧
      ∃ f : G →* H, Function.Injective f := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := envelope G hG
  let := hfp
  let : Countable Γ := by
    obtain ⟨n,φ,hφ,_⟩ := hfp.out
    exact Function.Surjective.countable hφ
  let : Group.FG Γ := by
    obtain ⟨n,φ,hφ,_⟩ := hfp.out
    exact Group.fg_of_surjective hφ
  let := hcount
  let := hinf
  let := hfaith
  let : MulAction.IsPretransitive Γ X := ⟨by
    intro a b
    obtain ⟨a',ha⟩ := exists_ne a
    obtain ⟨b',hb⟩ := exists_ne b
    obtain ⟨g,hg,hg'⟩ := htwo a a' b b' (Ne.symm ha) (Ne.symm hb)
    exact ⟨g,hg⟩⟩
  let x : X := Classical.arbitrary X
  refine ⟨TwistedBrinThompson.group (Γ:=Γ) (X:=X),inferInstance,
    TwistedBrinThompson.Generators.finite_generation x,inferInstance,
    inferInstance,(TwistedBrinThompson.embedding (X:=X)).comp f,?_⟩
  exact TwistedBrinThompson.embedding_injective.comp hf

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Finite presentation of the actual twisted finite-chart group for a faithful
2-transitive action with finitely generated point stabilizers. -/
theorem finitelyPresented [Group.IsFinitelyPresented Γ] [Infinite X]
    [FaithfulSMul Γ X]
    (htwo : ∀ x₁ x₂ y₁ y₂ : X, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂)
    (hstab : ∀ x : X, Group.FG (MulAction.stabilizer Γ x)) :
    Group.IsFinitelyPresented (group (Γ:=Γ) (X:=X)) := by
  classical
  let : MulAction.IsPretransitive Γ X := ⟨by
    intro a b
    obtain ⟨a',ha⟩ := exists_ne a
    obtain ⟨b',hb⟩ := exists_ne b
    obtain ⟨g,hg,_⟩ := htwo a a' b b' (Ne.symm ha) (Ne.symm hb)
    exact ⟨g,hg⟩⟩
  let x : X := Classical.arbitrary X
  obtain ⟨y,hy⟩ := exists_ne x
  let : Group.FG (Generators.Seed (Γ:=Γ) x) := by
    obtain ⟨n,φ,hφ,_⟩ := Group.IsFinitelyPresented.out (G:=Generators.Seed (Γ:=Γ) x)
    exact Group.fg_of_surjective hφ
  let := hstab x
  obtain ⟨s,hs⟩ := Group.fg_def.mp (inferInstance : Group.FG (Generators.Seed (Γ:=Γ) x))
  obtain ⟨t,ht⟩ := Group.fg_def.mp (inferInstance : Group.FG (MulAction.stabilizer Γ x))
  exact Group.IsFinitelyPresented.equiv
    (Generators.endpointEquivalence x s t y hs ht (Ne.symm hy) htwo)

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes
universe u

/-- Forward direction of the Boone–Higman equivalence, using the proved action
envelope and the complete finite presentation of its concrete simple endpoint. -/
theorem main_forward (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) : EmbedsInFinitelyPresentedSimpleGroup G := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := envelope G hG
  let := hfp
  let := hcount
  let := hinf
  let := hfaith
  refine ⟨TwistedBrinThompson.group (Γ:=Γ) (X:=X),inferInstance,
    TwistedBrinThompson.finitelyPresented htwo hstab,inferInstance,
    (TwistedBrinThompson.embedding (X:=X)).comp f,?_⟩
  exact TwistedBrinThompson.embedding_injective.comp hf

/-- Manuscript Theorem 1.1, with arbitrary finitely generated input, including
finite and trivial input groups, and genuine algorithmic word-problem decidability. -/
theorem main (G : Type u) [Group G] [Group.FG G] :
    HasDecidableWordProblem G ↔ EmbedsInFinitelyPresentedSimpleGroup G :=
  ⟨main_forward G, main_reverse G⟩

end FiniteAlgebraicEnvelopes

end

end OAI
