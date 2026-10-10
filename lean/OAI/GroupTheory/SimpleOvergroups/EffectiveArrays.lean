import Mathlib
import OAI.Computability.FiniteCompiler.Effectivity
import OAI.Computability.FiniteCompiler.Selectors
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.SimpleOvergroups.ArrayNames
import OAI.GroupTheory.SimpleOvergroups.CanonicalNames

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Array
open FiniteAlgebraicEnvelopes
noncomputable section
open scoped Classical
variable {A X J D : Type*} [AddCommMonoid D] [Primcodable A] [Primcodable X] [Primcodable J]
  (coeff : A → D)

def collect (f : X → Part J) (p : Name A X) : Part (Name A J) :=
  Effect.traverse (fun a => (f a.2).map (fun k => (a.1,k))) p

def collectedKey (f : X → Part J) (p : Name A X) : Part ℕ :=
  (collect f p).map (key (value coeff id))

omit [Primcodable A] [Primcodable X] [Primcodable J] in
theorem collect_full (f : X → Part J) (g : X → J) (p : Name A X)
    (h : ∀ a ∈ p, g a.2 ∈ f a.2) :
    p.map (fun a => (a.1,g a.2)) ∈ collect f p := by
  apply FiniteAlgebraicEnvelopes.Bootstrap.Search.traverse_map
  intro a ha
  exact Part.mem_map _ (h a ha)

omit [Primcodable X] in
theorem collectedKey_full (hc : Function.Surjective coeff) (f : X → Part J)
    {K : Type*} (index : X → K) (g : K → J) (p : Name A X)
    (h : ∀ a ∈ p, g (index a.2) ∈ f a.2) :
    semanticKey (value coeff id) (value_surjective coeff id hc Function.surjective_id)
      (Finsupp.mapDomain g (value coeff index p)) ∈ collectedKey coeff f p := by
  rw [← value_map_index coeff index (g ∘ index) id g (fun _ => rfl) p,
    semanticKey_value]
  exact Part.mem_map _ (collect_full f (g ∘ index) p h)

variable {P : Type*} [Primcodable P] {f : P → X → Part J}

theorem partrec_collect (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => (collect (f p) : Name A X → Part (Name A J))) := by
  have hc : Partrec₂ (fun (p : P) (a : A × X) =>
      (f p a.2).map (fun k => (a.1,k))) := by
    exact ((hf.comp Computable.fst (Computable.snd.comp Computable.snd)).map
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd).to₂).to₂
  exact Effect.partrec_traverse_parameter hc

theorem partrec_collectedKey (heq : ComputablePred
    (fun p : Name A J × Name A J => value coeff id p.1 = value coeff id p.2))
    (hf : Partrec₂ f) : Partrec₂ (fun p : P => collectedKey coeff (f p)) := by
  exact (partrec_collect hf).map (((computable_key (value coeff id) heq).comp Computable.snd).to₂)

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
