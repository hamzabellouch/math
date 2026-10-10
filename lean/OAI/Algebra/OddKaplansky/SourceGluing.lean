import OAI.Algebra.OddKaplansky.LocalGroup

namespace OAI

section

namespace OddKaplansky.SourceGluing
noncomputable section
open scoped Classical
open SourceGraph

def pDefinition : ℕ := sourcePrime
opaque pWrapped : Subtype (Eq pDefinition) := ⟨_, rfl⟩

def p : ℕ := pWrapped.1
theorem p_def : p = sourcePrime := by
  delta p
  rw [show pWrapped = ⟨pDefinition, rfl⟩ from Subtype.ext pWrapped.2.symm]
  rfl
attribute [irreducible] p pDefinition
attribute [eqns p_def] p
lemma p_prime : p.Prime := by rw [p_def]; exact sourcePrime_prime
lemma p_gt : sourceM < p := by rw [p_def]; exact sourcePrime_gt

instance : Fact p.Prime := ⟨p_prime⟩
instance : NeZero p := ⟨p_prime.ne_zero⟩
@[irreducible] def modulus : ℕ := p ^ 4 - 1
lemma modulus_gt : 1 < modulus := by
  have hp : 3 ≤ p := by have := p_gt; have := sourceM_large; omega
  have h : 81 ≤ p ^ 4 := Nat.pow_le_pow_left hp 4
  unfold modulus
  omega
instance : NeZero modulus := ⟨by have := modulus_gt; omega⟩
abbrev H := LocalGroup p modulus

def edgeHom (v : Vertex) (e : Edge) : Multiplicative (ZMod p) →* H :=
  LocalGroup.edgeHom p modulus (decide (v = e.val.1)) (index (neighbor v e))

lemma neighbor_cast_injective (v : Vertex) : Function.Injective (fun e : {e : Edge // Inc v e} =>
    (index (neighbor v e.val) : ZMod p)) := by
  intro e f hef
  apply GraphEdges.neighbor_injective graph v
  apply index_injective
  have h₁ : index (neighbor v e.val) < p := (index_le _).trans_lt p_gt
  have h₂ : index (neighbor v f.val) < p := (index_le _).trans_lt p_gt
  have hh := congrArg ZMod.val hef
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] using hh

lemma shortWords : Planar.ShortWords Inc edgeHom where
  one v f _ a ha := LocalGroup.edge_word_one _ _ _ _ _ ha
  two v f g hf hg hfg a b ha _ := by
    apply LocalGroup.edge_word_two _ _ _ _ _ _ _ _ ha
    intro h
    exact hfg (congrArg Subtype.val (neighbor_cast_injective v (a₁ := ⟨f,hf⟩) (a₂ := ⟨g,hg⟩) h))
  three v f g h hf hg hh hfg _ hhf a b c ha _ _ := by
    have h₁ : (index (neighbor v f) : ZMod p) ≠ index (neighbor v g) := by
      intro he
      exact hfg (congrArg Subtype.val (neighbor_cast_injective v (a₁ := ⟨f,hf⟩)
        (a₂ := ⟨g,hg⟩) he))
    have h₂ : (index (neighbor v f) : ZMod p) ≠ index (neighbor v h) := by
      intro he
      exact hhf (congrArg Subtype.val (neighbor_cast_injective v (a₁ := ⟨f,hf⟩)
        (a₂ := ⟨h,hh⟩) he)).symm
    exact LocalGroup.edge_word_three _ _ _ _ _ _ _ _ _ _ _ ha h₁ h₂

abbrev G₀ := Gluing.Q Inc edgeHom
def vertex (v : Vertex) : H →* G₀ := Gluing.vertex Inc edgeHom v
lemma vertex_injective (v : Vertex) : Function.Injective (vertex v) :=
  Gluing.vertex_injective Inc edgeHom (GraphEdges.incident_exists graph) shortWords incidence_girth v

instance : Group.FG G₀ := inferInstance

end
end OddKaplansky.SourceGluing

end

end OAI
