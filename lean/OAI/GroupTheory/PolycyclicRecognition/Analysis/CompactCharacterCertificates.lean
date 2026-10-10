import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveCharacterIdeal
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! # Finite positive identities over compact character families

The identities are locally valid in character space. Compact families therefore
have finitely many certificates and one positive lower bound for their supports.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
open Set Filter
variable {Q M X : Type} [CommGroup Q] [AddCommGroup M] [TopologicalSpace X]
  (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
  (χ : X → Q →* Multiplicative ℝ)
  (heval : ∀ q, Continuous (fun x => (χ x q).toAdd))
include heval

theorem isOpen_positiveIdentitySupport (a : ℤ[Q]) (c : ℝ) :
    IsOpen {x : X | ∀ q ∈ a.coeff.support, c < (χ x q).toAdd} := by
  have h := isOpen_biInter_finset (s := a.coeff.support)
    (f := fun q => {x : X | c < (χ x q).toAdd})
    (fun q _ => isOpen_lt continuous_const (heval q))
  convert h using 1
  ext x
  simp only [mem_iInter, mem_ofPred_eq]

theorem isOpen_finiteCharacterMonoidDirections
    (hpos : ∀ x, ∃ t, 0 < (χ x t).toAdd) :
    IsOpen {x : X | Module.Finite ℤ[characterNonnegativeMonoid (χ x)]
      (characterMonoidRepresentation ρ (χ x)).asModule} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hx' : Module.Finite ℤ[characterNonnegativeMonoid (χ x)]
      (characterMonoidRepresentation ρ (χ x)).asModule := hx
  let := hx'
  obtain ⟨t, ht⟩ := hpos x
  obtain ⟨a, ha, hid⟩ := positive_identity_of_finite_characterMonoidModule ρ (χ x) t ht
  apply Filter.mem_of_superset ((isOpen_positiveIdentitySupport χ heval a 0).mem_nhds ha)
  intro y hy
  exact finite_characterMonoidModule_of_positive_identity ρ (χ y) a hy hid

omit [Module.Finite ℤ[Q] ρ.asModule] in
theorem compact_positiveIdentity_certificates (K : Set X) (hK : IsCompact K)
    (hpos : ∀ x ∈ K, ∃ t, 0 < (χ x t).toAdd)
    (hfinite : ∀ x ∈ K, Module.Finite ℤ[characterNonnegativeMonoid (χ x)]
      (characterMonoidRepresentation ρ (χ x)).asModule) :
    ∃ A : Finset ℤ[Q], (∀ a ∈ A, ρ.asAlgebraHom a = 1) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∃ a ∈ A,
        ∀ q ∈ a.coeff.support, δ ≤ (χ x q).toAdd := by
  classical
  have cert (x : K) : ∃ a : ℤ[Q], ∃ δ : ℝ, 0 < δ ∧ ρ.asAlgebraHom a = 1 ∧
      ∀ q ∈ a.coeff.support, δ ≤ (χ x q).toAdd := by
    let := hfinite x x.property
    obtain ⟨t, ht⟩ := hpos x x.property
    obtain ⟨a, ha, hid⟩ := positive_identity_of_finite_characterMonoidModule ρ (χ x) t ht
    obtain ⟨δ, hδ, hb⟩ := finite_character_positive_lower_bound a.coeff.support
      (fun q => (χ x q).toAdd) ha
    exact ⟨a, δ, hδ, hid, hb⟩
  choose a δ hδ hid hb using cert
  let U (y : K) := {x : X | ∀ q ∈ (a y).coeff.support, δ y / 2 < (χ x q).toAdd}
  have hU : ∀ y, IsOpen (U y) := fun y => isOpen_positiveIdentitySupport χ heval (a y) _
  have hcover : K ⊆ ⋃ y : K, U y := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, ?_⟩
    intro q hq
    have hp := hb ⟨x, hx⟩ q hq
    have hd := hδ ⟨x, hx⟩
    linarith
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  obtain ⟨ε, hε, hbound⟩ := finite_character_positive_lower_bound s
    (fun y => δ y / 2) (fun y _ => half_pos (hδ y))
  refine ⟨s.image a, ?_, ε, hε, ?_⟩
  · intro b hb
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    exact hid y
  · intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy, hxU⟩ := mem_iUnion.mp hy
    refine ⟨a y, Finset.mem_image_of_mem a hy, ?_⟩
    intro q hq
    exact (hbound y hy).trans (hxU q hq).le

end PolycyclicRecognition

end

end OAI
