import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExhaustiveCharacter
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TopHomologyCharacter
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentExhaustionDimension

namespace OAI

/-! # One orientation representation for every stage of the nilpotent exhaustion -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem exists_exhaustion_orientation (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ i, g ∈ S i) (n : ℕ)
    (hd : ∀ i, IsIntegralPoincareDualityGroup (S i) n)
    (hindex : ∀ i j, ((S i).subgroupOf (S j)).FiniteIndex) :
    ∃ R : Rep ℤ G, Nonempty (R.V ≃ₗ[ℤ] ℤ) ∧
      ∀ (i : ℕ) (A : Rep ℤ (S i)),
        Nonempty (groupHomology A n ≃ₗ[ℤ] (Rep.res (S i).subtype R ⟶ A)) := by
  classical
  choose D hDr hD using fun i => (hd i).topHomology_orientation
  let e (i : ℕ) := Classical.choice (hDr i)
  let χ (i : ℕ) := rankOneCharacter (D i) (e i)
  have hχ : ∀ i j (hij : i ≤ j) (g : S i),
      χ j (Subgroup.inclusion (hS hij) g) = χ i g := by
    intro i j hij g
    let f := Subgroup.inclusion (hS hij)
    have hrange : f.range = (S i).subgroupOf (S j) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    let : f.range.FiniteIndex := by rw [hrange]; exact hindex i j
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : S j => (z : G)) h)
    have hc := topHomology_character_embedding f hf n (D j) (D i) (e j) (e i)
      (hD j) (hD i)
    exact congrArg (fun c : S i →* ℤ => c g) hc
  let ψ := exhaustiveCharacter S hS hcover χ hχ
  let R := scalarCharacterRep ψ
  refine ⟨R, ⟨LinearEquiv.refl ℤ ℤ⟩, ?_⟩
  intro i A
  have hvalue (g : S i) : ψ (g : G) = χ i g :=
    congrArg (fun c : S i →* ℤ => c g) (exhaustiveCharacter_restrict S hS hcover χ hχ i)
  let u : D i ≅ Rep.res (S i).subtype R :=
    Rep.mkIso (Representation.Equiv.mk (e i) (by
      intro g
      ext x
      change (e i) ((D i).ρ g x) = ψ (g : G) * (e i) x
      rw [rankOne_action_coordinate, hvalue]
      exact mul_comm _ _))
  obtain ⟨a⟩ := hD i A
  exact ⟨a.trans (Linear.homCongr ℤ u (Iso.refl A))⟩

theorem exists_nilpotent_oriented_exhaustion [Countable G] [Group.IsNilpotent G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ n : ℕ, ∃ S : ℕ → Subgroup G, ∃ R : Rep ℤ G,
      Monotone S ∧ (∀ i, (S i).FG) ∧ (∀ g, ∃ i, g ∈ S i) ∧
      Nonempty (R.V ≃ₗ[ℤ] ℤ) ∧
      (∀ i j, ((S i).subgroupOf (S j)).FiniteIndex) ∧
      (∀ (i : ℕ) (A : Rep ℤ (S i)),
        Nonempty (groupHomology A n ≃ₗ[ℤ] (Rep.res (S i).subtype R ⟶ A))) := by
  obtain ⟨n, S, hS, hfg, hcover, hd, hindex⟩ :=
    exists_nilpotent_duality_exhaustion_finiteIndex hG
  obtain ⟨R, hR, htop⟩ := exists_exhaustion_orientation S hS hcover n hd hindex
  exact ⟨n, S, R, hS, hfg, hcover, hR, hindex, htop⟩

end PolycyclicRecognition

end

end OAI
