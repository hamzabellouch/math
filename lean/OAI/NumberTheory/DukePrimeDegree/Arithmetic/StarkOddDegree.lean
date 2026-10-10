import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkCharacters

namespace OAI

/-!
# Odd-degree descent for real cyclic zero characters

For the application to Stark's argument it is enough to know the
restrictions of the zero character to cyclic subgroups. A real class
function with these restrictions and average one on an odd-index
subgroup is identically one. The proof uses a Sylow two-subgroup acting
on the odd set of cosets; it does not require a global Artin character.
-/

open scoped BigOperators
open PrimeDegreePackets

namespace DukePrimeDegree

/-- A real class function whose cyclic restrictions are linear characters
is trivial if it is trivial on an odd-index subgroup. -/
theorem cyclic_real_classFunction_trivial_of_odd_index
    {G : Type*} [Group G] [Finite G]
    (f : G → ℝˣ)
    (hconj : ∀ a g, f (a * g * a⁻¹) = f g)
    (hcyclic : ∀ g : G, ∃ χ : Subgroup.zpowers g →* ℝˣ,
      ∀ x : Subgroup.zpowers g, χ x = f (x : G))
    (H : Subgroup G) (hodd : Odd H.index)
    (hH : ∀ g ∈ H, f g = 1) : ∀ g, f g = 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  obtain ⟨χ, hχ⟩ := hcyclic g
  let C := Subgroup.zpowers g
  let P : Sylow 2 C := Classical.choice Sylow.nonempty
  let j : P →* G := C.subtype.comp P.toSubgroup.subtype
  let : MulAction P (G ⧸ H) := MulAction.compHom (G ⧸ H) j
  have hodd' : ¬ 2 ∣ Nat.card (G ⧸ H) := hodd.not_two_dvd_nat
  obtain ⟨q, hq⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
    (G ⧸ H) hodd'
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  have hP : P.toSubgroup ≤ χ.ker := by
    intro p hp
    let x : P := ⟨p, hp⟩
    have hx := hq x⁻¹
    change QuotientGroup.mk (j x⁻¹ * a) = QuotientGroup.mk a at hx
    have ha : a⁻¹ * j x * a ∈ H := by
      have ht := QuotientGroup.eq.mp hx
      simpa only [map_inv, mul_inv_rev, inv_inv, mul_assoc] using ht
    change χ p = 1
    rw [hχ]
    change f (j x) = 1
    rw [← hconj a⁻¹ (j x)]
    simpa only [inv_inv] using hH _ ha
  have hPodd : Odd P.toSubgroup.index :=
    Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using P.not_dvd_index)
  have ht := realFiniteCharacter_trivial_of_odd_index χ P.toSubgroup hPodd hP
  rw [← hχ ⟨g, Subgroup.mem_zpowers g⟩]
  exact ht _

/-- Average one on a subgroup forces all its values to be one, since
each real finite-order character takes only the values one and minus one. -/
theorem cyclic_real_classFunction_trivial_of_odd_average
    {G : Type*} [Group G] [Finite G]
    (f : G → ℝˣ)
    (hconj : ∀ a g, f (a * g * a⁻¹) = f g)
    (hcyclic : ∀ g : G, ∃ χ : Subgroup.zpowers g →* ℝˣ,
      ∀ x : Subgroup.zpowers g, χ x = f (x : G))
    (H : Subgroup G) [Fintype H] (hodd : Odd H.index)
    (havg : ∑ h : H, (f h : ℝ) = Fintype.card H) :
    ∀ g, f g = 1 := by
  apply cyclic_real_classFunction_trivial_of_odd_index f hconj hcyclic H hodd
  have hf (g : G) : (f g : ℝ) ≤ 1 := by
    obtain ⟨χ, hχ⟩ := hcyclic g
    have ht := realFiniteCharacter_values χ ⟨g, Subgroup.mem_zpowers g⟩
    rw [hχ] at ht
    rcases ht with ht | ht <;> simp [ht]
  have hs : ∑ h : H, (1 - (f h : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, havg]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (h : H) _ => sub_nonneg.mpr (hf h))).mp hs
  intro g hg
  apply Units.ext
  have ht := hz ⟨g, hg⟩ (Finset.mem_univ _)
  exact (sub_eq_zero.mp ht).symm

end DukePrimeDegree

end OAI
