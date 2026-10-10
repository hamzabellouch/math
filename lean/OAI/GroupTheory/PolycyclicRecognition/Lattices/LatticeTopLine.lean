import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeNormalFlag
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalCyclicTopStep
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionHomologyBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalInvariantTopClass

namespace OAI

/-! # A nonzero top class above a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G] {r : ℕ}

theorem invariantTopLine_of_subgroup_eq (N M : Subgroup G) [N.Normal] [M.Normal]
    (h : N = M) (d : ℕ)
    (hN : ∃ A : Rep ℤ G,
      Nonempty (groupHomology (Rep.res N.subtype A) d ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ N A d g = 𝟙 _) :
    ∃ A : Rep ℤ G,
      Nonempty (groupHomology (Rep.res M.subtype A) d ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ M A d g = 𝟙 _ := by
  subst M
  exact hN

theorem exists_latticeTopLine_of_kernelLine
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ R : Rep ℤ q.ker, ∀ j, d < j → IsZero (groupHomology R j))
    (A : Rep ℤ G) (eA : groupHomology (Rep.res q.ker.subtype A) d ≃ₗ[ℤ] ℚ)
    (hA : ∀ g, normalHomologyMap ℤ q.ker A d g = 𝟙 _) :
    ∃ B : Rep ℤ G, Nonempty (groupHomology B (d + r) ≃ₗ[ℤ] ℚ) := by
  have H : ∀ i, i ≤ r →
      (∀ R : Rep ℤ (latticeNormalFlag q i), ∀ j, d + i < j → IsZero (groupHomology R j)) ∧
      ∃ B : Rep ℤ G,
        Nonempty (groupHomology (Rep.res (latticeNormalFlag q i).subtype B) (d + i) ≃ₗ[ℤ] ℚ) ∧
        ∀ g, normalHomologyMap ℤ (latticeNormalFlag q i) B (d + i) g = 𝟙 _ := by
    intro i
    induction i with
    | zero =>
      intro _
      let e := MulEquiv.subgroupCongr (latticeNormalFlag_zero q).symm
      exact ⟨homology_bound_of_equiv e d hbound,
        invariantTopLine_of_subgroup_eq q.ker (latticeNormalFlag q 0)
          (latticeNormalFlag_zero q).symm d ⟨A, ⟨eA⟩, hA⟩⟩

    | succ i ih =>
      intro hi
      obtain ⟨hb, B, ⟨eB⟩, hB⟩ := ih (by omega)
      let j : Fin r := ⟨i, by omega⟩
      let p := latticeNormalFlagStep q j
      obtain ⟨t, ht⟩ := latticeNormalFlagStep_generator q hq j
      have hker : p.ker = (latticeNormalFlag q i).subgroupOf (latticeNormalFlag q (i + 1)) :=
        latticeNormalFlagStep_ker q j
      have hle : latticeNormalFlag q i ≤ latticeNormalFlag q (i + 1) :=
        latticeNormalFlag_mono q (Nat.le_succ i)
      let e : p.ker ≃* latticeNormalFlag q i :=
        (MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe hle)
      have hbker := homology_bound_of_equiv e.symm (d + i) hb
      have hbnext := homology_bound_of_integer_quotient p t ht (d + i) hbker
      have hnext := exists_normalCyclicTopStep (latticeNormalFlag q i)
        (latticeNormalFlag q (i + 1)) hle p t ht hker (d + i) hb B eB hB
      have hdim : d + i + 1 = d + (i + 1) := Nat.add_assoc d i 1
      rw [hdim] at hbnext hnext
      exact ⟨hbnext, hnext⟩
  obtain ⟨_, B, ⟨eB⟩, _⟩ := H r (le_refl r)
  have eTop : groupHomology (Rep.res (⊤ : Subgroup G).subtype B) (d + r) ≃ₗ[ℤ] ℚ := by
    rw [latticeNormalFlag_top] at eB
    exact eB
  let E := groupHomology.mapIso (A := Rep.res (⊤ : Subgroup G).subtype B) (B := B)
    Subgroup.topEquiv (LinearEquiv.refl ℤ B.V) (by intro g; rfl) (d + r)
  exact ⟨B, ⟨E.symm.toLinearEquiv.trans eTop⟩⟩

theorem exists_latticeTopLine
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ A : Rep ℤ q.ker, ∀ j, d < j → IsZero (groupHomology A j))
    (R : Rep ℤ q.ker) (eR : R.V ≃ₗ[ℤ] ℤ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology R d), a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology R d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z)
    (hdetect : ∀ A : Rep ℤ q.ker, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A)) :
    ∃ B : Rep ℤ G, Nonempty (groupHomology B (d + r) ≃ₗ[ℤ] ℚ) := by
  obtain ⟨χ, _, hχ, _, hact⟩ := exists_rationalInvariantTopClass q.ker R eR d x hx htor hcomm hdetect
  obtain ⟨eA⟩ := rationalOrientation_topLine q.ker R eR d χ hχ x hx htor hcomm
  exact exists_latticeTopLine_of_kernelLine q hq d hbound (rationalCharacterRep χ) eA hact

end PolycyclicRecognition

end

end OAI
