import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableUnionDimension
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GroupDimensionTransport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeCyclicExtension

namespace OAI

/-! # An increasing union of inverse images under an automorphism -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

variable {G : Type} [Group G] (α : MulAut G) (B : Subgroup G)

def automorphismStage (n : ℕ) : Subgroup G :=
  B.map ((α⁻¹) ^ n).toMonoidHom

@[simp] theorem automorphismStage_zero : automorphismStage α B 0 = B := by
  change B.map (MonoidHom.id G) = B
  exact Subgroup.map_id B

def automorphismStageEquiv (n : ℕ) : B ≃* automorphismStage α B n :=
  B.equivMapOfInjective ((α⁻¹) ^ n).toMonoidHom ((α⁻¹) ^ n).injective

theorem automorphismStage_monotone (hB : B.map α.toMonoidHom ≤ B) :
    Monotone (automorphismStage α B) := by
  apply monotone_nat_of_le_succ
  intro n
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨α b, hB ⟨b, hb, rfl⟩, ?_⟩
  simp [pow_succ]

theorem mem_automorphismStage_iff (n : ℕ) (g : G) :
    g ∈ automorphismStage α B n ↔ (α ^ n) g ∈ B := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    change (α ^ n) (((α⁻¹) ^ n) b) ∈ B
    rw [inv_pow, MulAut.apply_inv_self]
    exact hb
  · intro hg
    refine ⟨(α ^ n) g, hg, ?_⟩
    change ((α⁻¹) ^ n) ((α ^ n) g) = g
    simp only [inv_pow, MulAut.inv_apply_self]

theorem automorphism_pow_mem_of_stable (hB : B.map α.toMonoidHom ≤ B)
    (n : ℕ) {g : G} (hg : g ∈ B) : (α ^ n) g ∈ B := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact hB ⟨_, ih, rfl⟩

theorem automorphismStage_map_succ (n : ℕ) :
    (automorphismStage α B (n + 1)).map α.toMonoidHom = automorphismStage α B n := by
  rw [automorphismStage, Subgroup.map_map, automorphismStage]
  congr 1
  ext g
  simp [pow_succ']

theorem automorphismStage_stable (hB : B.map α.toMonoidHom ≤ B) (n : ℕ) :
    (automorphismStage α B n).map α.toMonoidHom ≤ automorphismStage α B n := by
  cases n with
  | zero => simpa only [automorphismStage_zero] using hB
  | succ n =>
    rw [automorphismStage_map_succ]
    exact automorphismStage_monotone α B hB (Nat.le_succ n)

theorem automorphism_iSup_invariant (hB : B.map α.toMonoidHom ≤ B) :
    (⨆ n, automorphismStage α B n).map α.toMonoidHom =
      ⨆ n, automorphismStage α B n := by
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro n
    cases n with
    | zero =>
      have h0 : B ≤ ⨆ n, automorphismStage α B n := by
        simpa only [automorphismStage_zero] using le_iSup (automorphismStage α B) 0
      rw [automorphismStage_zero]
      exact hB.trans h0
    | succ n =>
      rw [automorphismStage_map_succ]
      exact le_iSup _ n
  · apply iSup_le
    intro n
    calc
      automorphismStage α B n =
          (automorphismStage α B (n + 1)).map α.toMonoidHom :=
        (automorphismStage_map_succ α B n).symm
      _ ≤ ⨆ i, (automorphismStage α B i).map α.toMonoidHom :=
        le_iSup (fun i : ℕ => (automorphismStage α B i).map α.toMonoidHom) (n + 1)

theorem cohomologicalDimension_of_automorphism_exhaustion
    (hB : B.map α.toMonoidHom ≤ B)
    (hcover : ∀ g, ∃ n, g ∈ automorphismStage α B n)
    (d : ℕ) [HasProjectiveDimensionLE (trivialIntegral B) d] :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) :=
  cohomologicalDimension_le_of_exhaustion (automorphismStage α B)
    (automorphismStage_monotone α B hB) hcover d
    (fun n => cohomologicalDimension_le_of_equiv (automorphismStageEquiv α B n) d)

theorem torsionFree_of_automorphism_exhaustion
    (hcover : ∀ g, ∃ n, g ∈ automorphismStage α B n)
    (htf : HasNoNontrivialTorsion B) : HasNoNontrivialTorsion G := by
  intro g m hm hgm
  obtain ⟨n, hn⟩ := hcover g
  have ht := htf.of_injective (automorphismStageEquiv α B n).symm.toMonoidHom
    (automorphismStageEquiv α B n).symm.injective
  have he : (⟨g, hn⟩ : automorphismStage α B n) ^ m = 1 := Subtype.ext hgm
  exact congrArg Subtype.val (ht ⟨g, hn⟩ m hm he)

end PolycyclicRecognition

end

end OAI
