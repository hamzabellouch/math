import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentConjugationWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActionDepth

namespace OAI

/-! # Pulling the rational action filtration back to the group

The rational filtration on an abelian normal subgroup gives actual ambient
subgroups. Commuting with the ambient group advances the filtration. Its last
term is trivial when the abelian subgroup is torsion free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

def rationalPreimageSubgroup (W : Submodule ℚ (RationalAbelianSpace H)) : Subgroup H where
  carrier := {a | rationalAbelianMap (Additive.ofMul a) ∈ W}
  one_mem' := by
    change rationalAbelianMap 0 ∈ W
    rw [map_zero]
    exact W.zero_mem
  mul_mem' ha hb := by
    change rationalAbelianMap (Additive.ofMul _ + Additive.ofMul _) ∈ W
    rw [map_add]
    exact W.add_mem ha hb
  inv_mem' ha := by
    change rationalAbelianMap (-Additive.ofMul _) ∈ W
    rw [map_neg]
    exact W.neg_mem ha

def rationalSubgroupFiltration (n : ℕ) : Subgroup G :=
  (rationalPreimageSubgroup H (linearActionFiltration
    (fun g => (rationalConjugation H g).toLinearMap - 1) n)).map H.subtype

theorem rationalSubgroupFiltration_zero : rationalSubgroupFiltration H 0 = H := by
  have htop : rationalPreimageSubgroup H ⊤ = ⊤ := by ext; simp [rationalPreimageSubgroup]
  simp only [rationalSubgroupFiltration, linearActionFiltration, htop,
    Subgroup.map_top, Subgroup.range_subtype]

theorem rationalAbelianMap_conjugationDifference (g : G) (a : Additive H) :
    rationalAbelianMap (integralConjugationDifference H g a) =
      ((rationalConjugation H g).toLinearMap - 1) (rationalAbelianMap a) := by
  rw [rationalConjugationDifference_baseChange]
  rfl

theorem rationalSubgroupFiltration_commutator (n : ℕ) :
    ⁅rationalSubgroupFiltration H n, (⊤ : Subgroup G)⁆ ≤ rationalSubgroupFiltration H (n + 1) := by
  apply Subgroup.commutator_le.mpr
  rintro x ⟨a, ha, rfl⟩ y _
  let b := (integralConjugationDifference H y (Additive.ofMul a)).toMul
  have hD : rationalAbelianMap (integralConjugationDifference H y (Additive.ofMul a)) ∈
      linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) (n + 1) := by
    rw [rationalAbelianMap_conjugationDifference]
    exact ActionDepth.generator y n _ ha
  refine ⟨b⁻¹, ?_, ?_⟩
  · change rationalAbelianMap (-integralConjugationDifference H y (Additive.ofMul a)) ∈
      linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) (n + 1)
    rw [map_neg]
    exact Submodule.neg_mem _ hD
  · change (b : G)⁻¹ = ⁅(a : G), y⁆
    rw [show (b : G) = ⁅y, (a : G)⁆ from integralConjugationDifference_apply H y _]
    exact commutatorElement_inv y (a : G)

theorem rationalSubgroupFiltration_eq_bot (hH : HasNoNontrivialTorsion H) {n : ℕ}
    (hn : linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) n = ⊥) :
    rationalSubgroupFiltration H n = ⊥ := by
  apply eq_bot_iff.mpr
  rintro g ⟨a, ha, rfl⟩
  change rationalAbelianMap (Additive.ofMul a) ∈
    linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) n at ha
  rw [hn, Submodule.mem_bot] at ha
  have ha0 : Additive.ofMul a = 0 := rationalAbelianMap_injective hH (by simpa using ha)
  exact congrArg (fun x : Additive H => ((x.toMul : H) : G)) ha0

theorem lowerCentralSeries_le_rationalSubgroupFiltration (r : ℕ)
    (hr : (⊤ : Subgroup G).lowerCentralSeries r ≤ H) (n : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries (r + n) ≤ rationalSubgroupFiltration H n := by
  induction n with
  | zero => simpa only [Nat.add_zero, rationalSubgroupFiltration_zero] using hr
  | succ n ih =>
    rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ]
    exact (Subgroup.commutator_mono ih le_rfl).trans (rationalSubgroupFiltration_commutator H n)

end PolycyclicRecognition

end

end OAI
