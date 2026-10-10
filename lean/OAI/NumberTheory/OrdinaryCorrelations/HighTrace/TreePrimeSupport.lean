import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardTreeVerticesLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeFactorsCardLeLog

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def treePrimeSupport (w : ClosedLine h ℓ) : Finset ℕ :=
  w.treeSteps.biUnion (fun i => (w.label i).primeFactors)

lemma treePrimeSupport_card_le (w : ClosedLine h ℓ) (hlabels : ∀ i, w.label i ∈ D.members) :
    (treePrimeSupport w).card ≤ ℓ * ⌈C₀ * Real.log B⌉₊ := by
  have hcard : w.treeSteps.card ≤ ℓ := by
    exact (card_le_card (filter_subset _ _)).trans_eq (by simp)
  exact (card_biUnion_le_card_mul w.treeSteps _ _
    (fun i _ => D.omega _ (hlabels i))).trans (Nat.mul_le_mul_right _ hcard)

lemma Specification.primeSupport_card_le (s : S.Specification D h L) :
    s.primeSupport.card ≤ L * ⌈C₀ * Real.log B⌉₊ + 1 := by
  calc
    _ ≤ (univ.biUnion (fun i : Fin s.length => (s.label i).primeFactors)).card + 1 :=
      card_insert_le _ _
    _ ≤ s.length * ⌈C₀ * Real.log B⌉₊ + 1 := by
      gcongr
      simpa only [card_univ, Fintype.card_fin] using card_biUnion_le_card_mul
        (univ : Finset (Fin s.length)) (fun i => (s.label i).primeFactors) _
        (fun i _ => D.omega _ (s.label_mem i))
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ s.length_le) _

lemma listSupport_card_le (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :
    (listSupport w 𝔏).card ≤ 𝔏.length * (L * ⌈C₀ * Real.log B⌉₊ + 1) := by
  exact (card_biUnion_le_card_mul 𝔏.toFinset _ _
    (fun s _ => s.spec.primeSupport_card_le)).trans
    (Nat.mul_le_mul_right _ (List.toFinset_card_le _))

lemma usedPrime_mem_support (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) : UsedPrime w 𝔏 p ↔ (p : ℕ) ∈ treePrimeSupport w ∪ listSupport w 𝔏 := by
  unfold UsedPrime
  rw [mem_union]
  refine or_congr ?_ Iff.rfl
  unfold treePrimeSupport
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨het,hep⟩ := mem_filter.mp he
    exact mem_biUnion.mpr ⟨e,het, Nat.mem_primeFactors.mpr
      ⟨S.prime_mem p p.property,hep,(w.label_pos e).ne'⟩⟩
  · intro hm
    obtain ⟨e,he,hep⟩ := mem_biUnion.mp hm
    exact ⟨e,mem_filter.mpr ⟨he,(Nat.mem_primeFactors.mp hep).2.1⟩⟩

def usedIndices (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) : Finset S.Index :=
  univ.filter (UsedPrime w 𝔏)

def lineListSlots (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) : ℕ :=
  ℓ * ⌈C₀ * Real.log B⌉₊ + 𝔏.length * (L * ⌈C₀ * Real.log B⌉₊ + 1)

lemma usedIndices_card_le (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (hlabels : ∀ i, w.label i ∈ D.members) :
    (usedIndices w 𝔏).card ≤ lineListSlots w 𝔏 := by
  have hsub : (usedIndices w 𝔏).image Subtype.val ⊆ treePrimeSupport w ∪ listSupport w 𝔏 := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := mem_image.mp hp
    rw [← hqp]
    exact (usedPrime_mem_support w 𝔏 q).mp (mem_filter.mp hq).2
  calc
    _ = ((usedIndices w 𝔏).image Subtype.val).card :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (treePrimeSupport w ∪ listSupport w 𝔏).card := card_le_card hsub
    _ ≤ (treePrimeSupport w).card + (listSupport w 𝔏).card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (treePrimeSupport_card_le w hlabels) (listSupport_card_le w 𝔏)

lemma restorationError_le_masses (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :
    restorationError w 𝔏 ≤ ((ℓ : ℝ)+1) *
      ((∑ p ∈ usedIndices w 𝔏, (p : ℝ)⁻¹) +
       ∑ p ∈ collisionIndices (S := S) w, (p : ℝ)⁻¹) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [usedIndices, collisionIndices, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  unfold OmittedPrime
  by_cases hu : UsedPrime w 𝔏 p <;> by_cases hc : IsCollision w p <;>
    simp [hu,hc, inv_nonneg.mpr (show 0 ≤ (p : ℝ) from Nat.cast_nonneg _)]

lemma card_tree_offDiag_le (w : ClosedLine h ℓ) :
    (treeVertices w).offDiag.card ≤ (ℓ+1)^2 := by
  have hsub : (treeVertices w).offDiag ⊆ (treeVertices w) ×ˢ (treeVertices w) := by
    intro vu hvu
    obtain ⟨hv,hu,_⟩ := mem_offDiag.mp hvu
    exact mem_product.mpr ⟨hv,hu⟩
  calc
    _ ≤ ((treeVertices w) ×ˢ (treeVertices w)).card := card_le_card hsub
    _ = (treeVertices w).card * (treeVertices w).card := card_product _ _
    _ ≤ (ℓ+1) * (ℓ+1) := Nat.mul_le_mul (card_treeVertices_le w) (card_treeVertices_le w)
    _ = _ := (pow_two _).symm

theorem restorationError_le (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (hlabels : ∀ i, w.label i ∈ D.members) (M P₀ : ℝ) (hM₀ : 0 ≤ M) (hP₀ : 0 < P₀)
    (hp : ∀ p : S.Index, P₀ ≤ (p : ℝ))
    (hM : ∀ v ∈ treeVertices w, ∀ u ∈ treeVertices w,
      v ≠ u → ((u-v).natAbs : ℝ) ≤ Real.exp M) :
    restorationError w 𝔏 ≤ ((ℓ : ℝ)+1) *
      ((lineListSlots w 𝔏 : ℝ) + ((ℓ : ℝ)+1)^2 * (M / Real.log 2)) / P₀ := by
  have huCard : ((usedIndices w 𝔏).card : ℝ) ≤ (lineListSlots w 𝔏 : ℝ) := by
    exact_mod_cast usedIndices_card_le w 𝔏 hlabels
  have hused := (sum_inv_le_card_div (usedIndices w 𝔏) P₀ hP₀ (fun p _ => hp p)).trans
    (div_le_div_of_nonneg_right huCard hP₀.le)
  have hcoll := collision_reciprocal_mass w M P₀ hP₀ hp hM
  have hcoll' : (∑ p ∈ collisionIndices (S := S) w, (p : ℝ)⁻¹) ≤
      ((ℓ : ℝ)+1)^2 * (M / Real.log 2) / P₀ := by
    apply hcoll.trans
    apply div_le_div_of_nonneg_right _ hP₀.le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_tree_offDiag_le w)
      (div_nonneg hM₀ (Real.log_nonneg (by norm_num)))
  apply (restorationError_le_masses w 𝔏).trans
  have hm := mul_le_mul_of_nonneg_left (add_le_add hused hcoll') (by positivity : 0 ≤ (ℓ : ℝ)+1)
  convert hm using 1
  ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
