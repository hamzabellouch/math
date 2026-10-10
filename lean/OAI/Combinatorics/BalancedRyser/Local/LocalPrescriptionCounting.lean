import OAI.Combinatorics.BalancedRyser.Incidence.LocalOrderedPencils
import OAI.Combinatorics.BalancedRyser.Local.LocalAsymptotics
import OAI.Combinatorics.BalancedRyser.Local.LocalKernel
import OAI.Combinatorics.BalancedRyser.Local.LocalPatternTransport

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def prescriptionSlots (a : DirectionAssignment F b κ) (side : Fin b → Bool) :
    Fin b → Slot F := fun i => (a.1 i, side i)

def PencilPrescriptionOccurs (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (side : Fin b → Bool)
    (p : Point F) (C : Configuration F) : Prop :=
  Eligible P a ∧ AdmissibleBadCover P a bits p C.merged ∧
    ∀ i, (C.choice (prescriptionSlots a side i)).tuple = prescribedTuple P a bits i

abbrev PencilPrescriptions (R : Finset (EqualityPattern b κ)) :=
  R × DirectionAssignment F b κ × Bits b × (Fin b → Bool)

def prescriptionOccurs (R : Finset (EqualityPattern b κ))
    (p : Point F) (j : PencilPrescriptions (F := F) R) (C : Configuration F) : Prop :=
  PencilPrescriptionOccurs j.1.1 j.2.1 j.2.2.1 j.2.2.2 p C

def prescriptionRead (R : Finset (EqualityPattern b κ))
    (j : PencilPrescriptions (F := F) R) : Fin b → Slot F :=
  prescriptionSlots j.2.1 j.2.2.2

theorem orderedBadPencil_has_representative
    (R : Finset (EqualityPattern b κ))
    (hR : ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
      ∀ ij kl : Fin b × Fin 4,
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (p : Point F) (used : Fin b → Slot F) (C : Configuration F)
    (h : OrderedBadPencil b κ p used C) :
    ∃ j : PencilPrescriptions (F := F) R,
      prescriptionOccurs R p j C ∧ prescriptionRead R j = used := by
  obtain ⟨_, P, a, bits, he, hg, hm⟩ := h
  obtain ⟨Q, hQ, hPQ⟩ := hR P
  obtain ⟨e, heq⟩ := exists_classRelabeling hPQ
  let a' := relabelAssignment e a
  let side : Fin b → Bool := fun i => (used i).2
  have hs : prescriptionSlots a' side = used := by
    funext i
    apply Prod.ext
    · exact (hm i).1.symm
    · rfl
  refine ⟨(⟨Q, hQ⟩, a', bits, side), ?_, hs⟩
  change Eligible Q a' ∧ AdmissibleBadCover Q a' bits p C.merged ∧ _
  refine ⟨(eligible_relabelAssignment e heq a).mpr he,
    (admissibleBadCover_relabelAssignment e heq a bits p C.merged).mpr hg, ?_⟩
  intro i
  rw [hs]
  exact (hm i).2.1.trans (prescribedTuple_relabelAssignment e heq a bits i).symm

theorem selectedProbability_le_encodedOrder_sum
    {J : Type*} [Fintype J] (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E : Configuration F → Prop) (R : J → Configuration F → Prop)
    (read : J → Fin b → Slot F)
    (hcover : ∀ M v, 0 < w M v → E (configuration M v) →
      ∃ f : Fin b → Slot F, Function.Injective f ∧
        ∀ σ : Equiv.Perm (Fin b), ∃ j,
          R j (configuration M v) ∧ read j = f ∘ σ) :
    selectedProbability w E ≤
      (∑ j, selectedProbability w (R j)) / (b.factorial : ℝ) := by
  have h := OrderedEventCounting.weighted_encoded_order_bound
    (fun z : MergedPairs F × Output F => w z.1 z.2)
    (fun z => hw z.1 z.2) (fun z => E (configuration z.1 z.2))
    (fun j z => R j (configuration z.1 z.2)) read (fun z => hcover z.1 z.2)
  simp only [Fintype.sum_prod_type] at h
  have hd := div_le_div_of_nonneg_right h
    (show (0 : ℝ) ≤ Fintype.card (MergedPairs F) by positivity)
  simpa only [selectedProbability, Finset.sum_div, div_div, mul_comm] using hd

theorem bad_pencil_probability_le_canonical_sum
    (R : Finset (EqualityPattern b κ))
    (hR : ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
      ∀ ij kl : Fin b × Fin 4,
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (∑ j : PencilPrescriptions (F := F) R,
        selectedProbability w (prescriptionOccurs R p j)) / (b.factorial : ℝ) := by
  apply selectedProbability_le_encodedOrder_sum w hK.1 _ _ (prescriptionRead R)
  intro M v hv hbad
  obtain ⟨hV, hC, _, hcap⟩ := hK.2.2.1 M v hv
  obtain ⟨f, hf, hall⟩ := bad_local_cover_all_orders (configuration M v) hV hC p hcap
    hbad.1 hb hbad.2.1 hbad.2.2
  exact ⟨f, hf, fun σ => orderedBadPencil_has_representative R hR p (f ∘ σ)
    (configuration M v) (hall σ)⟩

theorem pencilPrescription_probability_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (side : Fin b → Bool)
    (p : Point F) :
    selectedProbability w (PencilPrescriptionOccurs P a bits side p) ≤
      if Eligible P a then (K / Fintype.card F) ^ b *
        offsetProbability (AdmissibleBadCover P a bits p) else 0 := by
  by_cases he : Eligible P a
  · rw [ite_eq_left he]
    have hi : Function.Injective (prescriptionSlots a side) := by
      intro i j hij
      exact he.1 (congrArg Prod.fst hij)
    let S : Finset (Slot F) := Finset.univ.image (prescriptionSlots a side)
    let t : Slot F → TupleCode F := Function.extend (prescriptionSlots a side)
      (fun i => KernelBridge.encodeTuple (prescribedTuple P a bits i))
      (fun _ => (fun _ => none, fun _ => false))
    have hcard : S.card = b := by
      rw [Finset.card_image_of_injective _ hi]
      simp
    have hp := KernelBridge.selected_prescription_and_offset_le Q w K hK S
      (fun _ => t) (AdmissibleBadCover P a bits p)
    rw [hcard] at hp
    refine (KernelBridge.selectedProbability_mono w hK.1 ?_).trans hp
    intro C hC
    refine ⟨hC.2.1, ?_⟩
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    change KernelBridge.encodeTuple (C.choice (prescriptionSlots a side i)).tuple =
      Function.extend (prescriptionSlots a side)
        (fun i => KernelBridge.encodeTuple (prescribedTuple P a bits i))
        (fun _ => (fun _ => none, fun _ => false)) (prescriptionSlots a side i)
    rw [hi.extend_apply, hC.2.2 i]
  · simp only [ite_eq_right he]
    simp only [selectedProbability, PencilPrescriptionOccurs, he, false_and,
      ite_false, Finset.sum_const_zero, zero_div, le_refl]

theorem bad_pencil_probability_le_canonical_offset_sum
    (R : Finset (EqualityPattern b κ))
    (hR : ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
      ∀ ij kl : Fin b × Fin 4,
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (∑ j : PencilPrescriptions (F := F) R,
        if Eligible j.1.1 j.2.1 then (K / Fintype.card F) ^ b *
          offsetProbability (AdmissibleBadCover j.1.1 j.2.1 j.2.2.1 p) else 0) /
        (b.factorial : ℝ) := by
  refine (bad_pencil_probability_le_canonical_sum R hR Q w K hK p hb).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  exact pencilPrescription_probability_le Q w K hK j.1.1 j.2.1 j.2.2.1 j.2.2.2 p

theorem exists_canonical_offset_bound (hb : 2 ≤ b) (hk : κ ≤ 2) :
    ∃ R : Finset (EqualityPattern b κ), R.card ≤ (4 * b) ^ 4 ∧
      ∀ (Q : RetentionRule F) (w : Kernel F) (K : ℝ), KernelConditions Q w K →
        ∀ p : Point F,
          selectedProbability w (fun C => C.splitMultiplicity p = b ∧
            reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
            (∑ j : PencilPrescriptions (F := F) R,
              if Eligible j.1.1 j.2.1 then (K / Fintype.card F) ^ b *
                offsetProbability (AdmissibleBadCover j.1.1 j.2.1 j.2.2.1 p) else 0) /
              (b.factorial : ℝ) := by
  obtain ⟨R, hcard, hR⟩ := PatternCodes.exists_pattern_representatives (by omega : 1 ≤ b) hk
  exact ⟨R, hcard, fun Q w K hK p =>
    bad_pencil_probability_le_canonical_offset_sum R hR Q w K hK p hb⟩

theorem canonical_offset_sum_eq (R : Finset (EqualityPattern b κ))
    (K : ℝ) (p : Point F) :
    (∑ j : PencilPrescriptions (F := F) R,
      if Eligible j.1.1 j.2.1 then (K / Fintype.card F) ^ b *
        offsetProbability (AdmissibleBadCover j.1.1 j.2.1 j.2.2.1 p) else 0) =
      (2 : ℝ) ^ b * (K / Fintype.card F) ^ b *
        ∑ P : R, ∑ bits : Bits b, directionBadCoverMass P.1 bits p := by
  have hgeom (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
      (bits : Bits b) :
      (fun M => Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) =
        AdmissibleBadCover P a bits p := by
    funext M
    apply propext
    exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩
  have hprod : (∑ j : PencilPrescriptions (F := F) R,
      if Eligible j.1.1 j.2.1 then (K / Fintype.card F) ^ b *
        offsetProbability (AdmissibleBadCover j.1.1 j.2.1 j.2.2.1 p) else 0) =
      ∑ P : R, ∑ a : DirectionAssignment F b κ, ∑ bits : Bits b,
        ∑ _side : Fin b → Bool, if Eligible P.1 a then (K / Fintype.card F) ^ b *
          offsetProbability (AdmissibleBadCover P.1 a bits p) else 0 := by
    simp only [PencilPrescriptions, Fintype.sum_prod_type]
  rw [hprod]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [directionBadCoverMass, hgeom]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

theorem bad_pencil_probability_le_direction_bound
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) (hk : κ ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hgeom : ∀ (P : EqualityPattern b κ) (bits : Bits b),
      directionBadCoverMass P bits p ≤ D) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (4 * (b : ℝ)) ^ 4 * (32 : ℝ) ^ b * (K / Fintype.card F) ^ b * D /
        (b.factorial : ℝ) := by
  obtain ⟨R, hcard, hR⟩ := PatternCodes.exists_pattern_representatives (by omega : 1 ≤ b) hk
  have hbound := bad_pencil_probability_le_canonical_offset_sum R hR Q w K hK p hb
  rw [canonical_offset_sum_eq] at hbound
  have hbits : Fintype.card (Bits b) = 16 ^ b := by
    simp [Bits]
  have hsum : (∑ P : R, ∑ bits : Bits b, directionBadCoverMass P.1 bits p) ≤
      (R.card : ℝ) * (16 : ℝ) ^ b * D := by
    calc
      _ ≤ ∑ _P : R, ∑ _bits : Bits b, D := by
        apply Finset.sum_le_sum
        intro P _
        exact Finset.sum_le_sum (fun bits _ => hgeom P.1 bits)
      _ = _ := by simp [hbits, mul_assoc]
  have hcard' : (R.card : ℝ) ≤ (4 * (b : ℝ)) ^ 4 := by exact_mod_cast hcard
  refine hbound.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
  calc
    _ ≤ (2 : ℝ) ^ b * (K / Fintype.card F) ^ b *
        ((R.card : ℝ) * (16 : ℝ) ^ b * D) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 : ℝ) ^ b * (K / Fintype.card F) ^ b *
        ((4 * (b : ℝ)) ^ 4 * (16 : ℝ) ^ b * D) := by gcongr
    _ = _ := by
      have hp : (2 : ℝ) ^ b * (16 : ℝ) ^ b = (32 : ℝ) ^ b := by
        rw [← mul_pow]
        norm_num
      rw [← hp]
      ring

theorem bad_pencil_probability_le_common_factor
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) (hk : κ ≤ 2)
    (t : ℝ) (ht : 0 ≤ t)
    (hgeom : ∀ (P : EqualityPattern b κ) (bits : Bits b),
      directionBadCoverMass P bits p ≤
        ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - κ) /
          (Fintype.card F : ℝ) ^ (4 * b) * t) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (4 * (b : ℝ)) ^ 4 * (1024 * K) ^ b / (b.factorial : ℝ) *
        (t / (Fintype.card F : ℝ) ^ κ) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty F)
  have hraw := bad_pencil_probability_le_direction_bound Q w K hK0 hK p hb hk
    (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - κ) /
      (Fintype.card F : ℝ) ^ (4 * b) * t) (by positivity) hgeom
  have hc := LocalAsymptotics.pencil_common_factor_le (Fintype.card F : ℝ) K b κ
    hq hK0 (by omega)
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ (4 * (b : ℝ)) ^ 4 * t / (b.factorial : ℝ) by positivity)
  refine hraw.trans ?_
  convert hm using 1 <;> push_cast <;> ring

end
end Balanced.Local

end OAI
