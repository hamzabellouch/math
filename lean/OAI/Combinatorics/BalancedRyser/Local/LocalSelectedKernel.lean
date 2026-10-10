import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletion
import OAI.Combinatorics.BalancedRyser.Local.LocalKernel

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def encodeOutput (M : MergedPairs F) (y : SelectedDeletion.Output F) : Output F :=
  fun s => encodeChoice (retainedChoice M (s.1, y s))

@[simp] theorem configuration_encodeOutput (M : MergedPairs F)
    (y : SelectedDeletion.Output F) :
    configuration M (encodeOutput M y) = SelectedDeletion.configuration M y := by
  simp only [configuration, encodeOutput, decode_encode_choice, SelectedDeletion.configuration]

def transportedKernel (κ : SelectedDeletion.Kernel F) : Kernel F :=
  fun M v => ∑ y, if encodeOutput M y = v then κ M y else 0

theorem sum_transported_event (κ : SelectedDeletion.Kernel F) (M : MergedPairs F)
    (E : Output F → Prop) :
    (∑ v, if E v then transportedKernel κ M v else 0) =
      ∑ y, if E (encodeOutput M y) then κ M y else 0 := by
  rw [← Finset.sum_filter]
  unfold transportedKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp

theorem transported_nonneg (κ : SelectedDeletion.Kernel F)
    (hκ : ∀ M y, 0 ≤ κ M y) : ∀ M v, 0 ≤ transportedKernel κ M v := by
  intro M v
  unfold transportedKernel
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact hκ M y
  · exact le_rfl

theorem exists_positive_preimage (κ : SelectedDeletion.Kernel F)
    (hκ : ∀ M y, 0 ≤ κ M y) {M : MergedPairs F} {v : Output F}
    (hv : 0 < transportedKernel κ M v) :
    ∃ y, encodeOutput M y = v ∧ 0 < κ M y := by
  unfold transportedKernel at hv
  obtain ⟨y, _, hy⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ => by
    split_ifs
    · exact hκ M y
    · exact le_rfl)).mp hv
  by_cases he : encodeOutput M y = v
  · exact ⟨y, he, by simpa [he] using hy⟩
  · simp [he] at hy

theorem canonical_choice_mem (M : MergedPairs F) (g : Direction F) (a : F)
    (h : ValidChoice M g (retainedChoice M (g, a))) :
    encodeChoice (retainedChoice M (g, a)) ∈ (canonicalRetention (F := F)).candidates M g := by
  apply Finset.mem_image.mpr
  refine ⟨(g, a), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, rfl, ?_⟩
  exact ⟨(retainedChoice M (g, a)).tuple, h⟩

theorem positive_outputs_tuple_eq
    (κ : SelectedDeletion.Kernel F) (c C : ℝ)
    (hκ : SelectedDeletion.IsExperiment κ c C) (M : MergedPairs F)
    (x y : SelectedDeletion.Output F) (hx : 0 < κ M x) (hy : 0 < κ M y)
    (s : Slot F) (heq : (encodeOutput M x s).2 = (encodeOutput M y s).2) :
    x s = y s := by
  have vx := (hκ.2.2.2 M x hx).1.2 s
  have vy := (hκ.2.2.2 M y hy).1.2 s
  have hc := retained_tuple_injective (canonicalRetention (F := F)) M s.1
    (canonical_choice_mem M s.1 (x s) vx)
    (canonical_choice_mem M s.1 (y s) vy) heq
  exact congrArg (fun z : ChoiceCode F => z.1.2) hc

theorem transported_cylinder_le
    (κ : SelectedDeletion.Kernel F) (c C K : ℝ) (hK : 0 ≤ K)
    (hκ : SelectedDeletion.IsExperiment κ c C)
    (hcyl : ∀ M (S : Finset (Slot F)) (a : SelectedDeletion.Output F),
      SelectedDeletion.fixedCylinderMass κ M S a ≤
        (K / Fintype.card F) ^ S.card)
    (M : MergedPairs F) (S : Finset (Slot F)) (t : Slot F → TupleCode F) :
    (∑ v, if ∀ s ∈ S, (v s).2 = t s then transportedKernel κ M v else 0) ≤
      (K / Fintype.card F) ^ S.card := by
  have hsum := sum_transported_event κ M (fun v => ∀ s ∈ S, (v s).2 = t s)
  have hsum' : (∑ v, if ∀ s ∈ S, (v s).2 = t s then transportedKernel κ M v else 0) =
      ∑ y, if ∀ s ∈ S, (encodeOutput M y s).2 = t s then κ M y else 0 := by
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    · apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> rfl
  rw [hsum']
  by_cases hex : ∃ y : SelectedDeletion.Output F,
      0 < κ M y ∧ ∀ s ∈ S, (encodeOutput M y s).2 = t s
  · obtain ⟨a, ha, hat⟩ := hex
    apply le_trans _ (hcyl M S a)
    unfold SelectedDeletion.fixedCylinderMass
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : 0 < κ M y
    · by_cases ht : ∀ s ∈ S, (encodeOutput M y s).2 = t s
      · have hya : ∀ s ∈ S, y s = a s := by
          intro s hs
          exact positive_outputs_tuple_eq κ c C hκ M y a hy ha s
            ((ht s hs).trans (hat s hs).symm)
        split_ifs; try contradiction
        exact le_rfl
      · simp only [ht, ite_false]
        split_ifs
        · exact hκ.1 M y
        · exact le_rfl
    · have hz : κ M y = 0 := le_antisymm (le_of_not_gt hy) (hκ.1 M y)
      simp [hz]
  · have hz : (∑ y : SelectedDeletion.Output F,
        if ∀ s ∈ S, (encodeOutput M y s).2 = t s then κ M y else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      split_ifs with ht
      · exact le_antisymm (le_of_not_gt (fun hy => hex ⟨y, hy, ht⟩)) (hκ.1 M y)
      · rfl
    rw [hz]
    positivity

theorem transported_kernelConditions
    (κ : SelectedDeletion.Kernel F) (c C K : ℝ) (hK : 0 ≤ K)
    (hκ : SelectedDeletion.IsExperiment κ c C)
    (hcyl : ∀ M (S : Finset (Slot F)) (a : SelectedDeletion.Output F),
      SelectedDeletion.fixedCylinderMass κ M S a ≤
        (K / Fintype.card F) ^ S.card) :
    KernelConditions canonicalRetention (transportedKernel κ) K := by
  refine ⟨transported_nonneg κ hκ.1, ?_, ?_, transported_cylinder_le κ c C K hK hκ hcyl⟩
  · intro M
    have hs := sum_transported_event κ M (fun _ => True)
    have hs' : (∑ v, transportedKernel κ M v) = ∑ y, κ M y := by
      simpa using hs
    exact hs'.trans_le (hκ.2.1 M)
  · intro M v hv
    obtain ⟨y, rfl, hy⟩ := exists_positive_preimage κ hκ.1 hv
    have hvalid := hκ.2.2.2 M y hy
    have hgood : SelectedDeletion.InitialGood M c C := by
      by_contra hbad
      have hz := hκ.2.2.1 M hbad y
      linarith
    rw [configuration_encodeOutput]
    refine ⟨hvalid.1, hvalid.2, ?_, ?_⟩
    · intro s
      exact canonical_choice_mem M s.1 (y s) (hvalid.1.2 s)
    · intro p
      exact hgood.1.2.2.2.1 p

theorem original_offset_atom_real (M : MergedPairs F) :
    ((offsetLaw F) M).toReal = (Fintype.card (MergedPairs F) : ℝ)⁻¹ := by
  simp [offsetLaw]

theorem transported_probability_eq_jointMass (κ : SelectedDeletion.Kernel F)
    (E : Configuration F → Prop) :
    selectedProbability (transportedKernel κ) E =
      SelectedDeletion.jointMass κ (fun M y => E (SelectedDeletion.configuration M y)) := by
  have hinner : ∀ M : MergedPairs F,
      (∑ v : Output F, if E (configuration M v) then transportedKernel κ M v else 0) =
        ∑ y : SelectedDeletion.Output F,
          if E (SelectedDeletion.configuration M y) then κ M y else 0 := by
    intro M
    have hs := sum_transported_event κ M (fun v => E (configuration M v))
    simpa only [configuration_encodeOutput] using hs
  unfold selectedProbability SelectedDeletion.jointMass
  simp_rw [hinner, original_offset_atom_real]
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

theorem transported_successMass_eq (κ : SelectedDeletion.Kernel F) :
    selectedProbability (transportedKernel κ) (fun _ => True) =
      SelectedDeletion.successMass κ := by
  exact transported_probability_eq_jointMass κ (fun _ => True)

end
end Balanced.Local.KernelBridge

end OAI
