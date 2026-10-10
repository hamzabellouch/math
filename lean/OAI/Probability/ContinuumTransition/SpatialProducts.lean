import OAI.Probability.ContinuumTransition.TrialConfigurations

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem generalPartition_relabel {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (e : ι ≃ κ) :
    generalPartition φ β A ι = generalPartition φ β A κ := by
  let p : (ι → Space) ≃ᵐ (κ → Space) := MeasurableEquiv.piCongrLeft (fun _ : κ => Space) e
  have hp : MeasurePreserving p volume volume := by
    simpa only [volume_pi] using measurePreserving_piCongrLeft (fun _ : κ => volume) e
  have hpx (x : ι → Space) : p x = x ∘ e.symm := by
    funext i
    simpa only [p, Equiv.apply_symm_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ => Space) x (e.symm i))
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : κ → Space | ∀ i, x i ∈ A}
  have hpre : p ⁻¹' {x : κ → Space | ∀ i, x i ∈ A} =
      {x : ι → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hpx, Function.comp_apply]
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (e i)
    · intro h i
      exact h (e.symm i)
  rw [hpre] at heq
  simp only [hpx, symmetricWeight_relabel] at heq
  unfold generalPartition
  rw [Fintype.card_congr e, heq]

noncomputable def setPartition (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) : ℝ :=
  generalPartition φ β A (Fin N)

theorem generalPartition_eq_setPartition {ι : Type u_1} [Fintype ι]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    generalPartition φ β A ι = setPartition φ β A (Fintype.card ι) :=
  generalPartition_relabel φ β A (Fintype.equivFin ι)

theorem setPartition_zero (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    setPartition φ β A 0 = 1 := by
  have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
  simp [setPartition, generalPartition, symmetricWeight, realPairEnergy, hinj,
    Measure.real, volume_pi]

theorem setPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) :
    0 ≤ setPartition φ β A N := generalPartition_nonneg φ β A

theorem setPartition_translate (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) (a : Space) :
    setPartition φ β ((fun x => x+a) '' A) N = setPartition φ β A N := by
  let p : (Fin N → Space) ≃ᵐ (Fin N → Space) := MeasurableEquiv.addRight (fun _ => a)
  have hp : MeasurePreserving p volume volume := measurePreserving_add_right volume (fun _ => a)
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A}
  have hpre : p ⁻¹' {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A} =
      {x : Fin N → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    apply forall_congr'
    intro i
    change x i + a ∈ (fun y => y+a) '' A ↔ x i ∈ A
    simp only [mem_image, add_left_inj, exists_eq_right]
  have hsym (x : Fin N → Space) : symmetricWeight φ β (p x) = symmetricWeight φ β x :=
    symmetricWeight_translate φ β x a
  rw [hpre] at heq
  simp only [hsym] at heq
  simpa only [setPartition, generalPartition, Fintype.card_fin] using
    congrArg (fun z : ℝ => z / (N.factorial : ℝ)) heq.symm

theorem setPartition_binary_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a-b‖ ≤ 0) (n m : ℕ) :
    setPartition φ β A n * setPartition φ β B m ≤ setPartition φ β C (n+m) := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset (Fin (n+m))).card by simp)
  have hh := generalPartition_binary_lower hφ hβ hstable hA hB hC hd haC hbC hcross s
  simpa only [generalPartition_eq_setPartition, Fintype.card_coe, Fintype.card_subtype_compl,
    Fintype.card_fin, hs, Nat.add_sub_cancel_left] using hh

theorem setPartition_product_lower {κ : Type u_1} {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (A : κ → Set Space) (n : κ → ℕ) (s : Finset κ)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (s : Set κ).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, φ ‖a-b‖ ≤ 0)
    {C : Set Space} (hC : volume C ≠ ⊤) (hinc : ∀ i ∈ s, A i ⊆ C) :
    (∏ i ∈ s, setPartition φ β (A i) (n i)) ≤ setPartition φ β C (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simp [setPartition_zero]
  | @insert i s hi ih =>
    let U := ⋃ j ∈ s, A j
    have hU : MeasurableSet U := MeasurableSet.biUnion s.finite_toSet.countable (fun j hj =>
      hA j (Finset.mem_insert_of_mem hj))
    have hUC : U ⊆ C := iUnion₂_subset (fun j hj => hinc j (Finset.mem_insert_of_mem hj))
    have hUf : volume U ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hUC)
    have hsub : ∀ j ∈ s, A j ⊆ U := fun j hj => subset_iUnion₂_of_subset j hj Subset.rfl
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hUf hsub
    have hdis : Disjoint (A i) U := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro j hj
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have henergy : ∀ a ∈ A i, ∀ b ∈ U, φ ‖a-b‖ ≤ 0 := by
      intro a ha b hb
      obtain ⟨j, hj, hjb⟩ := mem_iUnion₂.mp hb
      exact hcross i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj)) a ha b hjb
    have hbin := setPartition_binary_lower hφ hβ hstable
      (hA i (Finset.mem_insert_self _ _)) hU hC hdis
      (hinc i (Finset.mem_insert_self _ _)) hUC henergy (n i) (∑ j ∈ s, n j)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (mul_le_mul_of_nonneg_left ih' (setPartition_nonneg φ β (A i) (n i))).trans hbin

end ContinuumTemperature
end

end OAI
