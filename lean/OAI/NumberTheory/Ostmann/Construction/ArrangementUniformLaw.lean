import OAI.NumberTheory.Ostmann.Construction.ArrangementProductImage
import OAI.NumberTheory.Ostmann.Preliminaries.UniformHomAverage
import OAI.NumberTheory.Ostmann.Tree.PairedRationalReduction

namespace OAI

/-! # The exact joint law of the two actual bulk leaf products -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def arrangementProductMap {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) :
    (L × Fin m → G) →* ((L → G) × (L → G)) where
  toFun x := (bulkBlockProduct x, bulkBlockProduct (x ∘ e.symm))
  map_one' := by ext <;> simp [bulkBlockProduct]
  map_mul' x y := by
    ext <;> simp [bulkBlockProduct, Function.comp_apply, Finset.prod_mul_distrib]

theorem mem_arrangementProductMap_range {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) (ab : (L → G) × (L → G)) :
    ab ∈ (arrangementProductMap (G := G) e).range ↔
      partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact arrangement_partition_products e x
  · intro h
    obtain ⟨x, hx, hy⟩ := arrangement_leaf_products_surjective hm e ab.1 ab.2 h
    exact ⟨x, Prod.ext hx hy⟩

noncomputable def arrangementRangeEquiv {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) :
    (arrangementProductMap (G := G) e).range ≃
      {ab : (L → G) × (L → G) //
        partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2} where
  toFun x := ⟨x.val, (mem_arrangementProductMap_range hm e x.val).mp x.property⟩
  invFun x := ⟨x.val, (mem_arrangementProductMap_range hm e x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem arrangementProductMap_range_card {L G : Type*} [Fintype L] [CommGroup G]
    [Fintype G] {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) :
    Fintype.card (arrangementProductMap (G := G) e).range =
      Fintype.card (L → G) * Fintype.card G ^
        (Fintype.card L - Fintype.card (arrangementGraph m e).ConnectedComponent) := by
  choose pivot hpivot using arrangementRight_surjective hm e
  rw [Fintype.card_congr (arrangementRangeEquiv (G := G) hm e)]
  exact (Fintype.card_subtype _).trans (card_pairedPartitions
    (arrangementLeft e) (arrangementRight e) (fun c => ⟨pivot c, hpivot c⟩))

theorem pairedPartitionCorrelation_fintype {L C G : Type*} [Finite L] [Finite C] [Finite G]
    [CommGroup G] (fL : Fintype L) (fC : Fintype C) (fG : Fintype G)
    (dL : DecidableEq L) (dC : DecidableEq C) (dG : DecidableEq G)
    (a b : L → C) (F H : (L → G) → ℂ) :
    @pairedPartitionCorrelation L C G fL fC dL dC _ fG dG a b F H =
      @pairedPartitionCorrelation L C G (Fintype.ofFinite L) (Fintype.ofFinite C)
        (Classical.decEq L) (Classical.decEq C) _ (Fintype.ofFinite G) (Classical.decEq G) a b F H := by
  cases Subsingleton.elim fL (Fintype.ofFinite L)
  cases Subsingleton.elim fC (Fintype.ofFinite C)
  cases Subsingleton.elim fG (Fintype.ofFinite G)
  cases Subsingleton.elim dL (Classical.decEq L)
  cases Subsingleton.elim dC (Classical.decEq C)
  cases Subsingleton.elim dG (Classical.decEq G)
  rfl

noncomputable def bulkPairCorrelation {L G : Type*} [Fintype L] [Fintype G] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (F H : (L → G) → ℂ) : ℂ :=
  (Fintype.card (L × Fin m → G) : ℂ)⁻¹ *
    ∑ x : L × Fin m → G, F (bulkBlockProduct x) * conj (H (bulkBlockProduct (x ∘ e.symm)))

theorem arrangement_uniform_correlation {L G : Type*} [Fintype L] [CommGroup G]
    [Fintype G] {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m))
    (F H : (L → G) → ℂ) :
    (Fintype.card (L × Fin m → G) : ℂ)⁻¹ *
      (∑ x : L × Fin m → G, F (bulkBlockProduct x) * conj (H (bulkBlockProduct (x ∘ e.symm)))) =
      pairedPartitionCorrelation (arrangementLeft e) (arrangementRight e) F H := by
  have hu := uniform_hom_average (arrangementProductMap (G := G) e).rangeRestrict
    (arrangementProductMap (G := G) e).rangeRestrict_surjective
    (fun y => F y.val.1 * conj (H y.val.2))
  change _ = (Fintype.card (arrangementProductMap (G := G) e).range : ℂ)⁻¹ * _ at hu
  rw [arrangementProductMap_range_card hm e] at hu
  apply hu.trans
  unfold pairedPartitionCorrelation
  push_cast
  congr 1
  rw [← (arrangementRangeEquiv (G := G) hm e).symm.sum_comp
    (fun y => F y.val.1 * conj (H y.val.2))]
  change (∑ y : {ab : (L → G) × (L → G) //
    partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2},
    F y.val.1 * conj (H y.val.2)) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun ab : (L → G) × (L → G) =>
    partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2))
    (by simp) (fun ab => F ab.1 * conj (H ab.2))]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem arrangement_uniform_norm_sq_le {L G : Type*} [Fintype L] [CommGroup G]
    [Fintype G] {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m))
    (F H : (L → G) → ℂ) (B : ℝ)
    (h : ‖pairedPartitionCorrelation (arrangementLeft e) (arrangementRight e) F H‖ ^ 2 ≤ B) :
    ‖bulkPairCorrelation e F H‖ ^ 2 ≤ B := by
  unfold bulkPairCorrelation
  rw [arrangement_uniform_correlation hm e F H]
  exact h

end Ostmann

end OAI
