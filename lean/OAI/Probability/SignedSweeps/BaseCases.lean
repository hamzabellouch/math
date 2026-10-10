import OAI.Probability.SignedSweeps.SpectralGap

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma partition_mem_bounds {n : ℕ} (lam : Partition n) {c : ℕ × ℕ}
    (hc : c ∈ lam.1.cells) : c.1 < n ∧ c.2 < n := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hc' := YoungDiagram.mem_iff_lt_colLen.mp hc
  have hrb : lam.1.rowLen c.1 ≤ n := by
    rw [YoungDiagram.rowLen_eq_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
  have hcb : lam.1.colLen c.2 ≤ n := by
    rw [YoungDiagram.colLen_eq_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
  exact ⟨hc'.trans_le hcb, hr.trans_le hrb⟩

instance partitionFinite (n : ℕ) : Finite (Partition n) := by
  let f : Partition n → {s // s ∈ (Finset.range n ×ˢ Finset.range n).powerset} :=
    fun lam => ⟨lam.1.cells, Finset.mem_powerset.mpr (by
      intro c hc
      simpa only [Finset.mem_product, Finset.mem_range] using partition_mem_bounds lam hc)⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

lemma rowOf_eq_zero {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1)
    (x : Fin n) : lam.rowOf x = 0 := by
  have hc := (lam.tableau.symm x).property
  have hb := YoungDiagram.mem_iff_lt_colLen.mp hc
  have ha := lam.1.colLen_anti 0 (lam.colOf x) (Nat.zero_le _)
  change lam.rowOf x < lam.1.colLen (lam.colOf x) at hb
  omega

lemma rowSubgroup_eq_top {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    rowSubgroup lam = ⊤ := by
  apply top_unique
  intro g _ x
  simp only [rowOf_eq_zero lam hl]

lemma colSubgroup_eq_bot {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    colSubgroup lam = ⊥ := by
  apply bot_unique
  intro g hg
  change g = 1
  apply Equiv.ext
  intro x
  change g x = x
  apply lam.tableau.symm.injective
  apply Subtype.ext
  apply Prod.ext
  · change lam.rowOf (g x) = lam.rowOf x
    rw [rowOf_eq_zero lam hl, rowOf_eq_zero lam hl]
  · exact hg x

def regularOnes (n : ℕ) : RegularSpace n := WithLp.toLp 2 (fun _ => 1)

@[simp]
lemma regularOnes_apply {n : ℕ} (g : SymmetricGroup n) : regularOnes n g = 1 := rfl

lemma regularOnes_ne_zero (n : ℕ) : regularOnes n ≠ 0 := by
  intro he
  have hh := congrArg (fun f : RegularSpace n => f 1) he
  simp at hh

lemma regularOnes_invariant {n : ℕ} (g : SymmetricGroup n) :
    regularRepresentation n g (regularOnes n) = regularOnes n := by
  ext x
  rfl

lemma polytabloid_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    polytabloid lam = regularOnes n := by
  classical
  have : Subsingleton (colSubgroup lam) := by
    rw [colSubgroup_eq_bot lam hl]
    infer_instance
  let : Unique (colSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  simp only [polytabloid, Fintype.sum_unique]
  rw [(Subsingleton.elim (default : colSubgroup lam) 1)]
  simp only [OneMemClass.coe_one, map_one, Units.val_one, Int.cast_one, one_smul, one_mul]
  have he : (∑ a : rowSubgroup lam, EuclideanSpace.single (a : SymmetricGroup n) (1 : ℂ)) =
      ∑ a : SymmetricGroup n, EuclideanSpace.single a (1 : ℂ) := by
    let e : rowSubgroup lam ≃ SymmetricGroup n :=
      { toFun := Subtype.val
        invFun := fun g => ⟨g, by rw [rowSubgroup_eq_top lam hl]; trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [he]
  ext x
  simp [regularOnes]

lemma spechtSubrepresentation_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    (spechtSubrepresentation lam).toSubmodule = Submodule.span ℂ {regularOnes n} := by
  change Submodule.span ℂ _ = _
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    simp [polytabloid_row lam hl, regularOnes_invariant]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨1, by simp [hx, polytabloid_row lam hl]⟩

lemma spechtDimension_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    spechtDimension lam = 1 := by
  change finrank ℂ (spechtSubrepresentation lam).toSubmodule = 1
  rw [spechtSubrepresentation_row lam hl]
  exact finrank_span_singleton (regularOnes_ne_zero n)

lemma spechtRepresentation_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1)
    (g : SymmetricGroup n) : spechtRepresentation lam g = 1 := by
  ext x
  have hx : spechtInclusion lam x ∈ Submodule.span ℂ {regularOnes n} := by
    rw [← spechtSubrepresentation_row lam hl]
    exact x.property
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  change regularRepresentation n g (spechtInclusion lam x) = spechtInclusion lam x
  rw [← hc, map_smul, regularOnes_invariant]

lemma layerOperator_row {d : ℕ} (lam : Partition (2 ^ d)) (hl : lam.1.colLen 0 ≤ 1)
    (i : Fin d) : layerOperator lam i = 1 := by
  classical
  ext x
  exact groupAverage_fixed ((spechtRepresentation lam).comp (coordinateSubgroup d i).subtype)
    x (fun g => by simpa using LinearMap.congr_fun (spechtRepresentation_row lam hl g.1) x)

lemma sweepOperator_row {d : ℕ} (lam : Partition (2 ^ d)) (hl : lam.1.colLen 0 ≤ 1) :
    sweepOperator lam = 1 := by
  have he : layerOperator lam = fun _ => 1 := funext (layerOperator_row lam hl)
  simp [sweepOperator, he, List.ofFn_const]

lemma weightedMoment_row {d : ℕ} (lam : Partition (2 ^ d)) (hl : lam.1.colLen 0 ≤ 1)
    (r : ℕ) : weightedMoment lam r = 1 := by
  simp [weightedMoment, sweepSquare, positiveSquare, sweepOperator_row lam hl,
    LinearMap.trace_one, spechtDimension_row lam hl]
  exact spechtDimension_row lam hl

lemma finite_base_moments (d₀ : ℕ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d ≤ d₀, ∀ lam : Partition (2 ^ d),
      weightedMoment lam r ≤ 1 := by
  let I := Σ d : Fin (d₀ + 1), Partition (2 ^ (d : ℕ))
  have he : ∀ i : I, ∀ᶠ r in Filter.atTop, weightedMoment i.2 r ≤ 1 := by
    intro ⟨d, lam⟩
    by_cases hl : 1 < lam.1.colLen 0
    · exact eventually_weightedMoment_le_one lam hl
    · exact Filter.Eventually.of_forall (fun r => by rw [weightedMoment_row lam (by omega)])
  have hh : ∀ᶠ r in Filter.atTop, ∀ i : I, weightedMoment i.2 r ≤ 1 :=
    Filter.eventually_all.mpr he
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hh
  refine ⟨max 1 r₀, le_max_left _ _, ?_⟩
  intro r hr d hd lam
  exact hr₀ r ((le_max_right _ _).trans hr) ⟨⟨d, by omega⟩, lam⟩

end SignedSweeps
end

end OAI
