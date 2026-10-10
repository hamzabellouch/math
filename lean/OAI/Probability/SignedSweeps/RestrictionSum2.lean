import OAI.Probability.SignedSweeps.RestrictionSum

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

def subdiagramLabels {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) : Fin m ↪ Fin n where
  toFun i := lam.tableau ⟨(μ.tableau.symm i).1, h (μ.tableau.symm i).2⟩
  inj' := by
    intro i j hij
    apply μ.tableau.symm.injective
    apply Subtype.ext
    exact congrArg (fun b : {c // c ∈ lam.1.cells} => b.1) (lam.tableau.injective hij)

@[simp] lemma subdiagramLabels_row {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (i : Fin m) : lam.rowOf (subdiagramLabels h i) = μ.rowOf i := by
  change (lam.tableau.symm (lam.tableau ⟨(μ.tableau.symm i).1, _⟩)).1.1 = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma subdiagramLabels_col {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (i : Fin m) : lam.colOf (subdiagramLabels h i) = μ.colOf i := by
  change (lam.tableau.symm (lam.tableau ⟨(μ.tableau.symm i).1, _⟩)).1.2 = _
  rw [Equiv.symm_apply_apply]
  rfl

def subdiagramEmbedding {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) : SymmetricGroup m →* SymmetricGroup n :=
  Equiv.Perm.viaEmbeddingHom (subdiagramLabels h)

lemma subdiagramEmbedding_row {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (a : rowSubgroup μ) : subdiagramEmbedding h a.1 ∈ rowSubgroup lam := by
  intro x
  by_cases hx : x ∈ Set.range (subdiagramLabels h)
  · obtain ⟨i, rfl⟩ := hx
    change lam.rowOf (a.1.viaEmbedding (subdiagramLabels h) (subdiagramLabels h i)) = _
    rw [Equiv.Perm.viaEmbedding_apply, subdiagramLabels_row, subdiagramLabels_row]
    exact a.2 i
  · change lam.rowOf (a.1.viaEmbedding _ x) = _
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]

lemma subdiagramEmbedding_col {m n : ℕ} {μ : Partition m} {lam : Partition n}
    (h : μ.1 ≤ lam.1) (a : colSubgroup μ) : subdiagramEmbedding h a.1 ∈ colSubgroup lam := by
  intro x
  by_cases hx : x ∈ Set.range (subdiagramLabels h)
  · obtain ⟨i, rfl⟩ := hx
    change lam.colOf (a.1.viaEmbedding (subdiagramLabels h) (subdiagramLabels h i)) = _
    rw [Equiv.Perm.viaEmbedding_apply, subdiagramLabels_col, subdiagramLabels_col]
    exact a.2 i
  · change lam.colOf (a.1.viaEmbedding _ x) = _
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]

lemma complexSign_viaEmbedding {m n : ℕ} (j : Fin m ↪ Fin n) (a : SymmetricGroup m) :
    complexSign n (Equiv.Perm.viaEmbeddingHom j a) = complexSign m a := by
  simp [complexSign, Equiv.Perm.viaEmbeddingHom, Equiv.Perm.extendDomainHom]

theorem subdiagram_specht_occurs {m n : ℕ} (μ : Partition m) (lam : Partition n)
    (h : μ.1 ≤ lam.1) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ)
      ((spechtRepresentation lam).comp (subdiagramEmbedding h)), Function.Injective f := by
  apply specht_occurs_of_row_average μ ((spechtRepresentation lam).comp (subdiagramEmbedding h))
    (fun g => spechtRepresentation_norm lam (subdiagramEmbedding h g)) (spechtGenerator lam)
  · intro c
    have he := spechtGenerator_column_action lam
      ⟨subdiagramEmbedding h c.1, subdiagramEmbedding_col h c⟩
    simpa only [MonoidHom.comp_apply, subdiagramEmbedding, complexSign_viaEmbedding] using he
  · let ρ := (spechtRepresentation lam).comp (subdiagramEmbedding h)
    have ha (a : rowSubgroup μ) :
        spechtInclusion lam (ρ a.1 (spechtGenerator lam)) 1 = 1 := by
      change polytabloid lam ((subdiagramEmbedding h a.1)⁻¹ * 1) = 1
      let b : rowSubgroup lam := ⟨subdiagramEmbedding h a.1, subdiagramEmbedding_row h a⟩
      calc
        _ = polytabloid lam (1 * (b⁻¹).1) := by simp [b]
        _ = polytabloid lam 1 := polytabloid_right_row lam b⁻¹ 1
        _ = 1 := polytabloid_at_one lam
    have he : spechtInclusion lam (groupAverage (ρ.comp (rowSubgroup μ).subtype)
        (spechtGenerator lam)) 1 = 1 := by
      have hn : (Fintype.card (rowSubgroup μ) : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
        map_smul, map_sum, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
      simp only [ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        smul_eq_mul, inv_mul_cancel₀ hn]
    intro hz
    rw [hz, map_zero, PiLp.zero_apply] at he
    exact zero_ne_one he

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

def blockEmbeddingHom {u v l n : ℕ} (h : u + v + l = n) :
    ((SymmetricGroup u × SymmetricGroup v) × SymmetricGroup l) →* SymmetricGroup n :=
  (blockEquiv h).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin u ⊕ Fin v) (Fin l)).comp
      ((Equiv.Perm.sumCongrHom (Fin u) (Fin v)).prodMap (MonoidHom.id _)))

@[simp] lemma blockEmbeddingHom_apply {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    blockEmbeddingHom h ((a,b),c) = blockEmbedding h a b c := rfl

def blockSpinInjection {u v l n : ℕ} (h : u + v + l = n) :
    (Fin u ⊕ Fin v) ↪ Fin n :=
  Function.Embedding.inl.trans (blockEquiv h).toEmbedding

lemma blockEmbedding_one_remainder {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    blockEmbedding h a b 1 = (a.sumCongr b).viaEmbedding (blockSpinInjection h) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (blockEquiv h).surjective x
  cases x with
  | inl y =>
    change (blockEquiv h).permCongr _ (blockEquiv h (Sum.inl y)) =
      (a.sumCongr b).viaEmbedding _ (blockSpinInjection h y)
    rw [Equiv.Perm.viaEmbedding_apply]
    simp [Equiv.permCongr_apply, blockSpinInjection]
  | inr z =>
    have hn : blockEquiv h (Sum.inr z) ∉ Set.range (blockSpinInjection h) := by
      rintro ⟨y, he⟩
      have he' := (blockEquiv h).injective he
      exact Sum.inl_ne_inr he'
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]
    simp [blockEmbedding_eq, Equiv.permCongr_apply]

lemma viaEmbedding_trans {A B C : Type*} (i : A ↪ B) (j : B ↪ C) (g : Equiv.Perm A) :
    g.viaEmbedding (i.trans j) = (g.viaEmbedding i).viaEmbedding j := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    by_cases hy : y ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hy
      change g.viaEmbedding (i.trans j) ((i.trans j) z) = j (g.viaEmbedding i (i z))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      rfl
    · have hn : j y ∉ Set.range (i.trans j) := by
        rintro ⟨z, he⟩
        exact hy ⟨z, j.injective he⟩
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy]
  · have hn : x ∉ Set.range (i.trans j) := by
      rintro ⟨z, rfl⟩
      exact hx ⟨i z, rfl⟩
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]

lemma sumCongr_viaEmbedding {A B C D : Type*} (i : A ↪ B) (j : C ↪ D)
    (a : Equiv.Perm A) (b : Equiv.Perm C) :
    (a.viaEmbedding i).sumCongr (b.viaEmbedding j) =
      (a.sumCongr b).viaEmbedding (i.sumMap j) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl y =>
    by_cases hy : y ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hy
      change Sum.inl (a.viaEmbedding i (i z)) =
        (a.sumCongr b).viaEmbedding _ ((i.sumMap j) (Sum.inl z))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      rfl
    · have hn : Sum.inl y ∉ Set.range (i.sumMap j) := by
        rintro ⟨z, he⟩
        cases z with
        | inl z => exact hy ⟨z, Sum.inl.inj he⟩
        | inr z => exact Sum.inr_ne_inl he
      change Sum.inl (a.viaEmbedding i y) = _
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]
  | inr y =>
    by_cases hy : y ∈ Set.range j
    · obtain ⟨z, rfl⟩ := hy
      change Sum.inr (b.viaEmbedding j (j z)) =
        (a.sumCongr b).viaEmbedding _ ((i.sumMap j) (Sum.inr z))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      rfl
    · have hn : Sum.inr y ∉ Set.range (i.sumMap j) := by
        rintro ⟨z, he⟩
        cases z with
        | inl z => exact Sum.inl_ne_inr he
        | inr z => exact hy ⟨z, Sum.inr.inj he⟩
      change Sum.inr (b.viaEmbedding j y) = _
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn]

lemma viaEmbedding_conjugate {A B : Type*} (i j : A ↪ B) (σ : Equiv.Perm B)
    (hσ : ∀ x, σ (i x) = j x) (g : Equiv.Perm A) :
    σ * g.viaEmbedding i * σ⁻¹ = g.viaEmbedding j := by
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ Set.range j
  · obtain ⟨x, rfl⟩ := hy
    have he : σ⁻¹ (j x) = i x := by
      rw [← hσ]; exact σ.symm_apply_apply (i x)
    simp only [Equiv.Perm.mul_apply, he, Equiv.Perm.viaEmbedding_apply, hσ]
  · have hn : σ⁻¹ y ∉ Set.range i := by
      rintro ⟨x, hx⟩
      apply hy
      refine ⟨x, ?_⟩
      rw [← hσ, hx]
      exact Equiv.apply_symm_apply σ y
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hn,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy]
    exact σ.apply_symm_apply y

def spinRestriction {u v l n : ℕ} (h : u + v + l = n) (lam : Partition n) :
    Representation ℂ (SymmetricGroup u × SymmetricGroup v) (Specht lam) :=
  (spechtRepresentation lam).comp ((blockEmbeddingHom h).comp
    (MonoidHom.inl (SymmetricGroup u × SymmetricGroup v) (SymmetricGroup l)))

@[simp] lemma spinRestriction_apply {u v l n : ℕ} (h : u + v + l = n) (lam : Partition n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    spinRestriction h lam (a,b) = spechtRepresentation lam (blockEmbedding h a b 1) := rfl

theorem signed_occurrence_of_spin_intertwiner {u v l n : ℕ} (h : u + v + l = n)
    (α : Partition u) (β : Partition v) (lam : Partition n)
    (f : Representation.IntertwiningMap
      (outerTensorRepresentation (spechtRepresentation α) (spechtRepresentation β.transpose))
      (spinRestriction h lam)) (hf : f ≠ 0) :
    ∃ γ : Partition l, SignedOccurrence h α β γ lam := by
  let ρ := outerTensorRepresentation (spechtRepresentation α) (spechtRepresentation β.transpose)
  let τ := (spechtRepresentation lam).comp (blockEmbeddingHom h)
  let : (spechtRepresentation α).IsIrreducible := specht_irreducible α
  let : (spechtRepresentation β.transpose).IsIrreducible := specht_irreducible β.transpose
  have hρ := outerTensorRepresentation_norm _ _
    (spechtRepresentation_norm α) (spechtRepresentation_norm β.transpose)
  let : ρ.IsIrreducible := outerTensorRepresentation_irreducible _ _
    (spechtRepresentation_norm α) (spechtRepresentation_norm β.transpose)
  obtain ⟨γ, k, hk⟩ := exists_external_specht_extension ρ τ hρ f hf
  refine ⟨γ, k.toLinearMap, hk, ?_⟩
  intro a b c x
  simpa only [τ, ρ, outerTensorRepresentation_apply, MonoidHom.comp_apply, blockEmbeddingHom_apply,
    Representation.IntertwiningMap.toLinearMap_apply]
    using (Representation.IntertwiningMap.isIntertwining _ _ k ((a,b),c) x)

theorem signed_occurrence_subdiagrams {u v l n u' v' L : ℕ}
    {h : u + v + l = n} {α : Partition u} {β : Partition v}
    {γ : Partition l} {lam : Partition n} (ho : SignedOccurrence h α β γ lam)
    (α' : Partition u') (β' : Partition v') (ha : α'.1 ≤ α.1) (hb : β'.1 ≤ β.1)
    (hL : u' + v' + L = n) :
    ∃ γ' : Partition L, SignedOccurrence hL α' β' γ' lam := by
  obtain ⟨F, hF, hinter⟩ := ho
  have hbt : β'.transpose.1 ≤ β.transpose.1 := YoungDiagram.transpose_mono hb
  obtain ⟨fa, hfa⟩ := subdiagram_specht_occurs α' α ha
  obtain ⟨fb, hfb⟩ := subdiagram_specht_occurs β'.transpose β.transpose hbt
  let i := (subdiagramLabels ha).sumMap (subdiagramLabels hbt)
  let j := i.trans (blockSpinInjection h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (blockSpinInjection hL) j (blockSpinInjection hL).injective j.injective
  have hconj (a : SymmetricGroup u') (b : SymmetricGroup v') :
      σ * blockEmbedding hL a b 1 * σ⁻¹ =
        blockEmbedding h (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1 := by
    rw [blockEmbedding_one_remainder, blockEmbedding_one_remainder]
    change σ * (a.sumCongr b).viaEmbedding (blockSpinInjection hL) * σ⁻¹ =
      ((a.viaEmbedding (subdiagramLabels ha)).sumCongr
        (b.viaEmbedding (subdiagramLabels hbt))).viaEmbedding (blockSpinInjection h)
    rw [sumCongr_viaEmbedding, ← viaEmbedding_trans]
    exact viaEmbedding_conjugate _ _ σ hσ _
  let A := Specht α ⊗[ℂ] Specht β.transpose
  let k : (Specht α' ⊗[ℂ] Specht β'.transpose) →ₗ[ℂ] Specht lam :=
    F.comp (((TensorProduct.mk ℂ A (Specht γ)).flip (spechtGenerator γ)).comp
      (TensorProduct.map fa.toLinearMap fb.toLinearMap))
  have hk (a : SymmetricGroup u') (b : SymmetricGroup v')
      (x : Specht α' ⊗[ℂ] Specht β'.transpose) :
      k (TensorProduct.map (spechtRepresentation α' a) (spechtRepresentation β'.transpose b) x) =
      spechtRepresentation lam
        (blockEmbedding h (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1) (k x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change F ((TensorProduct.map fa.toLinearMap fb.toLinearMap
        (TensorProduct.map _ _ (x ⊗ₜ[ℂ] y))) ⊗ₜ[ℂ] spechtGenerator γ) = _
      simp only [TensorProduct.map_tmul, Representation.IntertwiningMap.toLinearMap_apply]
      rw [fa.isIntertwining, fb.isIntertwining]
      have he := hinter (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1
        ((fa x ⊗ₜ[ℂ] fb y) ⊗ₜ[ℂ] spechtGenerator γ)
      dsimp [k, A] at *
      simpa only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        TensorProduct.map_tmul, Representation.IntertwiningMap.toLinearMap_apply,
        MonoidHom.comp_apply, map_one, Module.End.one_apply] using he
    | add x y hx hy => simp only [map_add, hx, hy]
  have hk0 : k ≠ 0 := by
    intro hz
    have hax : fa (spechtGenerator α') ≠ 0 := by
      intro he
      exact spechtGenerator_ne_zero α' (hfa (he.trans (map_zero fa).symm))
    have hby : fb (spechtGenerator β'.transpose) ≠ 0 := by
      intro he
      exact spechtGenerator_ne_zero β'.transpose (hfb (he.trans (map_zero fb).symm))
    have he := congrArg (fun t : (Specht α' ⊗[ℂ] Specht β'.transpose) →ₗ[ℂ] Specht lam =>
      t (spechtGenerator α' ⊗ₜ[ℂ] spechtGenerator β'.transpose)) hz
    change F ((fa (spechtGenerator α') ⊗ₜ[ℂ] fb (spechtGenerator β'.transpose)) ⊗ₜ[ℂ]
      spechtGenerator γ) = 0 at he
    exact complex_tmul_ne_zero (complex_tmul_ne_zero hax hby) (spechtGenerator_ne_zero γ)
      (hF (he.trans (map_zero F).symm))
  let k' := ((spechtRepresentation lam σ⁻¹).comp k).intertwiningMap_of_isIntertwiningMap
    (outerTensorRepresentation (spechtRepresentation α') (spechtRepresentation β'.transpose))
    (spinRestriction hL lam) (by
      rintro ⟨a,b⟩ x
      change spechtRepresentation lam σ⁻¹ (k (TensorProduct.map
        (spechtRepresentation α' a) (spechtRepresentation β'.transpose b) x)) =
        spechtRepresentation lam (blockEmbedding hL a b 1) (spechtRepresentation lam σ⁻¹ (k x))
      rw [hk]
      change (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam
        (blockEmbedding h (subdiagramEmbedding ha a) (subdiagramEmbedding hbt b) 1)) (k x) =
        (spechtRepresentation lam (blockEmbedding hL a b 1) * spechtRepresentation lam σ⁻¹) (k x)
      rw [← map_mul, ← map_mul, ← hconj]
      simp only [← mul_assoc, inv_mul_cancel, one_mul])
  apply signed_occurrence_of_spin_intertwiner hL α' β' lam k'
  intro hz
  apply hk0
  apply LinearMap.ext
  intro x
  have he := congrArg (fun t => spechtRepresentation lam σ (t x)) hz
  change (spechtRepresentation lam σ * spechtRepresentation lam σ⁻¹) (k x) = 0 at he
  simpa only [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, LinearMap.zero_apply] using he

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

lemma truncatePartition_le {n : ℕ} (q : ℕ) (lam : Partition n) :
    (truncatePartition q lam).1 ≤ lam.1 := by
  intro c hc
  change c ∈ YoungDiagram.ofRowLens _
    ((lam.1.rowLens_sorted.pairwise.sublist (List.take_sublist q _)).sortedGE) at hc
  obtain ⟨hi, hj⟩ := YoungDiagram.mem_ofRowLens.mp hc
  have hi' : c.1 < lam.1.rowLens.length := by
    rw [List.length_take] at hi
    exact lt_of_lt_of_le hi (min_le_right _ _)
  rw [List.getElem_take] at hj
  rw [YoungDiagram.get_rowLens] at hj
  exact YoungDiagram.mem_iff_lt_rowLen.mpr hj

lemma truncatePartition_length {n : ℕ} (q : ℕ) (lam : Partition n) :
    (truncatePartition q lam).1.rowLens.length ≤ q := by
  rw [truncatePartition_rowLens, List.length_take]
  exact min_le_left _ _

def truncatedRemainder {u v : ℕ} (q l : ℕ) (α : Partition u) (β : Partition v) : ℕ :=
  l + (α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum

lemma truncated_size_eq {u v l n : ℕ} (q : ℕ) (α : Partition u) (β : Partition v)
    (h : u + v + l = n) :
    (α.1.rowLens.take q).sum + (β.1.rowLens.take q).sum +
      truncatedRemainder q l α β = n := by
  have hu := List.sum_take_add_sum_drop α.1.rowLens q
  have hv := List.sum_take_add_sum_drop β.1.rowLens q
  rw [partition_rowLens_sum] at hu hv
  dsimp [truncatedRemainder]
  omega

theorem signed_occurrence_truncate {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (ho : SignedOccurrence h α β γ lam) (q : ℕ) :
    ∃ γ' : Partition (truncatedRemainder q l α β),
      SignedOccurrence (truncated_size_eq q α β h)
        (truncatePartition q α) (truncatePartition q β) γ' lam :=
  signed_occurrence_subdiagrams ho _ _ (truncatePartition_le q α)
    (truncatePartition_le q β) _

theorem signed_moment_of_bounded_lengths {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {d r q : ℕ} (hd : 1 ≤ d) (hq : 0 < q)
    (hcost : coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1 ≤
      coefficient η d * Real.log q)
    (H : ∀ (lam : Partition (2 ^ d)) (u v l : ℕ) (h : u + v + l = 2 ^ d)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      α.1.rowLens.length ≤ q → β.1.rowLens.length ≤ q →
      SignedOccurrence h α β γ lam →
      logMoment (weightedMoment lam r) ≤
        ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal))
    (lam : Partition (2 ^ d)) (u v l : ℕ) (h : u + v + l = 2 ^ d)
    (α : Partition u) (β : Partition v) (γ : Partition l)
    (ho : SignedOccurrence h α β γ lam) :
    logMoment (weightedMoment lam r) ≤
      ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  obtain ⟨γ', hγ'⟩ := signed_occurrence_truncate ho q
  have hm := H lam _ _ _ _ _ _ γ' (truncatePartition_length q α)
    (truncatePartition_length q β) hγ'
  exact hm.trans (EReal.coe_le_coe_iff.mpr (truncated_budget_le hη hκ hd h α β hq hcost))

end SignedSweeps
end

end OAI
