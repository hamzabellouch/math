import OAI.Probability.SignedSweeps.OccurrenceDominance

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def pairColor {u v n : ℕ} {I J : Type*} (e : Fin u ⊕ Fin v ≃ Fin n)
    (a : Fin u → I) (b : Fin v → J) : Fin n → I ⊕ J :=
  Sum.map a b ∘ e.symm

lemma pairColor_factor {u v n : ℕ} {I J : Type*}
    (e : Fin u ⊕ Fin v ≃ Fin n) (a : Fin u → I) (b : Fin v → J)
    (g : fiberSubgroup (pairColor e a b)) :
    ∃ f : fiberSubgroup a, ∃ h : fiberSubgroup b,
      g.1 = e.permCongr (f.1.sumCongr h.1) := by
  have hg : e.symm.permCongr g.1 ∈ fiberSubgroup (Sum.map a b) := by
    intro x
    have hx := g.2 (e x)
    simpa only [pairColor, Function.comp_apply, Equiv.symm_apply_apply,
      Equiv.permCongr_apply, Equiv.symm_symm] using hx
  obtain ⟨f, h, he⟩ := fiberSubgroup_sum_factor a b ⟨_, hg⟩
  refine ⟨f, h, ?_⟩
  have he' := congrArg e.permCongr he
  apply Equiv.ext
  intro x
  simpa only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    using congrArg (fun t : Equiv.Perm (Fin n) => t x) he'

lemma complexSign_pair {u v n : ℕ} (e : Fin u ⊕ Fin v ≃ Fin n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) :
    complexSign n (e.permCongr (a.sumCongr b)) = complexSign u a * complexSign v b := by
  change (((Equiv.Perm.sign (e.permCongr (a.sumCongr b)) : ℤˣ) : ℤ) : ℂ) =
    (((Equiv.Perm.sign a : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ)
  simp only [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
    Units.val_mul, Int.cast_mul]

lemma pairColor_left_card {u v n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (e : Fin u ⊕ Fin v ≃ Fin n) (a : Fin u → I) (b : Fin v → J) (i : I) :
    Fintype.card {x : Fin n // pairColor e a b x = Sum.inl i} =
      Fintype.card {x : Fin u // a x = i} := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [pairColor, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr_ne_inl, ↓reduceIte,
    Finset.sum_const_zero, add_zero]

lemma pairColor_right_card {u v n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (e : Fin u ⊕ Fin v ≃ Fin n) (a : Fin u → I) (b : Fin v → J) (j : J) :
    Fintype.card {x : Fin n // pairColor e a b x = Sum.inr j} =
      Fintype.card {x : Fin v // b x = j} := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [pairColor, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.map_inl, Sum.map_inr, Sum.inr.injEq, Sum.inl_ne_inr, ↓reduceIte,
    Finset.sum_const_zero, zero_add]

lemma Partition.colIndex_fiber_card {n : ℕ} (lam : Partition n)
    (j : Fin (lam.1.rowLen 0)) :
    Fintype.card {x : Fin n // lam.colIndex x = j} = lam.1.colLen j := by
  let f : Fin (lam.1.colLen j) → {x : Fin n // lam.colIndex x = j} :=
    fun i => ⟨lam.colEquiv ⟨j,i⟩, Fin.ext (lam.colOf_colEquiv j i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have he := lam.colEquiv.injective (congrArg Subtype.val hab)
      exact (Sigma.mk.inj_iff.mp he).2.eq
    · intro x
      obtain ⟨⟨k,i⟩, he⟩ := lam.colEquiv.surjective x.1
      have hk : k = j := by
        apply Fin.ext
        have hx := congrArg Fin.val x.2
        simpa only [← he, Partition.colIndex, Partition.colOf_colEquiv] using hx
      subst k
      exact ⟨i, Subtype.ext he⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

lemma Partition.rowIndex_fiber_card {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) :
    Fintype.card {x : Fin n // lam.rowIndex x = i} = lam.1.rowLen i := by
  let f : Fin (lam.1.rowLen i) → {x : Fin n // lam.rowIndex x = i} :=
    fun j => ⟨lam.rowEquiv ⟨i,j⟩, Fin.ext (lam.rowOf_rowEquiv i j)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have he := lam.rowEquiv.injective (congrArg Subtype.val hab)
      exact (Sigma.mk.inj_iff.mp he).2.eq
    · intro x
      obtain ⟨⟨k,j⟩, he⟩ := lam.rowEquiv.surjective x.1
      have hk : k = i := by
        apply Fin.ext
        have hx := congrArg Fin.val x.2
        simpa only [← he, Partition.rowIndex, Partition.rowOf_rowEquiv] using hx
      subst k
      exact ⟨j, Subtype.ext he⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

theorem pair_occurrence_topRowCount {u v n : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b) →ₗ[ℂ] Specht lam) (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    topRowCount lam.1 k ≤ topRowCount a.1 k + topRowCount b.1 k := by
  let color := pairColor e a.colIndex b.colIndex
  let z := spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b
  have hz : f z ≠ 0 := by
    intro h
    exact complex_tmul_ne_zero (spechtGenerator_ne_zero a) (spechtGenerator_ne_zero b)
      (hf (h.trans (map_zero f).symm))
  have hact (g : fiberSubgroup color) :
      spechtRepresentation lam g.1 (f z) = complexSign n g.1 • f z := by
    obtain ⟨s, t, he⟩ := pairColor_factor e a.colIndex b.colIndex g
    have hs : s.1 ∈ colSubgroup a := by rw [← fiberSubgroup_colIndex]; exact s.2
    have ht : t.1 ∈ colSubgroup b := by rw [← fiberSubgroup_colIndex]; exact t.2
    rw [he, ← hint]
    simp only [z, TensorProduct.map_tmul,
      spechtGenerator_column_action a ⟨_,hs⟩, spechtGenerator_column_action b ⟨_,ht⟩,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, map_smul,
      complexSign_pair, mul_comm]
  obtain ⟨g, hg⟩ := alternating_vector_transversal lam color (f z) hz (by
    intro i j hij hc
    rw [hact ⟨Equiv.swap i j, swap_mem_fiberSubgroup _ hc⟩]
    change (((Equiv.Perm.sign (Equiv.swap i j) : ℤˣ) : ℤ) : ℂ) • _ = _
    simp only [Equiv.Perm.sign_swap hij, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul])
  have hb := transversal_topRowCount_le lam color g hg k
  rw [Fintype.sum_sum_type] at hb
  dsimp only [color] at hb
  have heL (j : Fin (a.1.rowLen 0)) := pairColor_left_card e a.colIndex b.colIndex j
  have heR (j : Fin (b.1.rowLen 0)) := pairColor_right_card e a.colIndex b.colIndex j
  simp only [Fintype.card_eq_nat_card] at hb heL heR
  rw [topRowCount_eq_sum_columns a.1, topRowCount_eq_sum_columns b.1]
  apply hb.trans_eq
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heL j).trans (by simpa only [Fintype.card_eq_nat_card] using a.colIndex_fiber_card j))))
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heR j).trans (by simpa only [Fintype.card_eq_nat_card] using b.colIndex_fiber_card j))))

lemma invariant_vector_column_transversal {n : ℕ} {C : Type*} (lam : Partition n)
    (color : Fin n → C) (v : Specht lam) (hv : v ≠ 0)
    (hswap : ∀ i j, i ≠ j → color i = color j →
      spechtRepresentation lam (Equiv.swap i j) v = v) :
    ∃ g : SymmetricGroup n, ∀ x y,
      lam.transpose.rowOf x = lam.transpose.rowOf y → color (g x) = color (g y) → x = y := by
  obtain ⟨e⟩ := specht_transpose_sign_equiv lam
  apply alternating_vector_transversal lam.transpose color (e.symm v)
  · intro hz
    apply hv
    have h := congrArg e hz
    simpa only [Representation.Equiv.apply_symm_apply, map_zero] using h
  · intro i j hij hc
    apply e.injective
    change e.toIntertwiningMap (spechtRepresentation lam.transpose (Equiv.swap i j) (e.symm v)) =
      e.toIntertwiningMap (-e.symm v)
    rw [e.toIntertwiningMap.isIntertwining, map_neg]
    have hev : e.toIntertwiningMap (e.symm v) = v := e.apply_symm_apply v
    rw [hev]
    change complexSign n (Equiv.swap i j) • spechtRepresentation lam (Equiv.swap i j) v = -v
    rw [hswap i j hij hc]
    change (((Equiv.Perm.sign (Equiv.swap i j) : ℤˣ) : ℤ) : ℂ) • _ = _
    simp only [Equiv.Perm.sign_swap hij, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul]

theorem pair_occurrence_topColCount {u v n : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b) →ₗ[ℂ] Specht lam) (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    topRowCount lam.1.transpose k ≤ topRowCount a.1.transpose k + topRowCount b.1.transpose k := by
  let color := pairColor e a.rowIndex b.rowIndex
  let z := spechtRowVector a ⊗ₜ[ℂ] spechtRowVector b
  have hz : f z ≠ 0 := by
    intro h
    exact complex_tmul_ne_zero (spechtRowVector_ne_zero a) (spechtRowVector_ne_zero b)
      (hf (h.trans (map_zero f).symm))
  have hact (g : fiberSubgroup color) : spechtRepresentation lam g.1 (f z) = f z := by
    obtain ⟨s, t, he⟩ := pairColor_factor e a.rowIndex b.rowIndex g
    have hs : s.1 ∈ rowSubgroup a := by rw [← fiberSubgroup_rowIndex]; exact s.2
    have ht : t.1 ∈ rowSubgroup b := by rw [← fiberSubgroup_rowIndex]; exact t.2
    rw [he, ← hint]
    simp only [z, TensorProduct.map_tmul,
      spechtRowVector_invariant a ⟨_,hs⟩, spechtRowVector_invariant b ⟨_,ht⟩]
  obtain ⟨g, hg⟩ := invariant_vector_column_transversal lam color (f z) hz
    (fun i j _ hc => hact ⟨Equiv.swap i j, swap_mem_fiberSubgroup _ hc⟩)
  have hb := transversal_topRowCount_le lam.transpose color g hg k
  rw [Fintype.sum_sum_type] at hb
  dsimp only [color] at hb
  have heL (j : Fin (a.1.colLen 0)) := pairColor_left_card e a.rowIndex b.rowIndex j
  have heR (j : Fin (b.1.colLen 0)) := pairColor_right_card e a.rowIndex b.rowIndex j
  simp only [Fintype.card_eq_nat_card] at hb heL heR
  have heT (μ : YoungDiagram) : topRowCount μ.transpose k =
      ∑ i : Fin (μ.colLen 0), min k (μ.rowLen i) := by
    rw [topRowCount_eq_sum_columns]
    have heR := YoungDiagram.rowLen_transpose μ 0
    rw [Fin.sum_univ_eq_sum_range (fun j => min k (μ.transpose.colLen j)),
      Fin.sum_univ_eq_sum_range (fun j => min k (μ.rowLen j)), heR]
    simp only [YoungDiagram.colLen_transpose]
  rw [heT a.1, heT b.1]
  apply hb.trans_eq
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heL j).trans (by simpa only [Fintype.card_eq_nat_card] using a.rowIndex_fiber_card j))))
    (Finset.sum_congr rfl (fun j _ => congrArg (min k) ((heR j).trans (by simpa only [Fintype.card_eq_nat_card] using b.rowIndex_fiber_card j))))

end SignedSweeps
end

end OAI
