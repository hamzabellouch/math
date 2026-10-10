import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungSpecht

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

def rowPrefix (μ : YoungDiagram) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Cell μ => row x < k)).card

def Dominates (μ ν : YoungDiagram) : Prop := ∀ k, rowPrefix ν k ≤ rowPrefix μ k

lemma filter_column_card (μ : YoungDiagram) (j k : ℕ) :
    ((columnCells μ j).filter (fun x => row x < k)).card = min k (μ.colLen j) := by
  have hinj := row_injectiveOn_column μ j
  rw [← Finset.card_image_of_injOn (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))]
  have he : (((columnCells μ j).filter (fun x => row x < k)).image row) =
      Finset.range (min k (μ.colLen j)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨x, ⟨hx, hk⟩, rfl⟩
      exact ⟨hk, Finset.mem_range.mp (image_row_columnCells μ j ▸
        Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
    · rintro ⟨hk, hj⟩
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp
        ((image_row_columnCells μ j).symm ▸ Finset.mem_range.mpr hj)
      exact ⟨x, ⟨hx, he ▸ hk⟩, he⟩
  rw [he, Finset.card_range]

lemma filter_injective_column_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j k : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ((columnCells μ j).filter (fun x => f x < k)).card ≤ min k (μ.colLen j) := by
  apply le_min
  · calc
      _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card_of_injOn f
        · intro x hx
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
        · exact hf.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
      _ = k := Finset.card_range k
  · rw [← card_columnCells μ j]
    exact Finset.card_le_card (Finset.filter_subset _ _)

lemma card_filter_eq_sum_columns (μ : YoungDiagram) (p : Cell μ → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ j ∈ (Finset.univ : Finset (Cell μ)).image col, ((columnCells μ j).filter p).card := by
  simp only [Finset.card_filter]
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) (fun x => if p x then 1 else 0)

theorem dominates_of_column_injective (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (he : ∀ j, Set.InjOn (fun x => row (e x)) (columnCells μ j)) : Dominates μ ν := by
  intro k
  have hc : rowPrefix ν k = (Finset.univ.filter (fun x : Cell μ => row (e x) < k)).card := by
    simp only [rowPrefix, Finset.card_filter]
    exact (Equiv.sum_comp e (fun x => if row x < k then 1 else 0)).symm
  rw [hc, card_filter_eq_sum_columns, rowPrefix, card_filter_eq_sum_columns]
  apply Finset.sum_le_sum
  intro j hj
  rw [filter_column_card]
  exact filter_injective_column_le μ _ j k (he j)

lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  have he : (Finset.univ.filter (fun x : Cell μ => row x < k+1)) =
      (Finset.univ.filter (fun x : Cell μ => row x < k)) ∪
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.univ.filter (fun x : Cell μ => row x < k))
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    omega
  rw [rowPrefix, he, Finset.card_union_of_disjoint hd]
  congr 1
  rw [YoungDiagram.rowLen_eq_card]
  apply Finset.card_bij (fun (x : Cell μ) _ => x.val)
  · intro x hx
    rw [YoungDiagram.mem_row_iff]
    exact ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    have h := YoungDiagram.mem_row_iff.mp hx
    exact ⟨⟨x, h.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h.2, rfl⟩

lemma dominates_antisymm {μ ν : YoungDiagram} (hμ : Dominates μ ν) (hν : Dominates ν μ) : μ = ν := by
  have hp (k : ℕ) : rowPrefix μ k = rowPrefix ν k := le_antisymm (hν k) (hμ k)
  have hr (k : ℕ) : μ.rowLen k = ν.rowLen k := by
    have h := hp (k+1)
    rw [rowPrefix_succ, rowPrefix_succ, hp k] at h
    exact Nat.add_left_cancel h
  apply SetLike.coe_injective
  ext x
  rcases x with ⟨i,j⟩
  simp only [SetLike.mem_coe, YoungDiagram.mem_iff_lt_rowLen, hr]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable {μ ν : YoungDiagram}

def crossAnti (e : Cell μ ≃ Cell ν) : Module.End ℂ (Tabloid ν → ℂ) :=
  ∑ c : C μ, signC μ c.val • tabloidRepresentation ν (e.permCongr c.val)

lemma crossAnti_apply (e : Cell μ ≃ Cell ν) (v : Tabloid ν → ℂ) :
    crossAnti e v = ∑ c : C μ, signC μ c.val •
      tabloidRepresentation ν (e.permCongr c.val) v := by
  simp [crossAnti, LinearMap.sum_apply]

lemma crossAnti_rep (e : Cell μ ≃ Cell ν) (c : C μ) (v : Tabloid ν → ℂ) :
    crossAnti e (tabloidRepresentation ν (e.permCongr c.val) v) =
      signC μ c.val • crossAnti e v := by
  rw [crossAnti_apply, crossAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val •
      (signC μ d.val • tabloidRepresentation ν (e.permCongr d.val) v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation ν (e.permCongr d.val)
    (tabloidRepresentation ν (e.permCongr c.val) v) =
    signC μ c.val • (signC μ (d*c).val •
      tabloidRepresentation ν (e.permCongr (d*c).val) v)
  simp only [Subgroup.coe_mul, map_mul, Equiv.permCongr_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

lemma crossAnti_basis_collision (e : Cell μ ≃ Cell ν) (t : Tabloid ν)
    {x y : Cell μ} (hne : x ≠ y) (hc : col x = col y) (ht : t.val (e x) = t.val (e y)) :
    crossAnti e (tabloidBasis ν t) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have he : e.permCongr c.val = Equiv.swap (e x) (e y) := by
    apply Equiv.ext
    intro z
    change e (Equiv.swap x y (e.symm z)) = _
    rw [Function.Injective.map_swap e.injective, e.apply_symm_apply]
  have hf : e.permCongr c.val • t = t := by
    rw [he]
    exact swap_fixes_tabloid ν _ ht
  have h := crossAnti_rep e c (tabloidBasis ν t)
  rw [rep_basis, hf, show signC μ c.val = -1 from signC_swap μ hne, neg_one_smul] at h
  ext u
  have hu := congrFun h u
  simp only [Pi.neg_apply] at hu
  change crossAnti e (tabloidBasis ν t) u = 0
  linear_combination (1/2 : ℂ) * hu

theorem crossAnti_eq_zero_of_not_dominates (e : Cell μ ≃ Cell ν) (h : ¬ Dominates μ ν) :
    crossAnti e = 0 := by
  have hb (t : Tabloid ν) : crossAnti e (tabloidBasis ν t) = 0 := by
    obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective ν t
    by_contra hn
    apply h
    apply dominates_of_column_injective μ ν (e.trans π.symm)
    intro j x hx y hy hxy
    by_contra hne
    apply hn
    exact crossAnti_basis_collision e _ hne
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy
  apply LinearMap.ext
  intro v
  have hv : crossAnti e v = 0 := by
    conv_lhs => rw [← sum_tabloidBasis ν v]
    simp only [map_sum, map_smul, hb, smul_zero, Finset.sum_const_zero]
  exact hv

lemma spechtInclude_column_sum :
    (∑ c : C μ, signC μ c.val • spechtRep μ c.val (spechtPoly μ)) =
      (Fintype.card (C μ) : ℂ) • spechtPoly μ := by
  apply spechtInclude_injective μ
  simp only [map_sum, map_smul, spechtInclude_rep, spechtInclude_poly]
  simpa only [columnAnti_apply] using columnAnti_polytabloid μ

theorem intertwiner_dominance (e : Cell μ ≃ Cell ν)
    (f : SpechtSpace μ →ₗ[ℂ] (Tabloid ν → ℂ))
    (hf : ∀ g v, f (spechtRep μ g v) = tabloidRepresentation ν (e.permCongr g) (f v))
    (hne : f (spechtPoly μ) ≠ 0) : Dominates μ ν := by
  by_contra h
  have he : crossAnti e (f (spechtPoly μ)) = (Fintype.card (C μ) : ℂ) • f (spechtPoly μ) := by
    rw [crossAnti_apply]
    simp_rw [← hf]
    have hh := congrArg f (spechtInclude_column_sum (μ := μ))
    simpa only [map_sum, map_smul] using hh
  rw [crossAnti_eq_zero_of_not_dominates e h, LinearMap.zero_apply] at he
  exact hne ((smul_eq_zero.mp he.symm).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem equivalence_implies_diagram_eq (e : Cell μ ≃ Cell ν)
    (f : SpechtSpace μ ≃ₗ[ℂ] SpechtSpace ν)
    (hf : ∀ g v, f (spechtRep μ g v) = spechtRep ν (e.permCongr g) (f v)) : μ = ν := by
  apply dominates_antisymm
  · apply intertwiner_dominance e ((spechtInclude ν).comp f.toLinearMap)
    · intro g v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf, spechtInclude_rep]
    · intro hz
      apply spechtPoly_ne_zero μ
      apply f.injective
      apply spechtInclude_injective ν
      simpa using hz
  · apply intertwiner_dominance e.symm ((spechtInclude μ).comp f.symm.toLinearMap)
    · intro g v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [show f.symm (spechtRep ν g v) =
        spechtRep μ (e.symm.permCongr g) (f.symm v) from by
          apply f.injective
          rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]
          congr 2
          exact (e.permCongr.apply_symm_apply g).symm]
      exact spechtInclude_rep μ _ _
    · intro hz
      apply spechtPoly_ne_zero ν
      apply f.symm.injective
      apply spechtInclude_injective μ
      simpa using hz

end BinaryCoordinateSweeps.Young

end

end OAI
