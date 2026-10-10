import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonAction

instance : Countable CutRing := Countable.of_equiv (ℤ × ℤ) (QuadraticAlgebra.equivProd 1 1).symm

theorem fract_fract_add (x y : ℝ) : Int.fract (Int.fract x + y) = Int.fract (x + y) := by
  change Int.fract (x - (⌊x⌋ : ℝ) + y) = _
  rw [sub_add_eq_add_sub, Int.fract_sub_intCast]

noncomputable def translate (a : ℕ) (u : CutRing × CutRing) (p : GenericSquare a) :
    GenericSquare a := by
  let k : CutRing × CutRing :=
    ((⌊p.val.1 + ordinary u.1⌋ : ℤ), (⌊p.val.2 + ordinary u.2⌋ : ℤ))
  refine ⟨(Int.fract (p.val.1 + ordinary u.1), Int.fract (p.val.2 + ordinary u.2)),
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
  have h := avoidsCuts_translate p.property.2.2 (u - k)
  convert h using 1
  simp only [k, Int.fract, Prod.fst_sub, Prod.snd_sub, map_sub, map_intCast]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

@[simp] theorem translate_val (a : ℕ) (u : CutRing × CutRing) (p : GenericSquare a) :
    (translate a u p).val =
      (Int.fract (p.val.1 + ordinary u.1), Int.fract (p.val.2 + ordinary u.2)) := rfl

@[simp] theorem translate_zero (a : ℕ) (p : GenericSquare a) : translate a 0 p = p := by
  apply Subtype.ext
  simp only [translate_val, Prod.fst_zero, Prod.snd_zero, map_zero, add_zero]
  exact Prod.ext (Int.fract_eq_self.mpr p.property.1) (Int.fract_eq_self.mpr p.property.2.1)

theorem translate_add (a : ℕ) (u v : CutRing × CutRing) (p : GenericSquare a) :
    translate a (u + v) p = translate a u (translate a v p) := by
  apply Subtype.ext
  simp only [translate_val, Prod.fst_add, Prod.snd_add, map_add]
  rw [fract_fract_add, fract_fract_add]
  congr 1 <;> congr 1 <;> ring

noncomputable def translation (a : ℕ) (u : CutRing × CutRing) : Equiv.Perm (GenericSquare a) where
  toFun := translate a u
  invFun := translate a (-u)
  left_inv p := by rw [← translate_add, neg_add_cancel, translate_zero]
  right_inv p := by rw [← translate_add, add_neg_cancel, translate_zero]

@[simp] theorem translation_apply (a : ℕ) (u : CutRing × CutRing) (p : GenericSquare a) :
    translation a u p = translate a u p := rfl

@[simp] theorem translation_mul (a : ℕ) (u v : CutRing × CutRing) :
    translation a (u + v) = translation a u * translation a v := by
  ext p
  exact translate_add a u v p

theorem translation_period (a : ℕ) (u : CutRing × CutRing) (k : ℤ × ℤ) :
    translation a (u + ((k.1 : CutRing), (k.2 : CutRing))) = translation a u := by
  ext p
  apply Subtype.ext
  simp [translate_val]

theorem translation_reduce (a : ℕ) (u : CutRing × CutRing) :
    translation a u = translation a
      ((u.1.im : CutRing) * cutTau, (u.2.im : CutRing) * cutTau) := by
  have hu : u = ((u.1.im : CutRing) * cutTau, (u.2.im : CutRing) * cutTau) +
      ((u.1.re : CutRing), (u.2.re : CutRing)) := by
    apply Prod.ext <;> apply QuadraticAlgebra.ext <;> simp [cutTau]
  calc
    _ = translation a (((u.1.im : CutRing) * cutTau, (u.2.im : CutRing) * cutTau) +
        ((u.1.re : CutRing), (u.2.re : CutRing))) := congrArg (translation a) hu
    _ = _ := translation_period _ _ (u.1.re, u.2.re)

theorem halfPlane_mem (a : ℕ) (j : Fin 4) (z : CutRing) :
    halfPlane a j z ∈ polygonAlgebra a :=
  BooleanSubalgebra.subset_closure ⟨j, z, rfl⟩

noncomputable def wrapIndices (u : CutRing × CutRing) : Finset (ℤ × ℤ) :=
  (Finset.Icc ⌊ordinary u.1⌋ (⌊ordinary u.1⌋ + 1)) ×ˢ
    (Finset.Icc ⌊ordinary u.2⌋ (⌊ordinary u.2⌋ + 1))

def wrapCell (a : ℕ) (u : CutRing × CutRing) (k : ℤ × ℤ) : Set (GenericSquare a) :=
  (halfPlane a 0 ((k.1 : CutRing) + 1 - u.1) ∩
    (halfPlane a 0 ((k.1 : CutRing) - u.1))ᶜ) ∩
  (halfPlane a 1 ((k.2 : CutRing) + 1 - u.2) ∩
    (halfPlane a 1 ((k.2 : CutRing) - u.2))ᶜ)

theorem wrapCell_mem (a : ℕ) (u : CutRing × CutRing) (k : ℤ × ℤ) :
    wrapCell a u k ∈ polygonAlgebra a :=
  BooleanSubalgebra.inf_mem
    (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))
    (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))

theorem mem_wrapCell {a : ℕ} (u : CutRing × CutRing) (k : ℤ × ℤ) (p : GenericSquare a) :
    p ∈ wrapCell a u k ↔
      ⌊p.val.1 + ordinary u.1⌋ = k.1 ∧ ⌊p.val.2 + ordinary u.2⌋ = k.2 := by
  simp only [wrapCell, Set.mem_inter_iff, halfPlane, Set.mem_ofPred_eq,
    Set.mem_compl_iff, cutForm, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_sub, map_add, map_one, map_intCast, not_lt, Int.floor_eq_iff]
  constructor
  · rintro ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem floor_wrap_mem {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (t : ℝ) :
    ⌊x + t⌋ ∈ Finset.Icc ⌊t⌋ (⌊t⌋ + 1) := by
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (by linarith [hx.1]),
    (Int.floor_mono (show x + t ≤ t + 1 by linarith [hx.2])).trans_eq (Int.floor_add_one t)⟩

theorem point_wrap_mem {a : ℕ} (u : CutRing × CutRing) (p : GenericSquare a) :
    (⌊p.val.1 + ordinary u.1⌋, ⌊p.val.2 + ordinary u.2⌋) ∈ wrapIndices u := by
  exact Finset.mem_product.mpr
    ⟨floor_wrap_mem p.property.1 _, floor_wrap_mem p.property.2.1 _⟩

theorem translate_on_wrap {a : ℕ} (u : CutRing × CutRing) (k : ℤ × ℤ)
    {p : GenericSquare a} (hp : p ∈ wrapCell a u k) :
    (translate a u p).val = p.val +
      (ordinary (u.1 - (k.1 : CutRing)), ordinary (u.2 - (k.2 : CutRing))) := by
  obtain ⟨h1, h2⟩ := (mem_wrapCell u k p).mp hp
  simp only [translate_val, Int.fract, h1, h2, map_sub, map_intCast]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem preimage_halfPlane (a : ℕ) (u : CutRing × CutRing) (j : Fin 4) (z : CutRing) :
    translate a u ⁻¹' halfPlane a j z =
      ⋃ k ∈ wrapIndices u, wrapCell a u k ∩
        halfPlane a j (z - integralCutForm a j
          (u.1 - (k.1 : CutRing), u.2 - (k.2 : CutRing))) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hp
    let k := (⌊p.val.1 + ordinary u.1⌋, ⌊p.val.2 + ordinary u.2⌋)
    have hk : p ∈ wrapCell a u k := (mem_wrapCell u k p).mpr ⟨rfl, rfl⟩
    refine ⟨k, point_wrap_mem u p, hk, ?_⟩
    change cutForm a j (translate a u p).val < ordinary z at hp
    rw [translate_on_wrap u k hk, cutForm_add, cutForm_ordinary a j (u.1 - (k.1 : CutRing), u.2 - (k.2 : CutRing))] at hp
    change cutForm a j p.val < ordinary (z - _)
    rw [map_sub]
    linarith
  · rintro ⟨k, _, hk, hp⟩
    change cutForm a j p.val < ordinary (z - _) at hp
    rw [map_sub] at hp
    change cutForm a j (translate a u p).val < ordinary z
    rw [translate_on_wrap u k hk, cutForm_add,
      cutForm_ordinary a j (u.1 - (k.1 : CutRing), u.2 - (k.2 : CutRing))]
    linarith

theorem polygon_preimage_translate {a : ℕ} (u : CutRing × CutRing)
    {U : Set (GenericSquare a)} (hU : U ∈ polygonAlgebra a) :
    translate a u ⁻¹' U ∈ polygonAlgebra a := by
  apply polygon_induction (P := fun V => translate a u ⁻¹' V ∈ polygonAlgebra a) ?_ ?_ ?_ ?_ hU
  · intro j z
    rw [preimage_halfPlane]
    exact BooleanSubalgebra.biSup_mem (wrapIndices u).finite_toSet
      (fun k _ => BooleanSubalgebra.inf_mem (wrapCell_mem a u k) (halfPlane_mem _ _ _))
  · simpa using (BooleanSubalgebra.bot_mem : (∅ : Set (GenericSquare a)) ∈ polygonAlgebra a)
  · intro U V hU hV; exact BooleanSubalgebra.sup_mem hU hV
  · intro U hU; exact BooleanSubalgebra.compl_mem hU

theorem polygon_image_translation {a : ℕ} (u : CutRing × CutRing)
    {U : Set (GenericSquare a)} (hU : U ∈ polygonAlgebra a) :
    translation a u '' U ∈ polygonAlgebra a := by
  rw [(translation a u).image_eq_preimage_symm]
  exact polygon_preimage_translate (-u) hU

private theorem exists_in_interval_avoiding (l r : ℝ) (hlr : l < r)
    (S : Set ℝ) (hS : S.Countable) : ∃ x ∈ Set.Ioo l r, x ∉ S := by
  apply Set.not_subset.mp
  intro h
  have := Cardinal.Real.Ioo_countable_iff.mp (hS.mono h)
  linarith

theorem generic_rectangle (a : ℕ) (l₁ r₁ l₂ r₂ : ℝ)
    (hl₁ : 0 ≤ l₁) (hr₁ : r₁ ≤ 1) (h₁ : l₁ < r₁)
    (hl₂ : 0 ≤ l₂) (hr₂ : r₂ ≤ 1) (h₂ : l₂ < r₂) :
    ∃ p : GenericSquare a, p.val.1 ∈ Set.Ioo l₁ r₁ ∧ p.val.2 ∈ Set.Ioo l₂ r₂ := by
  obtain ⟨x, hx, hx'⟩ := exists_in_interval_avoiding l₁ r₁ h₁
    (Set.range ordinary) (Set.countable_range ordinary)
  let t := Real.goldenRatio ^ a
  have ht : t ≠ 0 := ne_of_gt (pow_pos Real.goldenRatio_pos a)
  let S := Set.range ordinary ∪ Set.range (fun z : CutRing => ordinary z + t*x) ∪
    Set.range (fun z : CutRing => (x - ordinary z)/t)
  have hS : S.Countable := ((Set.countable_range ordinary).union
    (Set.countable_range _)).union (Set.countable_range _)
  obtain ⟨y, hy, hy'⟩ := exists_in_interval_avoiding l₂ r₂ h₂ S hS
  have hav : AvoidsCuts a (x,y) := by
    intro j z hz
    fin_cases j
    · exact hx' ⟨z, by simpa [cutForm] using hz.symm⟩
    · apply hy'
      exact Or.inl (Or.inl ⟨z, by simpa [cutForm] using hz.symm⟩)
    · apply hy'
      apply Or.inl ∘ Or.inr
      refine ⟨z, ?_⟩
      change ordinary z + t*x = y
      change y - t*x = ordinary z at hz
      linarith
    · apply hy'
      apply Or.inr
      refine ⟨z, ?_⟩
      apply (div_eq_iff ht).mpr
      change x - t*y = ordinary z at hz
      linarith
  exact ⟨⟨(x,y), ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ⟨by linarith [hy.1], by linarith [hy.2]⟩, hav⟩, hx, hy⟩

instance (a : ℕ) : Nonempty (GenericSquare a) := by
  obtain ⟨p, _⟩ := generic_rectangle a 0 1 0 1 le_rfl le_rfl zero_lt_one le_rfl le_rfl zero_lt_one
  exact ⟨p⟩

end PolygonAction

end SimpleAmenable
end
end

end OAI
