import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.HookWord

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

variable (μ : YoungDiagram) (p : ℕ)

def hookPart : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1 < p ∨ x.2 < p)
  isLowerSet := by
    intro y x hxy hx
    rcases Finset.mem_filter.mp hx with ⟨hx,hp⟩
    apply Finset.mem_filter.mpr
    refine ⟨μ.isLowerSet hxy hx, ?_⟩
    rcases hp with hp | hp
    · exact Or.inl (lt_of_le_of_lt hxy.1 hp)
    · exact Or.inr (lt_of_le_of_lt hxy.2 hp)

def shiftCell (x : ℕ × ℕ) : ℕ × ℕ := (x.1+p,x.2+p)

lemma shiftCell_injective : Function.Injective (shiftCell p) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;> simp_all [shiftCell]

def southeast : YoungDiagram where
  cells := μ.cells.preimage (shiftCell p) (shiftCell_injective p).injOn
  isLowerSet := by
    intro y x hxy hx
    apply Finset.mem_preimage.mpr
    apply μ.isLowerSet _ (Finset.mem_preimage.mp hx)
    exact ⟨Nat.add_le_add_right hxy.1 _, Nat.add_le_add_right hxy.2 _⟩

@[simp] lemma mem_hookPart (x : ℕ × ℕ) :
    x ∈ hookPart μ p ↔ x ∈ μ ∧ (x.1 < p ∨ x.2 < p) := by
  change x ∈ μ.cells.filter (fun x => x.1 < p ∨ x.2 < p) ↔
    x ∈ μ.cells ∧ (x.1 < p ∨ x.2 < p)
  exact Finset.mem_filter

@[simp] lemma mem_southeast (x : ℕ × ℕ) :
    x ∈ southeast μ p ↔ (x.1+p,x.2+p) ∈ μ := by
  change x ∈ μ.cells.preimage (shiftCell p) (shiftCell_injective p).injOn ↔ shiftCell p x ∈ μ.cells
  exact Finset.mem_preimage

lemma hookPart_inHook : InHook (hookPart μ p) p := by
  intro x
  exact ((mem_hookPart μ p x.val).mp x.property).2

def hookIn : Cell (hookPart μ p) ↪ Cell μ where
  toFun x := ⟨x.val, ((mem_hookPart μ p x.val).mp x.property).1⟩
  inj' _ _ h := Subtype.ext (congrArg (fun a : Cell μ => a.val) h)

def southeastIn : Cell (southeast μ p) ↪ Cell μ where
  toFun x := ⟨(x.val.1+p,x.val.2+p), (mem_southeast μ p x.val).mp x.property⟩
  inj' _ _ h := Subtype.ext ((shiftCell_injective p) (congrArg Subtype.val h))

@[simp] lemma row_hookIn (x : Cell (hookPart μ p)) : row (hookIn μ p x) = row x := rfl
@[simp] lemma col_hookIn (x : Cell (hookPart μ p)) : col (hookIn μ p x) = col x := rfl
@[simp] lemma row_southeastIn (x : Cell (southeast μ p)) : row (southeastIn μ p x) = row x+p := rfl
@[simp] lemma col_southeastIn (x : Cell (southeast μ p)) : col (southeastIn μ p x) = col x+p := rfl

def cutEquiv : Cell (hookPart μ p) ⊕ Cell (southeast μ p) ≃ Cell μ where
  toFun := Sum.elim (hookIn μ p) (southeastIn μ p)
  invFun x := if h : row x < p ∨ col x < p then
    Sum.inl ⟨x.val,(mem_hookPart μ p x.val).mpr ⟨x.property,h⟩⟩
    else Sum.inr ⟨(row x-p,col x-p), (mem_southeast μ p _).mpr (by
      have hr : p ≤ row x := by omega
      have hc : p ≤ col x := by omega
      change (row x-p+p,col x-p+p) ∈ μ
      rw [Nat.sub_add_cancel hr,Nat.sub_add_cancel hc]
      exact x.property)⟩
  left_inv := by
    intro x
    cases x with
    | inl x =>
      dsimp only [Sum.elim]
      split_ifs with h
      · rfl
      · exact (h (hookPart_inHook μ p x)).elim
    | inr x =>
      dsimp only [Sum.elim]
      split_ifs with h
      · have h' : row x+p<p ∨ col x+p<p := h
        omega
      · apply congrArg Sum.inr
        apply Subtype.ext
        change (row x+p-p,col x+p-p) = x.val
        simp [row,col]
  right_inv := by
    intro x
    dsimp
    split_ifs with h
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · change row x-p+p = row x
        omega
      · change col x-p+p = col x
        omega

@[simp] lemma cutEquiv_inl (x : Cell (hookPart μ p)) :
    cutEquiv μ p (Sum.inl x) = hookIn μ p x := rfl
@[simp] lemma cutEquiv_inr (x : Cell (southeast μ p)) :
    cutEquiv μ p (Sum.inr x) = southeastIn μ p x := rfl

lemma card_cut : Fintype.card (Cell μ) =
    Fintype.card (Cell (hookPart μ p))+Fintype.card (Cell (southeast μ p)) := by
  rw [← Fintype.card_congr (cutEquiv μ p),Fintype.card_sum]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Equiv Equiv.Perm

variable (μ : YoungDiagram) (p : ℕ)

def cutPerm : (G (hookPart μ p) × G (southeast μ p)) →* G μ :=
  (cutEquiv μ p).permCongrHom.toMonoidHom.comp (sumCongrHom _ _)

lemma cutPerm_apply_hook (g : G (hookPart μ p) × G (southeast μ p))
    (x : Cell (hookPart μ p)) :
    cutPerm μ p g (hookIn μ p x) = hookIn μ p (g.1 x) := by
  change (cutEquiv μ p) ((Equiv.sumCongr g.1 g.2) ((cutEquiv μ p).symm (cutEquiv μ p (Sum.inl x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma cutPerm_apply_southeast (g : G (hookPart μ p) × G (southeast μ p))
    (x : Cell (southeast μ p)) :
    cutPerm μ p g (southeastIn μ p x) = southeastIn μ p (g.2 x) := by
  change (cutEquiv μ p) ((Equiv.sumCongr g.1 g.2) ((cutEquiv μ p).symm (cutEquiv μ p (Sum.inr x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma cutPerm_injective : Function.Injective (cutPerm μ p) :=
  (cutEquiv μ p).permCongr.injective.comp sumCongrHom_injective

lemma signC_cutPerm (g : G (hookPart μ p) × G (southeast μ p)) :
    signC μ (cutPerm μ p g) = signC (hookPart μ p) g.1 * signC (southeast μ p) g.2 := by
  change (((sign ((cutEquiv μ p).permCongr (Equiv.sumCongr g.1 g.2))) : ℤ) : ℂ) = _
  rw [sign_permCongr,sign_sumCongr,Units.val_mul,Int.cast_mul]
  rfl

def glueLabels (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) (x : Cell μ) : ℕ :=
  Sum.elim (fun a => t.1.val a) (fun a => t.2.val a+p) ((cutEquiv μ p).symm x)

@[simp] lemma glueLabels_hook (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p))
    (x : Cell (hookPart μ p)) : glueLabels μ p t (hookIn μ p x) = t.1.val x := by
  change Sum.elim _ _ ((cutEquiv μ p).symm ((cutEquiv μ p) (Sum.inl x))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma glueLabels_southeast (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p))
    (x : Cell (southeast μ p)) : glueLabels μ p t (southeastIn μ p x) = t.2.val x+p := by
  change Sum.elim _ _ ((cutEquiv μ p).symm ((cutEquiv μ p) (Sum.inr x))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma labels_cutPerm (g : G (hookPart μ p) × G (southeast μ p)) :
    labels μ (cutPerm μ p g) =
      glueLabels μ p (tabloidOfPerm (hookPart μ p) g.1,tabloidOfPerm (southeast μ p) g.2) := by
  funext x
  obtain ⟨y,rfl⟩ := (cutEquiv μ p).surjective x
  cases y with
  | inl y =>
    simp only [labels,← map_inv,cutEquiv_inl,cutPerm_apply_hook,row_hookIn,glueLabels_hook]
    rfl
  | inr y =>
    simp only [labels,← map_inv,cutEquiv_inr,cutPerm_apply_southeast,row_southeastIn,glueLabels_southeast]
    rfl

def glueTabloid (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) : Tabloid μ := by
  refine ⟨glueLabels μ p t, ?_⟩
  obtain ⟨g,hg⟩ := tabloidOfPerm_surjective (hookPart μ p) t.1
  obtain ⟨d,hd⟩ := tabloidOfPerm_surjective (southeast μ p) t.2
  refine ⟨cutPerm μ p (g,d),?_⟩
  rw [labels_cutPerm,hg,hd]

@[simp] lemma glueTabloid_val (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    (glueTabloid μ p t).val = glueLabels μ p t := rfl

lemma glueTabloid_injective : Function.Injective (glueTabloid μ p) := by
  intro t u h
  apply Prod.ext
  · apply Subtype.ext
    funext x
    have hh := congrArg (fun v : Tabloid μ => v.val (hookIn μ p x)) h
    simpa only [glueTabloid_val,glueLabels_hook] using hh
  · apply Subtype.ext
    funext x
    have hh := congrArg (fun v : Tabloid μ => v.val (southeastIn μ p x)) h
    simpa only [glueTabloid_val,glueLabels_southeast,Nat.add_right_cancel_iff] using hh

lemma glueTabloid_perm (g : G (hookPart μ p) × G (southeast μ p)) :
    glueTabloid μ p (tabloidOfPerm (hookPart μ p) g.1,tabloidOfPerm (southeast μ p) g.2) =
      tabloidOfPerm μ (cutPerm μ p g) := by
  apply Subtype.ext
  exact (labels_cutPerm μ p g).symm

lemma glueTabloid_smul (g : G (hookPart μ p) × G (southeast μ p))
    (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    glueTabloid μ p (g.1 • t.1,g.2 • t.2) = cutPerm μ p g • glueTabloid μ p t := by
  obtain ⟨a,ha⟩ := tabloidOfPerm_surjective (hookPart μ p) t.1
  obtain ⟨b,hb⟩ := tabloidOfPerm_surjective (southeast μ p) t.2
  have ht : t = (tabloidOfPerm (hookPart μ p) a,tabloidOfPerm (southeast μ p) b) :=
    Prod.ext ha.symm hb.symm
  rw [ht]
  dsimp only
  rw [smul_tabloidOfPerm,smul_tabloidOfPerm,glueTabloid_perm μ p (g.1*a,g.2*b),
    glueTabloid_perm μ p (a,b),smul_tabloidOfPerm]
  congr 1
  exact map_mul (cutPerm μ p) g (a,b)

end BinaryCoordinateSweeps.Young

end

end OAI
