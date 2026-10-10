import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice06
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators
noncomputable section
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)
lemma expProduct_rational {x : Fin n → ℝ} (hx : ∀ i, ∃ q : ℚ, (q:ℝ) = x i) :
    IsRational c (expProduct c x) := by
  intro i
  obtain ⟨P,hP⟩ := polynomialMap_expProduct c
    (f := fun x : Fin n → ℝ => x) (fun j => RationalPolynomialMap.coordinate j) i
  obtain ⟨q,hq⟩ := eval_rational P x hx
  exact ⟨q,hq.trans (hP x).symm⟩
lemma expCoordinates_rational {g : G} (hg : IsRational c g) :
    ∀ i, ∃ q : ℚ, (q:ℝ) = expCoordinates c g i := by
  intro i
  have hpoly : IsPolynomialMap c (fun x : Fin n → ℝ => c.coord.symm x) := by
    intro j
    simpa only [Homeomorph.apply_symm_apply] using RationalPolynomialMap.coordinate j
  obtain ⟨P,hP⟩ := polynomial_expCoordinates c hpoly i
  obtain ⟨q,hq⟩ := eval_rational P (c.coord g) hg
  refine ⟨q,?_⟩
  rw [hq,← hP]
  simp only [Homeomorph.symm_apply_apply]
end RationalLattice

namespace IntegerHyperplane
variable {n : ℕ}

lemma exists_last_nonzero (k : Fin (n+1) → ℤ) (hk : k ≠ 0) :
    ∃ p : Fin (n+1), k p ≠ 0 ∧ ∀ j : Fin (n+1), p < j → k j = 0 := by
  classical
  let S := Finset.univ.filter (fun j => k j ≠ 0)
  have hs : S.Nonempty := by
    by_contra he
    apply hk
    funext j
    by_contra hj
    exact he ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  refine ⟨S.max' hs,(Finset.mem_filter.mp (Finset.max'_mem S hs)).2,?_⟩
  intro j hj
  by_contra hj0
  exact (not_le_of_gt hj) (Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj0⟩))

def deletedCutoff (p : Fin (n+1)) (r : ℕ) : ℕ := r - if p.val < r then 1 else 0

lemma succAbove_lt_cutoff (p : Fin (n+1)) (j : Fin n) (r : ℕ) :
    (p.succAbove j).val < r ↔ j.val < deletedCutoff p r := by
  unfold deletedCutoff
  by_cases hj : j.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    have hh : j.val < p.val := hj
    simp only [Fin.val_castSucc]
    split_ifs <;> omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hj)]
    have hh : p.val ≤ j.val := le_of_not_gt hj
    simp only [Fin.val_succ]
    split_ifs <;> omega

lemma lift_prefix_zero_iff (k : Fin (n+1) → ℤ) (p : Fin (n+1))
    (hlast : ∀ j : Fin (n+1), p < j → k j = 0) (x : Fin n → ℝ) (r : ℕ) :
    (∀ a : Fin (n+1), a.val < r → lift k p x a = 0) ↔
      ∀ j : Fin n, j.val < deletedCutoff p r → x j = 0 := by
  constructor
  · intro hx j hj
    simpa using hx (p.succAbove j) ((succAbove_lt_cutoff p j r).mpr hj)
  · intro hx a ha
    rcases Fin.eq_self_or_eq_succAbove p a with he | ⟨j,he⟩
    · subst a
      rw [lift_pivot]
      have hs : (∑ j, (k (p.succAbove j):ℝ)*x j) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : (p.succAbove j).val < r
        · rw [hx j ((succAbove_lt_cutoff p j r).mp hj),mul_zero]
        · have hk := hlast (p.succAbove j) (by change p.val < (p.succAbove j).val; omega)
          simp [hk]
      simp [hs]
    · subst a
      rw [lift_succAbove]
      exact hx j ((succAbove_lt_cutoff p j r).mp ha)

end IntegerHyperplane

namespace RationalCharacterKernel
open RationalLattice IntegerHyperplane
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G (n+1)) (χ : G →* Multiplicative ℝ)
variable (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0)
variable (hχ : ∀ g : G, Multiplicative.toAdd (χ g) = form k (c.coord g))
variable (hlast : ∀ j : Fin (n+1), p < j → k j = 0)

 
lemma kernelCoordinates_adapted (H : Subgroup G) (r : ℕ)
    (hH : ∀ g : G, g ∈ H ↔ ∀ i : Fin (n+1), i.val < r → c.coord g i = 0)
    (g : χ.ker) :
    g.val ∈ H ↔ ∀ i : Fin n, i.val < deletedCutoff p r →
      (kernelCoordinates c χ k p hp hχ hlast).coord g i = 0 := by
  rw [hH,coord_lift c χ k p hp hχ]
  exact lift_prefix_zero_iff k p hlast _ r

variable [IsTopologicalGroup G]
 

theorem exists_rational_kernel_chart (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
    (hcont : Continuous χ) (hz : ∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z)
    (hne : χ ≠ 1) :
    ∃ d : RealCoordinates χ.ker n,
      (∀ g : χ.ker, IsRational d g ↔ IsRational c g.val) ∧
      ∀ H : Subgroup G, ∀ r : ℕ,
        (∀ g : G, g ∈ H ↔ ∀ i : Fin (n+1), i.val < r → c.coord g i = 0) →
        ∃ t : ℕ, ∀ g : χ.ker, g.val ∈ H ↔ ∀ i : Fin n, i.val < t → d.coord g i = 0 := by
  obtain ⟨k,hk⟩ := integer_character_expCoordinates c Γ hΓ χ hcont hz
  have hk0 : k ≠ 0 := by
    intro he
    apply hne
    ext g
    apply Multiplicative.toAdd.injective
    rw [hk,he]
    simp
  obtain ⟨p,hp,hlast⟩ := exists_last_nonzero k hk0
  have he : ∀ g : G, Multiplicative.toAdd (χ g) = form k ((secondCoordinates c).coord g) := by
    intro g
    rw [hk]
    change (∑ i, expCoordinates c g i * (k i:ℝ)) = ∑ i, (k i:ℝ)*expCoordinates c g i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  let d := kernelCoordinates (secondCoordinates c) χ k p hp he hlast
  refine ⟨d,?_,?_⟩
  · intro g
    rw [kernelCoordinates_rational]
    constructor
    · intro hg
      rw [← expProduct_expCoordinates c g.val]
      exact expProduct_rational c hg
    · exact expCoordinates_rational c
  · intro H r hH
    refine ⟨deletedCutoff p r,fun g => ?_⟩
    exact kernelCoordinates_adapted (secondCoordinates c) χ k p hp he hlast H r
      (secondCoordinates_adapted c H r hH) g

end RationalCharacterKernel
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace RationalTailCoordinates
open RationalLattice RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] {r n : ℕ}
variable (c : RealCoordinates G (r+n)) (H : Subgroup G)
variable (hH : ∀ g : G, g ∈ H ↔ ∀ i : Fin (r+n), i.val < r → c.coord g i = 0)
def embed (r : ℕ) (j : Fin n) : Fin (r+n) := ⟨r+j.val,by omega⟩
def lift (r : ℕ) (x : Fin n → ℝ) (a : Fin (r+n)) : ℝ :=
  if h : r ≤ a.val then x ⟨a.val-r,by have := a.isLt; omega⟩ else 0
@[simp] lemma lift_embed (x : Fin n → ℝ) (j : Fin n) : lift r x (embed r j) = x j := by
  simp [lift,embed]
lemma lift_prefix (x : Fin n → ℝ) (a : Fin (r+n)) (ha : a.val < r) : lift r x a = 0 := by
  simp [lift,not_le_of_gt ha]
lemma lift_continuous : Continuous (lift (n:=n) r) := by
  apply continuous_pi
  intro a
  unfold lift
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

def coordinates (g : H) (i : Fin n) : ℝ := c.coord g.val (embed r i)
include hH in
lemma coord_lift (g : H) : c.coord g.val = lift r (coordinates c H g) := by
  funext a
  unfold lift
  split_ifs with ha
  · apply congrArg (c.coord g.val)
    apply Fin.ext
    change a.val = r+(a.val-r)
    omega
  · exact (hH g.val).mp g.property a (by omega)

def rebuild (x : Fin n → ℝ) : H :=
  ⟨c.coord.symm (lift r x),(hH _).mpr (by
    intro a ha
    rw [c.coord.apply_symm_apply]
    exact lift_prefix x a ha)⟩
lemma coordinates_rebuild (x : Fin n → ℝ) : coordinates c H (rebuild c H hH x) = x := by
  funext j
  simp only [coordinates,rebuild,Homeomorph.apply_symm_apply,lift_embed]
lemma rebuild_coordinates (g : H) : rebuild c H hH (coordinates c H g) = g := by
  apply Subtype.ext
  apply c.coord.injective
  simpa only [rebuild,Homeomorph.apply_symm_apply] using (coord_lift c H hH g).symm
lemma coordinates_continuous : Continuous (coordinates c H) := by
  apply continuous_pi
  intro i
  exact (continuous_apply _).comp (c.coord.continuous.comp continuous_subtype_val)
lemma rebuild_continuous : Continuous (rebuild c H hH) := by
  apply Continuous.subtype_mk
  exact c.coord.symm.continuous.comp lift_continuous

def tailHomeomorph : H ≃ₜ (Fin n → ℝ) where
  toFun := coordinates c H
  invFun := rebuild c H hH
  left_inv := rebuild_coordinates c H hH
  right_inv := coordinates_rebuild c H hH
  continuous_toFun := coordinates_continuous c H
  continuous_invFun := rebuild_continuous c H hH

def lowerLift (r : ℕ) (i : Fin n) (x : Fin i.val → ℝ) (a : Fin (r+i.val)) : ℝ :=
  if h : r ≤ a.val then x ⟨a.val-r,by have := a.isLt; omega⟩ else 0

lemma exists_correction (i : Fin n) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ,
    ∀ v : (Fin i.val ⊕ Fin i.val) → ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (lowerLift r i (fun a => v (.inl a)))
          (lowerLift r i (fun a => v (.inr a)))) (c.correction (embed r i)) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  apply RationalPolynomialMap.eval
  intro a
  cases a with
  | inl a =>
    simp only [Sum.elim_inl]
    unfold lowerLift
    split_ifs
    · exact coordinate _
    · exact zero
  | inr a =>
    simp only [Sum.elim_inr]
    unfold lowerLift
    split_ifs
    · exact coordinate _
    · exact zero

def correction (i : Fin n) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  (exists_correction c i).choose
include hH in
lemma mul_coord (g h : H) (i : Fin n) :
    coordinates c H (g*h) i = coordinates c H g i + coordinates c H h i +
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => coordinates c H g ⟨j.val,lt_trans j.isLt i.isLt⟩)
          (fun j => coordinates c H h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (correction c i) := by
  change c.coord (g.val*h.val) (embed r i) = _
  rw [c.mul_coord]
  change coordinates c H g i + coordinates c H h i + _ = _
  congr 1
  let v : (Fin i.val ⊕ Fin i.val) → ℝ :=
    Sum.elim (fun j => coordinates c H g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => coordinates c H h ⟨j.val,lt_trans j.isLt i.isLt⟩)
  unfold correction
  rw [← (exists_correction c i).choose_spec v]
  congr 1
  funext a
  have hl (u : H) (a : Fin (r+i.val)) :
      c.coord u.val ⟨a.val,by have := a.isLt; have := i.isLt; omega⟩ =
        lowerLift r i (fun j => coordinates c H u ⟨j.val,lt_trans j.isLt i.isLt⟩) a := by
    unfold lowerLift
    split_ifs with ha
    · apply congrArg (c.coord u.val)
      apply Fin.ext
      change a.val = r+(a.val-r)
      omega
    · exact (hH u.val).mp u.property _ (by change a.val < r; omega)
  cases a with
  | inl a => exact hl g a
  | inr a => exact hl h a

def tailCoordinates : RealCoordinates H n where
  coord := tailHomeomorph c H hH
  one_coord i := c.one_coord (embed r i)
  correction := correction c
  mul_coord := mul_coord c H hH

lemma tailCoordinates_rational (g : H) :
    IsRational (tailCoordinates c H hH) g ↔ IsRational c g.val := by
  constructor
  · intro hg i
    rw [coord_lift c H hH g]
    unfold lift
    split_ifs
    · exact hg _
    · exact ⟨0,by simp⟩
  · intro hg i
    exact hg (embed r i)

lemma tailCoordinates_lattice (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z) (g : H) :
    g.val ∈ Γ ↔ ∀ i, ∃ z : ℤ, (tailCoordinates c H hH).coord g i = z := by
  constructor
  · intro hg i
    exact (hΓ _).mp hg (embed r i)
  · intro hg
    apply (hΓ _).mpr
    intro i
    rw [coord_lift c H hH g]
    unfold lift
    split_ifs
    · exact hg _
    · exact ⟨0,by simp⟩

lemma tailCoordinates_adapted (K : Subgroup G) (s : ℕ)
    (hK : ∀ g : G, g ∈ K ↔ ∀ i : Fin (r+n), i.val < s → c.coord g i = 0) (g : H) :
    g.val ∈ K ↔ ∀ i : Fin n, i.val < s-r → (tailCoordinates c H hH).coord g i = 0 := by
  rw [hK]
  constructor
  · intro hg i hi
    exact hg (embed r i) (by dsimp [embed]; omega)
  · intro hg i hi
    rw [coord_lift c H hH g]
    unfold lift
    split_ifs with hr
    · exact hg _ (by change i.val-r < s-r; omega)
    · rfl

end RationalTailCoordinates

end
end
end
end
end

end OAI
