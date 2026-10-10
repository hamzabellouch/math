import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice07
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
noncomputable section
namespace PairTail
open RationalLattice RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d r : ℕ} (c : RealCoordinates G (t+d))

def lowerArgs (i : Fin (r+d)) (X Y : Fin (r+d) → ℝ) : (Fin i.val ⊕ Fin i.val) → ℝ :=
  Sum.elim (fun j => X ⟨j.val,lt_trans j.isLt i.isLt⟩)
    (fun j => Y ⟨j.val,lt_trans j.isLt i.isLt⟩)

def baseInput (j : Fin d) (v : (Fin (r+j.val) ⊕ Fin (r+j.val)) → ℝ) : G :=
  c.coord.symm (fun a => if h : a.val < r then v (.inr ⟨a.val,by omega⟩) else 0)

def tailInput (j : Fin d) (v : Fin (r+j.val) → ℝ) : Fin (t+j.val) → ℝ :=
  fun a => if h : t ≤ a.val then v ⟨r+(a.val-t),by have := a.isLt; omega⟩ else 0

omit [IsTopologicalGroup G] in
lemma baseInput_polynomial (j : Fin d) :
    IsPolynomialMap c (baseInput c (r:=r) j) := by
  intro a
  simp only [baseInput,Homeomorph.apply_symm_apply]
  split_ifs
  · exact coordinate _
  · exact zero

omit [IsTopologicalGroup G] in
lemma tailCorrection_exists (j : Fin d) :
    ∃ P : MvPolynomial (Fin (r+j.val) ⊕ Fin (r+j.val)) ℚ,
      ∀ v : (Fin (r+j.val) ⊕ Fin (r+j.val)) → ℝ,
        c.coord ((baseInput c j v)⁻¹ *
          truncate c (RationalTailCoordinates.embed t j) (tailInput j (fun a => v (.inl a))) *
          baseInput c j v *
          truncate c (RationalTailCoordinates.embed t j) (tailInput j (fun a => v (.inr a))))
          (RationalTailCoordinates.embed t j) = MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  have hu : IsPolynomialMap c (fun v : (Fin (r+j.val) ⊕ Fin (r+j.val)) → ℝ =>
      truncate c (RationalTailCoordinates.embed t j) (tailInput j (fun a => v (.inl a)))) := by
    apply polynomialMap_truncate
    intro a
    unfold tailInput
    split_ifs
    · exact coordinate _
    · exact zero
  have hv : IsPolynomialMap c (fun v : (Fin (r+j.val) ⊕ Fin (r+j.val)) → ℝ =>
      truncate c (RationalTailCoordinates.embed t j) (tailInput j (fun a => v (.inr a)))) := by
    apply polynomialMap_truncate
    intro a
    unfold tailInput
    split_ifs
    · exact coordinate _
    · exact zero
  exact polynomialMap_mul c (polynomialMap_mul c
    (polynomialMap_mul c (polynomialMap_inv c (baseInput_polynomial c j)) hu)
    (baseInput_polynomial c j)) hv (RationalTailCoordinates.embed t j)

def tailCorrection (j : Fin d) : MvPolynomial (Fin (r+j.val) ⊕ Fin (r+j.val)) ℚ :=
  (tailCorrection_exists c j).choose

omit [IsTopologicalGroup G] in
lemma baseInput_args (j : Fin d) (X Y : Fin (r+d) → ℝ) :
    baseInput c j (lowerArgs (j.natAdd r) X Y) =
      MalcevPrefixQuotient.represent c (fun a : Fin r => Y (a.castAdd d)) := by
  apply c.coord.injective
  funext a
  simp only [baseInput,MalcevPrefixQuotient.represent,Homeomorph.apply_symm_apply,
    MalcevPrefixQuotient.lift]
  split_ifs <;> rfl

variable (K : Subgroup G) [K.Normal]
variable (hK : ∀ g : G, g ∈ K ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i = 0)

omit [IsTopologicalGroup G] [K.Normal] in
lemma tailInput_args (j : Fin d) (X : Fin (r+d) → ℝ) (a : Fin (t+j.val)) :
    tailInput j (fun u : Fin (r+j.val) => X ⟨u.val,by have := u.isLt; have := j.isLt; omega⟩) a =
      c.coord (RationalTailCoordinates.rebuild c K hK (fun u : Fin d => X (u.natAdd r))).val
        ⟨a.val,by have := a.isLt; have := j.isLt; omega⟩ := by
  simp only [tailInput,RationalTailCoordinates.rebuild,Homeomorph.apply_symm_apply,
    RationalTailCoordinates.lift]
  split_ifs <;> rfl

omit [IsTopologicalGroup G] [K.Normal] in
lemma tailCorrection_args (j : Fin d) (X Y : Fin (r+d) → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (lowerArgs (j.natAdd r) X Y) (tailCorrection c j) =
      c.coord (
        (MalcevPrefixQuotient.represent c (fun a : Fin r => Y (a.castAdd d)))⁻¹ *
        truncate c (RationalTailCoordinates.embed t j) (fun a =>
          c.coord (RationalTailCoordinates.rebuild c K hK (fun u : Fin d => X (u.natAdd r))).val
            ⟨a.val,lt_trans a.isLt (RationalTailCoordinates.embed t j).isLt⟩) *
        MalcevPrefixQuotient.represent c (fun a : Fin r => Y (a.castAdd d)) *
        truncate c (RationalTailCoordinates.embed t j) (fun a =>
          c.coord (RationalTailCoordinates.rebuild c K hK (fun u : Fin d => Y (u.natAdd r))).val
            ⟨a.val,lt_trans a.isLt (RationalTailCoordinates.embed t j).isLt⟩))
          (RationalTailCoordinates.embed t j) := by
  unfold tailCorrection
  rw [← (tailCorrection_exists c j).choose_spec,baseInput_args]
  have hx : tailInput j (fun a => lowerArgs (j.natAdd r) X Y (.inl a)) =
      (fun a : Fin (t+j.val) => c.coord
        (RationalTailCoordinates.rebuild c K hK (fun u : Fin d => X (u.natAdd r))).val
        ⟨a.val,by have := a.isLt; have := j.isLt; omega⟩) := by
    funext a
    exact tailInput_args c K hK j X a
  have hy : tailInput j (fun a => lowerArgs (j.natAdd r) X Y (.inr a)) =
      (fun a : Fin (t+j.val) => c.coord
        (RationalTailCoordinates.rebuild c K hK (fun u : Fin d => Y (u.natAdd r))).val
        ⟨a.val,by have := a.isLt; have := j.isLt; omega⟩) := by
    funext a
    exact tailInput_args c K hK j Y a
  rw [hx,hy]
  rfl

variable (hr : r ≤ t+d) (N : Subgroup G) [N.Normal]
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i : Fin (t+d), i.val < r → c.coord g i = 0)
variable (hcent : N ≤ Subgroup.center G)
variable [(diagonal K N).Normal]

def correction (i : Fin (r+d)) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  Fin.addCases (motive := fun i : Fin (r+d) => MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ)
    (fun j : Fin r => c.correction (MalcevPrefixQuotient.embed hr j))
    (fun j : Fin d => tailCorrection c j) i

omit [IsTopologicalGroup G] in
@[simp] lemma correction_base (j : Fin r) : correction c hr (j.castAdd d) =
    c.correction (MalcevPrefixQuotient.embed hr j) := by
  exact Fin.addCases_left (motive := fun i : Fin (r+d) =>
    MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ) j
omit [IsTopologicalGroup G] in
@[simp] lemma correction_tail (j : Fin d) : correction c hr (j.natAdd r) = tailCorrection c j := by
  exact Fin.addCases_right (motive := fun i : Fin (r+d) =>
    MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ) j

omit [N.Normal] in
lemma coordinate_mul (x y : square K ⧸ diagonal K N) (i : Fin (r+d)) :
    chartHomeomorph c K hK hr N hN hcent (x*y) i =
      chartHomeomorph c K hK hr N hN hcent x i + chartHomeomorph c K hK hr N hN hcent y i +
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (lowerArgs i (chartHomeomorph c K hK hr N hN hcent x)
          (chartHomeomorph c K hK hr N hN hcent y)) (correction c hr i) := by
  obtain ⟨X,rfl⟩ := (chartHomeomorph c K hK hr N hN hcent).symm.surjective x
  obtain ⟨Y,rfl⟩ := (chartHomeomorph c K hK hr N hN hcent).symm.surjective y
  simp only [Homeomorph.apply_symm_apply]
  rw [chart_rebuild_base,chart_rebuild_base,← QuotientGroup.mk_mul]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [chart_base,correction_base]
    change c.coord (_ * _) _ = _
    rw [c.mul_coord]
    simp only [pair,MalcevPrefixQuotient.represent,Homeomorph.apply_symm_apply]
    congr 1
    · simp [MalcevPrefixQuotient.lift,MalcevPrefixQuotient.embed]
    · congr 1
      funext a
      cases a with
      | inl a =>
          change (if h : a.val < r then X ⟨a.val,by omega⟩ else 0) = X ⟨a.val,by have ha : a.val < j.val := a.isLt; have := j.isLt; omega⟩
          rw [dite_eq_left (lt_trans a.isLt j.isLt)]
      | inr a =>
          change (if h : a.val < r then Y ⟨a.val,by omega⟩ else 0) = Y ⟨a.val,by have ha : a.val < j.val := a.isLt; have := j.isLt; omega⟩
          rw [dite_eq_left (lt_trans a.isLt j.isLt)]
  · rw [chart_tail,correction_tail,tailCorrection_args c K hK]
    let a := MalcevPrefixQuotient.represent c (fun i : Fin r => X (i.castAdd d))
    let b := MalcevPrefixQuotient.represent c (fun i : Fin r => Y (i.castAdd d))
    let u := (RationalTailCoordinates.rebuild c K hK (fun i : Fin d => X (i.natAdd r))).val
    let v := (RationalTailCoordinates.rebuild c K hK (fun i : Fin d => Y (i.natAdd r))).val
    change c.coord ((a*b)⁻¹*((a*u)*(b*v))) _ = _
    rw [show (a*b)⁻¹*((a*u)*(b*v)) = b⁻¹*u*b*v from by group]
    rw [conj_mul_truncated]
    congr 2
    · simp [u,RationalTailCoordinates.rebuild]
    · simp [v,RationalTailCoordinates.rebuild]

 
def reducedCoordinates : RealCoordinates (square K ⧸ diagonal K N) (r+d) where
  coord := chartHomeomorph c K hK hr N hN hcent
  one_coord i := congrFun (chart_one c K hK hr N hN hcent) i
  correction := correction c hr
  mul_coord := coordinate_mul c K hK hr N hN hcent

end PairTail
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

 

def reduceCoordinates (g : G) : ℕ → G
  | 0 => g
  | k+1 => if h : k < n then
      reduceCoordinates g k * basisFlow c ⟨k,h⟩ (-(⌊c.coord (reduceCoordinates g k) ⟨k,h⟩⌋:ℝ))
    else reduceCoordinates g k

lemma reduceCoordinates_bounds (g : G) (k : ℕ) :
    ∀ i : Fin n, i.val < k → c.coord (reduceCoordinates c g k) i ∈ Set.Ico (0:ℝ) 1 := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    by_cases hk : k < n
    · rw [reduceCoordinates,dite_eq_left hk]
      rw [coord_mul_of_right_zero c _ _ i (by
        intro j hj
        rw [basisFlow_coord c _ j (show j.val ≤ k from by change j.val < i.val at hj; omega)]
        simp [show j ≠ (⟨k,hk⟩:Fin n) from fun h => by
          have := congrArg Fin.val h; change j.val < i.val at hj; dsimp at this; omega])]
      by_cases hik : i.val < k
      · rw [basisFlow_coord c _ i (show i.val ≤ k from by omega)]
        simp only [ite_eq_right (show i ≠ (⟨k,hk⟩:Fin n) from fun h => by
          have := congrArg Fin.val h; dsimp at this; omega),add_zero]
        exact ih i hik
      · have he : i = (⟨k,hk⟩:Fin n) := Fin.ext (show i.val = k from by omega)
        subst i
        rw [basisFlow_coord c _ _ le_rfl,ite_eq_left rfl]
        constructor
        · have h := Int.floor_le (c.coord (reduceCoordinates c g k) ⟨k,hk⟩); linarith
        · have h := Int.lt_floor_add_one (c.coord (reduceCoordinates c g k) ⟨k,hk⟩); linarith
    · rw [reduceCoordinates,dite_eq_right hk]
      exact ih i (by omega)

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
include hΓ in
lemma reduceCoordinates_coset (g : G) (k : ℕ) : (reduceCoordinates c g k)⁻¹*g ∈ Γ := by
  induction k with
  | zero => simp [reduceCoordinates]
  | succ k ih =>
    simp only [reduceCoordinates]
    split_ifs with hk
    · rw [mul_inv_rev,mul_assoc]
      apply Γ.mul_mem _ ih
      apply Γ.inv_mem
      rw [← Int.cast_neg]
      exact basisFlow_int_mem c Γ hΓ _ _
    · exact ih

include hΓ in
 

theorem compact_reps_of_integerCoordinates :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, ∃ a ∈ C, a⁻¹*g ∈ Γ := by
  let B : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  refine ⟨c.coord.symm '' B,hB.image c.coord.symm.continuous,fun g => ?_⟩
  refine ⟨reduceCoordinates c g n,?_,reduceCoordinates_coset c Γ hΓ g n⟩
  refine ⟨c.coord (reduceCoordinates c g n),?_,c.coord.symm_apply_apply _⟩
  intro i _
  exact ⟨(reduceCoordinates_bounds c g n i i.isLt).1,
    (reduceCoordinates_bounds c g n i i.isLt).2.le⟩

end RationalLattice

end
end
end
end
end

end OAI
