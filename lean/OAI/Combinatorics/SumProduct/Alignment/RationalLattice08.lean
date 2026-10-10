import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerHyperplane02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace RationalCharacterFirst
open RationalLattice IntegerHyperplane RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G (n+1)) (χ : G →* Multiplicative ℝ)
variable (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p ≠ 0)
variable (hχ : ∀ g : G, Multiplicative.toAdd (χ g) = form k (c.coord g))
variable (hlast : ∀ j : Fin (n+1), p < j → k j = 0)

def coordinates (g : G) : Fin (n+1) → ℝ := splitCoordinates k p (c.coord g)

lemma exists_correction (i : Fin n) :
    ∃ P : MvPolynomial (Fin (i.val+1) ⊕ Fin (i.val+1)) ℚ,
    ∀ v : (Fin (i.val+1) ⊕ Fin (i.val+1)) → ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim
          (fun a => splitLift k p (lowerExtend i.succ (fun j => v (Sum.inl j)))
            ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩)
          (fun a => splitLift k p (lowerExtend i.succ (fun j => v (Sum.inr j)))
            ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩)) (c.correction (p.succAbove i)) =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  apply RationalPolynomialMap.eval
  intro a
  cases a with
  | inl a =>
    apply RationalPolynomialMap.comp (splitLift_polynomial k p _)
    intro j
    unfold lowerExtend
    split_ifs
    · exact RationalPolynomialMap.coordinate _
    · exact RationalPolynomialMap.zero
  | inr a =>
    apply RationalPolynomialMap.comp (splitLift_polynomial k p _)
    intro j
    unfold lowerExtend
    split_ifs
    · exact RationalPolynomialMap.coordinate _
    · exact RationalPolynomialMap.zero

def tailCorrection (i : Fin n) : MvPolynomial (Fin (i.val+1) ⊕ Fin (i.val+1)) ℚ :=
  (exists_correction c k p i).choose

include hp hlast in
lemma tail_mul_coord (g h : G) (i : Fin n) :
    coordinates c k p (g*h) i.succ = coordinates c k p g i.succ + coordinates c k p h i.succ +
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => coordinates c k p g ⟨j.val,lt_trans j.isLt i.succ.isLt⟩)
          (fun j => coordinates c k p h ⟨j.val,lt_trans j.isLt i.succ.isLt⟩)) (tailCorrection c k p i) := by
  change c.coord (g*h) (p.succAbove i) = _
  rw [c.mul_coord]
  change coordinates c k p g i.succ + coordinates c k p h i.succ + _ = _
  congr 1
  let v : (Fin (i.val+1) ⊕ Fin (i.val+1)) → ℝ :=
    Sum.elim (fun j => coordinates c k p g ⟨j.val,lt_trans j.isLt i.succ.isLt⟩)
      (fun j => coordinates c k p h ⟨j.val,lt_trans j.isLt i.succ.isLt⟩)
  unfold tailCorrection
  rw [← (exists_correction c k p i).choose_spec v]
  congr 1
  funext a
  have hl (u : G) (a : Fin (p.succAbove i).val) :
      c.coord u ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩ =
      splitLift k p (lowerExtend i.succ
        (fun j => coordinates c k p u ⟨j.val,lt_trans j.isLt i.succ.isLt⟩))
        ⟨a.val,lt_trans a.isLt (p.succAbove i).isLt⟩ := by
    conv_lhs => rw [← splitLift_splitCoordinates k p hp (c.coord u)]
    apply splitLift_lower_dep k p hlast i
    · intro j hj
      have hj' : j.val < i.succ.val := hj
      simp only [lowerExtend,hj',dite_eq_left,coordinates]
    · exact a.isLt
  cases a with
  | inl a => exact hl g a
  | inr a => exact hl h a

include hχ in
lemma head_mul_coord (g h : G) :
    coordinates c k p (g*h) 0 = coordinates c k p g 0+coordinates c k p h 0 := by
  change form k (c.coord (g*h))/(k p:ℝ) = form k (c.coord g)/(k p:ℝ)+form k (c.coord h)/(k p:ℝ)
  rw [← hχ,← hχ,← hχ,map_mul]
  exact add_div _ _ _

 

def characterFirstCoordinates : RealCoordinates G (n+1) where
  coord := c.coord.trans (splitHomeomorph k p hp)
  one_coord i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change form k (c.coord 1)/(k p:ℝ) = 0
      simp [form,c.one_coord]
    · exact c.one_coord _
  correction := Fin.cases 0 (tailCorrection c k p)
  mul_coord g h i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change coordinates c k p (g*h) 0 = coordinates c k p g 0+coordinates c k p h 0+
        MvPolynomial.eval₂ _ _ 0
      rw [MvPolynomial.eval₂_zero,add_zero]
      exact head_mul_coord c χ k p hχ g h
    · exact tail_mul_coord c k p hp hlast g h j

lemma inclusion_polynomial (i : Fin (n+1)) :
    RationalPolynomialMap.IsPolynomial (fun x : Fin (n+1) → ℝ =>
      c.coord ((characterFirstCoordinates c χ k p hp hχ hlast).coord.symm x) i) := by
  change RationalPolynomialMap.IsPolynomial (fun x => c.coord (c.coord.symm (splitLift k p x)) i)
  simp only [Homeomorph.apply_symm_apply]
  exact splitLift_polynomial k p i

include hp hχ hlast in
lemma characterFirst_adapted (H : Subgroup G) (r : ℕ)
    (hH : ∀ g : G, g ∈ H ↔ ∀ i : Fin (n+1), i.val < r → c.coord g i = 0) (g : G) :
    g ∈ H ⊓ χ.ker ↔ ∀ i : Fin (n+1), i.val < deletedCutoff p r+1 →
      (characterFirstCoordinates c χ k p hp hχ hlast).coord g i = 0 := by
  have hpR : (k p:ℝ) ≠ 0 := by exact_mod_cast hp
  have hhead : (characterFirstCoordinates c χ k p hp hχ hlast).coord g 0 = 0 ↔ g ∈ χ.ker := by
    change form k (c.coord g)/(k p:ℝ) = 0 ↔ χ g=1
    rw [← hχ,div_eq_zero_iff]
    simp only [hpR,or_false]
    constructor
    · intro h
      exact Multiplicative.toAdd.injective h
    · intro h
      rw [h]
      rfl
  constructor
  · rintro ⟨hg,hker⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _; exact hhead.mpr hker
    · intro hi
      have ha := (RationalCharacterKernel.kernelCoordinates_adapted c χ k p hp hχ hlast H r hH ⟨g,hker⟩).mp hg
      exact ha j (by change j.val+1 < deletedCutoff p r+1 at hi; omega)
  · intro hg
    have hker := hhead.mp (hg 0 (by change 0 < deletedCutoff p r+1; omega))
    refine ⟨?_,hker⟩
    apply (RationalCharacterKernel.kernelCoordinates_adapted c χ k p hp hχ hlast H r hH ⟨g,hker⟩).mpr
    intro j hj
    exact hg j.succ (by change j.val+1 < deletedCutoff p r+1; omega)

end RationalCharacterFirst
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace TriangularDenominators

 

theorem polynomial_origin_grid {ι : Type*} (P : MvPolynomial ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ T : ℕ, ∀ x : ι → ℤ, ∃ z : ℤ,
      MvPolynomial.eval (fun j => (D:ℚ)*(T:ℚ)*(x j:ℚ)) P -
        MvPolynomial.eval (fun _ => 0) P = (T:ℚ)*(z:ℚ) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨1,by norm_num,fun T x => ⟨0,by simp⟩⟩
  | add P Q hP hQ =>
    obtain ⟨D,hD,hP⟩ := hP
    obtain ⟨E,hE,hQ⟩ := hQ
    refine ⟨D*E,Nat.mul_pos hD hE,?_⟩
    intro T x
    obtain ⟨a,ha⟩ := hP T (fun j => (E:ℤ)*x j)
    obtain ⟨b,hb⟩ := hQ T (fun j => (D:ℤ)*x j)
    have hDE : (fun j => (D:ℚ)*(T:ℚ)*(((E:ℤ)*x j):ℚ)) =
        (fun j => ((D*E:ℕ):ℚ)*(T:ℚ)*(x j:ℚ)) := by funext j; push_cast; ring
    have hED : (fun j => (E:ℚ)*(T:ℚ)*(((D:ℤ)*x j):ℚ)) =
        (fun j => ((D*E:ℕ):ℚ)*(T:ℚ)*(x j:ℚ)) := by funext j; push_cast; ring
    simp only [Int.cast_mul] at ha hb
    rw [hDE] at ha
    rw [hED] at hb
    refine ⟨a+b,?_⟩
    simp only [map_add,Int.cast_add]
    linarith
  | mul_X P i hP =>
    obtain ⟨D,hD,hgrid⟩ := polynomial_grid P 1 (by norm_num)
    refine ⟨D,hD,?_⟩
    intro T x
    obtain ⟨a,ha⟩ := hgrid (fun j => (D:ℚ)*(T:ℚ)*(x j:ℚ)) (by
      intro j
      refine ⟨(D:ℤ)*(T:ℤ)*x j,?_⟩
      simp)
    refine ⟨a*x i,?_⟩
    simp only [map_mul,MvPolynomial.eval_X,mul_zero,sub_zero,Int.cast_mul]
    calc
      _ = (T:ℚ)*((D:ℚ)*MvPolynomial.eval (fun j => (D:ℚ)*(T:ℚ)*(x j:ℚ)) P)*(x i:ℚ) := by ring
      _ = _ := by rw [ha]; ring

theorem polynomial_origin_grid_real {ι : Type*} (P : MvPolynomial ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ T : ℕ, ∀ x : ι → ℝ,
      (∀ j, ∃ z : ℤ, x j = ((D*T:ℕ):ℝ)*(z:ℝ)) → ∃ z : ℤ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P -
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun _ => 0) P = (T:ℝ)*(z:ℝ) := by
  obtain ⟨D,hD,hgrid⟩ := polynomial_origin_grid P
  refine ⟨D,hD,?_⟩
  intro T x hx
  choose z hz using hx
  obtain ⟨a,ha⟩ := hgrid T z
  refine ⟨a,?_⟩
  have he : ∀ v : ι → ℚ, ((MvPolynomial.eval v P : ℚ):ℝ) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => (v i:ℝ)) P := by
    intro v
    exact MvPolynomial.eval₂_comp_left (algebraMap ℚ ℝ) (RingHom.id ℚ) v P
  have hh := congrArg (fun q : ℚ => (q:ℝ)) ha
  simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast] at hh
  rw [he,he] at hh
  simp only [Rat.cast_zero] at hh
  convert hh using 1
  · congr 1
    congr 1
    funext j
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast,Nat.cast_mul] using hz j
end TriangularDenominators

end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

def correctionDenom (i : Fin n) : ℕ :=
  (TriangularDenominators.polynomial_origin_grid_real (c.correction i)).choose

lemma correctionDenom_pos (i : Fin n) : 0 < correctionDenom c i :=
  (TriangularDenominators.polynomial_origin_grid_real (c.correction i)).choose_spec.1

lemma correction_at_zero (i : Fin n) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun _ => 0) (c.correction i) = 0 := by
  have h := c.mul_coord 1 1 i
  simp only [mul_one,c.one_coord,zero_add] at h
  have he : (Sum.elim (fun _ : Fin i.val => (0:ℝ)) (fun _ : Fin i.val => (0:ℝ))) = (fun _ => (0:ℝ)) := by
    funext j; cases j <;> rfl
  rw [he] at h
  exact h.symm

variable (w : Fin n → ℕ)
variable (hw : ∀ i : Fin n, ∀ j : Fin n, j < i → correctionDenom c i * w i ∣ w j)

def OnGrid (g : G) : Prop := ∀ i, ∃ z : ℤ, c.coord g i = (w i:ℝ)*(z:ℝ)

include hw in
lemma correction_on_grid (g h : G) (i : Fin n)
    (hg : ∀ j : Fin n, j < i → ∃ z : ℤ, c.coord g j = (w j:ℝ)*(z:ℝ))
    (hh : ∀ j : Fin n, j < i → ∃ z : ℤ, c.coord h j = (w j:ℝ)*(z:ℝ)) :
    ∃ z : ℤ, MvPolynomial.eval₂ (algebraMap ℚ ℝ)
      (Sum.elim (fun j => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i) = (w i:ℝ)*(z:ℝ) := by
  have hl (a : G) (ha : ∀ j : Fin n, j < i → ∃ z : ℤ, c.coord a j = (w j:ℝ)*(z:ℝ))
      (j : Fin i.val) : ∃ z : ℤ, c.coord a ⟨j.val,lt_trans j.isLt i.isLt⟩ =
        ((correctionDenom c i*w i:ℕ):ℝ)*(z:ℝ) := by
    let k : Fin n := ⟨j.val,lt_trans j.isLt i.isLt⟩
    obtain ⟨z,hz⟩ := ha k j.isLt
    obtain ⟨b,hb⟩ := hw i k j.isLt
    refine ⟨(b:ℤ)*z,?_⟩
    change c.coord a k = _
    rw [hz,hb]
    push_cast
    ring
  have he := (TriangularDenominators.polynomial_origin_grid_real (c.correction i)).choose_spec.2
    (w i) (Sum.elim (fun j => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (by
        intro j
        cases j with
        | inl j => exact hl g hg j
        | inr j => exact hl h hh j)
  simpa only [correction_at_zero,sub_zero] using he

include hw in
lemma onGrid_mul {g h : G} (hg : OnGrid c w g) (hh : OnGrid c w h) : OnGrid c w (g*h) := by
  intro i
  obtain ⟨a,ha⟩ := hg i
  obtain ⟨b,hb⟩ := hh i
  obtain ⟨d,hd⟩ := correction_on_grid c w hw g h i (fun j _ => hg j) (fun j _ => hh j)
  refine ⟨a+b+d,?_⟩
  rw [c.mul_coord,ha,hb,hd]
  push_cast
  ring

include hw in
lemma onGrid_inv {g : G} (hg : OnGrid c w g) : OnGrid c w g⁻¹ := by
  have hi : ∀ a : ℕ, ∀ ha : a < n, ∃ z : ℤ,
      c.coord g⁻¹ ⟨a,ha⟩ = (w ⟨a,ha⟩:ℝ)*(z:ℝ) := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro ha
      let i : Fin n := ⟨a,ha⟩
      obtain ⟨b,hb⟩ := hg i
      obtain ⟨d,hd⟩ := correction_on_grid c w hw g g⁻¹ i (fun j _ => hg j)
        (fun j hj => ih j.val hj j.isLt)
      have he := c.mul_coord g g⁻¹ i
      rw [mul_inv_cancel,c.one_coord,hb,hd] at he
      refine ⟨-b-d,?_⟩
      change c.coord g⁻¹ i = _
      push_cast
      linarith
  exact fun i => hi i.val i.isLt

 

def weightedLattice : Subgroup G where
  carrier := OnGrid c w
  one_mem' := fun i => ⟨0,by simp [c.one_coord]⟩
  mul_mem' := onGrid_mul c w hw
  inv_mem' := onGrid_inv c w hw

 

theorem exists_lattice_weights (E : ℕ) (hE : 0 < E) : ∃ w : Fin n → ℕ,
    (∀ i, 0 < w i) ∧ (∀ i, E ∣ w i) ∧
    ∀ i : Fin n, ∀ j : Fin n, j < i → correctionDenom c i*w i ∣ w j := by
  let D : ℕ := E * ∏ i, correctionDenom c i
  have hD : 0 < D := Nat.mul_pos hE (Finset.prod_pos (fun i _ => correctionDenom_pos c i))
  refine ⟨fun i => D^(n-i.val),fun i => pow_pos hD _,?_,?_⟩
  · intro i
    exact (dvd_mul_right E _).trans (dvd_pow_self D (by omega))
  · intro i j hji
    have hc : correctionDenom c i ∣ D :=
      (Finset.dvd_prod_of_mem (fun i => correctionDenom c i) (Finset.mem_univ i)).trans (dvd_mul_left _ _)
    have he : correctionDenom c i*D^(n-i.val) ∣ D^(n-i.val+1) := by
      rw [pow_succ]
      rw [mul_comm (D^(n-i.val)) D]
      exact mul_dvd_mul_right hc _
    exact he.trans (pow_dvd_pow D (by change j.val < i.val at hji; omega))

variable (hpos : ∀ i, 0 < w i)

def divideCoordinates : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun x i := x i/(w i:ℝ)
  invFun x i := (w i:ℝ)*x i
  left_inv x := by funext i; exact mul_div_cancel₀ (x i) (by exact_mod_cast (hpos i).ne')
  right_inv x := by funext i; exact mul_div_cancel_left₀ (x i) (by exact_mod_cast (hpos i).ne')
  continuous_toFun := continuous_pi (fun i => (continuous_apply i).div_const _)
  continuous_invFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i))

lemma exists_scaled_correction (i : Fin n) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ, ∀ x : (Fin i.val ⊕ Fin i.val) → ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => (w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ)*x (Sum.inl j))
          (fun j => (w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ)*x (Sum.inr j)))
        (c.correction i) / (w i:ℝ) = MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P := by
  have he : RationalPolynomialMap.IsPolynomial (fun x : (Fin i.val ⊕ Fin i.val) → ℝ =>
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => (w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ)*x (Sum.inl j))
          (fun j => (w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ)*x (Sum.inr j))) (c.correction i)) := by
    apply RationalPolynomialMap.eval
    intro j
    cases j with
    | inl j => simpa using RationalPolynomialMap.mul (RationalPolynomialMap.const (w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℚ)) (RationalPolynomialMap.coordinate (Sum.inl j))
    | inr j => simpa using RationalPolynomialMap.mul (RationalPolynomialMap.const (w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℚ)) (RationalPolynomialMap.coordinate (Sum.inr j))
  have hm := RationalPolynomialMap.mul he (RationalPolynomialMap.const (w i:ℚ)⁻¹)
  simpa only [RationalPolynomialMap.IsPolynomial,div_eq_mul_inv,Rat.cast_inv,Rat.cast_natCast] using hm

def scaledCorrection (i : Fin n) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  (exists_scaled_correction c w i).choose

 
def scaledCoordinates : RealCoordinates G n where
  coord := c.coord.trans (divideCoordinates w hpos)
  one_coord i := by change c.coord 1 i / (w i:ℝ) = 0; rw [c.one_coord,zero_div]
  correction := scaledCorrection c w
  mul_coord g h i := by
    change c.coord (g*h) i/(w i:ℝ) = _
    have he := (exists_scaled_correction c w i).choose_spec
      (Sum.elim (fun j => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩/(w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ))
        (fun j => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩/(w ⟨j.val,lt_trans j.isLt i.isLt⟩:ℝ)))
    have hc (v : ℝ) (j : Fin n) : (w j:ℝ)*(v/(w j:ℝ)) = v := mul_div_cancel₀ _ (by exact_mod_cast (hpos j).ne')
    simp only [Sum.elim_inl,Sum.elim_inr,hc] at he
    change c.coord (g*h) i/(w i:ℝ) = c.coord g i/(w i:ℝ)+c.coord h i/(w i:ℝ)+_
    dsimp [scaledCorrection,divideCoordinates]
    rw [← he,c.mul_coord]
    ring

lemma weightedLattice_iff (g : G) : g ∈ weightedLattice c w hw ↔
    ∀ i, ∃ z : ℤ, (scaledCoordinates c w hpos).coord g i = z := by
  constructor <;> intro hg i <;> obtain ⟨z,hz⟩ := hg i <;> refine ⟨z,?_⟩
  · change c.coord g i/(w i:ℝ) = z
    rw [hz]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (hpos i).ne')
  · change c.coord g i/(w i:ℝ) = z at hz
    exact (div_eq_iff (by exact_mod_cast (hpos i).ne')).mp hz |>.trans (mul_comm _ _)

end RationalLattice

end
end
end
end
end

end OAI
