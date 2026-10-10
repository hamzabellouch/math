import OAI.Combinatorics.HadwigerCounterexample.FinitePhaseAlternative

namespace OAI

/-! # Weighted Partitions -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A : Type} [Fintype A]

abbrev Tiles (A : Type) := Finset (Finset A)
def inTiles (T : Tiles A) := fun x:A => ∃ i∈ T,x∈i

def apart (T : Tiles A) :=
  ∀ x,∀ S∈T, ∀ F∈ T,x∈S→x∈F→ S=F

def partMass (w : Wgt A) (S : Finset A) := pr w (fun x => x∈S)
def partW (w : Wgt A) (S : Finset A) := onW w (fun x => x∈S)

def allMass (w : Wgt A) (T : Tiles A) := pr w (inTiles T)
def allW (w : Wgt A) (T : Tiles A) := onW w (inTiles T)

variable {w : Wgt A} {T : Tiles A}

theorem issued_sub (w : Wgt A) (hw : ∀ x, 0≤w x) (S R : Finset A) (h : R⊆S) :
    partMass w R=partMass w S*partMass (partW w S) R := by
  have he : (fun x => x∈ R)=(fun x => x∈S∧x∈R) := by ext; tauto
  unfold partMass
  exact ((congrArg (pr w) he).trans (pr_of_on hw _ _))

theorem issued_law (w : Wgt A) (hw : ∀ x, 0≤w x)
    {S R : Finset A} (hp : 0 < partMass w S) (h : R⊆S)
    (he : 0 < partMass (partW w S) R) :
    0 < partMass w R ∧ partW w R=partW (partW w S) R := by
  refine ⟨by rw [issued_sub w hw S R h]; exact mul_pos hp he,?_⟩
  have ht := on_both w (fun x => x∈S) (fun x => x∈R) hw hp he
  unfold partW; rw [ht]
  exact congrArg (onW w) (by ext; tauto)

omit [Fintype A] in
theorem ind_tiles (ht : apart T) (x : A) :
    ind (inTiles T x)= ∑ i∈T,ind (x∈i) := by
  classical
  by_cases hh : inTiles T x
  · rw [ind_one hh]
    obtain ⟨i,hi,hx⟩ := hh
    rw [Finset.sum_eq_single i]
    · rw [ind_one hx]
    · intro j hj h; exact ind_zero (fun hc => h (ht x j hj i hi hc hx))
    simp [hi]
  rw [ind_zero hh]
  exact (Finset.sum_eq_zero (fun i hi => ind_zero (fun h => hh ⟨i,hi,h⟩))).symm

theorem tiles_inter (w : Wgt A) (T : Tiles A) (P : A→Prop) (hT : apart T) :
    pr w (fun x => inTiles T x∧P x)= ∑ i∈T,pr w (fun x => x∈i ∧ P x) := by
  unfold pr
  simp_rw [ind_and, ind_tiles hT,Finset.sum_mul,avg_sum]

theorem mass_apart (h : apart T) : allMass w T=∑ i∈T,partMass w i := by
  simpa only [and_true,allMass,partMass] using tiles_inter w T (fun x => True) h

def portionW (w : Wgt A) (T : Tiles A) : Wgt T :=
  fun x => partMass w x.val / allMass w T

theorem rebuild {T : Tiles A} (hw : ∀ x, 0 ≤ w x)
    (hT : apart T) (he : ∀ i ∈ T, 0 < partMass w i)
    (h : 0 < allMass w T) :
    IsLaw (portionW w T) ∧ allW w T = mixW (portionW w T) (fun i => partW w i.val) := by
  classical
  constructor
  · refine ⟨fun i => div_nonneg (pr_nonneg hw) h.le,?_⟩
    unfold tot portionW
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul,Finset.sum_coe_sort,← mass_apart hT,mul_inv_cancel₀ h.ne']
  funext x
  rw [allW,onW_val,ind_tiles hT]
  unfold mixW avg
  have hg (i:T) :
      portionW w T i* partW w i.val x = w x*ind (x∈i.val)/allMass w T := by
    have hx : pr w (fun x => x∈i.val) ≠ 0 := (he _ i.property).ne'
    unfold portionW partW partMass
    rw [onW_val]; field_simp
  change w x * _ / allMass w T=_
  simp_rw [hg]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul,← Finset.mul_sum, Finset.sum_coe_sort T (fun y => ind (x∈y))]

/-- Refine on every old tile, with rules allowed to be different on every
tile. Total loss bound relative to the old tiled union. -/
theorem improve (T : Tiles A) (w : Wgt A) (hw : ∀ x,0 ≤ w x)
    (P : A→Prop) (R : Finset A→Finset A→Prop) (hT : apart T) {c : ℝ}
    (h : ∀ i∈T,∃ V : Tiles A, apart V ∧
      (∀ S∈V,S ⊆ i ∧ R i S) ∧
      pr (partW w i) (fun x => x∈i∧P x∧¬inTiles V x) ≤ c) :
    ∃ V : Tiles A,apart V∧ (∀ S∈V,∃ i∈T,S⊆i ∧ R i S) ∧
      pr w (fun x => inTiles T x ∧ P x ∧ ¬inTiles V x)≤ allMass w T*c := by
  classical
  have h1 : ∀ i : Finset A, ∃ V : Tiles A,i∈T → apart V ∧
      (∀ S∈V,S ⊆ i ∧ R i S) ∧
      pr (partW w i) (fun x => x∈i∧P x∧¬inTiles V x) ≤ c := by
    intro i
    by_cases hi : i∈T
    · obtain ⟨V,h⟩ := h i hi
      exact ⟨V,fun _ => h⟩
    exact ⟨∅,fun h => (hi h).elim⟩
  choose V hV using h1
  let G := T.biUnion V
  refine ⟨G,?_,?_,?_⟩
  · intro x S hS W hw hx hx'
    obtain ⟨i,hi,hS⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨j,hj,hW⟩ := Finset.mem_biUnion.mp hw
    obtain rfl := hT x i hi j hj (((hV i hi).2.1 S hS).1 hx) (((hV j hj).2.1 W hW).1 hx')
    exact (hV i hi).1 x S hS W hW hx hx'
  · rintro S hS
    obtain ⟨i,hi,hS⟩ := Finset.mem_biUnion.mp hS
    exact ⟨i,hi,(hV i hi).2.1 _ hS⟩
  · rw [mass_apart hT,tiles_inter _ T _ hT, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have he (x) (hx : inTiles (V i) x) : inTiles G x := by
      obtain ⟨S,hS,h⟩ := hx
      exact ⟨S,Finset.mem_biUnion.mpr ⟨i,hi,hS⟩,h⟩
    let Z (x : A) := x∈i∧P x∧¬inTiles (V i) x
    calc pr w _
      _ ≤ pr w (fun x => x∈i∧ Z x) :=
        pr_mono hw (fun x h => ⟨h.1,h.1,h.2.1,fun hx => h.2.2 (he _ hx)⟩)
      _ = _ := pr_of_on hw (fun x => x∈i) Z
      _ ≤ _ := mul_le_mul_of_nonneg_left (hV i hi).2.2 (pr_nonneg hw)

end HadwigerCounterexample

end

end OAI
