import Mathlib
import OAI.Probability.CoordinateSweeps.Transition
import OAI.RepresentationTheory.Placement.Chart
import OAI.Analysis.Matrix.BlockCycles
import OAI.Probability.CoordinateSweeps.Decomposition

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

abbrev Placement := Fin k ↪ H.FreeAt 0

def placementAction : H.stabilizer →* Equiv.Perm (H.Placement (k := k)) :=
  OrderedPlacements.action.comp H.stabilizerFreeEquiv.toMonoidHom

def placementChart (u : H.Placement (k := k)) : Chart (H.placementAction (k := k)) where
  base := u
  rep x := H.stabilizerFreeEquiv.symm ((OrderedPlacements.chart u).rep x)
  reaches x := by
    change OrderedPlacements.action (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      ((OrderedPlacements.chart u).rep x))) u=x
    rw [MulEquiv.apply_symm_apply]
    exact (OrderedPlacements.chart u).reaches x

lemma placementAction_apply (g : H.stabilizer) (x : H.Placement (k := k)) (i : Fin k) :
    ((H.placementAction g x) i).val=g.val (x i).val := rfl

lemma placement_valid (x : H.Placement (k := k)) : H.ValidInput (fun i => (x i).val) := by
  refine ⟨?_,?_⟩
  · intro i j he
    exact x.injective (Subtype.ext he)
  · intro i a
    exact (x i).property a

lemma pointFix_iff (u x : H.Placement (k := k)) (g : H.stabilizer) :
    g ∈ (H.placementChart u).pointFix x ↔ ∀ i, g.val (x i).val=(x i).val := by
  change H.placementAction g x=x ↔ _
  constructor
  · intro hh i
    exact congrArg (fun z : H.Placement (k := k) => (z i).val) hh
  · intro hh
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact hh i

variable (u x : H.Placement (k := k)) (v : Fin k → G.Slot)
    (ω₀ : G.Choices) (h₀ : H.Compatible ω₀) (hv : ∀ i, G.sweep ω₀ (x i).val=v i)

/- The point--placement stabilizer is the literal stabilizer of all augmented
holes, not an abstract group with the same cardinality. -/
def augmentFixEquiv : (H.placementChart u).pointFix x ≃*
    (H.augment (fun i => (x i).val) v (H.placement_valid x) ω₀ h₀ hv).stabilizer where
  toFun g := ⟨g.val.val,by
    intro i
    cases i using Fin.addCases with
    | left a => simpa only [augment_old] using g.val.property a
    | right a =>
      simpa only [augment_new,Grid.pathBetween_zero] using
        (H.pointFix_iff u x g.val).mp g.property a⟩
  invFun g := ⟨⟨g.val,by
    intro i
    exact (show g.val (H.path i 0)=H.path i 0 by simpa only [augment_old] using g.property (Fin.castAdd k i))⟩,
    (H.pointFix_iff u x _).mpr (fun i => by
      simpa only [augment_new,Grid.pathBetween_zero] using g.property (Fin.natAdd h i))⟩
  left_inv g := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' g l := by apply Subtype.ext; rfl

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def augmented (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}) : G.Holes (h+k) :=
  H.augment (fun i => (x i).val) (fun i => G.sweep ω₀.val (x i).val)
    (H.placement_valid x) ω₀.val ω₀.property (fun _ => rfl)

lemma augmented_compatible (x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) (ω : G.Choices) :
    (H.augmented x ω₀).Compatible ω ↔ H.Compatible ω ∧
      ∀ i, G.sweep ω (x i).val=G.sweep ω₀.val (x i).val :=
  H.augment_compatible_iff _ _ _ _ _ _ _

def augmentedReference (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    {ω : G.Choices // (H.augmented x ω₀).Compatible ω} :=
  ⟨ω₀.val,(H.augmented_compatible x ω₀ ω₀.val).mpr ⟨ω₀.property,fun _ => rfl⟩⟩

lemma augmented_feasible (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    (H.augmented x ω₀).Feasible := ⟨ω₀.val,(H.augmentedReference x ω₀).property⟩

lemma transition_event (hf : H.Feasible) (x : H.Placement (k := k))
    (ω₀ ω : {ω : G.Choices // H.Compatible ω}) :
    H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x ↔
      ∀ i, G.sweep ω.val (x i).val=G.sweep ω₀.val (x i).val := by
  constructor
  · intro hh i
    have hi := congrArg (fun z : H.Placement (k := k) => (z i).val) hh
    change (G.sweep (H.reference hf)).symm (G.sweep ω₀.val (x i).val)=
      (G.sweep (H.reference hf)).symm (G.sweep ω.val (x i).val) at hi
    exact ((G.sweep (H.reference hf)).symm.injective hi).symm
  · intro hh
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    change (G.sweep (H.reference hf)).symm (G.sweep ω₀.val (x i).val)=
      (G.sweep (H.reference hf)).symm (G.sweep ω.val (x i).val)
    rw [hh i]

/- Conditioning on a placement transition is exactly conditioning on the full,
unique augmented coordinate paths, not an endpoint approximation. -/
def augmentedChoices (hf : H.Feasible) (x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x} ≃
    {ω : G.Choices // (H.augmented x ω₀).Compatible ω} where
  toFun ω := ⟨ω.val.val,(H.augmented_compatible x ω₀ ω.val.val).mpr
    ⟨ω.val.property,(H.transition_event hf x ω₀ ω.val).mp ω.property⟩⟩
  invFun ω := ⟨⟨ω.val,((H.augmented_compatible x ω₀ ω.val).mp ω.property).1⟩,
    (H.transition_event hf x ω₀ _).mpr ((H.augmented_compatible x ω₀ ω.val).mp ω.property).2⟩
  left_inv ω := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv ω := by apply Subtype.ext; rfl

/- A concrete cardinal-free group identity behind the conditional-fiber frame. -/
lemma augmented_residual (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ω : {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x}) :
    H.augmentFixEquiv u x (fun i => G.sweep ω₀.val (x i).val) ω₀.val ω₀.property (fun _ => rfl)
      ((H.placementChart u).transitionResidual x (H.placementAction (H.residual hf ω₀) x)
        (H.residual hf ω₀) (H.residual hf ω.val) rfl ω.property)=
      (H.augmented x ω₀).residualWithReference (H.augmentedReference x ω₀)
        (H.augmentedChoices hf x ω₀ ω) := by
  apply Subtype.ext
  change (((G.sweep (H.reference hf))⁻¹*G.sweep ω₀.val)⁻¹*
    ((G.sweep (H.reference hf))⁻¹*G.sweep ω.val.val))=(G.sweep ω₀.val)⁻¹*G.sweep ω.val.val
  group

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def placementWeight (z : ℝ) (ω : {ω : G.Choices // H.Compatible ω}) : ℝ :=
  G.choiceWeight z ω.val/H.probability z

lemma placementWeight_nonneg (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (ω : {ω : G.Choices // H.Compatible ω}) : 0 ≤ H.placementWeight z ω :=
  div_nonneg (G.choiceWeight_pos hz hz' ω.val).le (H.probability_pos hf hz hz').le

lemma placementWeight_sum (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    ∑ ω, H.placementWeight z ω=1 := by
  unfold placementWeight
  rw [← Finset.sum_div]
  exact div_self (H.probability_pos hf hz hz').ne'

/- Transition probability in the induced representation is the exact conditional
probability of the augmented path family. -/
theorem transition_probability (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) (z : ℝ) :
    (H.placementChart u).transition (H.placementWeight z) (H.residual hf)
      (H.placementAction (H.residual hf ω₀) x) x=
      (H.augmented x ω₀).probability z/H.probability z := by
  classical
  let : Fintype {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x} := Subtype.fintype _
  have he : (∑ ω : {ω : G.Choices // H.Compatible ω},
      if H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x
      then G.choiceWeight z ω.val else 0)=(H.augmented x ω₀).probability z := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun ω : {ω : G.Choices // H.Compatible ω} =>
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x)
      _ (by intro ω; simp)]
    exact Equiv.sum_comp (H.augmentedChoices hf x ω₀) (fun ω => G.choiceWeight z ω.val)
  unfold PlacementInduction.Chart.transition placementWeight
  rw [← he,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

def augmentedIrrep (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) : UnitaryIrrep (H.augmented x ω₀).stabilizer :=
  ((H.placementChart u).pointIrrep ρ x).pullback
    (H.augmentFixEquiv u x (fun i => G.sweep ω₀.val (x i).val) ω₀.val ω₀.property (fun _ => rfl)).symm

lemma augmentedIrrep_residual (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer)
    (ω : {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x}) :
    (H.augmentedIrrep u x ω₀ ρ).matrix
      ((H.augmented x ω₀).residualWithReference (H.augmentedReference x ω₀)
        (H.augmentedChoices hf x ω₀ ω))=
      ρ.matrix ((H.placementChart u).pointEquiv x |>.symm <|
        (H.placementChart u).transitionResidual x (H.placementAction (H.residual hf ω₀) x)
          (H.residual hf ω₀) (H.residual hf ω.val) rfl ω.property) := by
  change ρ.matrix ((H.placementChart u).pointEquiv x |>.symm <|
    (H.augmentFixEquiv u x (fun i => G.sweep ω₀.val (x i).val) ω₀.val ω₀.property (fun _ => rfl)).symm
      ((H.augmented x ω₀).residualWithReference (H.augmentedReference x ω₀)
        (H.augmentedChoices hf x ω₀ ω)))=_
  rw [← H.augmented_residual hf u x ω₀ ω,MulEquiv.symm_apply_apply]

/- Actual normalized placement-fiber average equals the augmented sweep average
in a feasible frame. No conditional law is extended to complex z. -/
theorem transitionAverage_eq_augmented (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    (H.placementChart u).transitionAverage ρ (H.placementWeight z) (H.residual hf)
      x (H.placementAction (H.residual hf ω₀) x) ω₀ rfl=
      (H.augmented x ω₀).averageWithReference (H.augmentedReference x ω₀) z (H.augmentedIrrep u x ω₀ ρ) := by
  classical
  let : Fintype {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x} := Subtype.fintype _
  unfold PlacementInduction.Chart.transitionAverage averageWithReference
  rw [H.transition_probability hf u x ω₀ z,Finset.smul_sum]
  rw [← Equiv.sum_comp (H.augmentedChoices hf x ω₀)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [H.augmentedIrrep_residual hf u x ω₀ ρ ω,smul_smul]
  congr 1
  change ((↑((H.augmented x ω₀).probability z/H.probability z) : ℂ)⁻¹*
    ↑(G.choiceWeight z ω.val.val/H.probability z))=↑(G.choiceWeight z ω.val.val/(H.augmented x ω₀).probability z)
  have hH : (H.probability z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (H.probability_pos hf hz hz').ne'
  have hJ : ((H.augmented x ω₀).probability z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((H.augmented x ω₀).probability_pos (H.augmented_feasible x ω₀) hz hz').ne'
  push_cast
  field_simp

/- The original conditional fiber moment in06:eq23, with the full augmented path
potential available from03:eq4. All frame factors are proved unitary. -/
theorem conditionalBlock_augmented_moment (hf : H.Feasible) (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) (q : ℕ) :
    schattenMoment q ((H.placementChart u).conditionalBlock ρ (H.placementWeight z) (H.residual hf)
      (H.placementAction (H.residual hf ω₀) x) x)=
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep u x ω₀ ρ)) := by
  rw [(H.placementChart u).conditionalBlock_eq ρ (H.placementWeight z) (H.residual hf) x _ ω₀ rfl]
  rw [schattenMoment_unitary_left q _ _ (ρ.unitary _),H.transitionAverage_eq_augmented hf u x ω₀ ρ hz hz']
  exact (H.augmented x ω₀).averageWithReference_moment (H.augmented_feasible x ω₀)
    (H.augmentedReference x ω₀) z (H.augmentedIrrep u x ω₀ ρ) q

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma augmented_extends (x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) : (H.augmented x ω₀).Extends H :=
  H.augment_extends _ _ _ _ _ _

/- The uniform hook estimate is charged to each actual induced block using
source03:eq4. This is the precise attachment, not a new assumption about frames. -/
theorem augmented_block_budget (hf : H.Feasible) (u : H.Placement (k := k))
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz'.le g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz'.le g ≤ 2*FiniteLaw.uniform _ g)
    (q : ℕ) (B : ℝ)
    (hT : ∀ (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}),
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep u x ω₀ ρ)) ≤ Real.exp (B-(H.augmented x ω₀).cost))
    (y x : H.Placement (k := k)) :
    (H.placementChart u).transition (H.placementWeight z) (H.residual hf) y x*
      schattenMoment q ((H.placementChart u).conditionalBlock ρ (H.placementWeight z) (H.residual hf) y x)
      ≤ Real.exp (B-(k : ℝ)*Real.log G.size-H.cost+Real.log 4*k*G.b) := by
  by_cases he : ∃ ω₀ : {ω : G.Choices // H.Compatible ω}, y=H.placementAction (H.residual hf ω₀) x
  · obtain ⟨ω₀,rfl⟩ := he
    rw [H.conditionalBlock_augmented_moment hf u x ω₀ ρ hz hz',H.transition_probability hf u x ω₀ z]
    have hp := (H.augmented x ω₀).conditional_transition_bound H (H.augmented_extends x ω₀) hz hz'.le hlo hhi
    calc
      _ ≤ ((H.augmented x ω₀).probability z/H.probability z)*Real.exp (B-(H.augmented x ω₀).cost) :=
        mul_le_mul_of_nonneg_left (hT x ω₀) (div_nonneg
          ((H.augmented x ω₀).probability_pos (H.augmented_feasible x ω₀) hz hz').le
          (H.probability_pos hf hz hz').le)
      _ ≤ _ := (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; congr 1; ring)
  · have hp : (H.placementChart u).transition (H.placementWeight z) (H.residual hf) y x=0 := by
      apply Finset.sum_eq_zero
      intro ω _
      exact ite_eq_right (fun hh => he ⟨ω,hh⟩)
    rw [hp,zero_mul]
    exact (Real.exp_pos _).le
end CoordinateSweeps.Grid.Holes

/- Required analytic interpolation for the matrix trace Hölder step06 (23).
A bounded holomorphic function on a tube over a box is bounded on the tube
over the convex hull of its bounded vertices. No Schatten assertion assumed. -/
noncomputable section
open Set Complex
open scoped BigOperators Topology

open scoped Matrix.Norms.L2Operator

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep BlockCycles
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

/- Source06:eq23 for the genuine induced placement representation and its actual
normalized blocks. Frobenius reciprocity supplies the literal branching multiplicity. -/
theorem induced_cycle_bound (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G)
    (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω) (g : W → G) (q : ℕ) (hq : 0 < q) :
    let A := averageMatrix (C.action ρ) (fun ω => (w ω : ℂ)) g
    let L := evenWord q A
    letI : NeZero L.length := ⟨by rw [evenWord_length]; omega⟩
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) : ℝ)*
        (Matrix.trace (((averageMatrix τ.matrix (fun ω => (w ω : ℂ)) g).conjTranspose*
          averageMatrix τ.matrix (fun ω => (w ω : ℂ)) g)^q)).re ≤
      ∑ x : Fin L.length → Ω,
        (∏ i, edgeWeight A (L.get i) (C.transition w g) (x i) (x (i+1))) *
        ∏ i, (Matrix.trace (((edgeFiber A (L.get i) (C.conditionalBlock ρ w g)
          (x i) (x (i+1))).conjTranspose*edgeFiber A (L.get i) (C.conditionalBlock ρ w g)
          (x i) (x (i+1)))^q)).re ^ ((2*q : ℝ)⁻¹) := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  refine (C.induced_moment_bound ρ τ (fun ω => (w ω : ℂ)) g q).trans ?_
  apply even_cycle_bound q hq _ (C.transition w g) (C.transition_nonneg w hw g)
  intro y x
  exact C.average_block ρ w hw g y x

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps

variable {Ω : Type*} [Fintype Ω]

def tupleSplit (n : ℕ) : (Fin (n+1) → Ω) ≃ Ω × (Fin n → Ω) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by cases x; rfl

theorem sum_tuple_split (n : ℕ) (f : (Fin (n+1) → Ω) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x, f (Fin.cons a x) := by
  rw [← (tupleSplit n).symm.sum_comp f]
  exact Fintype.sum_prod_type _

def chainWeight {n : ℕ} (P : Fin n → Ω → Ω → ℝ) (x : Fin (n+1) → Ω) : ℝ :=
  ∏ i, P i (x i.castSucc) (x i.succ)

omit [Fintype Ω] in
theorem chainWeight_succ {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+2) → Ω) :
    chainWeight P x = P 0 (x 0) (x 1) *
      chainWeight (fun i => P i.succ) (fun i => x i.succ) := by
  rw [chainWeight, Fin.prod_univ_succ]
  rfl

theorem sum_chainWeight {n : ℕ} (P : Fin n → Ω → Ω → ℝ)
    (hP : ∀ i y, ∑ x, P i x y = 1) :
    ∑ x, chainWeight P x = Fintype.card Ω := by
  induction n with
  | zero => simp [chainWeight]
  | succ n ih =>
    rw [sum_tuple_split, Finset.sum_comm]
    simp only [chainWeight_succ, Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
    simp_rw [← Finset.sum_mul, hP 0, one_mul]
    apply ih
    intro i y
    exact hP i.succ y

/- The edge-deleted product from the source; the missing edge is represented
by 1, so the empty/one-node case is unambiguous. -/
def deletedCycle {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+1) → Ω) (r : Fin (n+1)) : ℝ :=
  ∏ i, if i = r then 1 else P i (x i) (x (i+1))

omit [Fintype Ω] in
theorem deletedCycle_last {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+1) → Ω) :
    deletedCycle P x (Fin.last n) = chainWeight (fun i => P i.castSucc) x := by
  rw [deletedCycle, Fin.prod_univ_castSucc]
  simp [chainWeight, Fin.castSucc_ne_last]

def tupleReindex {n : ℕ} (e : Equiv.Perm (Fin n)) : (Fin n → Ω) ≃ (Fin n → Ω) where
  toFun x := fun i => x (e i)
  invFun x := fun i => x (e.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

omit [Fintype Ω] in
theorem deletedCycle_rotate {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+1) → Ω) (r : Fin (n+1)) :
    let e := finCycle (r-Fin.last n)
    deletedCycle P x r =
      deletedCycle (fun i => P (e i)) (tupleReindex e x) (Fin.last n) := by
  intro e
  have he : e (Fin.last n) = r := by dsimp [e]; simp
  unfold deletedCycle
  rw [← Equiv.prod_comp e (fun i => if i = r then 1 else P i (x i) (x (i+1)))]
  apply Finset.prod_congr rfl
  intro i _
  have hiff : e i = r ↔ i = Fin.last n := by rw [← he, Equiv.apply_eq_iff_eq]
  simp only [hiff]
  by_cases hi : i = Fin.last n
  · simp [hi]
  · simp only [hi, ite_false, tupleReindex, Equiv.coe_fn_mk]
    congr 2
    dsimp [e]
    simp only [finCycle_apply]
    abel

theorem sum_deletedCycle {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (hP : ∀ i y, ∑ x, P i x y = 1) (r : Fin (n+1)) :
    ∑ x, deletedCycle P x r = Fintype.card Ω := by
  let e := finCycle (r-Fin.last n)
  calc
    _ = ∑ x, deletedCycle (fun i => P (e i)) (tupleReindex e x) (Fin.last n) := by
      apply Finset.sum_congr rfl
      intro x _
      exact deletedCycle_rotate P x r
    _ = ∑ y, deletedCycle (fun i => P (e i)) y (Fin.last n) := Equiv.sum_comp (tupleReindex e) (fun y => deletedCycle (fun i => P (e i)) y (Fin.last n))
    _ = ∑ y, chainWeight (fun i => P (e i.castSucc)) y := by simp_rw [deletedCycle_last]
    _ = _ := sum_chainWeight _ (fun i y => hP _ y)

/- The product identity retains zeros, so the eventual inequality does not
silently omit impossible cyclic placement terms. -/
theorem prod_deleted_numbers {n : ℕ} (p : Fin (n+1) → ℝ) :
    (∏ r, ∏ i, if i = r then (1 : ℝ) else p i) = (∏ i, p i)^n := by
  rw [Finset.prod_comm, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  have he := Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin (n+1))))
    (f := fun r => if i = r then (1 : ℝ) else p i) (Finset.mem_univ i)
  simp only [ite_true, mul_one] at he
  rw [← he]
  calc
    _ = ∏ _ ∈ (Finset.univ : Finset (Fin (n+1))).erase i, p i := by
      apply Finset.prod_congr rfl
      intro r hr
      exact ite_eq_right (Ne.symm (Finset.mem_erase.mp hr).1)
    _ = _ := by simp

theorem cycle_geometric_identity {n : ℕ} (p : Fin (n+1) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∏ i, (p i)^((n : ℝ)/(n+1))) =
      ∏ r, (∏ i, if i = r then (1 : ℝ) else p i)^((n+1 : ℝ)⁻¹) := by
  have hn : 0 ≤ ∏ i, p i := Finset.prod_nonneg (fun i _ => hp i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hp i), Real.finsetProd_rpow _ _ (by
    intro r _
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · positivity
    · exact hp i), prod_deleted_numbers,
    ← Real.rpow_natCast (∏ i, p i) n, ← Real.rpow_mul hn]
  congr 1

/- Exact scalar cycle bound used after (23); column stochasticity alone
suffices. The paper has both row and column stochasticity from bijections. -/
theorem stochastic_cycle_holder {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (hP0 : ∀ i x y, 0 ≤ P i x y) (hP : ∀ i y, ∑ x, P i x y = 1) :
    (∑ x : Fin (n+1) → Ω, ∏ i, (P i (x i) (x (i+1)))^((n : ℝ)/(n+1))) ≤
      Fintype.card Ω := by
  have hN : (n+1 : ℝ) ≠ 0 := by positivity
  have hweights : (∑ _ : Fin (n+1), (n+1 : ℝ)⁻¹) = 1 := by simp [hN]
  calc
    _ ≤ ∑ x : Fin (n+1) → Ω, ∑ r, (n+1 : ℝ)⁻¹ * deletedCycle P x r := by
      apply Finset.sum_le_sum
      intro x _
      rw [cycle_geometric_identity _ (fun i => hP0 i _ _)]
      apply Real.geom_mean_le_arith_mean_weighted
      · intro _ _; positivity
      · exact hweights
      · intro r _
        apply Finset.prod_nonneg
        intro i _
        split_ifs
        · positivity
        · exact hP0 i _ _
    _ = Fintype.card Ω := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_deletedCycle P hP]
      simp [hN]

end CoordinateSweeps

namespace CoordinateSweeps
variable {Ω : Type*} [Fintype Ω]

/- Archived scalar cycle inequality with the positive cycle length explicit. -/
theorem stochastic_cycle_holder_length {N : ℕ} [NeZero N]
    (P : Fin N → Ω → Ω → ℝ) (hP0 : ∀ i x y, 0 ≤ P i x y)
    (hP : ∀ i y, ∑ x, P i x y=1) :
    (∑ x : Fin N → Ω, ∏ i, (P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹)) ≤ Fintype.card Ω := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have he : 1-(n+1 : ℝ)⁻¹=(n : ℝ)/(n+1) := by field_simp; ring
    simpa only [Nat.cast_add,Nat.cast_one,he] using stochastic_cycle_holder P hP0 hP

lemma weighted_root_le {p t E r : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t) (hE : 0 ≤ E)
    (hr : 0 < r) (hh : p*t ≤ E) :
    p*t^r ≤ E^r*p^(1-r) := by
  by_cases hp0 : p=0
  · subst p
    simp only [zero_mul]
    positivity
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  calc
    p*t^r=(p*t)^r*p^(1-r) := by
      rw [Real.mul_rpow hp ht]
      have he : p^r*p^(1-r)=p := by rw [← Real.rpow_add hp',add_sub_cancel,Real.rpow_one]
      calc
        _ = (p^r*p^(1-r))*t^r := by rw [he]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (mul_nonneg hp ht) hh hr.le)
      (Real.rpow_nonneg hp _)

/- Source06:eq24 scalar endgame, with the full trajectory potential charged
once locally as P*T ≤ E. No independence or positivity of edges is assumed. -/
theorem cycle_potential_bound {N : ℕ} [NeZero N]
    (P T : Fin N → Ω → Ω → ℝ) (hP0 : ∀ i y x, 0 ≤ P i y x)
    (hT0 : ∀ i y x, 0 ≤ T i y x) (hP : ∀ i x, ∑ y, P i y x=1)
    {E : ℝ} (hE : 0 ≤ E) (hPT : ∀ i y x, P i y x*T i y x ≤ E) :
    (∑ x : Fin N → Ω, (∏ i, P i (x i) (x (i+1))) *
      ∏ i, (T i (x i) (x (i+1)))^((N : ℝ)⁻¹)) ≤ (Fintype.card Ω : ℝ)*E := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  calc
    _ ≤ ∑ x : Fin N → Ω, E*∏ i, (P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro x _
      rw [← Finset.prod_mul_distrib]
      calc
        _ ≤ ∏ i, E^((N : ℝ)⁻¹)*(P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹) := by
          apply Finset.prod_le_prod₀
          · intro i _; exact mul_nonneg (hP0 i _ _) (Real.rpow_nonneg (hT0 i _ _) _)
          · intro i _; exact weighted_root_le (hP0 i _ _) (hT0 i _ _) hE (inv_pos.mpr hN) (hPT i _ _)
        _ = _ := by
          rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
          congr 1
          rw [← Real.rpow_natCast,← Real.rpow_mul hE,inv_mul_cancel₀ hN.ne',Real.rpow_one]
    _ = E*∑ x : Fin N → Ω, ∏ i, (P i (x i) (x (i+1)))^(1-(N : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ E*Fintype.card Ω := mul_le_mul_of_nonneg_left (stochastic_cycle_holder_length P hP0 hP) hE
    _ = _ := mul_comm _ _
end CoordinateSweeps

namespace CoordinateSweeps.BlockCycles
open TraceHolder
open scoped ComplexOrder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq Ω] [DecidableEq n] [Nonempty n] in
lemma edgeWeight_columns (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (hc : ∀ x, ∑ y, p y x=1) (hr : ∀ y, ∑ x, p y x=1) (x : Ω) :
    ∑ y, edgeWeight A B p y x=1 := by
  unfold edgeWeight
  split_ifs <;> first | exact hc x | exact hr x

omit [DecidableEq Ω] [Nonempty n] in
lemma edge_moment_nonneg (A B : Matrix (Ω × n) (Ω × n) ℂ)
    (K : Ω → Ω → Matrix n n ℂ) (q : ℕ) (y x : Ω) :
    0 ≤ (Matrix.trace (((edgeFiber A B K y x).conjTranspose*edgeFiber A B K y x)^q)).re :=
  (((Matrix.posSemidef_conjTranspose_mul_self (edgeFiber A B K y x)).pow q).trace_nonneg).1

omit [DecidableEq Ω] [Nonempty n] in
lemma edge_potential (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (K : Ω → Ω → Matrix n n ℂ) (q : ℕ) (E : ℝ)
    (hPT : ∀ y x, p y x*(Matrix.trace (((K y x).conjTranspose*K y x)^q)).re ≤ E) (y x : Ω) :
    edgeWeight A B p y x*
      (Matrix.trace (((edgeFiber A B K y x).conjTranspose*edgeFiber A B K y x)^q)).re ≤ E := by
  unfold edgeWeight edgeFiber
  split_ifs
  · exact hPT y x
  · rw [Matrix.conjTranspose_conjTranspose,trace_mul_pow_comm]
    exact hPT x y

/- The genuine matrix placement-cycle bound closes using the literal doubly
stochastic transitions and source03's potential budget. -/
theorem even_potential_bound (q : ℕ) (hq : 0 < q) (A : Matrix (Ω × n) (Ω × n) ℂ)
    (p : Ω → Ω → ℝ) (hp : ∀ y x, 0 ≤ p y x)
    (hc : ∀ x, ∑ y, p y x=1) (hr : ∀ y, ∑ x, p y x=1)
    (K : Ω → Ω → Matrix n n ℂ)
    (hA : ∀ y x, blocks A y x=(p y x : ℂ) • K y x)
    {E : ℝ} (hE : 0 ≤ E)
    (hPT : ∀ y x, p y x*(Matrix.trace (((K y x).conjTranspose*K y x)^q)).re ≤ E) :
    (Matrix.trace ((A.conjTranspose*A)^q)).re ≤ (Fintype.card Ω : ℝ)*E := by
  let L := evenWord q A
  let : NeZero L.length := ⟨by dsimp [L]; rw [evenWord_length]; omega⟩
  refine (even_cycle_bound q hq A p hp K hA).trans ?_
  have hb := cycle_potential_bound (N := L.length)
    (fun i => edgeWeight A (L.get i) p)
    (fun i y x => (Matrix.trace (((edgeFiber A (L.get i) K y x).conjTranspose*
      edgeFiber A (L.get i) K y x)^q)).re)
    (fun i => edgeWeight_nonneg A (L.get i) p hp)
    (fun i => edge_moment_nonneg A (L.get i) K q)
    (fun i => edgeWeight_columns A (L.get i) p hc hr) hE
    (fun i => edge_potential A (L.get i) p K q E hPT)
  have he : ((L.length : ℝ)⁻¹)=((2*q : ℝ)⁻¹) := by dsimp [L]; rw [evenWord_length]; push_cast; rfl
  rw [he] at hb
  exact hb
end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep BlockCycles
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

theorem induced_potential_bound (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G)
    (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω=1) (g : W → G)
    (q : ℕ) (hq : 0 < q) {E : ℝ} (hE : 0 ≤ E)
    (hPT : ∀ y x, C.transition w g y x *
      (Matrix.trace (((C.conditionalBlock ρ w g y x).conjTranspose*C.conditionalBlock ρ w g y x)^q)).re ≤ E) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) : ℝ)*
        (Matrix.trace (((averageMatrix τ.matrix (fun ω => (w ω : ℂ)) g).conjTranspose*
          averageMatrix τ.matrix (fun ω => (w ω : ℂ)) g)^q)).re ≤ (Fintype.card Ω : ℝ)*E := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  refine (C.induced_moment_bound ρ τ (fun ω => (w ω : ℂ)) g q).trans ?_
  exact even_potential_bound q hq _ (C.transition w g) (C.transition_nonneg w hw g)
    (C.transition_columns w hs g) (C.transition_rows w hs g) _
    (C.average_block ρ w hw g) hE hPT
end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma placements_card_le : Fintype.card (H.Placement (k := k)) ≤ G.size^k := by
  rw [Fintype.card_embedding_eq,H.card_freeAt, Fintype.card_fin]
  exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

/- Source06:eq24's entire placement-counting and potential endgame, with true
branching Hom multiplicity and arbitrary feasible holes. The hook estimate is
its sole analytic input and will be discharged by the child induction. -/
theorem actual_induced_endgame (hf : H.Feasible) (u : H.Placement (k := k))
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) (τ : UnitaryIrrep H.stabilizer)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz'.le g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz'.le g ≤ 2*FiniteLaw.uniform _ g)
    (q : ℕ) (hq : 0 < q) (B : ℝ)
    (hT : ∀ (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}),
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep u x ω₀ ρ)) ≤ Real.exp (B-(H.augmented x ω₀).cost)) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (τ.matrix.comp (H.placementChart u).stabilizer.subtype))) : ℝ)*
        schattenMoment q (H.conditionalAverage hf z τ) ≤
      Real.exp (B-H.cost+Real.log 4*k*G.b) := by
  have hh := (H.placementChart u).induced_potential_bound ρ τ (H.placementWeight z)
    (H.placementWeight_nonneg hf hz hz') (H.placementWeight_sum hf hz hz') (H.residual hf) q hq
    (Real.exp_pos (B-(k : ℝ)*Real.log G.size-H.cost+Real.log 4*k*G.b)).le
    (H.augmented_block_budget hf u ρ hz hz' hlo hhi q B hT)
  have hav : averageMatrix τ.matrix (fun ω => (H.placementWeight z ω : ℂ)) (H.residual hf)=
      H.conditionalAverage hf z τ := by rw [H.conditionalAverage_eq_sum]; rfl
  rw [hav] at hh
  refine hh.trans ?_
  have hs : 0 < (G.size : ℝ) := by
    have hsN : 0<G.size := by
      unfold Grid.size
      exact Finset.prod_pos (fun j _ => pow_pos (by omega : 0<2) _)
    exact_mod_cast hsN
  calc
    _ ≤ (G.size : ℝ)^k*Real.exp (B-(k : ℝ)*Real.log G.size-H.cost+Real.log 4*k*G.b) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast H.placements_card_le (k := k)) (Real.exp_pos _).le
    _ = _ := by
      rw [show (G.size : ℝ)^k=Real.exp ((k : ℝ)*Real.log G.size) by
        rw [Real.exp_nat_mul,Real.exp_log hs],← Real.exp_add]
      congr 1
      ring
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
