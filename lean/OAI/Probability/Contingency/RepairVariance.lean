import Mathlib
import OAI.Probability.Contingency.ConditionalTransport

namespace OAI

/-! Repair Variance. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency

 
theorem variance_le_center {α : Type*} [Fintype α] (w H : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (a : ℝ) :
    weightedVariance w H ≤ ∑ x, w x*(H x-a)^2 := by
  by_cases h : totalWeight w = 0
  · have hz : ∀ x, w x=0 := by
      intro x
      have hh := Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)
      change w x ≤ totalWeight w at hh
      rw [h] at hh
      exact le_antisymm hh (hw x)
    simp [weightedVariance,hz]
  · rw [variance_translate w H h a]
    exact le_add_of_nonneg_right (mul_nonneg (Finset.sum_nonneg fun x _ => hw x) (sq_nonneg _))

 

theorem variance_repair_extension {T D P K : Type*}
    [Fintype T] [Fintype D] [Fintype P] [Fintype K]
    (wT hT : T → ℝ) (wD hD : D → ℝ) (wP hP : P → ℝ)
    (_hwT : ∀ t, 0 ≤ wT t) (hwD : ∀ x, 0 ≤ wD x) (hwP : ∀ p, 0 ≤ wP p)
    (f : T → P) (hf : Function.Injective f)
    (hTw : ∀ t, wT t=wP (f t)) (hTh : ∀ t, hT t=hP (f t))
    (g : D → K × P) (hg : Function.Injective g) (hDw : ∀ x, wD x≤wP (g x).2)
    (E : ℝ) (hE : (∑ x, wD x*(hD x-hP (g x).2)^2) ≤ E) :
    weightedVariance (Sum.elim wT wD) (Sum.elim hT hD) ≤
      (1+2*(Fintype.card K:ℝ))*weightedVariance wP hP+2*E := by
  classical
  let a := weightedMean wP hP
  have ht : (∑ t, wT t*(hT t-a)^2) ≤ weightedVariance wP hP := by
    simp_rw [hTw,hTh]
    rw [← Finset.sum_image (s := Finset.univ) (f := fun p => wP p*(hP p-a)^2)
      (fun x _ y _ h => hf h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => mul_nonneg (hwP x) (sq_nonneg _))
  have hd : (∑ x, wD x*(hP (g x).2-a)^2) ≤
      (Fintype.card K:ℝ)*weightedVariance wP hP := by
    calc
      _ ≤ ∑ x, wP (g x).2*(hP (g x).2-a)^2 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hDw x) (sq_nonneg _)
      _ = ∑ kp ∈ Finset.univ.image g, wP kp.2*(hP kp.2-a)^2 := by
        rw [Finset.sum_image (fun x _ y _ h => hg h)]
      _ ≤ ∑ kp : K × P, wP kp.2*(hP kp.2-a)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => mul_nonneg (hwP x.2) (sq_nonneg _))
      _ = _ := by simp [Fintype.sum_prod_type,weightedVariance,a]
  have hx : (∑ x, wD x*(hD x-a)^2) ≤
      2*(∑ x, wD x*(hD x-hP (g x).2)^2) +
      2*(∑ x, wD x*(hP (g x).2-a)^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have hs : (hD x-a)^2 ≤ 2*(hD x-hP (g x).2)^2+2*(hP (g x).2-a)^2 := by
      nlinarith [sq_nonneg (hD x-2*hP (g x).2+a)]
    have hm := mul_le_mul_of_nonneg_left hs (hwD x)
    nlinarith only [hm]
  have hb := variance_le_center (Sum.elim wT wD) (Sum.elim hT hD)
    (by intro x; cases x <;> simp_all) a
  rw [Fintype.sum_sum_type] at hb
  simp only [Sum.elim_inl,Sum.elim_inr] at hb
  nlinarith only [hb,ht,hd,hx,hE]

end Contingency

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

abbrev TransverseState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  {X : State m n // Feasible U r c X ∧ Transversal X}
abbrev DefectiveState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  {X : State m n // Feasible U r c X ∧ ∃ s t, DefectAt U r c s t X}
 
abbrev GraphState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  TransverseState U r c ⊕ DefectiveState U r c

instance transverseFinite (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finite (TransverseState U r c) :=
  Finite.of_injective (fun X => (⟨X.val,X.property.1⟩ : {X // Feasible U r c X}))
    (fun _ _ h => Subtype.ext (congrArg (fun Y : {X // Feasible U r c X} => Y.val) h))
instance defectiveFinite (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finite (DefectiveState U r c) :=
  Finite.of_injective (fun X => (⟨X.val,X.property.1⟩ : {X // Feasible U r c X}))
    (fun _ _ h => Subtype.ext (congrArg (fun Y : {X // Feasible U r c X} => Y.val) h))
noncomputable instance transverseFintype (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Fintype (TransverseState U r c) := Fintype.ofFinite _
noncomputable instance defectiveFintype (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Fintype (DefectiveState U r c) := Fintype.ofFinite _

noncomputable def defectPair (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : DefectiveState U r c) : Cell m n × Cell m n :=
  (X.property.2.choose, X.property.2.choose_spec.choose)

theorem defectPair_spec (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : DefectiveState U r c) :
    DefectAt U r c (defectPair U r c X).1 (defectPair U r c X).2 X.val :=
  X.property.2.choose_spec.choose_spec

theorem defect_not_transversal (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X) : ¬Transversal X := by
  intro hT
  have h := congrFun hd.2.2.2 s
  change X.q=X.x at hT
  rw [hT] at h
  simp [unit,hd.2.2.1] at h

noncomputable def repairedState (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : DefectiveState U r c) : TransverseState U r c :=
  ⟨repair U r c (defectPair U r c X).1 (defectPair U r c X).2 X.val,
    repair_feasible U r c _ _ _ X.property.1 (defectPair_spec U r c X),rfl⟩

theorem coordinates_state_inverse (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hX : ∀ w, IsLarge U r c w → X.x w=0 ∧ X.q w=0) :
    coordinatesState U r c (stateCoordinates U r c X)=X := by
  have hx : (coordinatesState U r c (stateCoordinates U r c X)).x=X.x := by
    funext w
    by_cases hw : IsSmall U r c w
    · simp [coordinatesState,stateCoordinates,hw]
    · simp [coordinatesState,hw,(hX w (Classical.not_not.mp hw)).1]
  have hq : (coordinatesState U r c (stateCoordinates U r c X)).q=X.q := by
    funext w
    by_cases hw : IsSmall U r c w
    · simp [coordinatesState,stateCoordinates,hw]
    · simp [coordinatesState,hw,(hX w (Classical.not_not.mp hw)).2]
  exact congrArg₂ State.mk hx hq

noncomputable def transverseTuple (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : TransverseState U r c) : SmallSlot U r c → Fin (U+1) :=
  fun s => ⟨(X.val.x s.val).toNat,by have h := X.property.1.1 s.val; omega⟩

@[simp] theorem tuple_transverseTuple (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : TransverseState U r c) : tupleState U r c (transverseTuple U r c X)=X.val := by
  have hh : (fun w : SmallCoord U r c => if w.2 then
      ((transverseTuple U r c X w.1:ℕ):ℤ) else (U:ℤ)-(transverseTuple U r c X w.1:ℕ)) =
      stateCoordinates U r c X.val := by
    funext ⟨s,b⟩
    have hnn := (X.property.1.1 s.val).1
    have hT : X.val.q=X.val.x := X.property.2
    cases b <;> simp [transverseTuple,stateCoordinates,Int.toNat_of_nonneg hnn,hT]
  unfold tupleState
  rw [hh]
  exact coordinates_state_inverse U r c X.val X.property.1.2.1

noncomputable def rootProfile (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (α : SmallSlot U r c → Fin (U+1)) : Profiles U (Fintype.card (SmallSlot U r c)) :=
  (profileEquiv U _).symm (α ∘ smallIndex U r c)

@[simp] theorem rootProfile_state (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (α : SmallSlot U r c → Fin (U+1)) :
    profileState U r c 0 (Fintype.card (SmallSlot U r c)) (by omega) Fin.elim0
      (rootProfile U r c α)=tupleState U r c α := by
  unfold profileState rootProfile
  rw [Equiv.apply_symm_apply]
  congr 1
  funext s
  simp [appendAssignment]

noncomputable def transverseProfile (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : TransverseState U r c) : Profiles U (Fintype.card (SmallSlot U r c)) :=
  rootProfile U r c (transverseTuple U r c X)

@[simp] theorem transverseProfile_state (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : TransverseState U r c) :
    profileState U r c 0 (Fintype.card (SmallSlot U r c)) (by omega) Fin.elim0
      (transverseProfile U r c X)=X.val := by
  simp [transverseProfile]

theorem transverseProfile_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Function.Injective (transverseProfile U r c) := by
  intro X Y he
  have hh := congrArg (profileState U r c 0 (Fintype.card (SmallSlot U r c)) (by omega) Fin.elim0) he
  simpa only [transverseProfile_state,Subtype.val_inj] using hh

noncomputable def taggedRepair (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : DefectiveState U r c) : (Cell m n × Cell m n) × Profiles U (Fintype.card (SmallSlot U r c)) :=
  (defectPair U r c X,transverseProfile U r c (repairedState U r c X))

theorem taggedRepair_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Function.Injective (taggedRepair U r c) := by
  intro X Y he
  have hp : defectPair U r c X=defectPair U r c Y := congrArg Prod.fst he
  have ht := transverseProfile_injective U r c (congrArg Prod.snd he)
  have ht' := congrArg Subtype.val ht
  change repair U r c _ _ X.val=repair U r c _ _ Y.val at ht'
  rw [← hp] at ht'
  apply Subtype.ext
  apply repair_injective U r c _ _ X.val Y.val (defectPair_spec U r c X) _ ht'
  rw [hp]
  exact defectPair_spec U r c Y

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

theorem defect_type_unique (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (s t s' t' : Cell m n)
    (h : DefectAt U r c s t X) (h' : DefectAt U r c s' t' X) : s=s' ∧ t=t' := by
  have hs := congrFun h.2.2.2 s
  have hs' := congrFun h'.2.2.2 s
  have ht := congrFun h.2.2.2 t
  have ht' := congrFun h'.2.2.2 t
  simp [unit,h.2.2.1,Ne.symm h.2.2.1] at hs ht
  constructor
  · by_contra he
    simp only [unit,ite_eq_right he] at hs'
    split_ifs at hs' <;> omega
  · by_contra he
    simp only [unit,ite_eq_right he] at ht'
    split_ifs at ht' <;> omega

theorem stateCoordinates_box (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hX : Feasible U r c X) :
    InBox (fun _ => (U:ℤ)) (stateCoordinates U r c X) := by
  intro ⟨s,b⟩
  have h := hX.1 s.val
  cases b <;> simp only [stateCoordinates,Bool.false_eq_true,ite_false,ite_true] <;> omega

@[simp] theorem fullOccupancy_state (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (s : SmallSlot U r c) :
    fullOccupancy U r c (stateCoordinates U r c X) s = (U:ℤ)+X.x s.val-X.q s.val := by
  simp [fullOccupancy,stateCoordinates]
  ring

theorem stateCoordinates_transverse_vertex (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : TransverseState U r c) : stateCoordinates U r c X.val∈fullVertices U r c := by
  apply (mem_fullVertices U r c _).mpr
  refine ⟨stateCoordinates_box U r c X.val X.property.1,Or.inl ?_⟩
  intro s
  rw [fullOccupancy_state,show X.val.q=X.val.x from X.property.2]
  omega

theorem stateCoordinates_defect_vertex (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : DefectiveState U r c) : stateCoordinates U r c X.val∈fullVertices U r c := by
  obtain ⟨s,t,hd⟩ := X.property.2
  apply (mem_fullVertices U r c _).mpr
  refine ⟨stateCoordinates_box U r c X.val X.property.1,Or.inr ?_⟩
  refine ⟨⟨s,hd.1⟩,⟨t,hd.2.1⟩,?_,?_,?_,?_⟩
  · intro he; exact hd.2.2.1 (congrArg Subtype.val he)
  · rw [fullOccupancy_state]
    change (U:ℤ)+X.val.x s-X.val.q s=(U:ℤ)-1
    rw [hd.2.2.2]
    simp [unit,hd.2.2.1]
    ring
  · rw [fullOccupancy_state]
    change (U:ℤ)+X.val.x t-X.val.q t=(U:ℤ)+1
    rw [hd.2.2.2]
    simp [unit,Ne.symm hd.2.2.1]
    ring
  · intro v hvs hvt
    have hvs' : v.val≠s := fun he => hvs (Subtype.ext he)
    have hvt' : v.val≠t := fun he => hvt (Subtype.ext he)
    rw [fullOccupancy_state,hd.2.2.2]
    simp [unit,hvs',hvt']

theorem state_kernel_weight (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (X : State m n) (hX : Feasible U r c X) :
    smallKernel 0 U L C r c (stateCoordinates U r c X)=(weight U L r c X:ℝ) := by
  classical
  rw [weight,ite_eq_left hX]
  exact smallKernel_zero_count U L C r c hrc X hX hC

noncomputable def repairEdge (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : DefectiveState U r c) : Sym2 (SmallCoord U r c → ℤ) :=
  s(stateCoordinates U r c X.val,stateCoordinates U r c (repairedState U r c X).val)

theorem stateCoordinates_inj_feasible (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X Y : State m n) (hX : Feasible U r c X) (hY : Feasible U r c Y)
    (he : stateCoordinates U r c X=stateCoordinates U r c Y) : X=Y := by
  have hh := congrArg (coordinatesState U r c) he
  simpa only [coordinates_state_inverse U r c X hX.2.1,
    coordinates_state_inverse U r c Y hY.2.1] using hh

theorem repairEdge_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Function.Injective (repairEdge U r c) := by
  intro X Y he
  rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
  · exact Subtype.ext (stateCoordinates_inj_feasible U r c _ _ X.property.1 Y.property.1 h)
  · have hh := stateCoordinates_inj_feasible U r c _ _ X.property.1
      (repairedState U r c Y).property.1 h
    have ht : Transversal X.val := hh ▸ (repairedState U r c Y).property.2
    exact (defect_not_transversal U r c _ _ X.val (defectPair_spec U r c X) ht).elim

noncomputable def fullRepairEdges (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finset (Sym2 (SmallCoord U r c → ℤ)) := by
  classical
  exact Finset.univ.image (repairEdge U r c)

 

noncomputable def fullEdges (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finset (Sym2 (SmallCoord U r c → ℤ)) := by
  classical
  exact fullUnitEdges U r c ∪ fullRepairEdges U r c

noncomputable def graphEnergy (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) : ℝ :=
  ∑ e ∈ fullEdges U r c, edgeEnergy (smallKernel 0 U L C r c)
    (H ∘ coordinatesState U r c) e

theorem graphEnergy_nonneg (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) : 0≤graphEnergy U L C r c H :=
  Finset.sum_nonneg fun e _ => edgeEnergy_nonneg _ _ (smallKernel_nonneg 0 (by positivity) U L C r c) e

theorem unitEnergy_le_graphEnergy (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) : fullUnitEnergy U L C r c H ≤ graphEnergy U L C r c H := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.subset_union_left
  · intro e _ _
    exact edgeEnergy_nonneg _ _ (smallKernel_nonneg 0 (by positivity) U L C r c) e

theorem repairEdge_energy (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : State m n → ℝ) (X : DefectiveState U r c) :
    edgeEnergy (smallKernel 0 U L C r c) (H ∘ coordinatesState U r c) (repairEdge U r c X) =
      (weight U L r c X.val:ℝ)*(H X.val-H (repairedState U r c X).val)^2 := by
  change min (smallKernel 0 U L C r c (stateCoordinates U r c X.val))
    (smallKernel 0 U L C r c (stateCoordinates U r c (repairedState U r c X).val)) *
    (H (coordinatesState U r c (stateCoordinates U r c X.val))-
      H (coordinatesState U r c (stateCoordinates U r c (repairedState U r c X).val)))^2 = _
  rw [state_kernel_weight U L C r c hrc hC X.val X.property.1,
    state_kernel_weight U L C r c hrc hC _ (repairedState U r c X).property.1,
    coordinates_state_inverse U r c _ X.property.1.2.1,
    coordinates_state_inverse U r c _ (repairedState U r c X).property.1.2.1]
  rw [min_eq_left]
  exact_mod_cast weight_repair_le U L r c _ _ X.val (defectPair_spec U r c X)

theorem repairEnergy_le_graphEnergy (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : State m n → ℝ) :
    (∑ X : DefectiveState U r c,
      (weight U L r c X.val:ℝ)*(H X.val-H (repairedState U r c X).val)^2) ≤
        graphEnergy U L C r c H := by
  classical
  simp_rw [← repairEdge_energy U L C r c hrc hC H]
  rw [← Finset.sum_image (fun X _ Y _ he => repairEdge_injective U r c he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.subset_union_right
  · intro e _ _
    exact edgeEnergy_nonneg _ _ (smallKernel_nonneg 0 (by positivity) U L C r c) e

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ}

def graphUnderlying (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    GraphState U r c → State m n := Sum.elim Subtype.val Subtype.val

theorem graphUnderlying_injective (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Function.Injective (graphUnderlying U r c) := by
  intro X Y h
  cases X with
  | inl X =>
    cases Y with
    | inl Y => exact congrArg Sum.inl (Subtype.ext h)
    | inr Y =>
      change X.val=Y.val at h
      have ht : Transversal Y.val := h ▸ X.property.2
      exact (defect_not_transversal U r c _ _ Y.val (defectPair_spec U r c Y) ht).elim
  | inr X =>
    cases Y with
    | inl Y =>
      change X.val=Y.val at h
      have ht : Transversal X.val := h.symm ▸ Y.property.2
      exact (defect_not_transversal U r c _ _ X.val (defectPair_spec U r c X) ht).elim
    | inr Y => exact congrArg Sum.inr (Subtype.ext h)

noncomputable def graphVariance (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (H : State m n → ℝ) : ℝ :=
  weightedVariance (fun X : GraphState U r c => (weight U L r c (graphUnderlying U r c X):ℝ))
    (H ∘ graphUnderlying U r c)

 

theorem graph_poincare_exact (U L C d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hU : 2 ≤ U) (hC2 : 2 ≤ C) (hd : 1 ≤ d) (hmn : m*n≤d)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i ≤ C)
    (H : State m n → ℝ) :
    graphVariance U L r c H ≤ ((1+2*(d:ℝ)^2)*4*(d:ℝ)^2*((U:ℝ)+1)^6+2)*
      graphEnergy U L C r c H := by
  let P := profileState U r c 0 (Fintype.card (SmallSlot U r c)) (by omega) Fin.elim0
  let wP := fun p => (weight U L r c (P p):ℝ)
  let hP := H ∘ P
  have hs : Fintype.card (SmallSlot U r c)≤d := by
    have hh := Fintype.card_le_of_injective (smallRank U r c) (smallRank_injective U r c)
    simp only [Fintype.card_fin] at hh
    omega
  have hv := concrete_transversal_variance U L C d r c hU hC2 hd hs hrc hC H
  change weightedVariance wP hP ≤ _ at hv
  have he := unitEnergy_le_graphEnergy U L C r c H
  have hv' : weightedVariance wP hP ≤ 4*(d:ℝ)^2*((U:ℝ)+1)^6*graphEnergy U L C r c H :=
    hv.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hb := variance_repair_extension
    (fun X : TransverseState U r c => (weight U L r c X.val:ℝ)) (fun X => H X.val)
    (fun X : DefectiveState U r c => (weight U L r c X.val:ℝ)) (fun X => H X.val)
    wP hP (fun X => by positivity) (fun X => by positivity) (fun p => by positivity)
    (transverseProfile U r c) (transverseProfile_injective U r c)
    (fun X => by simp [wP,P]) (fun X => by simp [hP,P])
    (taggedRepair U r c) (taggedRepair_injective U r c)
    (fun X => by
      dsimp [wP,P,taggedRepair]
      rw [transverseProfile_state]
      exact_mod_cast weight_repair_le U L r c _ _ X.val (defectPair_spec U r c X))
    (graphEnergy U L C r c H) (by
      simpa only [hP,P,taggedRepair,Function.comp_apply,transverseProfile_state] using
        repairEnergy_le_graphEnergy U L C r c hrc hC H)
  have heq : graphVariance U L r c H = weightedVariance
      (Sum.elim (fun X : TransverseState U r c => (weight U L r c X.val:ℝ))
        (fun X : DefectiveState U r c => (weight U L r c X.val:ℝ)))
      (Sum.elim (fun X => H X.val) (fun X => H X.val)) := by
    unfold graphVariance
    congr 1 <;> funext X <;> cases X <;> rfl
  rw [← heq] at hb
  have hc : (Fintype.card (Cell m n × Cell m n):ℝ) ≤ (d:ℝ)^2 := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact_mod_cast (show m*n*(m*n)≤d^2 by
      simpa only [pow_two] using Nat.mul_self_le_mul_self hmn)
  have hn := variance_nonneg wP hP (fun p => by positivity)
  have hm := mul_le_mul_of_nonneg_right hc hn
  have hv'' := mul_le_mul_of_nonneg_left hv' (show 0≤1+2*(d:ℝ)^2 by positivity)
  nlinarith only [hb,hm,hv'']

theorem poincare_constant_le (d U : ℕ) (hd : 1≤d) (hU : 1≤U) :
    (1+2*(d:ℝ)^2)*4*(d:ℝ)^2*((U:ℝ)+1)^6+2 ≤ 770*(d:ℝ)^4*(U:ℝ)^6 := by
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  have hU' : (1:ℝ)≤U := by exact_mod_cast hU
  have hd2 : (1:ℝ)≤(d:ℝ)^2 := one_le_pow₀ hd'
  have hd4 : (1:ℝ)≤(d:ℝ)^4 := one_le_pow₀ hd'
  have hU6 : (1:ℝ)≤(U:ℝ)^6 := one_le_pow₀ hU'
  have hu : ((U:ℝ)+1)^6≤64*(U:ℝ)^6 := by
    calc
      _ ≤ (2*(U:ℝ))^6 := by gcongr; linarith
      _ = _ := by ring
  calc
    _ ≤ (3*(d:ℝ)^2)*4*(d:ℝ)^2*(64*(U:ℝ)^6)+2 := by
      gcongr
      nlinarith only [hd2]
    _ ≤ _ := by nlinarith [mul_le_mul hd4 hU6 (by positivity) (by positivity)]

 
theorem graph_poincare (U L C d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hU : 2≤U) (hC2 : 2≤C) (hd : 1≤d) (hmn : m*n≤d)
    (hrc : (∑ i, r i)=∑ j, c j) (hC : ∀ i, paddedRow U L r c i≤C)
    (H : State m n → ℝ) :
    graphVariance U L r c H ≤ 770*(d:ℝ)^4*(U:ℝ)^6*graphEnergy U L C r c H :=
  (graph_poincare_exact U L C d r c hU hC2 hd hmn hrc hC H).trans
    (mul_le_mul_of_nonneg_right (poincare_constant_le d U hd (by omega))
      (graphEnergy_nonneg U L C r c H))

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def graphCoordinates (X : GraphState U r c) : SmallCoord U r c → ℤ :=
  stateCoordinates U r c (graphUnderlying U r c X)

theorem graph_feasible (X : GraphState U r c) : Feasible U r c (graphUnderlying U r c X) := by
  cases X with
  | inl X => exact X.property.1
  | inr X => exact X.property.1

theorem graphCoordinates_injective : Function.Injective (graphCoordinates U r c) := by
  intro X Y h
  apply graphUnderlying_injective U r c
  exact stateCoordinates_inj_feasible U r c _ _ (graph_feasible U r c X) (graph_feasible U r c Y) h

def GraphAdj (X Y : GraphState U r c) : Prop :=
  s(graphCoordinates U r c X,graphCoordinates U r c Y)∈fullEdges U r c

noncomputable instance graphAdjDecidable : DecidableRel (GraphAdj U r c) := fun _ _ => Classical.propDecidable _

theorem GraphAdj.symm {X Y : GraphState U r c} (h : GraphAdj U r c X Y) : GraphAdj U r c Y X := by
  simpa only [GraphAdj,Sym2.eq_swap] using h

theorem GraphAdj.irrefl (X : GraphState U r c) : ¬GraphAdj U r c X X := by
  classical
  intro hh
  rcases Finset.mem_union.mp hh with hu | hr
  · obtain ⟨_,D,i,j,hij,he⟩ := Finset.mem_filter.mp hu
    have he' : removeOne D i=removeOne D j := by
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact h1.symm.trans h2
      · exact h2.symm.trans h1
    have h := congrFun he' i
    simp [removeOne,hij] at h
  · obtain ⟨Y,_,hy⟩ := Finset.mem_image.mp hr
    have he' : stateCoordinates U r c Y.val=stateCoordinates U r c (repairedState U r c Y).val := by
      rcases Sym2.eq_iff.mp hy with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> exact h1.trans h2.symm
    have h := stateCoordinates_inj_feasible U r c _ _ Y.property.1 (repairedState U r c Y).property.1 he'
    exact defect_not_transversal U r c _ _ Y.val (defectPair_spec U r c Y) (h ▸ (repairedState U r c Y).property.2)

def unitCandidates (X : GraphState U r c) : Finset (SmallCoord U r c → ℤ) := by
  classical
  exact Finset.univ.image (fun ij : SmallCoord U r c × SmallCoord U r c =>
    fun w => graphCoordinates U r c X w + (if w=ij.1 then 1 else 0) - (if w=ij.2 then 1 else 0))

def outgoing (X : GraphState U r c) : Finset (GraphState U r c) := by
  classical
  exact match X with | .inl _ => ∅ | .inr Y => {Sum.inl (repairedState U r c Y)}

def incomingDefects (X : GraphState U r c) : Finset (DefectiveState U r c) := by
  classical
  exact Finset.univ.filter (fun Y => Sum.inl (repairedState U r c Y)=X)

theorem incoming_card (X : GraphState U r c) : (incomingDefects U r c X).card≤(m*n)^2 := by
  classical
  have hi : Set.InjOn (defectPair U r c) (incomingDefects U r c X : Set _) := by
    intro Y hY Z hZ h
    apply taggedRepair_injective U r c
    apply Prod.ext h
    have hY' := (Finset.mem_filter.mp hY).2
    have hZ' := (Finset.mem_filter.mp hZ).2
    have he := Sum.inl.inj (hY'.trans hZ'.symm)
    exact congrArg (transverseProfile U r c) he
  have hh := Finset.card_le_card_of_injOn (defectPair U r c) (s:=incomingDefects U r c X)
    (t:=Finset.univ) (fun _ _ => Finset.mem_univ _) hi
  simpa [Cell,Fintype.card_prod,pow_two] using hh

theorem neighbors_cover (X Y : GraphState U r c) (h : GraphAdj U r c X Y) :
    graphCoordinates U r c Y∈unitCandidates U r c X ∨
    Y∈outgoing U r c X ∨ Y∈(incomingDefects U r c X).image Sum.inr := by
  classical
  rcases Finset.mem_union.mp h with hu | hr
  · left
    obtain ⟨_,D,i,j,hij,he⟩ := Finset.mem_filter.mp hu
    rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · apply Finset.mem_image.mpr
      refine ⟨(i,j),Finset.mem_univ _,?_⟩
      funext w
      rw [hx,hy]
      simp only [removeOne]
      ring
    · apply Finset.mem_image.mpr
      refine ⟨(j,i),Finset.mem_univ _,?_⟩
      funext w
      rw [hx,hy]
      simp only [removeOne]
      ring
  · obtain ⟨Z,_,he⟩ := Finset.mem_image.mp hr
    rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hx' : Sum.inr Z=X := graphCoordinates_injective U r c hx
      have hy' : Sum.inl (repairedState U r c Z)=Y := graphCoordinates_injective U r c hy
      right; left
      rw [← hx',← hy']; simp [outgoing]
    · have hx' : Sum.inr Z=Y := graphCoordinates_injective U r c hx
      have hy' : Sum.inl (repairedState U r c Z)=X := graphCoordinates_injective U r c hy
      right; right
      exact Finset.mem_image.mpr ⟨Z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy'⟩,hx'⟩

 

theorem graph_degree (d : ℕ) (hmn : m*n≤d) (X : GraphState U r c) :
    (Finset.univ.filter (GraphAdj U r c X)).card≤5*d^2+1 := by
  classical
  let A := Finset.univ.filter (fun Y => graphCoordinates U r c Y∈unitCandidates U r c X)
  let B := outgoing U r c X
  let C : Finset (GraphState U r c) := (incomingDefects U r c X).image Sum.inr
  have hsub : Finset.univ.filter (GraphAdj U r c X) ⊆ A ∪ B ∪ C := by
    intro Y hY
    rcases neighbors_cover U r c X Y (Finset.mem_filter.mp hY).2 with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  have ha : A.card≤4*d^2 := by
    have hh := Finset.card_le_card_of_injOn (graphCoordinates U r c)
      (s:=A) (t:=unitCandidates U r c X) (fun _ h => (Finset.mem_filter.mp h).2)
      (fun _ _ _ _ h => graphCoordinates_injective U r c h)
    have hc : (unitCandidates U r c X).card≤(Fintype.card (SmallCoord U r c))^2 := by
      simpa [unitCandidates,Fintype.card_prod,pow_two] using (Finset.card_image_le
        (s:=(Finset.univ : Finset (SmallCoord U r c × SmallCoord U r c)))
        (f:=fun ij => fun w => graphCoordinates U r c X w+(if w=ij.1 then (1:ℤ) else 0)-(if w=ij.2 then 1 else 0)))
    have hs : Fintype.card (SmallSlot U r c)≤d := by
      have hh := Fintype.card_le_of_injective (smallRank U r c) (smallRank_injective U r c)
      simp only [Fintype.card_fin] at hh
      omega
    have hc' : Fintype.card (SmallCoord U r c)≤2*d := by
      simp only [SmallCoord,Fintype.card_prod,Fintype.card_bool]
      omega
    exact hh.trans (hc.trans (by nlinarith))
  have hb : B.card≤1 := by cases X <;> simp [B,outgoing]
  have hc : C.card≤d^2 := by
    exact Finset.card_image_le.trans ((incoming_card U r c X).trans (Nat.pow_le_pow_left hmn 2))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have hh := Finset.card_union_le A B
    omega))

end
end Contingency.PaddedGraph

end

end OAI
