import Mathlib
import OAI.Probability.Contingency.RepairVariance

namespace OAI

/-! Residual Margins. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def residualRow (X : State m n) (i : Fin m) : ℤ := r i-rowSum X.x i+rowPadding U L r c i
def residualCol (X : State m n) (j : Fin n) : ℤ := c j-colSum X.q j+colPadding U L r c j

theorem residualRow_nonneg (X : State m n) (hX : Feasible U r c X) (i : Fin m) :
    0≤residualRow U L r c X i := by
  have hp : 0≤rowPadding U L r c i := Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  have hh := (hX.2.2.1 i).1
  dsimp [residualRow]; omega

theorem residualCol_nonneg (X : State m n) (hX : Feasible U r c X) (j : Fin n) :
    0≤residualCol U L r c X j := by
  have hp : 0≤colPadding U L r c j := Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  have hh := (hX.2.2.2 j).1
  dsimp [residualCol]; omega

theorem residualRow_zero (X : State m n) (hX : Feasible U r c X) (i : Fin m)
    (hi : r i<U) : residualRow U L r c X i=0 := by
  have he : ∀ j,¬IsLarge U r c (i,j) := fun j h => by have h : U≤r i := h.1; omega
  simp only [residualRow,(hX.2.2.1 i).2 he,sub_self,zero_add,rowPadding,ite_eq_right (he _),Finset.sum_const_zero]

theorem residualCol_zero (X : State m n) (hX : Feasible U r c X) (j : Fin n)
    (hj : c j<U) : residualCol U L r c X j=0 := by
  have he : ∀ i,¬IsLarge U r c (i,j) := fun i h => by have h : U≤c j := h.2; omega
  simp only [residualCol,(hX.2.2.2 j).2 he,sub_self,zero_add,colPadding,ite_eq_right (he _),Finset.sum_const_zero]

theorem graph_small_totals (X : GraphState U r c) :
    (∑ w,(graphUnderlying U r c X).x w)=∑ w,(graphUnderlying U r c X).q w := by
  cases X with
  | inl X => rw [show (graphUnderlying U r c (.inl X)).q=X.val.x from X.property.2]; rfl
  | inr X =>
    change (∑ w,X.val.x w)=∑ w,X.val.q w
    rw [(defectPair_spec U r c X).2.2.2]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,unit]
    simp

theorem residual_totals (X : GraphState U r c) (hrc : (∑ i,r i)=∑ j,c j) :
    (∑ i,residualRow U L r c (graphUnderlying U r c X) i)=
      ∑ j,residualCol U L r c (graphUnderlying U r c X) j := by
  have ht := graph_small_totals U r c X
  have hp := padding_totals U L r c
  have hr : (∑ i,(r i:ℤ))=∑ j,(c j:ℤ) := by exact_mod_cast hrc
  simp only [residualRow,residualCol,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hr,hp]
  congr 2
  simp only [rowSum,colSum]
  rw [← Fintype.sum_prod_type,Finset.sum_comm,← Fintype.sum_prod_type]
  exact ht

def rowNat (X : State m n) (i : Fin m) : ℕ := (residualRow U L r c X i).toNat
def colNat (X : State m n) (j : Fin n) : ℕ := (residualCol U L r c X j).toNat

@[simp] theorem rowNat_cast (X : State m n) (hX : Feasible U r c X) (i : Fin m) :
    (rowNat U L r c X i:ℤ)=residualRow U L r c X i := Int.toNat_of_nonneg (residualRow_nonneg U L r c X hX i)
@[simp] theorem colNat_cast (X : State m n) (hX : Feasible U r c X) (j : Fin n) :
    (colNat U L r c X j:ℤ)=residualCol U L r c X j := Int.toNat_of_nonneg (residualCol_nonneg U L r c X hX j)

def completionTable (X : State m n) (hX : Feasible U r c X) (A : Completion U L r c X) :
    Tables (rowNat U L r c X) (colNat U L r c X) := by
  refine ⟨fun i j => (A.val (i,j)).toNat,?_,?_⟩
  · intro i
    apply Int.ofNat_inj.mp
    push_cast
    simp only [Int.toNat_of_nonneg (A.property.1 _),rowNat_cast U L r c X hX]
    exact A.property.2.2.1 i
  · intro j
    apply Int.ofNat_inj.mp
    push_cast
    simp only [Int.toNat_of_nonneg (A.property.1 _),colNat_cast U L r c X hX]
    exact A.property.2.2.2 j

def tableCompletion (X : State m n) (hX : Feasible U r c X)
    (A : Tables (rowNat U L r c X) (colNat U L r c X)) : Completion U L r c X := by
  refine ⟨fun w => (A.val w.1 w.2:ℤ),fun _ => by positivity,?_,?_,?_⟩
  · intro ⟨i,j⟩ h
    have h : ¬(U≤r i ∧ U≤c j) := h
    have hz : A.val i j=0 := by
      by_cases hi : U≤r i
      · have hj : c j<U := by omega
        have hs := A.property.2 j
        have he : colNat U L r c X j=0 := by simp [colNat,residualCol_zero U L r c X hX j hj]
        rw [he] at hs
        have hl := Finset.single_le_sum (fun i _ => Nat.zero_le (A.val i j)) (Finset.mem_univ i)
        omega
      · have hi : r i<U := by omega
        have hs := A.property.1 i
        have he : rowNat U L r c X i=0 := by simp [rowNat,residualRow_zero U L r c X hX i hi]
        rw [he] at hs
        have hl := Finset.single_le_sum (fun j _ => Nat.zero_le (A.val i j)) (Finset.mem_univ j)
        omega
    simp [hz]
  · intro i
    change (∑ j,(A.val i j:ℤ))=residualRow U L r c X i
    rw [← Nat.cast_sum,A.property.1,rowNat_cast U L r c X hX]
  · intro j
    change (∑ i,(A.val i j:ℤ))=residualCol U L r c X j
    rw [← Nat.cast_sum,A.property.2,colNat_cast U L r c X hX]

 

def completionTableEquiv (X : State m n) (hX : Feasible U r c X) :
    Completion U L r c X ≃ Tables (rowNat U L r c X) (colNat U L r c X) where
  toFun := completionTable U L r c X hX
  invFun := tableCompletion U L r c X hX
  left_inv A := by
    apply Subtype.ext; funext w
    exact Int.toNat_of_nonneg (A.property.1 w)
  right_inv A := by apply Subtype.ext; funext i j; simp [completionTable,tableCompletion]

theorem completion_nonempty (X : GraphState U r c) (hrc : (∑ i,r i)=∑ j,c j) :
    Nonempty (Completion U L r c (graphUnderlying U r c X)) := by
  have hf := graph_feasible U r c X
  have ht : (∑ i,rowNat U L r c (graphUnderlying U r c X) i)=
      ∑ j,colNat U L r c (graphUnderlying U r c X) j := by
    apply Int.ofNat_inj.mp
    push_cast
    simp only [rowNat_cast U L r c _ hf,colNat_cast U L r c _ hf]
    exact residual_totals U L r c X hrc
  obtain ⟨A⟩ := tables_nonempty _ _ ht
  exact ⟨(completionTableEquiv U L r c _ hf).symm A⟩

theorem graph_weight_pos (X : GraphState U r c) (hrc : (∑ i,r i)=∑ j,c j) :
    0<weight U L r c (graphUnderlying U r c X) := by
  have := completion_nonempty U L r c X hrc
  rw [weight,ite_eq_left (graph_feasible U r c X)]
  exact Nat.card_pos

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def shiftCoord (p : SmallCoord U r c → ℤ) (z : SmallCoord U r c) (t : ℤ) :=
  fun w => p w+t*(if w=z then 1 else 0)

theorem shift_x (p : SmallCoord U r c → ℤ) (z : SmallCoord U r c) (t : ℤ) (w : Cell m n) :
    (coordinatesState U r c (shiftCoord U r c p z t)).x w=
    (coordinatesState U r c p).x w+(if z.2 then t*unit z.1.val w else 0) := by
  rcases z with ⟨s,b⟩
  by_cases hw : IsSmall U r c w
  · cases b <;> simp [coordinatesState,shiftCoord,hw,unit,Subtype.ext_iff]
  · have hne : w≠s.val := fun h => hw (h ▸ s.property)
    cases b <;> simp [coordinatesState,shiftCoord,hw,unit,hne]

theorem shift_q (p : SmallCoord U r c → ℤ) (z : SmallCoord U r c) (t : ℤ) (w : Cell m n) :
    (coordinatesState U r c (shiftCoord U r c p z t)).q w=
    (coordinatesState U r c p).q w-(if z.2 then 0 else t*unit z.1.val w) := by
  rcases z with ⟨s,b⟩
  by_cases hw : IsSmall U r c w
  · cases b <;> simp [coordinatesState,shiftCoord,hw,unit,Subtype.ext_iff]
    ring
  · have hne : w≠s.val := fun h => hw (h ▸ s.property)
    cases b <;> simp [coordinatesState,shiftCoord,hw,unit,hne]

theorem shift_row (p : SmallCoord U r c → ℤ) (z : SmallCoord U r c) (t : ℤ) (i : Fin m) :
    rowSum (coordinatesState U r c (shiftCoord U r c p z t)).x i=
      rowSum (coordinatesState U r c p).x i+(if z.2 then t*(if i=z.1.val.1 then 1 else 0) else 0) := by
  simp only [rowSum,shift_x,Finset.sum_add_distrib]
  rw [Finset.sum_ite_irrel]
  congr 1
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const_zero]
  change (if z.2 then t*rowSum (unit z.1.val) i else 0)=_
  rw [rowSum_unit]

theorem shift_col (p : SmallCoord U r c → ℤ) (z : SmallCoord U r c) (t : ℤ) (j : Fin n) :
    colSum (coordinatesState U r c (shiftCoord U r c p z t)).q j=
      colSum (coordinatesState U r c p).q j-(if z.2 then 0 else t*(if j=z.1.val.2 then 1 else 0)) := by
  simp only [colSum,shift_q,Finset.sum_sub_distrib]
  rw [Finset.sum_ite_irrel]
  congr 1
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const_zero]
  change (if z.2 then 0 else t*colSum (unit z.1.val) j)=_
  rw [colSum_unit]

theorem unit_margin_movement (X Y : State m n) (hX : Feasible U r c X) (hY : Feasible U r c Y)
    (hu : s(stateCoordinates U r c X,stateCoordinates U r c Y)∈fullUnitEdges U r c) :
    (∀ i,|residualRow U L r c Y i-residualRow U L r c X i|≤2) ∧
    (∀ j,|residualCol U L r c Y j-residualCol U L r c X j|≤2) := by
  classical
  have hh : ∃ i j,stateCoordinates U r c Y =
      shiftCoord U r c (shiftCoord U r c (stateCoordinates U r c X) i 1) j (-1) := by
    obtain ⟨_,D,i,j,hij,he⟩ := Finset.mem_filter.mp hu
    rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · refine ⟨i,j,?_⟩
      rw [hx,hy]; funext w; simp only [shiftCoord,removeOne]; ring
    · refine ⟨j,i,?_⟩
      rw [hx,hy]; funext w; simp only [shiftCoord,removeOne]; ring
  obtain ⟨s,t,he⟩ := hh
  have hstate := congrArg (coordinatesState U r c) he
  rw [coordinates_state_inverse U r c Y hY.2.1] at hstate
  constructor
  · intro i
    have hh := congrArg (fun Z : State m n => rowSum Z.x i) hstate
    rw [shift_row,shift_row,coordinates_state_inverse U r c X hX.2.1] at hh
    dsimp [residualRow]
    rw [hh]
    rw [abs_le]
    split_ifs <;> omega
  · intro j
    have hh := congrArg (fun Z : State m n => colSum Z.q j) hstate
    rw [shift_col,shift_col,coordinates_state_inverse U r c X hX.2.1] at hh
    dsimp [residualCol]
    rw [hh]
    rw [abs_le]
    split_ifs <;> omega

theorem repair_margin_movement (X : DefectiveState U r c) :
    (∀ i,|residualRow U L r c (repairedState U r c X).val i-residualRow U L r c X.val i|≤2) ∧
    (∀ j,|residualCol U L r c (repairedState U r c X).val j-residualCol U L r c X.val j|≤2) := by
  constructor
  · intro i
    dsimp [residualRow,repairedState]
    rw [repair_rowSum,abs_le]
    split_ifs <;> omega
  · intro j
    dsimp [residualCol,repairedState]
    rw [repair_colSum U r c _ _ _ (defectPair_spec U r c X),abs_le]
    split_ifs <;> omega

 
theorem graph_margin_movement (X Y : GraphState U r c) (h : GraphAdj U r c X Y) :
    (∀ i,|residualRow U L r c (graphUnderlying U r c Y) i-
      residualRow U L r c (graphUnderlying U r c X) i|≤2) ∧
    (∀ j,|residualCol U L r c (graphUnderlying U r c Y) j-
      residualCol U L r c (graphUnderlying U r c X) j|≤2) := by
  classical
  rcases Finset.mem_union.mp h with hu | hr
  · exact unit_margin_movement U L r c _ _ (graph_feasible U r c X) (graph_feasible U r c Y) hu
  · obtain ⟨Z,_,he⟩ := Finset.mem_image.mp hr
    rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hx' : Sum.inr Z=X := graphCoordinates_injective U r c hx
      have hy' : Sum.inl (repairedState U r c Z)=Y := graphCoordinates_injective U r c hy
      rw [← hx',← hy']
      exact repair_margin_movement U L r c Z
    · have hx' : Sum.inr Z=Y := graphCoordinates_injective U r c hx
      have hy' : Sum.inl (repairedState U r c Z)=X := graphCoordinates_injective U r c hy
      rw [← hx',← hy']
      simpa only [graphUnderlying,Sum.elim_inl,Sum.elim_inr,abs_sub_comm] using repair_margin_movement U L r c Z

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

theorem pattern_graphState (p : SmallCoord U r c → ℤ)
    (hp : fullPattern U r c p) (hf : Feasible U r c (coordinatesState U r c p)) :
    ∃ X : GraphState U r c,graphCoordinates U r c X=p := by
  rcases hp with ht | ⟨s,t,hst,hs,ht,ho⟩
  · have hT : Transversal (coordinatesState U r c p) := by
      funext w
      by_cases hw : IsSmall U r c w
      · have hh := ht ⟨w,hw⟩
        simp only [fullOccupancy] at hh
        simp only [coordinatesState,dite_eq_left hw]
        omega
      · simp [coordinatesState,hw]
    exact ⟨Sum.inl ⟨_,hf,hT⟩,stateCoordinates_coordinatesState U r c p⟩
  · have hD : DefectAt U r c s.val t.val (coordinatesState U r c p) := by
      refine ⟨s.property,t.property,fun h => hst (Subtype.ext h),?_⟩
      funext w
      by_cases hw : IsSmall U r c w
      · simp only [coordinatesState,dite_eq_left hw]
        by_cases hws : w=s.val
        · subst w
          have hst' : s.val≠t.val := fun h => hst (Subtype.ext h)
          simp only [unit,ite_true,ite_eq_right hst']
          change (U:ℤ)-p (s,false)=p (s,true)-0+1
          dsimp [fullOccupancy] at hs
          omega
        · by_cases hwt : w=t.val
          · subst w
            simp only [unit,ite_eq_right hws,ite_true]
            change (U:ℤ)-p (t,false)=p (t,true)-1+0
            dsimp [fullOccupancy] at ht
            omega
          · have hh := ho ⟨w,hw⟩ (fun h => hws (congrArg Subtype.val h))
              (fun h => hwt (congrArg Subtype.val h))
            simp only [fullOccupancy] at hh
            simp only [unit,ite_eq_right hws,ite_eq_right hwt]
            omega
      · have hws : w≠s.val := fun h => hw (h ▸ s.property)
        have hwt : w≠t.val := fun h => hw (h ▸ t.property)
        simp [coordinatesState,hw,unit,hws,hwt]
    exact ⟨Sum.inr ⟨_,hf,s.val,t.val,hD⟩,stateCoordinates_coordinatesState U r c p⟩

theorem positive_vertex (p : SmallCoord U r c → ℤ) (hv : p∈fullVertices U r c)
    (hp : smallKernel 0 U L C r c p≠0) :
    ∃ X : GraphState U r c,graphCoordinates U r c X=p := by
  apply pattern_graphState U r c p ((mem_fullVertices U r c p).mp hv).2
  by_contra hf
  exact hp (smallKernel_zero_infeasible U L C r c p hf)

theorem positive_edge (H : State m n → ℝ) (e : Sym2 (SmallCoord U r c → ℤ))
    (he : e∈fullEdges U r c)
    (hp : edgeEnergy (smallKernel 0 U L C r c) (H ∘ coordinatesState U r c) e≠0) :
    ∃ X Y : GraphState U r c,e=s(graphCoordinates U r c X,graphCoordinates U r c Y) := by
  classical
  rcases Finset.mem_union.mp he with hu | hr
  · induction e using Sym2.inductionOn with | _ p q =>
      have hv := Finset.mem_filter.mp hu
      have hpq := Finset.mk_mem_sym2_iff.mp hv.1
      have hn := smallKernel_nonneg 0 (by positivity) U L C r c
      have hkp : smallKernel 0 U L C r c p≠0 := by
        intro h
        apply hp
        rw [edgeEnergy_mk]
        rw [h,min_eq_left (hn q),zero_mul]
      have hkq : smallKernel 0 U L C r c q≠0 := by
        intro h
        apply hp
        rw [edgeEnergy_mk]
        rw [h,min_eq_right (hn p),zero_mul]
      obtain ⟨X,hX⟩ := positive_vertex U L C r c p hpq.1 hkp
      obtain ⟨Y,hY⟩ := positive_vertex U L C r c q hpq.2 hkq
      exact ⟨X,Y,by rw [hX,hY]⟩
  · obtain ⟨Z,_,hz⟩ := Finset.mem_image.mp hr
    exact ⟨Sum.inr Z,Sum.inl (repairedState U r c Z),hz.symm⟩

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
open PaddedGraph
variable {m n : ℕ}

def tableInt {r : Fin m → ℕ} {c : Fin n → ℕ} (X : Tables r c) (w : Cell m n) : ℤ :=
  X.val w.1 w.2

@[simp] theorem tableInt_row {r : Fin m → ℕ} {c : Fin n → ℕ} (X : Tables r c) (i : Fin m) :
    rowSum (tableInt X) i = r i := by
  unfold rowSum tableInt
  exact_mod_cast X.property.1 i
@[simp] theorem tableInt_col {r : Fin m → ℕ} {c : Fin n → ℕ} (X : Tables r c) (j : Fin n) :
    colSum (tableInt X) j = c j := by
  unfold colSum tableInt
  exact_mod_cast X.property.2 j

def switchDirection (i i' : Fin m) (j j' : Fin n) : Cell m n → ℤ :=
  fun w => unit (i,j) w+unit (i',j') w-unit (i,j') w-unit (i',j) w

@[simp] theorem switchDirection_row (i i' : Fin m) (j j' : Fin n) (k : Fin m) :
    rowSum (switchDirection i i' j j') k=0 := by
  simp only [switchDirection,rowSum,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  change rowSum (unit (i,j)) k+rowSum (unit (i',j')) k-
    rowSum (unit (i,j')) k-rowSum (unit (i',j)) k=0
  simp

@[simp] theorem switchDirection_col (i i' : Fin m) (j j' : Fin n) (k : Fin n) :
    colSum (switchDirection i i' j j') k=0 := by
  simp only [switchDirection,colSum,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  change colSum (unit (i,j)) k+colSum (unit (i',j')) k-
    colSum (unit (i,j')) k-colSum (unit (i',j)) k=0
  simp

@[simp] theorem switchDirection_mark (i i' : Fin m) (j j' : Fin n)
    (hi : i≠i') (hj : j≠j') : switchDirection i i' j j' (i,j)=1 := by
  simp [switchDirection,unit,hi,hj]

theorem switch_nonneg {r : Fin m → ℕ} {c : Fin n → ℕ}
    (X : Tables r c) (i i' : Fin m) (j j' : Fin n) (hi : i≠i') (hj : j≠j')
    (v : ℕ) (hr : v≤X.val i j') (hc : v≤X.val i' j) (w : Cell m n) :
    0 ≤ tableInt X w+(v:ℤ)*switchDirection i i' j j' w := by
  have h0 : 0≤tableInt X w := by unfold tableInt; positivity
  by_cases hw : w=(i,j')
  · subst w
    simp [switchDirection,unit,hi,Ne.symm hj,tableInt]
    exact_mod_cast hr
  · by_cases hw' : w=(i',j)
    · subst w
      simp [switchDirection,unit,Ne.symm hi,hj,tableInt]
      exact_mod_cast hc
    · simp only [switchDirection,unit,ite_eq_right hw,ite_eq_right hw',sub_zero]
      split_ifs <;> omega

 

noncomputable def switchTable {r : Fin m → ℕ} {c : Fin n → ℕ}
    (X : Tables r c) (i i' : Fin m) (j j' : Fin n) (hi : i≠i') (hj : j≠j')
    (v : ℕ) (hr : v≤X.val i j') (hc : v≤X.val i' j) : Tables r c :=
  ⟨fun a b => (tableInt X (a,b)+(v:ℤ)*switchDirection i i' j j' (a,b)).toNat, by
    constructor
    · intro a
      have hn (b) := switch_nonneg X i i' j j' hi hj v hr hc (a,b)
      have he : (∑ b, (tableInt X (a,b)+(v:ℤ)*switchDirection i i' j j' (a,b))) = r a := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        change rowSum (tableInt X) a+(v:ℤ)*rowSum (switchDirection i i' j j') a= r a
        simp
      exact_mod_cast (show (∑ b, ((tableInt X (a,b)+(v:ℤ)*switchDirection i i' j j' (a,b)).toNat:ℤ)) = r a by
        simpa only [Int.toNat_of_nonneg (hn _)] using he)
    · intro b
      have hn (a) := switch_nonneg X i i' j j' hi hj v hr hc (a,b)
      have he : (∑ a, (tableInt X (a,b)+(v:ℤ)*switchDirection i i' j j' (a,b))) = c b := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        change colSum (tableInt X) b+(v:ℤ)*colSum (switchDirection i i' j j') b= c b
        simp
      exact_mod_cast (show (∑ a, ((tableInt X (a,b)+(v:ℤ)*switchDirection i i' j j' (a,b)).toNat:ℤ)) = c b by
        simpa only [Int.toNat_of_nonneg (hn _)] using he)⟩

@[simp] theorem switchTable_int {r : Fin m → ℕ} {c : Fin n → ℕ}
    (X : Tables r c) (i i' : Fin m) (j j' : Fin n) (hi : i≠i') (hj : j≠j')
    (v : ℕ) (hr : v≤X.val i j') (hc : v≤X.val i' j) (w : Cell m n) :
    tableInt (switchTable X i i' j j' hi hj v hr hc) w =
      tableInt X w+(v:ℤ)*switchDirection i i' j j' w := by
  exact Int.toNat_of_nonneg (switch_nonneg X i i' j j' hi hj v hr hc w)

theorem switch_injective_with_labels {r : Fin m → ℕ} {c : Fin n → ℕ}
    (X Y : Tables r c) (i i' : Fin m) (j j' : Fin n) (hi : i≠i') (hj : j≠j')
    (v u : ℕ) (hrX : v≤X.val i j') (hcX : v≤X.val i' j)
    (hrY : u≤Y.val i j') (hcY : u≤Y.val i' j)
    (hs : X.val i j=Y.val i j)
    (he : switchTable X i i' j j' hi hj v hrX hcX =
      switchTable Y i i' j j' hi hj u hrY hcY) : X=Y ∧ v=u := by
  have hm := congrArg (fun Z => tableInt Z (i,j)) he
  change tableInt (switchTable X i i' j j' hi hj v hrX hcX) (i,j) =
    tableInt (switchTable Y i i' j j' hi hj u hrY hcY) (i,j) at hm
  rw [switchTable_int,switchTable_int,switchDirection_mark i i' j j' hi hj] at hm
  simp only [mul_one,tableInt,hs] at hm
  have hv : v=u := by omega
  subst u
  refine ⟨?_,rfl⟩
  apply Subtype.ext
  funext a b
  have hh := congrArg (fun Z => tableInt Z (a,b)) he
  change tableInt (switchTable X i i' j j' hi hj v hrX hcX) (a,b) =
    tableInt (switchTable Y i i' j j' hi hj v hrY hcY) (a,b) at hh
  rw [switchTable_int,switchTable_int] at hh
  simp only [tableInt] at hh
  omega

end Contingency

 

 

open scoped BigOperators
namespace Contingency
variable {m n : ℕ}

 

theorem line_donor (d a t : ℕ) (x : Fin n → ℕ) (j : Fin n)
    (hn : n≤d) (ha : a≤∑ k, x k) (ht : 2*t≤a) (hj : x j<t) :
    ∃ k, k≠j ∧ a/(2*d)≤x k := by
  classical
  by_contra he
  push Not at he
  have hb : (∑ k, x k) ≤ n*(a/(2*d))+x j := by
    calc
      _ ≤ ∑ k, (a/(2*d) + if k=j then x j else 0) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k=j
        · subst k; simp
        · simp only [ite_eq_right hk,add_zero]
          exact (he k hk).le
      _ = _ := by simp [Finset.sum_add_distrib]
  have hdv := Nat.div_mul_le_self a (2*d)
  have hnd := Nat.mul_le_mul_right (a/(2*d)) hn
  nlinarith

abbrev SmallEntryBad (r : Fin m → ℕ) (c : Fin n → ℕ) (i : Fin m) (j : Fin n) (t : ℕ) :=
  {X : Tables r c // X.val i j<t}

noncomputable def rowDonor (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hn : n≤d) (ha : a≤r i) (ht : 2*t≤a)
    (X : SmallEntryBad r c i j t) : Fin n :=
  (line_donor d a t (X.val.val i) j hn (X.val.property.1 i ▸ ha) ht X.property).choose

theorem rowDonor_spec (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hn : n≤d) (ha : a≤r i) (ht : 2*t≤a)
    (X : SmallEntryBad r c i j t) :
    rowDonor d a t r c i j hn ha ht X≠j ∧
      a/(2*d)≤X.val.val i (rowDonor d a t r c i j hn ha ht X) :=
  (line_donor d a t (X.val.val i) j hn (X.val.property.1 i ▸ ha) ht X.property).choose_spec

noncomputable def colDonor (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hm : m≤d) (ha : a≤c j) (ht : 2*t≤a)
    (X : SmallEntryBad r c i j t) : Fin m :=
  (line_donor d a t (fun k => X.val.val k j) i hm (X.val.property.2 j ▸ ha) ht X.property).choose

theorem colDonor_spec (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hm : m≤d) (ha : a≤c j) (ht : 2*t≤a)
    (X : SmallEntryBad r c i j t) :
    colDonor d a t r c i j hm ha ht X≠i ∧
      a/(2*d)≤X.val.val (colDonor d a t r c i j hm ha ht X) j :=
  (line_donor d a t (fun k => X.val.val k j) i hm (X.val.property.2 j ▸ ha) ht X.property).choose_spec

noncomputable def smallEntryMoves (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hm : m≤d) (hn : n≤d) (hr : a≤r i) (hc : a≤c j) (ht : 2*t≤a)
    (z : SmallEntryBad r c i j t × Fin (a/(2*d))) : Tables r c × (Cell m n × Fin t) :=
  let i' := colDonor d a t r c i j hm hc ht z.1
  let j' := rowDonor d a t r c i j hn hr ht z.1
  let hi := colDonor_spec d a t r c i j hm hc ht z.1
  let hj := rowDonor_spec d a t r c i j hn hr ht z.1
  (switchTable z.1.val i i' j j' hi.1.symm hj.1.symm (z.2.val+1)
    (by exact (Nat.add_one_le_iff.mpr z.2.isLt).trans hj.2)
    (by exact (Nat.add_one_le_iff.mpr z.2.isLt).trans hi.2),
    ((i',j'),⟨z.1.val.val i j,z.1.property⟩))

theorem smallEntryMoves_injective (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hm : m≤d) (hn : n≤d) (hr : a≤r i) (hc : a≤c j) (ht : 2*t≤a) :
    Function.Injective (smallEntryMoves d a t r c i j hm hn hr hc ht) := by
  rintro ⟨X,v⟩ ⟨Y,u⟩ he
  have hi : colDonor d a t r c i j hm hc ht X=colDonor d a t r c i j hm hc ht Y :=
    congrArg (fun z => z.2.1.1) he
  have hj : rowDonor d a t r c i j hn hr ht X=rowDonor d a t r c i j hn hr ht Y :=
    congrArg (fun z => z.2.1.2) he
  have hs : X.val.val i j=Y.val.val i j := congrArg (fun z => z.2.2.val) he
  have htab := congrArg Prod.fst he
  dsimp only [smallEntryMoves] at htab
  have he' := congrArg (fun Z : Tables r c => tableInt Z (i,j)) htab
   
  change tableInt (switchTable _ _ _ _ _ _ _ _ _ _) (i,j) =
    tableInt (switchTable _ _ _ _ _ _ _ _ _ _) (i,j) at he'
  rw [switchTable_int,switchTable_int,
    switchDirection_mark _ _ _ _ (colDonor_spec d a t r c i j hm hc ht X).1.symm
      (rowDonor_spec d a t r c i j hn hr ht X).1.symm,
    switchDirection_mark _ _ _ _ (colDonor_spec d a t r c i j hm hc ht Y).1.symm
      (rowDonor_spec d a t r c i j hn hr ht Y).1.symm] at he'
  simp only [tableInt,hs,mul_one] at he'
  have hv : v=u := Fin.ext (by omega)
  subst u
  have hXY : X=Y := by
    apply Subtype.ext
    apply Subtype.ext
    funext k l
    have h := congrArg (fun Z : Tables r c => tableInt Z (k,l)) htab
    change tableInt (switchTable _ _ _ _ _ _ _ _ _ _) (k,l) =
      tableInt (switchTable _ _ _ _ _ _ _ _ _ _) (k,l) at h
    rw [switchTable_int,switchTable_int,hi,hj] at h
    simp only [tableInt] at h
    omega
  subst Y
  rfl

theorem small_entry_count_floor (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hm : m≤d) (hn : n≤d) (hr : a≤r i) (hc : a≤c j) (ht : 2*t≤a) :
    Nat.card (SmallEntryBad r c i j t)*(a/(2*d)) ≤ Nat.card (Tables r c)*(m*n*t) := by
  have hh := Nat.card_le_card_of_injective _ (smallEntryMoves_injective d a t r c i j hm hn hr hc ht)
  simpa only [Nat.card_prod,Nat.card_fin] using hh

theorem floor_donor_lower (d a : ℕ) (hd : 1≤d) (ha : 4*d≤a) :
    a≤4*d*(a/(2*d)) := by
  have hq : 0<a/(2*d) := Nat.div_pos (by omega) (by omega)
  have hh := Nat.lt_mul_div_succ a (show 0<2*d by omega)
  have hm := Nat.mul_le_mul_left (2*d) (show a/(2*d)+1≤2*(a/(2*d)) by omega)
  nlinarith only [hh,hm]

 

theorem small_entry_count (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hd : 1≤d) (hm : m≤d) (hn : n≤d)
    (ha : 4*d≤a) (hr : a≤r i) (hc : a≤c j) (ht : 2*t≤a) :
    Nat.card (SmallEntryBad r c i j t)*a ≤ 4*t*d^3*Nat.card (Tables r c) := by
  have hb := small_entry_count_floor d a t r c i j hm hn hr hc ht
  have hq := floor_donor_lower d a hd ha
  have hb' := Nat.mul_le_mul_left (4*d) hb
  have hq' := Nat.mul_le_mul_left (Nat.card (SmallEntryBad r c i j t)) hq
  have hmn : m*n≤d*d := Nat.mul_le_mul hm hn
  have hc' := Nat.mul_le_mul_left (4*d*t*Nat.card (Tables r c)) hmn
  nlinarith only [hb',hq',hc']

 

theorem small_entry_probability (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (i : Fin m) (j : Fin n) (hd : 1≤d) (hm : m≤d) (hn : n≤d)
    (ha : 4*d≤a) (hr : a≤r i) (hc : a≤c j) (ht : 2*t≤a) :
    (Nat.card (SmallEntryBad r c i j t):ℝ)/(Nat.card (Tables r c):ℝ) ≤
      4*(t:ℝ)*(d:ℝ)^3/(a:ℝ) := by
  have ha' : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  by_cases hp : Nat.card (Tables r c)=0
  · simp [hp]
    positivity
  · have hp' : (0:ℝ)<(Nat.card (Tables r c):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
    apply (div_le_div_iff₀ hp' ha').mpr
    exact_mod_cast small_entry_count d a t r c i j hd hm hn ha hr hc ht

end Contingency

end

end OAI
