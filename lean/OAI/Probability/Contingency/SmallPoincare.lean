import Mathlib
import OAI.Probability.Contingency.CompletionTranslation

namespace OAI

/-! Small Poincare. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n a b : ℕ} (d C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // d^20≤r i}) (ec : Fin b ≃ {j // d^20≤c j})
    (i₀ : Fin a) (j₀ : Fin b)
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 14≤d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n≤d)
    [Nonempty (GraphState (d^20) r c)]

theorem smallDim_one (d : ℕ) (hd : 14≤d) : 1≤d := by omega

local notation "A" => smallData (d^20) (d^12) d r c er ec i₀ j₀ hrc (smallDim_one d hd) hmn

include hm hn in
theorem small_poincare (hC2 : 2≤C) (hC : ∀ i,paddedRow (d^20) (d^12) r c i≤C)
    (H : GraphState (d^20) r c → ℝ) :
    (A).chain.variance H ≤ (d:ℝ)^160*(A).chain.energy H := by
  have hd' : (1:ℝ)≤d := by exact_mod_cast (smallDim_one d hd)
  have hd0 : (0:ℝ)<d := by linarith
  have hU : 2≤d^20 := by
    calc
      2 ≤ 14^20 := by norm_num
      _ ≤ d^20 := Nat.pow_le_pow_left hd _
  have hv := graph_poincare (d^20) (d^12) C d r c hU hC2 (by omega) hmn hrc hC
    (extendGraph (d^20) r c H)
  have he := graphEnergy_le_accepted (d^20) C d r c er ec i₀ j₀ hrc hd hm hn hmn hC H
  let S : ℝ := ∑ X,∑ Y,edgeCount (d^20) (d^12) r c er ec i₀ j₀ X Y*(H X-H Y)^2
  have hs : 0≤S := Finset.sum_nonneg (fun X _ => Finset.sum_nonneg (fun Y _ =>
    mul_nonneg (edgeCount_nonneg (d^20) (d^12) r c er ec i₀ j₀ X Y) (sq_nonneg _)))
  have hvar : (A).chain.variance H=graphVariance (d^20) (d^12) r c (extendGraph (d^20) r c H)/(A).total := by
    rw [AcceptedData.variance_formula]
    congr 1
    unfold graphVariance
    have hh : extendGraph (d^20) r c H ∘ graphUnderlying (d^20) r c=H := by
      funext X; exact extendGraph_apply (d^20) r c H X
    rw [hh]; rfl
  have hEn : (A).chain.energy H=(proposalRate (32*d^2)/(A).total)*S/2 := by
    rw [AcceptedData.energy_formula]; rfl
  have hq := (smallProposal_bounds d (by omega)).1
  have hrate : S/(A).total ≤128*(d:ℝ)^2*(A).chain.energy H := by
    rw [hEn]
    have hsum := mul_le_mul_of_nonneg_right hq hs
    apply (div_le_iff₀ (A).total_pos).mpr
    field_simp [(A).total_pos.ne']
    have hh : S≤64*(d:ℝ)^2*(proposalRate (32*d^2)*S) := by
      have hh := hsum
      rw [one_div_mul_eq_div,div_le_iff₀ (by positivity : 0<64*(d:ℝ)^2)] at hh
      nlinarith only [hh]
    nlinarith only [hh]
  have hpow : 770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6*2=1540*(d:ℝ)^124 := by
    push_cast
    rw [← pow_mul]
    ring
  have hvarS : (A).chain.variance H ≤1540*(d:ℝ)^124*(S/(A).total) := by
    rw [hvar]
    apply (div_le_iff₀ (A).total_pos).mpr
    have hh := hv.trans (mul_le_mul_of_nonneg_left he (by positivity))
    change graphVariance (d^20) (d^12) r c (extendGraph (d^20) r c H) ≤ _ at hh
    calc
      _ ≤ 770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6*(2*S) := hh
      _ = (1540*(d:ℝ)^124)*S := by rw [← mul_assoc,hpow]
      _ = _ := by field_simp [(A).total_pos.ne']
  have hconst : 197120*(d:ℝ)^126≤(d:ℝ)^160 := by
    have hh : (197120:ℝ)≤(d:ℝ)^34 := by
      calc
        _ ≤ (14:ℝ)^34 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hd) _
    have hh' := mul_le_mul_of_nonneg_right hh (pow_nonneg hd0.le 126)
    calc
      _ ≤ (d:ℝ)^34*(d:ℝ)^126 := hh'
      _ = _ := by rw [← pow_add]
  calc
    _ ≤ 1540*(d:ℝ)^124*(S/(A).total) := hvarS
    _ ≤ 1540*(d:ℝ)^124*(128*(d:ℝ)^2*(A).chain.energy H) := mul_le_mul_of_nonneg_left hrate (by positivity)
    _ = (197120*(d:ℝ)^126)*(A).chain.energy H := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (by rw [hEn]; have hp : 0 ≤ proposalRate (32*d^2) := le_trans (by positivity) hq; exact div_nonneg (mul_nonneg (div_nonneg hp (A).total_pos.le) hs) (by norm_num))

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def smallPart (Z : Tables r c) (w : Cell m n) : ℤ :=
  if IsSmall U r c w then Z.val w.1 w.2 else 0

theorem table_row_bound (Z : Tables r c) (i : Fin m) (j : Fin n) : Z.val i j≤r i := by
  rw [← Z.property.1 i]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (Z.val i j)) (Finset.mem_univ j)

theorem table_col_bound (Z : Tables r c) (i : Fin m) (j : Fin n) : Z.val i j≤c j := by
  rw [← Z.property.2 j]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (Z.val i j)) (Finset.mem_univ i)

theorem smallPart_bounds (Z : Tables r c) (w : Cell m n) :
    0≤ smallPart U r c Z w ∧ smallPart U r c Z w≤U := by
  unfold smallPart
  split_ifs with h
  · constructor
    · positivity
    · have hr := table_row_bound r c Z w.1 w.2
      have hc := table_col_bound r c Z w.1 w.2
      simp only [IsSmall,IsLarge,not_and_or,not_le] at h
      rcases h with h | h <;> exact_mod_cast (by omega : Z.val w.1 w.2≤U)
  · constructor <;> positivity

theorem smallPart_row (Z : Tables r c) (i : Fin m) :
    rowSum (smallPart U r c Z) i≤r i ∧
    ((∀ j,¬IsLarge U r c (i,j)) → rowSum (smallPart U r c Z) i=r i) := by
  have he : (∑ j,(Z.val i j:ℤ))=r i := by exact_mod_cast Z.property.1 i
  constructor
  · rw [← he]
    apply Finset.sum_le_sum; intro j _
    dsimp [smallPart]
    split_ifs
    · rfl
    · positivity
  · intro h
    simpa only [rowSum,smallPart,show ∀ j,IsSmall U r c (i,j) from h,ite_true] using he

theorem smallPart_col (Z : Tables r c) (j : Fin n) :
    colSum (smallPart U r c Z) j≤c j ∧
    ((∀ i,¬IsLarge U r c (i,j)) → colSum (smallPart U r c Z) j=c j) := by
  have he : (∑ i,(Z.val i j:ℤ))=c j := by exact_mod_cast Z.property.2 j
  constructor
  · rw [← he]
    apply Finset.sum_le_sum; intro i _
    dsimp [smallPart]
    split_ifs
    · rfl
    · positivity
  · intro h
    simpa only [colSum,smallPart,show ∀ i,IsSmall U r c (i,j) from h,ite_true] using he

 

def initialTransversal (Z : Tables r c) : TransverseState U r c := by
  refine ⟨⟨smallPart U r c Z,smallPart U r c Z⟩,?_,rfl⟩
  refine ⟨?_,?_,smallPart_row U r c Z,smallPart_col U r c Z⟩
  · intro w
    exact ⟨(smallPart_bounds U r c Z w).1,(smallPart_bounds U r c Z w).2,smallPart_bounds U r c Z w⟩
  · intro w hw
    simp [smallPart,IsSmall,hw]

theorem transverse_nonempty (hrc : (∑ i,r i)=∑ j,c j) : Nonempty (TransverseState U r c) := by
  obtain ⟨Z⟩ := tables_nonempty r c hrc
  exact ⟨initialTransversal U r c Z⟩

theorem graph_nonempty (hrc : (∑ i,r i)=∑ j,c j) : Nonempty (GraphState U r c) := by
  obtain ⟨X⟩ := transverse_nonempty U r c hrc
  exact ⟨Sum.inl X⟩

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def transverseMass : ℕ := ∑ X : TransverseState U r c,weight U L r c X.val
def graphMass : ℕ := ∑ X : GraphState U r c,weight U L r c (graphUnderlying U r c X)

theorem transverseMass_pos (hrc : (∑ i,r i)=∑ j,c j) : 0<transverseMass U L r c := by
  let := transverse_nonempty U r c hrc
  apply Finset.sum_pos
  · intro X _
    exact graph_weight_pos U L r c (Sum.inl X) hrc
  · exact Finset.univ_nonempty

def taggedState (X : DefectiveState U r c) : (Cell m n × Cell m n) × TransverseState U r c :=
  (defectPair U r c X,repairedState U r c X)

theorem taggedState_injective : Function.Injective (taggedState U r c) := by
  intro X Y h
  apply taggedRepair_injective U r c
  apply Prod.ext
  · exact congrArg (fun p : (Cell m n × Cell m n) × TransverseState U r c => p.1) h
  · exact congrArg (fun p : (Cell m n × Cell m n) × TransverseState U r c => transverseProfile U r c p.2) h

theorem defectMass_le (hmn : m*n≤d) :
    (∑ X : DefectiveState U r c,weight U L r c X.val)≤d^2*transverseMass U L r c := by
  classical
  calc
    _ ≤ ∑ X : DefectiveState U r c,weight U L r c (repairedState U r c X).val := by
      apply Finset.sum_le_sum; intro X _
      exact weight_repair_le U L r c _ _ X.val (defectPair_spec U r c X)
    _ = ∑ pp∈Finset.univ.image (taggedState U r c),weight U L r c pp.2.val := by
      rw [Finset.sum_image (fun X _ Y _ h => taggedState_injective U r c h)]
      rfl
    _ ≤ ∑ pp : (Cell m n × Cell m n) × TransverseState U r c,weight U L r c pp.2.val :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = (m*n)^2*transverseMass U L r c := by
      simp [Fintype.sum_prod_type,transverseMass,Cell,pow_two,Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hmn 2)

theorem graphMass_bounds (hrc : (∑ i,r i)=∑ j,c j) (hmn : m*n≤d) :
    0<transverseMass U L r c ∧ transverseMass U L r c≤graphMass U L r c ∧
      graphMass U L r c≤(1+d^2)*transverseMass U L r c := by
  have he : graphMass U L r c=transverseMass U L r c+
      ∑ X : DefectiveState U r c,weight U L r c X.val := by
    unfold graphMass transverseMass
    rw [Fintype.sum_sum_type]
    rfl
  have hd := defectMass_le U L d r c hmn
  rw [he]
  refine ⟨transverseMass_pos U L r c hrc,by omega,?_⟩
  rw [Nat.add_mul,Nat.one_mul]
  exact Nat.add_le_add_left hd _

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

abbrev Joint := Σ X : GraphState U r c, Completion U L r c (graphUnderlying U r c X)

instance : Fintype (Joint U L r c) := by
  letI (X : GraphState U r c) : Fintype (Completion U L r c (graphUnderlying U r c X)) := Fintype.ofFinite _
  exact inferInstance

theorem joint_card : Nat.card (Joint U L r c)=graphMass U L r c := by
  let (X : GraphState U r c) : Fintype (Completion U L r c (graphUnderlying U r c X)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  unfold graphMass
  apply Finset.sum_congr rfl
  intro X _
  rw [weight,ite_eq_left (graph_feasible U r c X),Nat.card_eq_fintype_card]

def jointCoordinates (P : Joint U L r c) : Coordinate m n → ℤ :=
  fullCoordinates U C r c (graphUnderlying U r c P.1) P.2.val

theorem jointCoordinates_injective : Function.Injective (jointCoordinates U L C r c) := by
  intro P Q h
  have hsmall (w : Cell m n) (hw : IsSmall U r c w) :
      (graphUnderlying U r c P.1).x w=(graphUnderlying U r c Q.1).x w ∧
      (graphUnderlying U r c P.1).q w=(graphUnderlying U r c Q.1).q w := by
    have hx := congrFun h (true,w)
    have hq := congrFun h (false,w)
    simp only [jointCoordinates,fullCoordinates,P.2.property.2.1 w hw,Q.2.property.2.1 w hw,
      Bool.false_eq_true,ite_false,ite_true,add_zero] at hx hq
    exact ⟨hx,by omega⟩
  have hX : graphUnderlying U r c P.1=graphUnderlying U r c Q.1 := by
    apply State.ext
    · funext w
      by_cases hw : IsSmall U r c w
      · exact (hsmall w hw).1
      · rw [(graph_feasible U r c P.1).2.1 w (Classical.not_not.mp hw) |>.1,
          (graph_feasible U r c Q.1).2.1 w (Classical.not_not.mp hw) |>.1]
    · funext w
      by_cases hw : IsSmall U r c w
      · exact (hsmall w hw).2
      · rw [(graph_feasible U r c P.1).2.1 w (Classical.not_not.mp hw) |>.2,
          (graph_feasible U r c Q.1).2.1 w (Classical.not_not.mp hw) |>.2]
  have hA : P.2.val=Q.2.val := by
    funext w
    have hx := congrFun h (true,w)
    simp only [jointCoordinates,fullCoordinates,ite_true,hX] at hx
    omega
  have he := graphUnderlying_injective U r c hX
  cases P with | mk X A =>
    cases Q with | mk Y B =>
      dsimp only at he
      subst Y
      congr 1
      exact Subtype.ext hA

def jointCode (hU : U≤C) (hC : ∀ i,paddedRow U L r c i≤C)
    (P : Joint U L r c) : Coordinate m n → Fin (C+1) := fun w =>
  ⟨(jointCoordinates U L C r c P w).toNat,by
    have hh := fullCoordinates_inBox U L C r c _ (graph_feasible U r c P.1) P.2 hC w
    have hc : capacity U C r c w.2≤C := by unfold capacity; split_ifs <;> omega
    change 0≤jointCoordinates U L C r c P w ∧ jointCoordinates U L C r c P w≤capacity U C r c w.2 at hh
    omega⟩

theorem jointCode_injective (hU : U≤C) (hC : ∀ i,paddedRow U L r c i≤C) :
    Function.Injective (jointCode U L C r c hU hC) := by
  intro P Q h
  apply jointCoordinates_injective U L C r c
  funext w
  have hh := congrArg (fun f : Coordinate m n → Fin (C+1) => (f w).val) h
  have hP := (fullCoordinates_inBox U L C r c _ (graph_feasible U r c P.1) P.2 hC w).1
  have hQ := (fullCoordinates_inBox U L C r c _ (graph_feasible U r c Q.1) Q.2 hC w).1
  change (jointCoordinates U L C r c P w).toNat=(jointCoordinates U L C r c Q w).toNat at hh
  change 0≤jointCoordinates U L C r c P w at hP
  change 0≤jointCoordinates U L C r c Q w at hQ
  omega

theorem graphMass_upper (d : ℕ) (hmn : m*n≤d)
    (hU : U≤C) (hC : ∀ i,paddedRow U L r c i≤C) : graphMass U L r c≤(C+1)^(2*d) := by
  rw [← joint_card U L r c]
  calc
    _ ≤ Nat.card (Coordinate m n → Fin (C+1)) :=
      Nat.card_le_card_of_injective _ (jointCode_injective U L C r c hU hC)
    _ = (C+1)^(2*(m*n)) := by simp [Coordinate,Cell]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hmn)

theorem stationary_lower (d : ℕ) (hrc : (∑ i,r i)=∑ j,c j) (hmn : m*n≤d)
    (hU : U≤C) (hC : ∀ i,paddedRow U L r c i≤C) (X : GraphState U r c) :
    1/(C+1:ℝ)^(2*d) ≤ (weight U L r c (graphUnderlying U r c X):ℝ)/graphMass U L r c := by
  have hM := graphMass_upper U L C r c d hmn hU hC
  have hpos := graphMass_bounds U L d r c hrc hmn
  have hMp : (0:ℝ)<graphMass U L r c := by exact_mod_cast lt_of_lt_of_le hpos.1 hpos.2.1
  have hw : (1:ℝ)≤weight U L r c (graphUnderlying U r c X) := by exact_mod_cast graph_weight_pos U L r c X hrc
  apply (div_le_div_iff₀ (by positivity) hMp).mpr
  have hM' : (graphMass U L r c:ℝ)≤(C+1:ℝ)^(2*d) := by exact_mod_cast hM
  nlinarith [mul_le_mul_of_nonneg_right hw (show 0≤(C+1:ℝ)^(2*d) by positivity)]

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n a b : ℕ} (d C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // d^20≤r i}) (ec : Fin b ≃ {j // d^20≤c j})
    (i₀ : Fin a) (j₀ : Fin b)
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 14≤d) (hm : m≤d) (hn : n≤d) (hmn : m*n≤d)
    [Nonempty (GraphState (d^20) r c)]
local notation "A" => smallData (d^20) (d^12) d r c er ec i₀ j₀ hrc (smallDim_one d hd) hmn

omit [Nonempty (GraphState (d^20) r c)] in
theorem small_total : (A).total=(graphMass (d^20) (d^12) r c:ℝ) := by
  simp [AcceptedData.total,smallData,graphMass,Nat.cast_sum]

include hm hn in
 
theorem small_mixing (hC2 : 2≤C) (hU : d^20≤C)
    (hC : ∀ i,paddedRow (d^20) (d^12) r c i≤C) (t : ℕ) (X : GraphState (d^20) r c) :
    ((A).chain.walk X t).tv (A).chain.invariant≤
      (C+1:ℝ)^(2*d)*Real.exp (-(t:ℝ)/(d:ℝ)^160) := by
  rw [Chain.walk_tv]
  have hk : (1:ℝ)≤(d:ℝ)^160 := one_le_pow₀ (by exact_mod_cast smallDim_one d hd)
  have hvar := small_poincare d C r c er ec i₀ j₀ hrc hd hm hn hmn hC2 hC
  have hmin (Y : GraphState (d^20) r c) : 1/(C+1:ℝ)^(2*d)≤(A).chain.π Y := by
    change _≤(weight (d^20) (d^12) r c (graphUnderlying (d^20) r c Y):ℝ)/(A).total
    rw [small_total d r c er ec i₀ j₀ hrc hd hmn]
    exact stationary_lower (d^20) (d^12) C r c d hrc hmn hU hC Y
  have hh := (A).chain.mixing_bound_min ((d:ℝ)^160) hk hvar
    (1/(C+1:ℝ)^(2*d)) (by positivity) hmin t X
  simpa only [one_div,inv_inv] using hh

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n a c' : ℕ} (d b k C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin (a+1) ≃ {i // d^20 ≤ r i}) (ec : Fin (c'+1) ≃ {j // d^20 ≤ c j})
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 14 ≤ d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n ≤ d)
    (hC : ∀ i,paddedRow (d^20) (d^12) r c i ≤ C) (hCb : C ≤ 2^b)

local notation "Comp" => fun X : GraphState (d^20) r c => Completion (d^20) (d^12) r c (graphUnderlying (d^20) r c X)
local instance (X : GraphState (d^20) r c) : Fintype (Comp X) := Fintype.ofFinite _
attribute [local instance] Dense.BinProblem.tableFintype

include hrc in
lemma comp_nonempty (X : GraphState (d^20) r c) : Nonempty (Comp X) := completion_nonempty _ _ _ _ _ hrc

include hC hCb in
lemma blockRow_upper (X : GraphState (d^20) r c) (i : Fin (a+1)) :
    blockRow (d^20) (d^12) r c er X i ≤ 2^b := by
  have hf := graph_feasible (d^20) r c X
  have hn : 0 ≤ rowSum (graphUnderlying (d^20) r c X).x (er i).val :=
    Finset.sum_nonneg (fun j _ => (hf.1 ((er i).val,j)).1)
  have hh := hC (er i).val
  have hb' : (C:ℤ) ≤ 2^b := by exact_mod_cast hCb
  apply Int.ofNat_le.mp
  change (rowNat (d^20) (d^12) r c _ _:ℤ) ≤ ((2^b:ℕ):ℤ)
  rw [rowNat_cast _ _ _ _ _ hf]
  unfold paddedRow at hh
  unfold residualRow
  push_cast
  omega

abbrev blockDraw (X : GraphState (d^20) r c) (fallback : Comp X) : DyadicLaw (Comp X) := by
  classical
  let e := blockEquiv (d^20) (d^12) r c er ec X
  let ha := (block_dimensions (d^20) r c er ec).1.trans hm
  let hc := (block_dimensions (d^20) r c er ec).2.trans hn
  let hac := (Nat.mul_le_mul (block_dimensions (d^20) r c er ec).1
    (block_dimensions (d^20) r c er ec).2).trans hmn
  let hR := fun i => block_row_lower (d^20) (d^12) r c er ec X i 0
  let hP := fun j => block_col_lower (d^20) (d^12) r c er ec X 0 j
  exact (Dense.literalDraw d _ _ hd ha hc hac hR hP (block_totals _ _ _ _ er ec X hrc) b k
    (blockRow_upper d b C r c er hC hCb X) (e fallback)).map e.symm

theorem blockDraw_bits (X : GraphState (d^20) r c) (fallback : Comp X) :
    (blockDraw d b k C r c er ec hrc hd hm hn hmn hC hCb X fallback).bits=Schedule.RD d b k := by
  classical
  simp only [blockDraw,DyadicLaw.map_bits,Dense.literalDraw_bits]

theorem blockDraw_tv (hk : 1 ≤ k) (X : GraphState (d^20) r c) (fallback : Comp X) :
    letI := completion_nonempty (d^20) (d^12) r c X hrc
    (blockDraw d b k C r c er ec hrc hd hm hn hmn hC hCb X fallback).toLaw.tv (Law.uniform (Comp X)) ≤
      (2:ℝ)^(-(Schedule.h d b k:ℤ)) := by
  classical
  let := completion_nonempty (d^20) (d^12) r c X hrc
  let e := blockEquiv (d^20) (d^12) r c er ec X
  let := tables_nonempty _ _ (block_totals (d^20) (d^12) r c er ec X hrc)
  unfold blockDraw
  rw [DyadicLaw.toLaw_map,← Law.uniform_map_equiv e.symm]
  exact (Law.tv_map e.symm _ _).trans (Dense.literalDraw_tv _ _ _ _ _ _ _ _ _ _ b k hk _ _)

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
namespace Law

theorem uniform_event {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) [DecidablePred p] :
    ((uniform α).map (fun x => decide (p x))).mass true=(Nat.card {x // p x}:ℝ)/Nat.card α := by
  classical
  simp only [map,bind,pure,uniform,decide_eq_true_eq,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,← Nat.card_eq_fintype_card]
  have he : (Finset.univ.filter p).card=Nat.card {x // p x} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [he]
  ring

end Law
namespace PaddedGraph
open CompletionTranslation FiniteChain
variable {m n a c' : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U ≤ r i}) (ec : Fin c' ≃ {j // U ≤ c j}) (i₀ : Fin a) (j₀ : Fin c')
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 1 ≤ d) (hmn : m*n ≤ d)

local notation "Comp" => fun X : GraphState U r c => Completion U L r c (graphUnderlying U r c X)
local instance (X : GraphState U r c) : Fintype (Comp X) := Fintype.ofFinite _
attribute [local instance] Dense.BinProblem.tableFintype

include hd hmn in
lemma proposal_degree (X : GraphState U r c) :
    (Finset.univ.filter (GraphAdj U r c X)).card ≤ 2^(Nat.clog 2 (32*d^2)) := by
  have hh := graph_degree U r c d hmn X
  have hp : 1 ≤ d^2 := one_le_pow₀ hd
  exact (hh.trans (by omega)).trans (Nat.le_pow_clog (by norm_num) _)

abbrev smallProposal (X : GraphState U r c) : DyadicLaw (GraphState U r c) :=
  DyadicLaw.neighborProposal (GraphAdj U r c) X (Nat.clog 2 (32*d^2))
    (GraphAdj.irrefl U r c X) (proposal_degree U d r c hd hmn X)

def completionTest (X Y : GraphState U r c) (A : Comp X) : Bool :=
  decide (∀ i j,0 ≤ (((blockEquiv U L r c er ec X A).val i j):ℤ)+blockD U L r c er ec i₀ j₀ X Y i j)

def completionKernel (μ : ∀ X,Law (Comp X)) (X : GraphState U r c) : Law (GraphState U r c) :=
  (smallProposal U d r c hd hmn X).toLaw.accept
    (fun Y => (μ X).map (completionTest U L r c er ec i₀ j₀ X Y)) X

def implementedTransition (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X : GraphState U r c) : DyadicLaw (GraphState U r c) := by
  classical
  exact (smallProposal U d r c hd hmn X).bind
    (fun Y => (μ X).map (fun A => if completionTest U L r c er ec i₀ j₀ X Y A then Y else X)) S
    (fun _ => by rw [DyadicLaw.map_bits,hS])

theorem implementedTransition_bits (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X : GraphState U r c) :
    (implementedTransition U L d r c er ec i₀ j₀ hd hmn μ S hS X).bits=Nat.clog 2 (32*d^2)+S := rfl

theorem toLaw_implementedTransition (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X : GraphState U r c) :
    (implementedTransition U L d r c er ec i₀ j₀ hd hmn μ S hS X).toLaw=
      completionKernel U L d r c er ec i₀ j₀ hd hmn (fun X => (μ X).toLaw) X := by
  classical
  simp only [implementedTransition,DyadicLaw.toLaw_bind,DyadicLaw.toLaw_map,
    completionKernel,Law.accept,Law.map_map]

theorem completionKernel_tv (μ ν : ∀ X,Law (Comp X)) (X : GraphState U r c) :
    (completionKernel U L d r c er ec i₀ j₀ hd hmn μ X).tv
      (completionKernel U L d r c er ec i₀ j₀ hd hmn ν X) ≤ (μ X).tv (ν X) := by
  unfold completionKernel Law.accept
  apply Law.tv_bind_right_bound
  intro Y
  exact (Law.tv_map _ _ _).trans (Law.tv_map _ _ _)

abbrev idealCompletion (X : GraphState U r c) : Law (Comp X) :=
  @Law.uniform (Comp X) inferInstance (completion_nonempty U L r c X hrc)

theorem idealCompletion_test (X Y : GraphState U r c) :
    ((idealCompletion U L r c hrc X).map (completionTest U L r c er ec i₀ j₀ X Y)).mass true=
      (acceptCount U L r c er ec i₀ j₀ X Y:ℝ)/weight U L r c (graphUnderlying U r c X) := by
  classical
  let := completion_nonempty U L r c X hrc
  let : Fintype (Tables (blockRow U L r c er X) (blockCol U L r c ec X)) := Fintype.ofFinite _
  let := tables_nonempty _ _ (block_totals U L r c er ec X hrc)
  let e := blockEquiv U L r c er ec X
  let p := fun A : Tables (blockRow U L r c er X) (blockCol U L r c ec X) =>
    ∀ i j,0 ≤ (A.val i j:ℤ)+blockD U L r c er ec i₀ j₀ X Y i j
  have he : completionTest U L r c er ec i₀ j₀ X Y = fun A => decide (p (e A)) := rfl
  rw [he]
  change ((Law.uniform (Comp X)).map (fun A => decide (p (e A)))).mass true=_
  rw [← Law.map_map (Law.uniform (Comp X)) e (fun A => decide (p A)),Law.uniform_map_equiv e,Law.uniform_event]
  rw [block_card U L r c er ec X]
  rfl

variable [Nonempty (GraphState U r c)]
theorem idealCompletion_kernel (X : GraphState U r c) :
    completionKernel U L d r c er ec i₀ j₀ hd hmn (idealCompletion U L r c hrc) X=
      (smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.transition X := by
  classical
  apply Law.ext_offdiag _ _ X
  intro Y hXY
  rw [completionKernel,Law.accept_offdiag _ _ _ _ hXY,
    DyadicLaw.neighborProposal_offdiag _ _ _ _ _ _ hXY,idealCompletion_test]
  simp only [FiniteChain.Chain.transition,AcceptedData.chain,AcceptedData.kernel,ite_eq_right hXY,
    AcceptedData.rate,smallData,edgeCount,proposalRate]
  split_ifs <;> ring

end PaddedGraph
end
end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
open FiniteChain
namespace DyadicLaw
variable {α : Type*} [Fintype α] [DecidableEq α]

 
theorem walk_tv_chain (q : α → DyadicLaw α) (S : ℕ) (hS : ∀ x,(q x).bits=S)
    (C : Chain α) (δ : ℝ) (hq : ∀ x,(q x).toLaw.tv (C.transition x)≤δ) (x₀ : α) (t : ℕ) :
    (walk q S hS x₀ t).toLaw.tv (C.walk x₀ t)≤(t:ℝ)*δ := by
  induction t with
  | zero => simp [walk,toLaw_pure,Chain.walk]
  | succ t ih =>
    rw [walk,toLaw_bind,Chain.walk]
    have hh := Law.tv_bind (walk q S hS x₀ t).toLaw (C.walk x₀ t)
      (fun x => (q x).toLaw) C.transition δ hq
    push_cast
    linarith

end DyadicLaw
namespace PaddedGraph
variable {m n a c' : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U ≤ r i}) (ec : Fin c' ≃ {j // U ≤ c j}) (i₀ : Fin a) (j₀ : Fin c')
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 1 ≤ d) (hmn : m*n ≤ d)
    [Nonempty (GraphState U r c)]
local notation "Comp" => fun X : GraphState U r c => Completion U L r c (graphUnderlying U r c X)
local instance (X : GraphState U r c) : Fintype (Comp X) := Fintype.ofFinite _

abbrev implementedWalk (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X₀ : GraphState U r c) (t : ℕ) : DyadicLaw (GraphState U r c) := by
  classical
  exact DyadicLaw.walk (implementedTransition U L d r c er ec i₀ j₀ hd hmn μ S hS)
    (Nat.clog 2 (32*d^2)+S) (implementedTransition_bits U L d r c er ec i₀ j₀ hd hmn μ S hS) X₀ t

theorem implementedWalk_tv (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (δ : ℝ) (hμ : ∀ X,(μ X).toLaw.tv (idealCompletion U L r c hrc X)≤δ)
    (X₀ : GraphState U r c) (t : ℕ) :
    (implementedWalk U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).toLaw.tv
      ((smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.walk X₀ t)≤(t:ℝ)*δ := by
  classical
  apply DyadicLaw.walk_tv_chain
  intro X
  rw [toLaw_implementedTransition,← idealCompletion_kernel U L d r c er ec i₀ j₀ hrc hd hmn]
  exact (completionKernel_tv U L d r c er ec i₀ j₀ hd hmn _ _ X).trans (hμ X)

end PaddedGraph
end
end Contingency

end

end OAI
