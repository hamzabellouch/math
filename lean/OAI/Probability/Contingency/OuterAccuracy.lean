import Mathlib
import OAI.Probability.Contingency.Unpadding

namespace OAI

/-! Outer Accuracy. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n a c' : ℕ} (d b k C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // d^20 ≤ r i}) (ec : Fin c' ≃ {j // d^20 ≤ c j}) (i₀ : Fin a) (j₀ : Fin c')
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 14 ≤ d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n ≤ d)
    [Nonempty (GraphState (d^20) r c)]
local notation "Comp" => fun X : GraphState (d^20) r c => Completion (d^20) (d^12) r c (graphUnderlying (d^20) r c X)
local instance outerAccuracyDrawCompletionFintype (X : GraphState (d^20) r c) :
    Fintype (Comp X) := Fintype.ofFinite _
local instance outerAccuracyDrawTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

include hd hm hn hmn hrc in
omit [Nonempty (GraphState (d^20) r c)] in
theorem stationary_failure_power (J : ℕ) :
    letI := tables_nonempty r c hrc
    (stationaryTrial r c (d^20) (d^12)).mass none^J≤Real.exp (-((J:ℝ)/(2*(1+(d:ℝ)^2)))) := by
  let := tables_nonempty r c hrc
  have hf := stationary_success_probability d r c hd hm hn hmn hrc
  have hh : (stationaryTrial r c (d^20) (d^12)).mass none≤Real.exp (-(1/(2*(1+(d:ℝ)^2)))) := by
    rw [stationaryTrial_none]
    have he := Real.add_one_le_exp (-(1/(2*(1+(d:ℝ)^2))))
    linarith
  have hp := pow_le_pow_left₀ ((stationaryTrial r c (d^20) (d^12)).nonneg none) hh J
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

def outerDraw (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X₀ : GraphState (d^20) r c) (fallback : Tables r c) : DyadicLaw (Tables r c) := by
  classical
  exact stoppedLaw (implementedTrial (d^20) (d^12) d r c er ec i₀ j₀ (smallDim_one d hd) hmn μ S hS X₀ (Schedule.T d b k)) fallback (Schedule.Jo d k)

omit [Nonempty (GraphState (d^20) r c)] in
theorem outerDraw_bits (μ : ∀ X,DyadicLaw (Comp X)) (hS : ∀ X,(μ X).bits=Schedule.RD d b k)
    (X₀ : GraphState (d^20) r c) (fallback : Tables r c) :
    (outerDraw d b k r c er ec i₀ j₀ hd hmn μ (Schedule.RD d b k) hS X₀ fallback).bits=Schedule.R d b k := by
  classical
  change (implementedTrial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).bits*Schedule.Jo d k=_
  rw [implementedTrial_bits]
  unfold Schedule.R Schedule.RT Schedule.qs
  ring

include hm hn in
theorem outerDraw_tv (hb : d ≤ b) (hk : 1 ≤ k) (hC2 : 2 ≤ C) (hU : d^20 ≤ C)
    (hC : ∀ i,paddedRow (d^20) (d^12) r c i ≤ C) (hCb : C+1 ≤ 2^b)
    (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (hμ : ∀ X,(μ X).toLaw.tv (idealCompletion (d^20) (d^12) r c hrc X) ≤ (2:ℝ)^(-(Schedule.h d b k:ℤ)))
    (X₀ : GraphState (d^20) r c) (fallback : Tables r c) :
    letI := tables_nonempty r c hrc
    (outerDraw d b k r c er ec i₀ j₀ hd hmn μ S hS X₀ fallback).toLaw.tv (Law.uniform (Tables r c))≤(2:ℝ)^(-(k:ℤ)) := by
  classical
  let := tables_nonempty r c hrc
  let p := implementedTrial (d^20) (d^12) d r c er ec i₀ j₀ (smallDim_one d hd) hmn μ S hS X₀ (Schedule.T d b k)
  let s := stationaryTrial r c (d^20) (d^12)
  have ht := implementedTrial_tv (d^20) (d^12) d r c er ec i₀ j₀ (smallDim_one d hd) hmn hrc μ S hS _ hμ X₀ (Schedule.T d b k)
  have hmix := small_mixing d C r c er ec i₀ j₀ hrc hd hm hn hmn hC2 hU hC (Schedule.T d b k) X₀
  have hfirst := Law.first_tv p.toLaw s fallback (Schedule.Jo d k)
  have hideal := Law.first_ideal_tv s fallback (Law.uniform (Tables r c)) (stationaryTrial_uniform r c (d^20) (d^12)) (Schedule.Jo d k)
  have hfail := stationary_failure_power d r c hrc hd hm hn hmn (Schedule.Jo d k)
  have htri := Law.tv_triangle (Law.first p.toLaw fallback (Schedule.Jo d k)) (Law.first s fallback (Schedule.Jo d k)) (Law.uniform (Tables r c))
  have hmul := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (Schedule.Jo d k))
  have hmm := mul_le_mul_of_nonneg_left hmix (Nat.cast_nonneg (Schedule.Jo d k))
  have htotal := Schedule.outer_error_schedule d b k hd hb hk C hCb
  unfold outerDraw
  rw [stoppedLaw_toLaw]
  change (Law.first p.toLaw fallback (Schedule.Jo d k)).tv _ ≤ _
  change _≤_ at hfail
  dsimp only [p,s] at hfirst hideal htri
  dsimp only [p]
  rw [neg_div] at hmm
  nlinarith only [hfirst,hideal,hfail,htri,hmul,hmm,htotal]

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n a c' : ℕ} (d b k C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin (a+1) ≃ {i // d^20 ≤ r i}) (ec : Fin (c'+1) ≃ {j // d^20 ≤ c j})
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 14 ≤ d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n ≤ d)
    [Nonempty (GraphState (d^20) r c)]
local notation "Comp" => fun X : GraphState (d^20) r c => Completion (d^20) (d^12) r c (graphUnderlying (d^20) r c X)
local instance outerAccuracyLiteralCompletionFintype (X : GraphState (d^20) r c) :
    Fintype (Comp X) := Fintype.ofFinite _
local instance outerAccuracyLiteralTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

 

def literalOuter (hC : ∀ i,paddedRow (d^20) (d^12) r c i ≤ C) (hCb : C ≤ 2^b)
    (fallbacks : ∀ X,Comp X) (X₀ : GraphState (d^20) r c) (fallback : Tables r c) : DyadicLaw (Tables r c) :=
  outerDraw d b k r c er ec 0 0 hd hmn
    (fun X => blockDraw d b k C r c er ec hrc hd hm hn hmn hC hCb X (fallbacks X))
    (Schedule.RD d b k)
    (fun X => blockDraw_bits d b k C r c er ec hrc hd hm hn hmn hC hCb X (fallbacks X)) X₀ fallback

omit [Nonempty (GraphState (d^20) r c)] in
theorem literalOuter_bits (hC : ∀ i,paddedRow (d^20) (d^12) r c i ≤ C) (hCb : C ≤ 2^b)
    (fallbacks : ∀ X,Comp X) (X₀ : GraphState (d^20) r c) (fallback : Tables r c) :
    (literalOuter d b k C r c er ec hrc hd hm hn hmn hC hCb fallbacks X₀ fallback).bits = Schedule.R d b k := by
  apply outerDraw_bits

theorem literalOuter_tv (hb : d ≤ b) (hk : 1 ≤ k) (hC2 : 2 ≤ C) (hU : d^20 ≤ C)
    (hC : ∀ i,paddedRow (d^20) (d^12) r c i ≤ C) (hCb : C+1 ≤ 2^b)
    (fallbacks : ∀ X,Comp X) (X₀ : GraphState (d^20) r c) (fallback : Tables r c) :
    letI := tables_nonempty r c hrc
    (literalOuter d b k C r c er ec hrc hd hm hn hmn hC (by omega) fallbacks X₀ fallback).toLaw.tv
      (Law.uniform (Tables r c)) ≤ (2:ℝ)^(-(k:ℤ)) := by
  apply outerDraw_tv d b k C r c er ec 0 0 hrc hd hm hn hmn hb hk hC2 hU hC hCb
  intro X
  exact blockDraw_tv d b k C r c er ec hrc hd hm hn hmn hC (by omega) hk X (fallbacks X)

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n : ℕ} (U L d C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

 
def EmptyBlock : Prop := ∀ w : Cell m n, IsSmall U r c w

theorem empty_completion_subsingleton (h : EmptyBlock U r c) (X : State m n) :
    Subsingleton (Completion U L r c X) := by
  constructor
  intro A B
  apply Subtype.ext
  funext w
  rw [A.property.2.1 w (h w),B.property.2.1 w (h w)]

theorem empty_weight (h : EmptyBlock U r c) (hrc : (∑ i,r i)=∑ j,c j)
    (X : GraphState U r c) : weight U L r c (graphUnderlying U r c X)=1 := by
  let := empty_completion_subsingleton U L r c h (graphUnderlying U r c X)
  let := completion_nonempty U L r c X hrc
  rw [weight,ite_eq_left (graph_feasible U r c X)]
  exact Nat.card_unique

def emptyCount (X Y : GraphState U r c) : ℝ := if GraphAdj U r c X Y then 1 else 0

theorem emptyCount_nonneg (X Y : GraphState U r c) : 0 ≤ emptyCount U r c X Y := by
  unfold emptyCount; split_ifs <;> norm_num

def emptyData (h : EmptyBlock U r c) (hrc : (∑ i,r i)=∑ j,c j)
    (hd : 1 ≤ d) (hmn : m*n ≤ d) : AcceptedData (GraphState U r c) where
  f X := weight U L r c (graphUnderlying U r c X)
  fpos X := by exact_mod_cast graph_weight_pos U L r c X hrc
  count := emptyCount U r c
  nonneg := emptyCount_nonneg U r c
  symmetric X Y := by
    unfold emptyCount
    have he : GraphAdj U r c X Y ↔ GraphAdj U r c Y X := ⟨GraphAdj.symm U r c,GraphAdj.symm U r c⟩
    simp only [he]
  diagonal X := by simp [emptyCount,GraphAdj.irrefl]
  q := proposalRate (32*d^2)
  qpos := by unfold proposalRate; positivity
  hold X := by
    rw [empty_weight U L r c h hrc X]
    have hs : (∑ Y,emptyCount U r c X Y) ≤ 5*(d:ℝ)^2+1 := by
      simp only [emptyCount,← Finset.sum_filter]
      simpa using (show ((Finset.univ.filter (GraphAdj U r c X)).card:ℝ) ≤ 5*(d:ℝ)^2+1 by
        exact_mod_cast graph_degree U r c d hmn X)
    have hp : 0 ≤ proposalRate (32*d^2) := by unfold proposalRate; positivity
    exact (mul_le_mul_of_nonneg_left hs hp).trans (by simpa using proposal_hold d hd)

theorem graphEnergy_le_empty (h : EmptyBlock U r c) (hrc : (∑ i,r i)=∑ j,c j)
    (hC : ∀ i,paddedRow U L r c i ≤ C) (H : GraphState U r c → ℝ) :
    graphEnergy U L C r c (extendGraph U r c H) ≤
      2*(∑ X,∑ Y,emptyCount U r c X Y*(H X-H Y)^2) := by
  apply (graphEnergy_le_ordered U L C r c hrc hC H).trans
  simp only [empty_weight U L r c h hrc,Nat.cast_one,min_self,one_mul]
  have he : (∑ X,∑ Y,if GraphAdj U r c X Y then (H X-H Y)^2 else 0) =
      ∑ X,∑ Y,emptyCount U r c X Y*(H X-H Y)^2 := by
    simp [emptyCount,ite_mul]
  rw [he]
  have hn : 0 ≤ ∑ X,∑ Y,emptyCount U r c X Y*(H X-H Y)^2 := Finset.sum_nonneg
    (fun X _ => Finset.sum_nonneg (fun Y _ => mul_nonneg (emptyCount_nonneg U r c X Y) (sq_nonneg _)))
  linarith

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n : ℕ} (d C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hempty : EmptyBlock (d^20) r c)
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 14≤d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n≤d)
    [Nonempty (GraphState (d^20) r c)]

local notation "A" => emptyData (d^20) (d^12) d r c hempty hrc (smallDim_one d hd) hmn

theorem empty_poincare (hC2 : 2≤C) (hC : ∀ i,paddedRow (d^20) (d^12) r c i≤C)
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
  have he := graphEnergy_le_empty (d^20) (d^12) C r c hempty hrc hC H
  let S : ℝ := ∑ X,∑ Y,emptyCount (d^20) r c X Y*(H X-H Y)^2
  have hs : 0≤S := Finset.sum_nonneg (fun X _ => Finset.sum_nonneg (fun Y _ =>
    mul_nonneg (emptyCount_nonneg (d^20) r c X Y) (sq_nonneg _)))
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
open FiniteChain
variable {m n : ℕ} (d C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hempty : EmptyBlock (d^20) r c)
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 14≤d) (hm : m≤d) (hn : n≤d) (hmn : m*n≤d)
    [Nonempty (GraphState (d^20) r c)]
local notation "A" => emptyData (d^20) (d^12) d r c hempty hrc (smallDim_one d hd) hmn

omit [Nonempty (GraphState (d^20) r c)] in
theorem empty_total : (A).total=(graphMass (d^20) (d^12) r c:ℝ) := by
  simp [AcceptedData.total,emptyData,graphMass,Nat.cast_sum]

 
theorem empty_mixing (hC2 : 2≤C) (hU : d^20≤C)
    (hC : ∀ i,paddedRow (d^20) (d^12) r c i≤C) (t : ℕ) (X : GraphState (d^20) r c) :
    ((A).chain.walk X t).tv (A).chain.invariant≤
      (C+1:ℝ)^(2*d)*Real.exp (-(t:ℝ)/(d:ℝ)^160) := by
  rw [Chain.walk_tv]
  have hk : (1:ℝ)≤(d:ℝ)^160 := one_le_pow₀ (by exact_mod_cast smallDim_one d hd)
  have hvar := empty_poincare d C r c hempty hrc hd hmn hC2 hC
  have hmin (Y : GraphState (d^20) r c) : 1/(C+1:ℝ)^(2*d)≤(A).chain.π Y := by
    change _≤(weight (d^20) (d^12) r c (graphUnderlying (d^20) r c Y):ℝ)/(A).total
    rw [empty_total d r c hempty hrc hd hmn]
    exact stationary_lower (d^20) (d^12) C r c d hrc hmn hU hC Y
  have hh := (A).chain.mixing_bound_min ((d:ℝ)^160) hk hvar
    (1/(C+1:ℝ)^(2*d)) (by positivity) hmin t X
  simpa only [one_div,inv_inv] using hh

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
namespace DyadicLaw
open FiniteChain
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem walk_toLaw_chain (q : α → DyadicLaw α) (S : ℕ) (hS : ∀ x,(q x).bits=S)
    (C : Chain α) (hq : ∀ x,(q x).toLaw=C.transition x) (x₀ : α) (t : ℕ) :
    (walk q S hS x₀ t).toLaw=C.walk x₀ t := by
  induction t with
  | zero => exact toLaw_pure _ _
  | succ t ih =>
    rw [walk,toLaw_bind,Chain.walk,ih]
    congr 1
    funext x
    exact hq x
end DyadicLaw
end
end Contingency
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hempty : EmptyBlock U r c) (hrc : (∑ i,r i)=∑ j,c j)
    (hd : 1 ≤ d) (hmn : m*n ≤ d)
local notation "Comp" => fun X : GraphState U r c => Completion U L r c (graphUnderlying U r c X)
local instance outerAccuracyEmptyTrialCompletionFintype (X : GraphState U r c) :
    Fintype (Comp X) := Fintype.ofFinite _
local instance (X : GraphState U r c) : DecidableEq (Comp X) := Classical.decEq _
local instance outerAccuracyEmptyTrialTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

theorem smallProposal_bits (X : GraphState U r c) :
    (smallProposal U d r c hd hmn X).bits=Nat.clog 2 (32*d^2) := rfl

theorem proposal_pad_bound (S : ℕ) (X : GraphState U r c) :
    (smallProposal U d r c hd hmn X).bits ≤ Nat.clog 2 (32*d^2)+S := by
  rw [smallProposal_bits]
  omega

theorem completion_pure_bits (S : ℕ) (X : GraphState U r c) (A : Comp X) :
    (DyadicLaw.pure A S).bits=S := rfl

def emptyTransition (S : ℕ) (X : GraphState U r c) : DyadicLaw (GraphState U r c) :=
  (smallProposal U d r c hd hmn X).pad (Nat.clog 2 (32*d^2)+S) (proposal_pad_bound U d r c hd hmn S X)

theorem emptyTransition_bits (S : ℕ) (X : GraphState U r c) :
    (emptyTransition U d r c hd hmn S X).bits=Nat.clog 2 (32*d^2)+S := rfl

variable [Nonempty (GraphState U r c)]

theorem emptyTransition_toLaw (S : ℕ) (X : GraphState U r c) :
    (emptyTransition U d r c hd hmn S X).toLaw = (emptyData U L d r c hempty hrc hd hmn).chain.transition X := by
  classical
  rw [emptyTransition,DyadicLaw.toLaw_pad]
  apply Law.ext_offdiag _ _ X
  intro Y hXY
  rw [DyadicLaw.neighborProposal_offdiag]
  simp only [Chain.transition,AcceptedData.chain_P,AcceptedData.kernel,ite_eq_right hXY]
  change _=(proposalRate (32*d^2)*emptyCount U r c X Y)/weight U L r c (graphUnderlying U r c X)
  rw [empty_weight U L r c hempty hrc X]
  simp only [Nat.cast_one,div_one,emptyCount,proposalRate]
  ring
  exact hXY

def emptyWalk (S : ℕ) (X₀ : GraphState U r c) (t : ℕ) : DyadicLaw (GraphState U r c) := by
  classical
  exact DyadicLaw.walk (emptyTransition U d r c hd hmn S) (Nat.clog 2 (32*d^2)+S) (emptyTransition_bits U d r c hd hmn S) X₀ t

theorem emptyWalk_toLaw (S : ℕ) (X₀ : GraphState U r c) (t : ℕ) :
    (emptyWalk U d r c hd hmn S X₀ t).toLaw=(emptyData U L d r c hempty hrc hd hmn).chain.walk X₀ t := by
  classical
  exact DyadicLaw.walk_toLaw_chain _ _ _ _ (emptyTransition_toLaw U L d r c hempty hrc hd hmn S) X₀ t

theorem empty_invariant_joint :
    letI := tables_nonempty r c hrc
    letI : Nonempty (Joint U L r c) := Nonempty.map (successfulJoint r c U L) inferInstance
    (emptyData U L d r c hempty hrc hd hmn).chain.invariant.sigma
      (idealCompletion U L r c hrc)=Law.uniform (Joint U L r c) := by
  classical
  let := tables_nonempty r c hrc
  let : Nonempty (Joint U L r c) := Nonempty.map (successfulJoint r c U L) inferInstance
  apply Law.ext; funext ⟨X,A⟩
  simp only [Law.sigma,Chain.invariant,AcceptedData.chain,emptyData,idealCompletion,Law.uniform]
  have htotal : (∑ X : GraphState U r c,(weight U L r c (graphUnderlying U r c X):ℝ))=(graphMass U L r c:ℝ) := by
    simp [graphMass,Nat.cast_sum]
  change (weight U L r c (graphUnderlying U r c X):ℝ)/
      (∑ X : GraphState U r c,(weight U L r c (graphUnderlying U r c X):ℝ)) *
      (1/(Fintype.card (Comp X):ℝ)) = 1/(Fintype.card (Joint U L r c):ℝ)
  rw [htotal,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,joint_card]
  have he : weight U L r c (graphUnderlying U r c X)=Nat.card (Comp X) := by
    rw [weight,ite_eq_left (graph_feasible U r c X)]
  rw [← he]
  have hp : (weight U L r c (graphUnderlying U r c X):ℝ)≠0 := by
    exact_mod_cast (graph_weight_pos U L r c X hrc).ne'
  field_simp

def emptyTrial (S : ℕ) (fallbacks : ∀ X,Comp X) (X₀ : GraphState U r c) (t : ℕ) : DyadicLaw (Option (Tables r c)) := by
  classical
  exact ((emptyWalk U d r c hd hmn S X₀ t).sigma (fun X => DyadicLaw.pure (fallbacks X) S) S (fun X => completion_pure_bits U L r c S X (fallbacks X))).map (decodeJoint r c U L)

omit [Nonempty (GraphState U r c)] in
theorem emptyTrial_bits (S : ℕ) (fallbacks : ∀ X,Comp X) (X₀ : GraphState U r c) (t : ℕ) :
    (emptyTrial U L d r c hd hmn S fallbacks X₀ t).bits=t*(Nat.clog 2 (32*d^2)+S)+S := by
  classical
  simp only [emptyTrial,DyadicLaw.map_bits,DyadicLaw.sigma_bits,emptyWalk,DyadicLaw.walk_bits]

include hempty in
omit [Nonempty (GraphState U r c)] in
theorem empty_completion_law (S : ℕ) (X : GraphState U r c) (fallback : Comp X) :
    (DyadicLaw.pure fallback S).toLaw=idealCompletion U L r c hrc X := by
  let := empty_completion_subsingleton U L r c hempty (graphUnderlying U r c X)
  let := completion_nonempty U L r c X hrc
  rw [DyadicLaw.toLaw_pure]
  apply Law.ext
  funext x
  have hx : x=fallback := Subsingleton.elim _ _
  subst x
  simp only [Law.pure,idealCompletion,Law.uniform]
  rw [← Nat.card_eq_fintype_card,Nat.card_unique]
  norm_num

theorem emptyTrial_tv (S : ℕ) (fallbacks : ∀ X,Comp X) (X₀ : GraphState U r c) (t : ℕ) :
    letI := tables_nonempty r c hrc
    (emptyTrial U L d r c hd hmn S fallbacks X₀ t).toLaw.tv (stationaryTrial r c U L) ≤
      ((emptyData U L d r c hempty hrc hd hmn).chain.walk X₀ t).tv (emptyData U L d r c hempty hrc hd hmn).chain.invariant := by
  classical
  let := tables_nonempty r c hrc
  unfold emptyTrial stationaryTrial
  rw [DyadicLaw.toLaw_map,DyadicLaw.toLaw_sigma,emptyWalk_toLaw U L d r c hempty hrc hd hmn,
    ← empty_invariant_joint U L d r c hempty hrc hd hmn]
  simp only [empty_completion_law U L r c hempty hrc]
  apply (Law.tv_map _ _ _).trans
  have hh := Law.tv_sigma ((emptyData U L d r c hempty hrc hd hmn).chain.walk X₀ t)
    (emptyData U L d r c hempty hrc hd hmn).chain.invariant (idealCompletion U L r c hrc)
    (idealCompletion U L r c hrc) 0 (fun _ => by simp [Law.tv_self])
  simpa using hh

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n : ℕ} (d b k C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hempty : EmptyBlock (d^20) r c) (hrc : (∑ i,r i)=∑ j,c j)
    (hd : 14 ≤ d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n ≤ d)
    [Nonempty (GraphState (d^20) r c)]
local notation "Comp" => fun X : GraphState (d^20) r c => Completion (d^20) (d^12) r c (graphUnderlying (d^20) r c X)
local instance outerAccuracyEmptyOuterCompletionFintype (X : GraphState (d^20) r c) :
    Fintype (Comp X) := Fintype.ofFinite _
local instance outerAccuracyEmptyOuterTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

def emptyOuter (fallbacks : ∀ X,Comp X) (X₀ : GraphState (d^20) r c) (fallback : Tables r c) : DyadicLaw (Tables r c) := by
  classical
  exact stoppedLaw (emptyTrial (d^20) (d^12) d r c (smallDim_one d hd) hmn (Schedule.RD d b k)
    fallbacks X₀ (Schedule.T d b k)) fallback (Schedule.Jo d k)

omit [Nonempty (GraphState (d^20) r c)] in
theorem emptyOuter_bits (fallbacks : ∀ X,Comp X) (X₀ : GraphState (d^20) r c) (fallback : Tables r c) :
    (emptyOuter d b k r c hd hmn fallbacks X₀ fallback).bits=Schedule.R d b k := by
  classical
  change (emptyTrial _ _ _ _ _ _ _ _ _ _ _).bits*Schedule.Jo d k=_
  rw [emptyTrial_bits]
  unfold Schedule.R Schedule.RT Schedule.qs
  ring

include hempty hm hn in
theorem emptyOuter_tv (hb : d ≤ b) (hk : 1 ≤ k) (hC2 : 2 ≤ C) (hU : d^20 ≤ C)
    (hC : ∀ i,paddedRow (d^20) (d^12) r c i ≤ C) (hCb : C+1 ≤ 2^b)
    (fallbacks : ∀ X,Comp X) (X₀ : GraphState (d^20) r c) (fallback : Tables r c) :
    letI := tables_nonempty r c hrc
    (emptyOuter d b k r c hd hmn fallbacks X₀ fallback).toLaw.tv (Law.uniform (Tables r c)) ≤ (2:ℝ)^(-(k:ℤ)) := by
  classical
  let := tables_nonempty r c hrc
  let p := emptyTrial (d^20) (d^12) d r c (smallDim_one d hd) hmn (Schedule.RD d b k) fallbacks X₀ (Schedule.T d b k)
  let s := stationaryTrial r c (d^20) (d^12)
  have ht := emptyTrial_tv (d^20) (d^12) d r c hempty hrc (smallDim_one d hd) hmn (Schedule.RD d b k) fallbacks X₀ (Schedule.T d b k)
  have hmix := empty_mixing d C r c hempty hrc hd hmn hC2 hU hC (Schedule.T d b k) X₀
  have hfirst := Law.first_tv p.toLaw s fallback (Schedule.Jo d k)
  have hideal := Law.first_ideal_tv s fallback (Law.uniform (Tables r c)) (stationaryTrial_uniform r c (d^20) (d^12)) (Schedule.Jo d k)
  have hfail := stationary_failure_power d r c hrc hd hm hn hmn (Schedule.Jo d k)
  have htri := Law.tv_triangle (Law.first p.toLaw fallback (Schedule.Jo d k)) (Law.first s fallback (Schedule.Jo d k)) (Law.uniform (Tables r c))
  have hmul := mul_le_mul_of_nonneg_left (ht.trans hmix) (Nat.cast_nonneg (Schedule.Jo d k))
  have htotal := Schedule.outer_error_schedule d b k hd hb hk C hCb
  have hnerr : 0 ≤ (Schedule.Jo d k:ℝ)*((Schedule.T d b k:ℝ)+1)*(2:ℝ)^(-(Schedule.h d b k:ℤ)) := by positivity
  unfold emptyOuter
  rw [stoppedLaw_toLaw]
  change (Law.first p.toLaw fallback (Schedule.Jo d k)).tv _ ≤ _
  change _≤_ at hfail
  dsimp only [p,s] at hfirst hideal htri
  dsimp only [p]
  rw [neg_div] at hmul
  nlinarith only [hfirst,hideal,hfail,htri,hmul,htotal,hnerr]

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
namespace Parameters

 
def dim (m n : ℕ) : ℕ := 10+(m+1)*(n+1)
def L (m n : ℕ) : ℕ := dim m n^12
def U (m n : ℕ) : ℕ := dim m n^20
def cap (m n N : ℕ) : ℕ := N+dim m n*L m n+U m n+2
def bits (m n N : ℕ) : ℕ := dim m n+Nat.clog 2 (cap m n N+2)

theorem dimensions {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    14 ≤ dim m n ∧ m ≤ dim m n ∧ n ≤ dim m n ∧ m*n ≤ dim m n := by
  unfold dim
  have hh : 4 ≤ (m+1)*(n+1) := by nlinarith
  refine ⟨by omega, ?_, ?_, ?_⟩ <;> nlinarith

theorem cap_pos (m n N : ℕ) : 2 ≤ cap m n N := by unfold cap; omega

theorem threshold_le_cap (m n N : ℕ) : U m n ≤ cap m n N := by unfold cap; omega

theorem dimension_le_bits (m n N : ℕ) : dim m n ≤ bits m n N := by unfold bits; omega

theorem cap_pow_bits (m n N : ℕ) : cap m n N+1 ≤ 2^bits m n N := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (cap m n N+2)
  apply (show cap m n N+1 ≤ cap m n N+2 by omega).trans
  apply h.trans
  exact Nat.pow_le_pow_right (by norm_num) (by unfold bits; omega)

 
theorem paddedRow_le_cap {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (i : Fin m) :
    PaddedGraph.paddedRow (U m n) (L m n) r c i ≤ cap m n (∑ i,r i) := by
  have hi : r i ≤ ∑ i,r i := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ i)
  have hn : n ≤ dim m n := by unfold dim; nlinarith
  have hp : PaddedGraph.rowPadding (U m n) (L m n) r c i ≤ (n:ℤ)*(L m n:ℤ) := by
    unfold PaddedGraph.rowPadding
    calc
      _ ≤ ∑ _j : Fin n,(L m n:ℤ) := Finset.sum_le_sum (fun j _ => by split_ifs <;> simp)
      _ = _ := by simp
  have hn' : (n:ℤ) ≤ dim m n := by exact_mod_cast hn
  have hi' : (r i:ℤ) ≤ (∑ i,r i:ℕ) := by exact_mod_cast hi
  have hx := mul_le_mul_of_nonneg_right hn' (Int.natCast_nonneg (L m n))
  unfold PaddedGraph.paddedRow cap
  push_cast at hi' ⊢
  omega

end Parameters
end Contingency

 

 

namespace Contingency.Parameters

 
theorem bits_le (m n N : ℕ) : bits m n N ≤ 21*dim m n+Nat.log2 (N+1)+4 := by
  let d := dim m n
  let B := 20*d+Nat.log2 (N+1)+1
  have hd : d ≤ 2^d := Nat.lt_two_pow_self.le
  have h13 : d^13 ≤ 2^(20*d) := by
    calc
      _ ≤ (2^d)^13 := Nat.pow_le_pow_left hd _
      _ = 2^(d*13) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h20 : d^20 ≤ 2^(20*d) := by
    calc
      _ ≤ (2^d)^20 := Nat.pow_le_pow_left hd _
      _ = 2^(20*d) := by rw [← pow_mul]; congr 1; omega
  have hN : N ≤ 2^(Nat.log2 (N+1)+1) := by
    have hh := Nat.lt_pow_succ_log_self (by norm_num : 1<2) (N+1)
    rw [← Nat.log2_eq_log_two] at hh
    omega
  have hpow : 2^(20*d) ≤ 2^B := Nat.pow_le_pow_right (by norm_num) (by dsimp [B]; omega)
  have hpow' : 2^(Nat.log2 (N+1)+1) ≤ 2^B := Nat.pow_le_pow_right (by norm_num) (by dsimp [B]; omega)
  have hpos : 1 ≤ 2^B := Nat.one_le_pow _ _ (by norm_num)
  have hcap : cap m n N+2 ≤ 2^(B+3) := by
    have h := h13.trans hpow
    have h' := h20.trans hpow
    have h'' := hN.trans hpow'
    have he : cap m n N+2=N+d^13+d^20+4 := by
      unfold cap L U
      dsimp only [d]
      rw [pow_succ]
      ring
    rw [he,pow_add]
    norm_num
    omega
  have hc : Nat.clog 2 (cap m n N+2) ≤ B+3 :=
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr hcap
  unfold bits
  dsimp [B,d] at hc
  omega

 
theorem dim_le_size_square (m n N : ℕ) : dim m n ≤ (inputSize m n N+3)^2 := by
  unfold dim inputSize
  nlinarith [Nat.zero_le (Nat.log2 (N+1))]

end Contingency.Parameters

end

end OAI
