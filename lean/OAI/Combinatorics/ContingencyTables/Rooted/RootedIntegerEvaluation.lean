import OAI.Combinatorics.ContingencyTables.Rooted.RootedScaledPenalty
import OAI.Combinatorics.ContingencyTables.Rooted.ForestAffineProgram

namespace OAI

/-! # Integral coefficients of the executed selected-root affine penalty -/

namespace ContingencyTables.RootedIntegerEvaluation

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit

variable {I J : Type*} [Fintype I] [Fintype J]

def integerIndicator (b : Bool) : ℤ := if b then 1 else 0

noncomputable def sign (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : ℤ :=
  integerIndicator (RootedCut.treeCut A.T S t (.inl a.1))-
    integerIndicator (RootedCut.treeCut A.T S t (.inr a.2))

lemma sign_real (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T) (a : I×J) :
    (sign A S t a:ℝ)=RootedCut.sign A.T S t a := by
  cases hr : RootedCut.treeCut A.T S t (.inl a.1) <;>
    cases hc : RootedCut.treeCut A.T S t (.inr a.2) <;>
    norm_num [sign,integerIndicator,RootedCut.sign,ForestCut.indicator,hr,hc]

lemma selfSign_square (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T) :
    (RootedCut.sign A.T S t t.val)^2=1 := by
  have hn := RootedCut.treeCut_self A.T S A.hT t
  cases hr : RootedCut.treeCut A.T S t (.inl t.val.1) <;>
    cases hc : RootedCut.treeCut A.T S t (.inr t.val.2) <;>
    simp_all [RootedCut.sign,ForestCut.indicator]

noncomputable def coefficient (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : ℤ :=
  if A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  then -(sign A S t a)*sign A S t t.val else 0

lemma coefficient_real (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) :
    (coefficient A S t a:ℝ)=RootedAffine.coefficient A S t a := by
  have hs := selfSign_square A S t
  have hn := RootedCut.sign_self_ne_zero A.T S A.hT t
  unfold coefficient RootedAffine.coefficient
  split_ifs
  · simp only [Int.cast_mul,Int.cast_neg,sign_real]
    apply (eq_div_iff hn).mpr
    calc
      (-(RootedCut.sign A.T S t a)*RootedCut.sign A.T S t t.val)*RootedCut.sign A.T S t t.val=
          -(RootedCut.sign A.T S t a)*(RootedCut.sign A.T S t t.val)^2 := by ring
      _=_ := by rw [hs,mul_one]
  · exact Int.cast_zero

noncomputable def smallContribution (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) : ℤ :=
  ∑ a : I×J,if A.small a.1 a.2 then
    integerIndicator (RootedCut.treeCut A.T S t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      integerIndicator (RootedCut.treeCut A.T S t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0

lemma smallContribution_real (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) :
    (smallContribution A S t x q:ℝ)=RootedAffine.smallContribution A S t
      (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ)) := by
  unfold smallContribution RootedAffine.smallContribution
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · cases hr : RootedCut.treeCut A.T S t (.inl a.1) <;>
      cases hc : RootedCut.treeCut A.T S t (.inr a.2) <;>
      simp_all [integerIndicator,ForestCut.indicator]
  · exact Int.cast_zero

noncomputable def offset (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) : ℤ :=
  A.X t.val.1 t.val.2-smallContribution A S t x q*sign A S t t.val-
    ∑ a : I×J,coefficient A S t a*A.X a.1 a.2

lemma offset_real (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q : I → J → ℤ) :
    (offset A S t x q:ℝ)=RootedAffine.offset A S t
      (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ)) := by
  have hs := selfSign_square A S t
  have hn := RootedCut.sign_self_ne_zero A.T S A.hT t
  have he : RootedAffine.smallContribution A S t (fun i j => (x i j:ℝ))
      (fun i j => (q i j:ℝ))*RootedCut.sign A.T S t t.val=
      RootedAffine.smallContribution A S t (fun i j => (x i j:ℝ))
        (fun i j => (q i j:ℝ))/RootedCut.sign A.T S t t.val := by
    apply (eq_div_iff hn).mpr
    rw [mul_assoc,←pow_two,hs,mul_one]
  simp only [offset,RootedAffine.offset,Int.cast_sub,Int.cast_mul,Int.cast_sum,
    smallContribution_real,sign_real,coefficient_real,he]

noncomputable def rationalScaledTree (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) (t : TreeCell A.T) : ℚ :=
  (offset A S t x q:ℚ)/(A.b t.val.1 t.val.2:ℚ)+
    ∑ f : FreeCell A.small A.T,
      ((coefficient A S t f.val:ℚ)*((A.b f.val.1 f.val.2:ℚ)+1)/B/
        (A.b t.val.1 t.val.2:ℚ))*v f

lemma rationalScaledTree_cast (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℚ) (t : TreeCell A.T) :
    (rationalScaledTree A S B x q v t:ℝ)=
      RootedScaledPenalty.scaledTree A S (B:ℝ) x q (fun f => (v f:ℝ)) t := by
  simp only [rationalScaledTree,RootedScaledPenalty.scaledTree,AffinePenalty.affineValue,
    RootedScaledPenalty.normalizedOffset,RootedScaledPenalty.normalizedCoefficient,
    Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_sum,Rat.cast_natCast,Rat.cast_one,
    Rat.cast_intCast,offset_real,coefficient_real]

noncomputable def numerator (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (t : TreeCell A.T) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) : ℤ :=
  (B:ℤ)*offset A S t x q+
    ∑ f : FreeCell A.small A.T,
      coefficient A S t f.val*((A.b f.val.1 f.val.2:ℤ)+1)*(v f:ℤ)

theorem numerator_div (A : Instance I J) (S : Selection A.T) (B : ℕ) (hB : 0<B)
    (t : TreeCell A.T) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) :
    (numerator A S B t x q v:ℚ)/((B:ℚ)*A.b t.val.1 t.val.2)=
      rationalScaledTree A S B x q (fun f => (v f:ℚ)) t := by
  have hBQ : (B:ℚ)≠0 := by exact_mod_cast hB.ne'
  have hb : (A.b t.val.1 t.val.2:ℚ)≠0 := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (A.hlarge _ _ (A.hTG t.property)).2).ne'
  have hsum : (∑ f : FreeCell A.small A.T,
      ((coefficient A S t f.val:ℚ)*((A.b f.val.1 f.val.2:ℚ)+1)/B/
        (A.b t.val.1 t.val.2:ℚ))*(v f:ℚ))=
      (∑ f : FreeCell A.small A.T,
        (coefficient A S t f.val:ℚ)*((A.b f.val.1 f.val.2:ℚ)+1)*(v f:ℚ))/
        ((B:ℚ)*A.b t.val.1 t.val.2) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro f _
    field_simp [hBQ,hb]
  simp only [numerator,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_sum,Int.cast_one,
    rationalScaledTree,hsum]
  field_simp [hBQ,hb]

noncomputable def forestData (A : Instance I J) (S : Selection A.T)
    (B : ℕ) (t : TreeCell A.T) (x y : I → J → ℤ)
    {n : ℕ} (e : Fin n ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    ForestAffineProgram.Input :=
  ForestAffineProgram.data ((B:ℤ)*offset A S t x y)
    (fun i => coefficient A S t (e i).val*((A.b (e i).val.1 (e i).val.2:ℤ)+1))
    (fun i => v (e i)) (B*A.b t.val.1 t.val.2)

theorem evaluate_forest (A : Instance I J) (S : Selection A.T) (B : ℕ) (hB : 0<B)
    (t : TreeCell A.T) (x y : I → J → ℤ)
    {n : ℕ} (e : Fin n ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    MatchingFPRAS.TreeFraction.val (ForestAffineProgram.evaluate (forestData A S B t x y e v))=
      max 0 (max (-rationalScaledTree A S B x y (fun f => (v f:ℚ)) t)
        (rationalScaledTree A S B x y (fun f => (v f:ℚ)) t-1)) := by
  have hb := (A.hlarge _ _ (A.hTG t.property)).2
  have hn : (((B:ℤ)*offset A S t x y:ℤ):ℚ)+
      ∑ i : Fin n,
        ((coefficient A S t (e i).val*((A.b (e i).val.1 (e i).val.2:ℤ)+1):ℤ):ℚ)*
          (v (e i):ℚ)=(numerator A S B t x y v:ℚ) := by
    simp only [numerator,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,Int.cast_sum]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold forestData
  rw [ForestAffineProgram.evaluate_data _ _ _ _ (Nat.mul_pos hB hb),hn,Nat.cast_mul,
    numerator_div A S B hB]

end ContingencyTables.RootedIntegerEvaluation

end OAI
