import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleRational
import OAI.Combinatorics.ContingencyTables.Machines.RationalIntervalProgram

namespace OAI

/-! # Integral numerators for the literal forest penalty

Cut signs and affine completion coefficients are integers in {-1,0,1}.
At an integral bin corner the tree value has the single denominator
B times its capacity. This identifies the integer arithmetic consumed
by the executable interval-penalty program.
-/

namespace ContingencyTables.ForestIntegerEvaluation

open CompanionFactorialApplication CompanionOracleDensity ForestAffineCoefficients
open ForestAssignmentSplit GraphCompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def indicator (b : Bool) : ℤ := if b then 1 else 0

def sign (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℤ :=
  indicator (cutSide A t (.inl a.1))-indicator (cutSide A t (.inr a.2))

lemma sign_cast (A : Instance I J) (t : TreeCell A.T) (a : I×J) :
    (sign A t a:ℚ)=rationalSign A t a := by
  cases hr : cutSide A t (.inl a.1) <;> cases hc : cutSide A t (.inr a.2) <;>
    norm_num [sign,indicator,rationalSign,rationalIndicator,hr,hc]

lemma selfSign_square (A : Instance I J) (t : TreeCell A.T) :
    (rationalSign A t t.val)^2=1 := by
  have hn := (cut_properties A t).2.2
  cases hr : cutSide A t (.inl t.val.1) <;>
    cases hc : cutSide A t (.inr t.val.2) <;>
    simp_all [rationalSign,rationalIndicator]

def coefficient (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℤ :=
  if A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  then -(sign A t a)*sign A t t.val else 0

lemma coefficient_cast (A : Instance I J) (t : TreeCell A.T) (a : I×J) :
    (coefficient A t a:ℚ)=rationalCoefficient A t a := by
  have hs := selfSign_square A t
  have hn : rationalSign A t t.val≠0 := by intro h; rw [h] at hs; norm_num at hs
  unfold coefficient rationalCoefficient
  split_ifs
  · simp only [Int.cast_mul,Int.cast_neg,sign_cast]
    apply (eq_div_iff hn).mpr
    calc
      (-(rationalSign A t a)*rationalSign A t t.val)*rationalSign A t t.val=
          -(rationalSign A t a)*(rationalSign A t t.val)^2 := by ring
      _ = _ := by rw [hs,mul_one]
  · exact Int.cast_zero

def smallContribution (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℤ) : ℤ :=
  ∑ a : I×J,if A.small a.1 a.2 then
    indicator (cutSide A t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      indicator (cutSide A t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0

lemma smallContribution_cast (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℤ) :
    (smallContribution A t x q:ℚ)=rationalSmallContribution A t x q := by
  unfold smallContribution rationalSmallContribution
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · cases hr : cutSide A t (.inl a.1) <;> cases hc : cutSide A t (.inr a.2) <;>
      simp_all [indicator,rationalIndicator]
  · exact Int.cast_zero

def offset (A : Instance I J) (t : TreeCell A.T) (x q : I → J → ℤ) : ℤ :=
  A.X t.val.1 t.val.2-smallContribution A t x q*sign A t t.val-
    ∑ a : I×J,coefficient A t a*A.X a.1 a.2

lemma offset_cast (A : Instance I J) (t : TreeCell A.T) (x q : I → J → ℤ) :
    (offset A t x q:ℚ)=rationalOffset A t x q := by
  have hs := selfSign_square A t
  have hn : rationalSign A t t.val≠0 := by intro h; rw [h] at hs; norm_num at hs
  have he : rationalSmallContribution A t x q*rationalSign A t t.val=
      rationalSmallContribution A t x q/rationalSign A t t.val := by
    apply (eq_div_iff hn).mpr
    rw [mul_assoc,←pow_two,hs,mul_one]
  simp only [offset,rationalOffset,Int.cast_sub,Int.cast_mul,Int.cast_sum,
    smallContribution_cast,sign_cast,coefficient_cast,he]

def numerator (A : Instance I J) (C : ℕ) (t : TreeCell A.T)
    (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) : ℤ :=
  (rationalBinWidth A C:ℤ)*offset A t x q+
    ∑ f : FreeCell A.small A.T,
      coefficient A t f.val*((A.b f.val.1 f.val.2:ℤ)+1)*(v f:ℤ)

/-- The exact affine tree value is a signed integral numerator divided
by the explicit natural denominator, even when the original margins
have very large binary representations. -/
theorem numerator_div (A : Instance I J) (C : ℕ) (hC : 0<C)
    (t : TreeCell A.T) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) :
    (numerator A C t x q v:ℚ)/
        ((rationalBinWidth A C:ℚ)*A.b t.val.1 t.val.2)=
      rationalScaledTree A C x q (fun f => (v f:ℚ)) t := by
  have hd : (0:ℚ)<A.d := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one A.hd
  have hCQ : (0:ℚ)<C := by exact_mod_cast hC
  have hB : (rationalBinWidth A C:ℚ)≠0 := by
    simp only [rationalBinWidth,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    positivity
  have hb : (A.b t.val.1 t.val.2:ℚ)≠0 := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (A.hlarge _ _ (A.hTG t.property)).2).ne'
  have hsum : (∑ f : FreeCell A.small A.T,
      (rationalCoefficient A t f.val*((A.b f.val.1 f.val.2:ℚ)+1)/rationalBinWidth A C/
        (A.b t.val.1 t.val.2:ℚ))*(v f:ℚ))=
      (∑ f : FreeCell A.small A.T,
        rationalCoefficient A t f.val*((A.b f.val.1 f.val.2:ℚ)+1)*(v f:ℚ))/
        ((rationalBinWidth A C:ℚ)*A.b t.val.1 t.val.2) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro f _
    field_simp [hB,hb]
  simp only [numerator,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_sum,Int.cast_one,
    offset_cast,coefficient_cast,rationalScaledTree,hsum]
  field_simp [hB,hb]


def treeData (A : Instance I J) (C : ℕ) (t : TreeCell A.T)
    (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) : RationalIntervalProgram.Input :=
  let z := numerator A C t x q v
  ((z.toNat,(-z).toNat),rationalBinWidth A C*A.b t.val.1 t.val.2)

/-- Each summand of the literal rational forest penalty is exactly the
output of the compiled nonnegative interval-arithmetic routine. -/
theorem treeData_value (A : Instance I J) (C : ℕ) (hC : 0<C)
    (t : TreeCell A.T) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) :
    MatchingFPRAS.TreeFraction.val (RationalIntervalProgram.intervalCode (treeData A C t x q v))=
      max 0 (max (-rationalScaledTree A C x q (fun f => (v f:ℚ)) t)
        (rationalScaledTree A C x q (fun f => (v f:ℚ)) t-1)) := by
  have hB : 0<rationalBinWidth A C := by
    unfold rationalBinWidth
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC)
      (pow_pos (lt_of_lt_of_le Nat.zero_lt_one A.hd) _)
  have ht := (A.hlarge _ _ (A.hTG t.property)).2
  have hd := Nat.mul_pos hB ht
  have he : ((numerator A C t x q v).toNat:ℚ)-
      ((-numerator A C t x q v).toNat:ℚ)=(numerator A C t x q v:ℚ) := by
    exact_mod_cast (show ((numerator A C t x q v).toNat:ℤ)-
      ((-numerator A C t x q v).toNat:ℤ)=numerator A C t x q v by omega)
  unfold treeData
  rw [RationalIntervalProgram.intervalCode_value _ _ _ hd,he,Nat.cast_mul,
    numerator_div A C hC]

end
end ContingencyTables.ForestIntegerEvaluation

end OAI
