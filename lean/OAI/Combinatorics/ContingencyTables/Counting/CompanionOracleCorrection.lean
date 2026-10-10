import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleMixing
import OAI.Combinatorics.ContingencyTables.Counting.CompanionBinPopulation
import OAI.Combinatorics.ContingencyTables.Rooted.ForestScaledIdentification

namespace OAI

/-! # Exact population correction for the literal companion weight -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def integerPoint (A : Instance I J) (C : ℝ) (f : FreeIndex A.small A.T A.b) :
    Fin (dimension A) → ℝ := fun i => integerCube A (binWidth A C) f (index A i)

lemma pull_integerPoint (A : Instance I J) (C : ℝ) (f : FreeIndex A.small A.T A.b) :
    pull A (integerPoint A C f)=integerCube A (binWidth A C) f := by
  funext t
  simp only [pull,integerPoint,Equiv.apply_symm_apply]

/-- The continuous evaluator density at every integer assignment is the
original summand defining the manuscript's h. -/
lemma density_at_integer (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    rho A C a z (integerPoint A C f)=
      (2:ℝ)^(-(a*C/height A C)*ForestPenaltyBound.penalty A z f) := by
  unfold rho DenseWeights.density D
  rw [pull_integerPoint]
  change (2:ℝ)^(-(a/height A C*penalty A C (binWidth A C)
      (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))
      (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))
      (integerCube A (binWidth A C) f)))=_
  rw [penalty_at_integer A C (binWidth A C) (binWidth_positive A C hC)]
  congr 1
  ring

lemma sum_density_integer (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (z : View A → ℕ) :
    (∑ f : FreeIndex A.small A.T A.b,rho A C a z (integerPoint A C f))=
      h A (a*C/height A C) z := by
  unfold h ForestCountIdentification.sourceMarginal
  apply Finset.sum_congr rfl
  intro f _
  exact density_at_integer A C a hC z f

def integerBin (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) : Grid (I := Fin (dimension A)) K := fun i =>
  let t := index A i
  ⟨(FairBits.scale K (A.b t.val.1 t.val.2+1) (f t).val:ℤ),by
    constructor
    · positivity
    · have hh := FairBits.scale_lt hK (Nat.succ_pos _) (f t).isLt
      have hhZ : (FairBits.scale K (A.b t.val.1 t.val.2+1) (f t).val:ℤ)<K := by
        exact_mod_cast hh
      omega⟩

def integerFiber (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) : Finset (FreeIndex A.small A.T A.b) :=
  Finset.univ.filter (fun f => integerBin A K hK f=v)

lemma ownFiber_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) :
    0 < (integerFiber A K hK (integerBin A K hK f)).card := by
  apply Finset.card_pos.mpr
  exact ⟨f,by simp [integerFiber]⟩

def binSum (A : Instance I J) (C a : ℝ) (z : View A → ℕ) (K : ℕ) : ℝ :=
  ∑ v : Grid (I := Fin (dimension A)) K,gridWeight A C a z v

lemma binSum_positive (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) : 0 < binSum A C a z K := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  exact Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty

def assignmentCount (A : Instance I J) : ℕ := Fintype.card (FreeIndex A.small A.T A.b)

lemma assignmentCount_positive (A : Instance I J) : 0 < assignmentCount A := by
  let : Nonempty (FreeIndex A.small A.T A.b) := ⟨fun _ => 0⟩
  exact Fintype.card_pos

def correctedMass (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) : ℝ :=
  gridWeight A C a z (integerBin A K hK f)/binSum A C a z K/
    (integerFiber A K hK (integerBin A K hK f)).card

def correction (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) : ℝ :=
  ((K:ℝ)^dimension A*(integerFiber A K hK (integerBin A K hK f)).card/assignmentCount A)*
    rho A C a z (integerPoint A C f)/gridWeight A C a z (integerBin A K hK f)

/-- Population correction cancels the bin size and bin weight exactly,
before taking any expectation or approximation. -/
lemma corrected_mass_product (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    correctedMass A C a z K hK f*correction A C a z K hK f=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A C a z K))*
        rho A C a z (integerPoint A C f) := by
  have hweight : gridWeight A C a z (integerBin A K hK f)≠0 :=
    (DenseWeights.binWeight_pos _ _ _).ne'
  have hfiber : ((integerFiber A K hK (integerBin A K hK f)).card:ℝ)≠0 := by
    exact_mod_cast (ownFiber_positive A K hK f).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  have hz := (binSum_positive A C a z K hK).ne'
  unfold correctedMass correction
  field_simp [hweight,hfiber,hc,hz]

/-- The exact corrected mean contains the literal original free-assignment
sum, not a continuous integral or a surrogate count. -/
theorem corrected_expectation (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (z : View A → ℕ) (K : ℕ) (hK : 0 < K) :
    (∑ f : FreeIndex A.small A.T A.b,
      correctedMass A C a z K hK f*correction A C a z K hK f)=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A C a z K))*
        h A (a*C/height A C) z := by
  simp_rw [corrected_mass_product]
  rw [←Finset.mul_sum,sum_density_integer A C a hC]

def ratioObservable (A : Instance I J) (C : ℝ) (a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ :=
  gridWeight A C (a+1) z v/gridWeight A C a z v

def ratioMean (A : Instance I J) (C : ℝ) (a : ℕ) (z : View A → ℕ) (K : ℕ) : ℝ :=
  ∑ v : Grid (I := Fin (dimension A)) K,
    (gridWeight A C a z v/binSum A C a z K)*ratioObservable A C a z v

private lemma floor_step (x q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ⌊x+q⌋=⌊x⌋ ∨ ⌊x+q⌋=⌊x⌋+1 := by
  have hlo := Int.floor_mono (show x ≤ x+q by linarith)
  have hhi := Int.floor_mono (show x+q ≤ x+1 by linarith)
  rw [Int.floor_add_one] at hhi
  omega

/-- The actual phase observable takes exactly the two source values,
since one annealing step changes its integer exponent by zero or one. -/
theorem ratioObservable_cases (A : Instance I J) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    ratioObservable A C a z v=1 ∨ ratioObservable A C a z v=1/2 := by
  have hD := D_bounds A C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  let q := D A C z (realCorner v)/height A C
  have hq0 : 0 ≤ q := div_nonneg hD.1 (height_positive A C hC).le
  have hq1 : q ≤ 1 := (div_le_one (height_positive A C hC)).mpr hD.2
  let x := (a:ℝ)/height A C*D A C z (realCorner v)
  have he : ((a:ℝ)+1)/height A C*D A C z (realCorner v)=x+q := by
    dsimp only [x,q]
    ring
  have hr : ratioObservable A C a z v=(2:ℝ)^(-((⌊x+q⌋:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)) := by
    unfold ratioObservable gridWeight V DenseWeights.binWeight
    rw [he,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    change -((⌊x+q⌋:ℤ):ℝ)- -((⌊x⌋:ℤ):ℝ)=_
    ring
  rcases floor_step x q hq0 hq1 with hf|hf
  · left
    rw [hr,hf]
    simp
  · right
    rw [hr,hf]
    have hh : -(((⌊x⌋:ℤ)+1:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)=(-1:ℝ) := by
      push_cast
      ring
    rw [hh]
    norm_num

lemma ratioMean_eq (A : Instance I J) (C : ℝ) (a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) :
    ratioMean A C a z K=binSum A C (a+1) z K/binSum A C a z K := by
  unfold ratioMean binSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  have hv : gridWeight A C a z v≠0 := (DenseWeights.binWeight_pos _ _ _).ne'
  have hZ := (binSum_positive A C a z K hK).ne'
  unfold ratioObservable
  change (gridWeight A C a z v/binSum A C a z K)*
    (gridWeight A C (a+1) z v/gridWeight A C a z v)=
      gridWeight A C (a+1) z v/binSum A C a z K
  field_simp [hv,hZ]

lemma binSum_zero (A : Instance I J) (C : ℝ) (z : View A → ℕ) (K : ℕ) :
    binSum A C 0 z K=(K:ℝ)^dimension A := by
  simp only [binSum,gridWeight,V,DenseWeights.binWeight,zero_div,zero_mul,Int.floor_zero,
    Int.cast_zero,neg_zero,Real.rpow_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,oracle_grid_card,Nat.cast_pow]

lemma ratio_telescope (A : Instance I J) (C : ℝ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (j : ℕ) :
    (∏ a∈Finset.range j,ratioMean A C a z K)=binSum A C j z K/(K:ℝ)^dimension A := by
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  induction j with
  | zero => simp only [Finset.range_zero,Finset.prod_empty,Nat.cast_zero,binSum_zero,div_self hp]
  | succ j ih =>
    rw [Finset.prod_range_succ,ih,ratioMean_eq A C j z K hK]
    have hZ := (binSum_positive A C j z K hK).ne'
    push_cast
    field_simp [hp,hZ]

/-- The original h-value is exactly the product of the actual stationary
ratio means and the integer-population correction mean. -/
theorem oracle_telescope (A : Instance I J) (C : ℝ) (hC : 0 < C)
    (z : View A → ℕ) (K : ℕ) (hK : 0 < K) (j : ℕ) :
    (assignmentCount A:ℝ)*(∏ a∈Finset.range j,ratioMean A C a z K)*
      (∑ f : FreeIndex A.small A.T A.b,
        correctedMass A C j z K hK f*correction A C j z K hK f)=
      h A ((j:ℝ)*C/height A C) z := by
  rw [ratio_telescope A C z K hK j,corrected_expectation A C j hC z K hK]
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  have hZ := (binSum_positive A C j z K hK).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  field_simp [hp,hZ,hc]


end

end ContingencyTables.CompanionOracleDensity

end OAI
