import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Probability.RootSuccessAsymptotics

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def eligibleTupleEquivRootPrescription (g : Direction F) :
    {T : FourTuple F // T ∈ eligibleTuples g} ≃ RootPrescription g where
  toFun T := (⟨fun i => ⟨T.1.generator i, (Finset.mem_filter.mp T.2).2.2 i⟩,
    fun i j h => (Finset.mem_filter.mp T.2).2.1 (congrArg Subtype.val h)⟩, T.1.side)
  invFun a := ⟨a.tuple, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.injective,
    fun i => (a.1 i).2⟩⟩
  left_inv T := by
    apply Subtype.ext
    cases T with
    | mk T h => cases T; rfl
  right_inv a := by
    apply Prod.ext
    · ext i
      rfl
    · rfl

omit [Field F] in
@[simp] theorem equivRootPrescription_tuple (g : Direction F)
    (T : {T : FourTuple F // T ∈ eligibleTuples g}) :
    (eligibleTupleEquivRootPrescription g T).tuple = T.1 := by
  cases T with
  | mk T h => cases T; rfl

theorem successfulTupleCount_eq_rootSuccessCount (g : Direction F) (M : MergedPairs F) :
    successfulTupleCount g M = rootSuccessCount g M := by
  let f : RootPrescription g → ℕ := fun a =>
    if (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g,c)) ∧
      Function.Injective (tuplePoint M a.tuple) then 1 else 0
  have h := Equiv.sum_comp (eligibleTupleEquivRootPrescription g) f
  simp only [f, equivRootPrescription_tuple] at h
  let fT : FourTuple F → ℕ := fun T =>
    if (∃ c, ∀ i, OnLine (tuplePoint M T i) (g,c)) ∧
      Function.Injective (tuplePoint M T) then 1 else 0
  have hs := Finset.sum_subtype (eligibleTuples g)
    (p := fun T => T ∈ eligibleTuples g) (F := inferInstance) (fun _ => Iff.rfl) fT
  have hsum : (∑ T ∈ eligibleTuples g, fT T) = ∑ a : RootPrescription g, f a :=
    hs.trans h
  unfold successfulTupleCount rootSuccessCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Eq.trans ?_ hsum
  apply Finset.sum_congr rfl
  intro tuple _
  dsimp only [fT]
  apply ite_cond_congr
  simp only [successfulInDirection, alignedInDirection, Set.mem_ofPred_eq]

theorem mean_successfulTupleCount (g : Direction F) :
    (∑ M : MergedPairs F, (successfulTupleCount g M : ℝ)) /
      Fintype.card (MergedPairs F) =
      16 * ((Fintype.card F).descFactorial 4 : ℝ)^2 / (Fintype.card F : ℝ)^7 := by
  simp_rw [successfulTupleCount_eq_rootSuccessCount]
  exact mean_rootSuccessCount g

theorem rootMean_lower_bound (q : ℕ) (hq : 24 ≤ q) :
    9 * (q : ℝ) ≤ 16 * (q.descFactorial 4 : ℝ)^2 / (q : ℝ)^7 := by
  have hqR : (24 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hprod : (q.descFactorial 4 : ℝ) =
      (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) - 2) * ((q : ℝ) - 3) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
      Nat.sub_zero, Nat.mul_one, Nat.cast_mul]
    rw [Nat.cast_sub (by omega : 3 ≤ q), Nat.cast_sub (by omega : 2 ≤ q),
      Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
    ring
  have hquarter : (3 / 4 : ℝ) * (q : ℝ)^4 ≤ (q.descFactorial 4 : ℝ) := by
    rw [hprod]
    have h1 : 0 ≤ (q : ℝ)^3 * ((q : ℝ) - 24) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ (q : ℝ) * (11 * (q : ℝ) - 6) := mul_nonneg hq0.le (by linarith)
    nlinarith
  apply (le_div_iff₀ (pow_pos hq0 7)).mpr
  calc
    9 * (q : ℝ) * (q : ℝ)^7 = 16 * ((3 / 4 : ℝ) * (q : ℝ)^4)^2 := by ring
    _ ≤ 16 * (q.descFactorial 4 : ℝ)^2 := by gcongr

theorem mean_successfulTupleCount_ge (g : Direction F) (hq : 24 ≤ Fintype.card F) :
    9 * (Fintype.card F : ℝ) ≤
      (∑ M : MergedPairs F, (successfulTupleCount g M : ℝ)) /
        Fintype.card (MergedPairs F) := by
  rw [mean_successfulTupleCount]
  exact rootMean_lower_bound _ hq

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]
open MeasureTheory

theorem integral_successfulTupleCount_original (g : Direction F) :
    (∫ M, (successfulTupleCount g M : ℝ) ∂(offsetLaw F).toMeasure) =
      16 * ((Fintype.card F).descFactorial 4 : ℝ)^2 / (Fintype.card F : ℝ)^7 := by
  rw [PMF.integral_eq_sum]
  simp only [offsetLaw, PMF.uniformOfFintype_apply, smul_eq_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  simpa only [div_eq_mul_inv, mul_comm, Fintype.card_fun, Fintype.card_option,
    Fintype.card_bool] using mean_successfulTupleCount g
end Measurable

theorem mean_successfulTupleCount_asymptotic
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (g : ∀ n, Direction (F n))
    (hcard : Filter.Tendsto (fun n => Fintype.card (F n)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n =>
      ((∑ M : MergedPairs (F n), (successfulTupleCount (g n) M : ℝ)) /
        Fintype.card (MergedPairs (F n))) / Fintype.card (F n))
      Filter.atTop (nhds 16) := by
  simp_rw [successfulTupleCount_eq_rootSuccessCount]
  exact mean_rootSuccessCount_asymptotic F g hcard

end
end Balanced.CandidateExposure

end OAI
