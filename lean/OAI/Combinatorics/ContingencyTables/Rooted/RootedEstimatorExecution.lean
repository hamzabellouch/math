import OAI.Combinatorics.ContingencyTables.Rooted.RootedComputedEstimator
import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorRange

namespace OAI

/-! # Literal input and output of the executed estimator blocks -/

namespace ContingencyTables.RootedEstimatorExecution

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedComputedEstimator
open MatchingFPRAS FiniteObservableTransport CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def ratioBlock (A : Instance (Fin m) (Fin n)) (C K j a : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : RootedComputedEstimator.RatioWords A C K j delta failure) :
    RootedEstimatorBlockProgram.RatioBlock :=
  List.ofFn (fun i => (RootedOracleWalkProgram.data A C a K z v,List.ofFn (draws i)))

def correctionBlock (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (draws : RootedComputedEstimator.CorrectionWords A C K j delta failure) :
    RootedEstimatorBlockProgram.CorrectionBlock :=
  List.ofFn (fun i => RootedCorrectionSampleProgram.data A C j K z v (offsetAccuracy A delta)
    degree depth (List.ofFn (draws i).1) (List.ofFn (draws i).2))

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (draws : Inputs A C K j delta failure) :
    RootedEstimatorBlockProgram.Input :=
  ((assignmentCount A,List.ofFn (fun a : Fin j => ratioBlock A C K j a.val delta failure z v (draws.1 a))),
    correctionBlock A C K j delta failure z v degree depth draws.2)

lemma ratioBlock_value (A : Instance (Fin m) (Fin n)) (C K j a : ℕ) (hC : 0 < C)
    (delta failure : ℚ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hB : (K:ℝ)=binWidth A C) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : RootedComputedEstimator.RatioWords A C K j delta failure) :
    TreeFraction.val (RootedEstimatorBlockProgram.ratioAverage
      (ratioBlock A C K j a delta failure z v draws))=
        RootedComputedEstimator.ratioAverage A C K j a delta failure z v draws := by
  rw [RootedEstimatorBlockProgram.ratioAverage_value]
  simp only [ratioBlock,List.map_ofFn,List.sum_ofFn,List.length_ofFn]
  unfold RootedComputedEstimator.ratioAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact RootedRatioSampleLaw.program_sample A C a K hC z hz hB.le v _ (draws i)

lemma correctionBlock_value (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (draws : RootedComputedEstimator.CorrectionWords A C K j delta failure) :
    TreeFraction.val (RootedEstimatorBlockProgram.correctionAverage
      (correctionBlock A C K j delta failure z v degree depth draws))=
        RootedComputedEstimator.correctionAverage A C K j hK hW delta failure z v draws := by
  rw [RootedEstimatorBlockProgram.correctionAverage_value]
  simp only [correctionBlock,List.map_ofFn,List.sum_ofFn,List.length_ofFn]
  unfold RootedComputedEstimator.correctionAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact RootedCorrectionSampleLaw.program_sample A C j K hC hj hK hW hB z
    (roundingTolerance delta) v _ _ degree depth hdegree hdepth (draws i)

/-- The actual list program returns the exact value of the transported
finite experiment, including unsuccessful statistical outcomes. -/
theorem output_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (draws : Inputs A C K j delta failure) :
    TreeFraction.val (RootedEstimatorBlockProgram.output
      (data A C K j delta failure z v degree depth draws))=
        RootedComputedEstimator.estimate A C K j hK hW delta failure z v draws := by
  rw [RootedEstimatorBlockProgram.output_value]
  simp only [data,List.map_ofFn,List.prod_ofFn]
  rw [correctionBlock_value A C K j hC hj hK hW hB delta failure z v degree depth hdegree hdepth]
  have hp : (∏ a : Fin j,TreeFraction.val (RootedEstimatorBlockProgram.ratioAverage
      (ratioBlock A C K j a.val delta failure z v (draws.1 a))))=
      ∏ a : Fin j,RootedComputedEstimator.ratioAverage A C K j a.val delta failure z v (draws.1 a) := by
    apply Finset.prod_congr rfl
    intro a _
    exact ratioBlock_value A C K j a.val hC delta failure z hz hB v (draws.1 a)
  simp only [Function.comp_apply]
  rw [hp]
  rfl


private lemma property_of_sameLaw {X Y Z : Type*} [Fintype X] [Fintype Y]
    (f : X → Z) (g : Y → Z) (h : SameLaw f g) (P : Z → Prop)
    (hg : ∀ y,P (g y)) (x : X) : P (f x) := by
  by_contra hx
  let bad : Z → ℝ := fun z => if P z then 0 else 1
  have he := h bad
  have hzero : uniformAverage (fun y => bad (g y))=0 := by
    simp only [bad,hg,ite_true,uniformAverage,Finset.sum_const_zero,zero_div]
  rw [hzero] at he
  have hnonneg (t : X) : 0 ≤ bad (f t) := by
    dsimp only [bad]
    split_ifs <;> norm_num
  have hsum : (∑ t : X,bad (f t))=0 := by
    have he' := (div_eq_zero_iff).mp he
    rcases he' with he'|he'
    · exact he'
    · have hc : Fintype.card X≠0 := by
        let : Nonempty X := ⟨x⟩
        exact Fintype.card_ne_zero
      exact False.elim (hc (by exact_mod_cast he'))
  have hxsum := Finset.single_le_sum (fun t _ => hnonneg t) (Finset.mem_univ x)
  rw [hsum] at hxsum
  simp only [bad,hx,ite_false] at hxsum
  norm_num at hxsum

/-- Full finite support transfers the proved deterministic range to
all physical sample words, not only to the high-probability event. -/
theorem output_range (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (draws : Inputs A C K j delta failure) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤
      (TreeFraction.val (RootedEstimatorBlockProgram.output
        (data A C K j delta failure z v degree depth draws)):ℝ) ∧
    (TreeFraction.val (RootedEstimatorBlockProgram.output
        (data A C K j delta failure z v degree depth draws)):ℝ) ≤ 8*assignmentCount A := by
  simp only [output_data A C K j hC hj hK hW hB delta failure z hz v degree depth hdegree hdepth]
  exact property_of_sameLaw _ _
    (RootedComputedEstimator.sameLaw A C K j hC hj hK hW hB delta failure z hz v)
    (fun q : ℚ => (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤ (q:ℝ) ∧ (q:ℝ) ≤ 8*assignmentCount A)
    (fun ys => RootedOracleDensity.estimateValue_range A (RootedCompletion.rowColumn A.T)
      C hC z hz K hK hW hB j hj delta failure hd0 hd1 hf (RootedCatalogGrid.gridEquiv A K v) ys) draws

theorem output_failure (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (epsilon failure : ℚ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance epsilon j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance epsilon j)))
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    uniformAverage (fun draws : Inputs A C K j (innerTolerance epsilon j) failure =>
      if (TreeFraction.val (RootedEstimatorBlockProgram.output
          (data A C K j (innerTolerance epsilon j) failure z v degree depth draws)):ℝ) <
            (1-(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
              ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
              ((j:ℝ)*C/height A C) z <
          (TreeFraction.val (RootedEstimatorBlockProgram.output
          (data A C K j (innerTolerance epsilon j) failure z v degree depth draws)):ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  let bad : ℚ → ℝ := fun q => if (q:ℝ) <
      (1-(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
        ((j:ℝ)*C/height A C) z ∨
      (1+(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
        ((j:ℝ)*C/height A C) z < (q:ℝ) then 1 else 0
  have hlaw := RootedComputedEstimator.sameLaw A C K j hC hj hK hW hB
    (innerTolerance epsilon j) failure z hz v bad
  have hdata := output_data A C K j hC hj hK hW hB (innerTolerance epsilon j)
    failure z hz v degree depth hdegree hdepth
  change uniformAverage (fun draws => bad (TreeFraction.val (RootedEstimatorBlockProgram.output
    (data A C K j (innerTolerance epsilon j) failure z v degree depth draws)))) ≤ _
  simp_rw [hdata]
  rw [hlaw]
  exact RootedOracleDensity.estimateValue_failure A (RootedCompletion.rowColumn A.T) C hC z hz
    K hK hW hB j hj epsilon failure he0 he1 hf hPL hCheeger (RootedCatalogGrid.gridEquiv A K v)

end
end ContingencyTables.RootedEstimatorExecution

end OAI
