import OAI.NumberTheory.DukePrimeDegree.Geometry.SparseUpperRootComparison
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularRootEntropyUpper
import OAI.NumberTheory.DukePrimeDegree.Entropy.BranchingSubordinateObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.PeriodicEntropyZero

namespace OAI

/-! # Actual regular entropy upper bound

The aperiodic case uses small complete orbit sections and actual quotient
charts. The periodic case has zero entropy. Full diagonal ergodicity is
used only for that dichotomy, never as ergodicity of the selected map.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

private lemma measurableSet_aperiodic {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] {T : Y → Y} (hT : Continuous T) :
    MeasurableSet {x | ∀ k : ℕ, 0 < k → T^[k] x ≠ x} := by
  rw [ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : 0 < k
  · simpa only [hk,true_implies,Function.id_def,compl_ofPred] using
      (isClosed_eq (hT.iterate k) continuous_id).measurableSet.compl
  · simpa only [hk,false_implies,ofPred_true] using (MeasurableSet.univ : MeasurableSet (univ : Set Y))

theorem negative_diagonal_entropy_le_root_sum (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal (∑ p : allPositiveRoots (d+1),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) := by
  rcases diagonal_entropy_zero_or_aperiodic d ell hell (-1) μ with hz | hap
  · rw [hz]
    exact bot_le
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hord : StrictMono ell := by
    intro i j hij
    have hh := hgap ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
    have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp at hh
    linarith
  obtain ⟨B,r₀,H,Q,hB,hr₀,hr₀1,hH,hQ,_hheight,hinj,_hcompact,_hfiniteLevels,
      _hheightEntropy,hlift,hbound,hgood,_hstep,_hheightRefinement,hneutral,_hfactor,hbranch,_hcode⟩ :=
    exists_bounded_branching_subordinate_observation_with_lifts d ell hell hgap μ hA
      (by norm_num : (0:ℝ) < 1)
  apply negative_diagonal_entropy_le_root_sum_of_small_auxiliary d ell hell μ Q hQ
    hbound hgood hbranch
  · intro x y hy
    exact hneutral x y hy.1 hy.2
  intro ε hε
  let E : Set (X (d+1)) := {x | ∀ k : ℕ, 0 < k → T^[k] x ≠ x}
  have hE : MeasurableSet E := measurableSet_aperiodic (continuous_rightAction _)
  have hEfull : ∀ᵐ x ∂μ, x ∈ E := hap
  let r := fun m : ℕ => r₀*Real.exp (-(4*B)*(m:ℝ))
  have hr (m : ℕ) : 0 < r m := mul_pos hr₀ (Real.exp_pos _)
  have hr1 (m : ℕ) : r m ≤ 1 := by
    apply le_trans _ hr₀1
    apply mul_le_of_le_one_right hr₀.le
    exact Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (α := ℝ) m)])
  have hanti : Antitone r := by
    intro i j hij
    apply mul_le_mul_of_nonneg_left _ hr₀.le
    apply Real.exp_le_exp.mpr
    have hc : (i:ℝ) ≤ j := Nat.cast_le.mpr hij
    exact mul_le_mul_of_nonpos_left hc (by linarith)
  obtain ⟨R,hR,hRs,hsmall,hcomparison⟩ := exists_sparse_upperRoot_comparison
    ell hell hord μ hT E hE (fun x hx => hx) H hH r hr hr1 hanti hinj Q hlift hε
  have hfull : ∀ᵐ x ∂μ, ∀ y,
      (∀ k : ℕ, Q (T^[k] y)=Q (T^[k] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) →
      ∃ u : UpperRootTime (d+1), rightAction x ((completeRootChain (d+1)).word u)=y := by
    filter_upwards [hEfull,hcomparison] with x hxE hx
    exact hx hxE
  obtain ⟨F,hF,hrelative⟩ := exists_conull_future1_root_relation ell hell μ hT Q R hfull
  exact ⟨R,hR,hRs,hsmall,F,hF,hrelative⟩

end DukePrimeDegree

end

end OAI
