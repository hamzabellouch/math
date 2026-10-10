import OAI.MeasureTheory.Falconer.Graphs.GraphDerivativeBounds

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff ComplexConjugate

noncomputable def graphBinPullback (δ : ℝ) (S : Finset ℕ) (plus : Bool) (c : ℝ) :
    (Plane × ℝ) → ℂ := graphAngularPullback
      (fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ):ℂ)) plus c

noncomputable def graphConePullback (plus : Bool) (c : ℝ) : (Plane × ℝ) → ℂ :=
  graphAngularPullback (fun θ => sourceConeCircle 0 (sourceUnitDirection θ)) plus c

noncomputable def graphWeightPullback (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (p : Plane × ℝ) : ℂ := graphSourceWeight distance plus axis (angularBinCount δ) j k
      (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
        sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus))

theorem graph_bin_derivative_budget (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
      ∀ (S : Finset ℕ) (plus : Bool) (c : ℝ),
      GraphDerivativeBound n (graphBinPullback δ S plus c) C (max 1 δ⁻¹) := by
  choose A hA ha using fun j => graph_selected_bins_mixed j
  let C := ∑ j ∈ Finset.range (n+1), A j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨C,hC,?_⟩
  intro δ hδ hcap S plus c
  have hf : ContDiff ℝ ∞ (fun θ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ) :=
    ContDiff.sum (fun k _ => periodicAngularBin_contDiff _ _)
  have hp : Function.Periodic (fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ):ℂ))
      (2*Real.pi) := by
    intro θ
    apply congrArg Complex.ofReal
    exact Finset.sum_congr rfl (fun k _ => periodicAngularBin_periodic _ _ θ)
  refine ⟨fun p hp' => (graphAngularPullback_contDiffAt
    (Complex.ofRealCLM.contDiff.comp hf) hp plus c hp').contDiffWithinAt,?_⟩
  intro j hj η z hhi hz hlo
  exact (ha j δ hδ hcap S plus c η z hhi hz hlo).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun l _ => hA l) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
      (by positivity))

theorem graph_cone_derivative_budget (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (plus : Bool) (c : ℝ),
      GraphDerivativeBound n (graphConePullback plus c) C 1 := by
  apply graph_periodic_derivative_budget sourceConeCircle_angular_contDiff
  intro θ
  exact congrArg (sourceConeCircle 0) (sourceUnitDirection_periodic θ)

theorem graphWeightPullback_distance (axis δ : ℝ) (j k : ℕ) (p : Plane × ℝ) :
    graphWeightPullback true true axis δ j k p =
      (graphConePullback true (-axis) p * graphBinPullback δ {j} true (-axis) p) *
        conj (graphConePullback false (-axis) p * graphBinPullback δ {k} false (-axis) p) := by
  simp only [graphWeightPullback, graphSourceWeight, graphSourceChartAxis, ↓reduceIte, add_zero,
    graphRotatedDistanceWeight_eq, sourceConeCircle, rotatedBinSelection,
    sourceCircleRotate_comp, graphConePullback, graphBinPullback, graphAngularPullback,
    neg_zero, Finset.sum_singleton, circleAngularBin_comp,
    Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg]

theorem graphWeightPullback_product (plus : Bool) (axis δ : ℝ) (j k : ℕ)
    {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    graphWeightPullback false plus axis δ j k p =
      (graphBinPullback δ {j} true 0 p *
        graphBinPullback δ {k} false (if plus then 0 else Real.pi) p) * graphFixedSign plus p := by
  rw [graphFixedSign_eq plus hp]
  cases plus <;> simp only [graphWeightPullback, graphSourceWeight, graphSourceChartAxis,
    graphProductWeight, graphBinWeight, graphBinPullback, graphAngularPullback,
    Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton, add_zero,
    ← sub_eq_add_neg, circleAngularBin_comp, Complex.ofReal_mul]

theorem graph_source_weight_derivative_budget (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
      ∀ (distance plus : Bool) (axis : ℝ) (j k : ℕ),
      GraphDerivativeBound n (graphWeightPullback distance plus axis δ j k) C (4*max 1 δ⁻¹) := by
  obtain ⟨B,hB,hbin⟩ := graph_bin_derivative_budget n
  obtain ⟨A,hA,hcone⟩ := graph_cone_derivative_budget n
  choose S hS hs using fun plus => graph_fixed_derivative_budget
    (fun _ hp => graphFixedSign_contDiffAt plus hp) n
  let T := max (S true) (S false)
  have hT : 0 ≤ T := (hS true).trans (le_max_left _ _)
  have hsign (plus : Bool) : GraphDerivativeBound n (graphFixedSign plus) T 1 :=
    (hs plus).mono (by cases plus <;> simp [T]) hT le_rfl zero_le_one
  let C := max ((A*B)*(A*B)) ((B*B)*T)
  have hC : 0 ≤ C := (mul_nonneg (mul_nonneg hA hB) (mul_nonneg hA hB)).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro δ hδ hcap distance plus axis j k
  let D := max 1 δ⁻¹
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  cases distance
  · have hb := ((hbin δ hδ hcap {j} true 0).mul
      (hbin δ hδ hcap {k} false (if plus then 0 else Real.pi)) hB hB hD0 hD0).mul
        (hsign plus) (mul_nonneg hB hB) hT (add_nonneg hD0 hD0) zero_le_one
    have hb' := hb.mono (le_max_right _ _) hC (show D+D+1 ≤ 4*D by linarith) (by positivity)
    exact hb'.congr (fun p hp => graphWeightPullback_product plus axis δ j k hp)
  · have hb₁ := (hcone true (-axis)).mul (hbin δ hδ hcap {j} true (-axis)) hA hB zero_le_one hD0
    have hb₂ := (hcone false (-axis)).mul (hbin δ hδ hcap {k} false (-axis)) hA hB zero_le_one hD0
    have hb := hb₁.mul hb₂.conj (mul_nonneg hA hB) (mul_nonneg hA hB)
      (by positivity) (by positivity)
    have hb' := hb.mono (le_max_left _ _) hC (show (1+D)+(1+D) ≤ 4*D by linarith) (by positivity)
    apply hb'.congr
    intro p _
    have he : graphWeightPullback true plus axis δ j k p = graphWeightPullback true true axis δ j k p := rfl
    rw [he, graphWeightPullback_distance]

end PlanarFalconer

end OAI
