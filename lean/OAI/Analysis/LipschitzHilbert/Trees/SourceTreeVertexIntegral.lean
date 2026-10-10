import OAI.Analysis.LipschitzHilbert.Packets.SourceTreePacketPath

namespace OAI

/-! Integrating the actual finite packet-tree vertex bound. The only
path inputs are the restricted good-path integrals, which are supplied
by the marked line and plane estimates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ] [MeasurableSpace X]

theorem source_packet_vertex_integral (μ : Measure X)
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hwint : ∀ t ∈ tops, Integrable (weight t) μ)
    (hwmeas : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ q, Measurable (fun x => value x q)) (phase : ℕ → ℂ) (a α p : ℝ)
    {Kb : ℕ} (hKb : 0 < Kb) (shift : Fin Kb) (count : ℕ) (cell : ℤ)
    (M C P : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) (hα : 1 ≤ α) (hp0 : 0 ≤ p)
    (good : Set X) (hgood : MeasurableSet good) (bad : τ → Set X)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ x ∈ good, ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (hbad : ∀ x ∈ good, (1+C^p*(M+1)^(α-1))*
      (∑ t ∈ (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).filter
        (fun t => x ∈ bad t), weight t x) ≤ 1/2)
    (hpathInt : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      Integrable ((good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x)) μ)
    (hpathBound : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      (∫ x, (good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a α p M shift t count x) x ∂μ) ≤ P*∫ x, weight t x ∂μ) :
    let V := fun x => vertexAmount
      (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell) α p
    Integrable (good.indicator V) μ ∧
      (∫ x, good.indicator V x ∂μ) ≤
        (1+C^p*(M+1)^(α-1))*(1+2*P)*
          ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
            ∫ x, weight t x ∂μ := by
  intro V
  let R := g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell
  let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell
  let cost := 1+C^p*(M+1)^(α-1)
  let f := fun t => (good\bad t).indicator (fun x => weight t x*
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M shift t count x)
  have hcost : 0 ≤ cost := by dsimp [cost]; positivity
  have hRtop {t : τ} (ht : t ∈ R) : t ∈ tops := (g.mem_cellTops _ _ _ _ _ _ _).mp ht |>.1
  have hnint : Integrable n μ := integrable_finsetSum R (fun t ht => hwint t (hRtop ht))
  have hn0 (x : X) : 0 ≤ n x := g.mass_nonnegative tops slope precision cutoff weight
    (fun t x => (hw t x).le) _ _ x
  have hfn (t : τ) (ht : t ∈ R) : Integrable (f t) μ := hpathInt t ht
  have hsumInt : Integrable (fun x => ∑ t ∈ R, f t x) μ := integrable_finsetSum R hfn
  have hVmeas : Measurable V := by
    have hn := g.measurable_mass tops slope precision cutoff weight hwmeas
      (ShiftedBlocks.endpoint shift 0) cell
    have hA := g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas
      K gap packets assigned stop value hv phase a (ShiftedBlocks.endpoint shift 0) cell
    dsimp only [V,vertexAmount]
    fun_prop
  have hV0 (x : X) : 0 ≤ V x := by
    dsimp only [V,vertexAmount]
    exact add_nonneg (hn0 x) (mul_nonneg (Real.rpow_nonneg (hn0 x) _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hpoint (x : X) : good.indicator V x ≤
      cost*good.indicator n x+2*cost*∑ t ∈ R, f t x := by
    by_cases hx : x ∈ good
    · have h := g.sourceTree_packet_vertex_bound tops slope precision cutoff weight K gap
        packets assigned stop value phase a α p shift x hp hw hKb count cell M C hM hC hα hp0
        hne hterminal (henvelope x hx) (R.filter (fun t => x ∈ bad t))
        (Finset.filter_subset ..) (hbad x hx)
      have hs : (∑ t ∈ R\R.filter (fun t => x ∈ bad t), weight t x*
          g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
            phase a α p M shift t count x) = ∑ t ∈ R, f t x := by
        rw [Finset.sdiff_eq_filter,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hb : x ∈ bad t <;> simp [f,ht,hb,hx]
      rw [hs] at h
      simpa only [Set.indicator_of_mem hx] using h
    · have hfzero (t : τ) : f t x = 0 := Set.indicator_of_notMem (fun h => hx h.1) _
      simp only [Set.indicator_of_notMem hx,hfzero,Finset.sum_const_zero,mul_zero,add_zero,le_refl]
  have hnG := hnint.indicator hgood
  have hmajor := (hnG.const_mul cost).add (hsumInt.const_mul (2*cost))
  have hVint : Integrable (good.indicator V) μ := hmajor.mono'
    (hVmeas.indicator hgood).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Set.indicator_nonneg (fun x _ => hV0 x) x)]
      exact hpoint x)
  have hnBound : (∫ x, good.indicator n x ∂μ) ≤ ∑ t ∈ R, ∫ x, weight t x ∂μ := by
    have hi := integral_mono hnG hnint (fun x => by
      by_cases hx : x ∈ good
      · simp only [Set.indicator_of_mem hx,le_refl]
      · simpa only [Set.indicator_of_notMem hx] using hn0 x)
    have heq : (∫ x, n x ∂μ) = ∑ t ∈ R, ∫ x, weight t x ∂μ :=
      integral_finsetSum R (fun t ht => hwint t (hRtop ht))
    exact hi.trans_eq heq
  have hfBound : (∫ x, ∑ t ∈ R, f t x ∂μ) ≤ P*∑ t ∈ R, ∫ x, weight t x ∂μ := by
    rw [integral_finsetSum R hfn,Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => hpathBound t ht
  refine ⟨hVint,?_⟩
  calc
    _ ≤ ∫ x, cost*good.indicator n x+2*cost*∑ t ∈ R, f t x ∂μ :=
      integral_mono hVint hmajor hpoint
    _ = cost*(∫ x, good.indicator n x ∂μ)+2*cost*(∫ x, ∑ t ∈ R, f t x ∂μ) := by
      rw [integral_add (hnG.const_mul cost) (hsumInt.const_mul (2*cost)),
        integral_const_mul,integral_const_mul]
    _ ≤ cost*(∑ t ∈ R, ∫ x, weight t x ∂μ)+
        2*cost*(P*∑ t ∈ R, ∫ x, weight t x ∂μ) := add_le_add
      (mul_le_mul_of_nonneg_left hnBound hcost)
      (mul_le_mul_of_nonneg_left hfBound (by positivity))
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
