import OAI.Analysis.LipschitzHilbert.Trees.SourceCrudeMassBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceUniformDamping
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeMomentBudget

namespace OAI

/-! The numerical thresholds are chosen before all spatial and coefficient
index types. These are the existing source estimates with their universal
type binders moved inside the eventual statement; no bound changes. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
theorem eventually_source_crude_mass_budget_types (q b : ℝ) (_hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ (X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (μ : Measure X)
      (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (U S alpha r : ℝ),
      (∀ x, 0 < n x) → (∀ᵐ x ∂μ, n x ≤ U) → Measurable n → Integrable n μ →
      Measurable A → 0 < U → 0 ≤ S → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ r →
      Real.log U ≤ 3*L → (∫ x, n x ∂μ) ≤ L^b*S →
      (∀ᵐ x ∂μ, ‖A x‖ ≤ L^q*(1+r)*n x) →
      Integrable (fun x => ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L)) μ ∧
      (∫ x, ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L) ∂μ)^(1/Real.sqrt L) ≤
        (L^(q+1)*S^(1/Real.sqrt L))*(1+r)*Real.exp (6*Real.sqrt L) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop b] with L hL hpB
  intro X κ _ _ μ n A U S alpha r hn hnU hnmeas hnint hAmeas hU hS ha ha3 hr hlog hmass hnode
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  obtain ⟨hi,hbound⟩ := source_node_normalized_moment_ae μ n A U (L^q*(1+r))
    alpha (Real.sqrt L) hn hnU hnmeas hnint hAmeas hU (by positivity) ha hp hnode
  have hUpow : U^((alpha-1)/Real.sqrt L) ≤ Real.exp (6*Real.sqrt L) :=
    by
      have hs2 := Real.sq_sqrt hL0.le
      have he : 0 ≤ (alpha-1)/Real.sqrt L := div_nonneg (by linarith) hp.le
      rw [Real.rpow_def_of_pos hU]
      apply Real.exp_le_exp.mpr
      calc
        Real.log U*((alpha-1)/Real.sqrt L) ≤ (3*L)*((alpha-1)/Real.sqrt L) :=
          mul_le_mul_of_nonneg_right hlog he
        _ ≤ (3*L)*(2/Real.sqrt L) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith) hp.le) (by positivity)
        _ = 6*Real.sqrt L := by
          field_simp
          nlinarith
  have hmasspow : (∫ x, n x ∂μ)^(1/Real.sqrt L) ≤ L*S^(1/Real.sqrt L) := by
    have h := Real.rpow_le_rpow (integral_nonneg fun x => (hn x).le) hmass
      (one_div_nonneg.mpr hp.le)
    rw [Real.mul_rpow (Real.rpow_nonneg hL0.le _) hS,← Real.rpow_mul hL0.le] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hS _)
    calc
      L^(b*(1/Real.sqrt L)) ≤ L^((1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL (by
          have hbp := (div_le_one hp).mpr hpB
          simpa only [div_eq_mul_inv,one_div,one_mul] using hbp)
      _ = L := Real.rpow_one L
  refine ⟨hi,hbound.trans ?_⟩
  calc
    _ ≤ (L^q*(1+r))*Real.exp (6*Real.sqrt L)*(L*S^(1/Real.sqrt L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hUpow (by positivity)) hmasspow
        (Real.rpow_nonneg (integral_nonneg fun x => (hn x).le) _) (by positivity)
    _ = _ := by
      rw [show L^(q+1) = L^q*L from by rw [Real.rpow_add hL0,Real.rpow_one]]
      ring

theorem eventually_source_damped_vertex_root_types (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (n : ℕ) (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
      (a eta : Fin n → ℝ) (mu P p : ℝ),
      (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → 0 ≤ mu → mu ≤ 1 → 0 ≤ P → 0 < p →
      (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤
        P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp (C*Real.sqrt L) →
      (Real.sqrt (∑ i, (eta i)^2) ≤ L^2 → (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ P) →
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint a eta) • F x‖^p ∂μ)^(1/p) ≤
        Real.exp 1*P := by
  filter_upwards [eventually_damped_vertex_bound_finite C hC] with L hL
  intro X κ _ _ n μ F a eta mu P p ha hsum hmu hmu1 hP hp hcrude hsmall
  let V := (∫ x, ‖F x‖^p ∂μ)^(1/p)
  have hV : 0 ≤ V := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hnorm : ‖(V:ℂ)‖ = V := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hV]
  have h := hL n a eta mu P (V:ℂ) ha hsum hmu hmu1 hP
    (by simpa only [hnorm] using hcrude) (by simpa only [hnorm] using hsmall)
  rw [norm_mul,hnorm] at h
  rwa [source_lp_root_smul μ F _ p hp]

namespace AngularGrid
attribute [local instance] Classical.propDecidable
theorem eventually_source_tree_vertex_moment_types (q A B Pconst : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ (μ : Measure X)
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
      (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
    ∀ (phase : ℕ → ℂ) (a alpha : ℝ), 1 ≤ alpha → alpha ≤ 3 →
    ∀ (Kb : ℕ), 0 < Kb → ∀ (shift : Fin Kb) (count : ℕ) (cell : ℤ)
      (good : Set X), MeasurableSet good → ∀ (bad : τ → Set X),
      (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty →
      (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
        ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count)) →
    let p := Real.sqrt L
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ x ∈ good, ∀ j ≤ count, ∀ c,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) c‖ ≤
        L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) c x) →
    (∀ x ∈ good, cost*
      (∑ t ∈ (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).filter
        (fun t => x ∈ bad t), weight t x) ≤ 1/2) →
    (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      Integrable ((good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a alpha p (L^A) shift t count x)) μ) →
    (∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      (∫ x, (good\bad t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          phase a alpha p (L^A) shift t count x) x ∂μ) ≤
        Pconst*L^B*cost*(∫ x, weight t x ∂μ)) →
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell
    let amp := fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell
    IntegrableOn (fun x => ‖(n x^(alpha/p-1)) • amp x‖^p) good μ ∧
      (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
        L^(2*q+1)*(∑ t ∈ g.cellTops tops slope precision cutoff
          (ShiftedBlocks.endpoint shift 0) cell, ∫ x, weight t x ∂μ)^(1/p) := by
  filter_upwards [eventually_source_vertex_constant_budget q A B (2*Pconst)
    hq hA hB (by positivity),eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro τ σ X κ _ _ μ g tops slope precision cutoff weight hp hw hwint hwmeas K gap packets assigned stop
    value hv phase a alpha ha ha3 Kb hKb shift count cell good hgood bad hne hterminal
    p cost henvelope hbad hpathInt hpathBound n amp
  have hp0 : 0 < p := Real.sqrt_pos.mpr (zero_lt_one.trans_le hL)
  have hM : 1 ≤ L^A := Real.one_le_rpow hL hA
  have hC : 0 ≤ L^q := Real.rpow_nonneg (zero_le_one.trans hL) _
  obtain ⟨hi,hbound⟩ := g.source_packet_vertex_moment μ tops slope precision cutoff weight hp hw
    hwint hwmeas K gap packets assigned stop value hv phase a alpha p hKb shift count cell
    (L^A) (L^q) (Pconst*L^B*cost) hM hC ha hp0 good hgood bad hne hterminal
    henvelope hbad hpathInt hpathBound
  let S := ∑ t ∈ g.cellTops tops slope precision cutoff
    (ShiftedBlocks.endpoint shift 0) cell, ∫ x, weight t x ∂μ
  have hS : 0 ≤ S := Finset.sum_nonneg fun t _ => integral_nonneg fun x => (hw t x).le
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have heq : cost*(1+2*(Pconst*L^B*cost)) = cost*(1+(2*Pconst)*L^B*cost) := by ring
  have hbudget' : (cost*(1+(2*Pconst)*L^B*cost))^(1/p) ≤ L^(2*q+1) :=
    hbudget alpha ha ha3
  refine ⟨hi,?_⟩
  change (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤ L^(2*q+1)*S^(1/p)
  change (∫ x in good, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤
    (cost*(1+2*(Pconst*L^B*cost))*S)^(1/p) at hbound
  rw [heq,Real.mul_rpow (mul_nonneg hcost (by positivity)) hS] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hbudget' (Real.rpow_nonneg hS _))

end AngularGrid
end LipschitzHilbert

end

end OAI
