import OAI.Geometry.CylinderCovering.Physical.CapFiniteDefinitions
import OAI.Geometry.CylinderCovering.Physical.Finite
import OAI.Geometry.CylinderCovering.Radial.FinitePair
import OAI.Geometry.CylinderCovering.Physical.CostVariants
import OAI.Geometry.CylinderCovering.Physical.SweepTransport

namespace OAI

open Set Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace RadialPhysical
open CylinderCovering

theorem physical_family_of_sweep_cover (centered : Bool) (b eta : ℝ)
    (hb : 0 < b) (T : ℝ → ℝ) (hT : ContinuousOn T (Icc (-b) b))
    (hT0 : ∀ s ∈ Icc (-b) b, 0 ≤ T s)
    (hcover : modelBody centered b ⊆
      upperSweepOn centered b eta T (Icc (-b) b) ∪
        lowerSweepOn centered b eta T (Icc (-b) b))
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (htagU : ∀ N, RadialRiemann.IsTagged (-b) b N (tagU N))
    (htagL : ∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) :
    ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
      PhysicalFamilyConclusion centered b eta T tagU tagL C := by
  obtain ⟨U, L, hUL, hlim, hbound, hsup⟩ :=
    physical_finite centered b eta hb T hT hT0 tagU tagL htagU htagL
  refine ⟨fun N => RadialPairedSweep.join (U N) (L N), ?_⟩
  refine {
    local_properties := ?_
    covers_body := ?_
    covers_sweeps := ?_
    actual_covers_body := ?_
    triangle_limit := RadialPairedSweep.join_totalArea_tendsto U L hlim
    actual_bound := hbound
    actual_limsup := hsup }
  · intro N hN i
    simpa only [RadialPairedSweep.join_upper, RadialPairedSweep.join_lower]
      using (hUL N hN).1 i
  · intro N hN z hz
    exact RadialPairedSweep.join_covers_union (U N) (L N)
      (fun z hz => ((hUL N hN).2.1 z hz).1)
      (fun z hz => ((hUL N hN).2.2 z hz).1) z (hcover hz)
  · intro N hN
    exact RadialPairedSweep.join_covers_union (U N) (L N)
      (fun z hz => ((hUL N hN).2.1 z hz).1)
      (fun z hz => ((hUL N hN).2.2 z hz).1)
  · intro N hN z hz
    rcases hcover hz with hU | hL
    · exact Or.inl (((hUL N hN).2.1 z hU).2)
    · exact Or.inr (((hUL N hN).2.2 z hL).2)

theorem PhysicalFamilyConclusion.eventually_strict
    {centered : Bool} {b eta : ℝ} {T : ℝ → ℝ}
    {tagU tagL : (N : ℕ) → Fin N → ℝ}
    {C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder}
    (hC : PhysicalFamilyConclusion centered b eta T tagU tagL C)
    {target : ℝ} (hsave : scaledCost b eta T < target) :
    ∀ᶠ N in atTop, 0 < N ∧ TriangularCovering.totalArea (C N) < target ∧
      physicalActualCost centered b eta T N (tagU N) (tagL N) < target := by
  have hgap : 0 < (target-scaledCost b eta T)/2 := by linarith
  filter_upwards [RadialPairedSweep.eventually_strict_finite_cost C hC.triangle_limit hsave,
    hC.actual_bound ((target-scaledCost b eta T)/2) hgap] with N hN hactual
  exact ⟨hN.1, hN.2, by linarith⟩

lemma capChoice_continuous (square : Bool) (b eta beta : ℝ) :
    Continuous (capChoice square b eta beta) := by
  cases square <;> unfold capChoice <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · unfold linearCap capPolynomial
    fun_prop
  · unfold squareCap capPolynomial
    fun_prop

lemma capChoice_nonneg (square : Bool) (b eta beta s : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ capChoice square b eta beta s := by
  cases square
  · simp only [capChoice, Bool.false_eq_true, ite_false]
    unfold linearCap capPolynomial
    positivity
  · simp only [capChoice, ite_true]
    exact Real.sqrt_nonneg _

lemma physicalModelCap_continuous (centered square : Bool) (b eta beta : ℝ) :
    Continuous (physicalModelCap centered square b eta beta) := by
  cases centered
  · exact capChoice_continuous square b eta beta
  · exact continuous_const.mul (capChoice_continuous square b eta beta)

lemma physicalModelCap_nonneg (centered square : Bool) (b eta beta s : ℝ)
    (hbeta : 0 ≤ beta) : 0 ≤ physicalModelCap centered square b eta beta s := by
  cases centered
  · exact capChoice_nonneg square b eta beta s hbeta
  · exact mul_nonneg (by norm_num) (capChoice_nonneg square b eta beta s hbeta)

lemma centered_linearCap_eq_double (b eta beta : ℝ) :
    centeredLinearCap b eta beta = fun s => 2*linearCap b eta beta s := by
  funext s
  unfold centeredLinearCap linearCap capPolynomial
  ring

theorem eventually_physicalModelCap_covers (centered square : Bool)
    {b beta : ℝ} (hb : 0 < b) (hbeta : 0 < beta) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      modelBody centered b ⊆
        upperSweepOn centered b eta (physicalModelCap centered square b eta beta) (Icc (-b) b) ∪
        lowerSweepOn centered b eta (physicalModelCap centered square b eta beta) (Icc (-b) b) := by
  cases centered <;> cases square
  · simpa only [physicalModelCap, capChoice, Bool.false_eq_true, ite_false] using
      eventually_halfheight_linear_covers hb hbeta
  · simpa only [physicalModelCap, capChoice, Bool.false_eq_true, ite_false, ite_true] using
      eventually_halfheight_square_covers hb hbeta
  · simpa only [physicalModelCap, capChoice, Bool.false_eq_true, ite_false, ite_true,
      centered_linearCap_eq_double] using eventually_centered_linear_covers hb hbeta
  · simpa only [physicalModelCap, capChoice, ite_true] using
      eventually_centered_square_covers hb hbeta

private lemma scaledCost_double (b eta : ℝ) (T : ℝ → ℝ) :
    scaledCost b eta (fun s => 2*T s) = 4*scaledCost b eta T := by
  unfold scaledCost
  have hd : (fun s => scaledDensity b eta (fun s => 2*T s) s) =
      fun s => 4*scaledDensity b eta T s := by
    funext s
    unfold scaledDensity
    ring
  rw [hd, intervalIntegral.integral_const_mul]
  ring

theorem eventually_physicalModelCap_strict (centered square : Bool)
    {b beta : ℝ} (hb : 0 < b) (hbeta : 0 < beta) (hbetamax : beta < 1/60) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      scaledCost b eta (physicalModelCap centered square b eta beta) <
        physicalHalfReference centered b := by
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] 0,
      scaledCost b eta (capChoice square b eta beta) < b*height b/2 := by
    cases square
    · exact scaled_linear_strict hb hbeta hbetamax
    · exact scaled_square_strict hb hbeta hbetamax
  cases centered
  · exact hhalf
  · filter_upwards [hhalf] with eta heta
    change scaledCost b eta (fun s => 2*capChoice square b eta beta s) < 2*b*height b
    rw [scaledCost_double]
    linarith

theorem physical_cap_coverage : PhysicalCapCoverageStatement := by
  intro centered square b beta hb hbeta
  filter_upwards [eventually_physicalModelCap_covers centered square hb hbeta] with eta hcover
  intro tagU tagL htagU htagL
  exact physical_family_of_sweep_cover centered b eta hb
    (physicalModelCap centered square b eta beta)
    (physicalModelCap_continuous centered square b eta beta).continuousOn
    (fun s _ => physicalModelCap_nonneg centered square b eta beta s hbeta.le)
    hcover tagU tagL htagU htagL

theorem physical_cap_finite : PhysicalCapFiniteStatement := by
  intro centered square b beta hb hbeta hbetamax
  filter_upwards [eventually_physicalModelCap_covers centered square hb hbeta,
    eventually_physicalModelCap_strict centered square hb hbeta hbetamax] with eta hcover hcost
  intro tagU tagL htagU htagL
  obtain ⟨C, hC⟩ := physical_family_of_sweep_cover centered b eta hb
    (physicalModelCap centered square b eta beta)
    (physicalModelCap_continuous centered square b eta beta).continuousOn
    (fun s _ => physicalModelCap_nonneg centered square b eta beta s hbeta.le)
    hcover tagU tagL htagU htagL
  exact ⟨C, hC, hC.eventually_strict hcost⟩

end RadialPhysical

end

end OAI
