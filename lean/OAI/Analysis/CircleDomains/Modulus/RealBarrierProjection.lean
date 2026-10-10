import OAI.Analysis.CircleDomains.Selection.RealSequenceRetention
import OAI.Analysis.CircleDomains.Rigidity.MatchedEndChains

namespace OAI

/-!
# Projection payment for a retained real barrier

The test is specified by its actual values on two source contours and
their matched target contours. All finite-model crossings and analytic
estimates are supplied by the constructed sequence.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure RetainedRealBarrier {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ) (F : ℂ → ℂ) (l : ℕ) where
  inner : SmoothJordanCore G
  outer : SmoothJordanCore G
  inner_index : Fin inner.count
  outer_index : Fin outer.count
  value_one : ∀ z ∈ frontier (jordanInterior (inner.disk inner_index)),
    d.physical l (Complex.equivRealProdCLM z) = 1
  value_zero : ∀ z ∈ frontier (jordanInterior (outer.disk outer_index)),
    d.physical l (Complex.equivRealProdCLM z) = 0
  target_inner : ℂ ≃ₜ ℂ
  target_outer : ℂ ≃ₜ ℂ
  inner_image : extendAtInfinity F ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior (inner.disk inner_index))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior target_inner)
  outer_image : extendAtInfinity F ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior (outer.disk outer_index))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior target_outer)
  inner_side : extendAtInfinity F ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (inner.disk inner_index))) =
    (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior target_inner)
  outer_side : extendAtInfinity F ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (outer.disk outer_index))) =
    (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior target_outer)
  nested : closure (jordanInterior target_inner) ⊆ jordanInterior target_outer

theorem exists_retained_real_barrier
    (hsch : PlanarSchoenflies)
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ)
    (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    {F : ℂ → ℂ} (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (A B : SmoothJordanCore G) (i : Fin A.count) (j : Fin B.count) (l : ℕ)
    (hOne : ∀ z ∈ frontier (jordanInterior (A.disk i)),
      d.physical l (Complex.equivRealProdCLM z) = 1)
    (hZero : ∀ z ∈ frontier (jordanInterior (B.disk j)),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    (hnest : closure (jordanInterior (A.disk i)) ⊆ jordanInterior (B.disk j)) :
    Nonempty (RetainedRealBarrier d F l) := by
  obtain ⟨J, _, _, hJ, hJs⟩ := exists_matched_image_core hsch hG hconn hinf
    hF.1 hF.bijOn.injOn (by simp) A
  obtain ⟨K, _, _, hK, hKs⟩ := exists_matched_image_core hsch hG hconn hinf
    hF.1 hF.bijOn.injOn (by simp) B
  have ht := (matched_jordan_disk_subset_iff hF.bijOn.injOn
    (B.disk j) (A.disk i) (K j) (J i) (A.boundary_subset_domain i) (hJ i) (hKs j)).mp
      (image_mono hnest)
  refine ⟨{
    inner := A, outer := B, inner_index := i, outer_index := j,
    value_one := hOne, value_zero := hZero,
    target_inner := J i, target_outer := K j,
    inner_image := hJ i, outer_image := hK j,
    inner_side := hJs i, outer_side := hKs j,
    nested := ?_ }⟩
  intro z hz
  exact OnePoint.coe_injective.mem_set_image.mp (ht ⟨z, hz, rfl⟩)

theorem RealModelExhaustion.projection_payment
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    {l : ℕ} (B : RetainedRealBarrier d F l)
    {C : Set ℂ} (hC : IsCompact C) (hCB : C ⊆ jordanInterior B.target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : closure (jordanInterior B.target_outer) ⊆ ball 0 L) :
    (volume (Complex.im '' C)).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
        (∫ x in realChartDomain G,
          gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  apply M.limiting_line_payment hsard hsch harea hε r hr l hL
    (hC.image Complex.continuous_im).measurableSet
  exact M.eventually_test_crossings hsch hG r hr F hF hlim B.inner B.outer
    B.inner_index B.outer_index l B.value_one B.value_zero B.target_inner B.target_outer
    B.inner_image B.outer_image B.inner_side B.outer_side B.nested hC hCB hBL

end CircleDomainRigidity.FiniteTransfer

end

end OAI
