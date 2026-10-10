import OAI.Analysis.CircleDomains.Topology.CircleCovectors
import OAI.Analysis.CircleDomains.Rigidity.MaskedMetric

namespace OAI

/-!
# Metric selection for local covectors

Periodic coordinates need not have a global scalar potential. The Gram
argument applies to their smooth covector fields, retaining the spherical
metric near a closed core and near infinity, and realizing masked fields
by smooth extensions.
-/

open Set Filter MeasureTheory Finset Metric
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def fieldEnergy (v : (ℝ × ℝ) → ℝ × ℝ) (g : (ℝ × ℝ) → PlanarMetric) (z : ℝ × ℝ) : ℝ :=
  covectorEnergy ![(v z).1, (v z).2] (g z)

def fieldGram (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (n : ℕ) (z : ℝ × ℝ) : PlanarMetric :=
  gramTensor (fun i => (v i z).1) (fun i => (v i z).2) n

def fieldWedges (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  covectorWedges (fun i => (v i z).1) (fun i => (v i z).2) n

theorem continuousOn_fieldEnergy
    {Ω : Set (ℝ × ℝ)} {v : (ℝ × ℝ) → ℝ × ℝ} (hv : ContinuousOn v Ω)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    ContinuousOn (fieldEnergy v g) Ω := by
  have hw : ContinuousOn (fun z => ![(v z).1, (v z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hv.fst
    · exact hv.snd
  have hA : ContinuousOn (fun z => Matrix.vecMulVec ![(v z).1, (v z).2]
      ![(v z).1, (v z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (continuousOn_pi.mp hw i).mul (continuousOn_pi.mp hw j)
  change ContinuousOn (fun z => covectorEnergy ![(v z).1, (v z).2] (g z)) Ω
  simpa only [covectorEnergy_eq_matrixEnergy] using
    continuousOn_matrixEnergy_local hA hg.continuousOn (fun z _ => hPD z)

theorem integral_fieldGram_eq_sum
    {Q K : Set (ℝ × ℝ)} (hQ : IsCompact Q)
    (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (hv : ∀ i, Continuous (v i)) (n : ℕ)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    (∫ z in Q \ K, matrixEnergy (fieldGram v n z) (g z)) =
      ∑ i ∈ range n, ∫ z in Q \ K, fieldEnergy (v i) g z := by
  simp only [fieldGram, gramEnergy_eq_sum_covectorEnergy]
  exact integral_finsetSum _ (fun i _ =>
    ((continuousOn_fieldEnergy (hv i).continuousOn hg hPD).integrableOn_compact hQ).mono_set sdiff_subset)

/-- The spherical Gram metric construction does not require exactness
of the covectors and therefore applies to periodic differentials. -/
theorem exists_spherical_metric_for_covectors
    (v : ℕ → (ℝ × ℝ) → ℝ × ℝ) (n : ℕ) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    {Q K : Set (ℝ × ℝ)} (hQ : IsCompact Q) (hK : IsClosed K) {ε : ℝ}
    (hε : (∫ z in Q \ K, 2 * fieldWedges v n z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∫ z in Q \ K, matrixEnergy (fieldGram v n z) (g z)) < ε := by
  obtain ⟨R, hR, hQR⟩ := hQ.isBounded.exists_pos_norm_lt
  have hQB : Q ⊆ ball 0 R := fun z hz => by
    simpa only [mem_ball, dist_zero_right] using hQR z hz
  let L := K ∩ closedBall 0 R
  have hL : IsCompact L := (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset
    (hK.inter isClosed_closedBall) inter_subset_right
  have hdiff : Q \ L = Q \ K := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, fun hzK => hz.2 ⟨hzK, ball_subset_closedBall (hQB hz.1)⟩⟩
    · exact fun hz => ⟨hz.1, fun hzL => hz.2 hzL.1⟩
  obtain ⟨τ, N, g₀, _, _, _, _, hg₀, hPD₀, hcore, _, henergy⟩ :=
    exists_smooth_core_gramMetric (fun i z => (v i z).1) (fun i z => (v i z).2) n
      (fun i => (hv i).fst) (fun i => (hv i).snd) hL hQ.isBounded
      hQ.isClosed.measurableSet isOpen_univ (subset_univ _) (hdiff.symm ▸ hε)
  obtain ⟨ψ, hzero, hone, hψrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ × ℝ)) isOpen_ball.isClosed_compl hQ.isClosed
      (disjoint_compl_left_iff_subset.mpr hQB) (n := (⊤ : ℕ∞))
  have hψ : ContDiff ℝ ∞ (ψ : (ℝ × ℝ) → ℝ) := contMDiff_iff_contDiff.mp ψ.contMDiff
  let b : (ℝ × ℝ) → PlanarMetric := fun z => blendMetric (g₀ z) (ψ z)
  have hb : ContDiff ℝ ∞ b :=
    ((contDiff_const.sub hψ).smul contDiff_const).add (hψ.smul hg₀)
  have hbPD (z : ℝ × ℝ) : (b z).PosDef := blendMetric_posDef (hPD₀ z) (hψrange z)
  have heqQ {z : ℝ × ℝ} (hz : z ∈ Q) : b z = g₀ z := by
    dsimp only [b]
    rw [hone.self_of_nhdsSet z hz, blendMetric_one]
  have hbcore : ∀ᶠ z in 𝓝ˢ K, b z = 1 := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro z hz
    by_cases hzB : z ∈ closedBall 0 R
    · filter_upwards [hcore.filter_mono (nhds_le_nhdsSet (show z ∈ L from ⟨hz, hzB⟩))]
        with w hw
      simp only [b, hw, blendMetric_identity]
    · have hzout : z ∈ (ball 0 R)ᶜ := fun hh => hzB (ball_subset_closedBall hh)
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hzout)] with w hw
      simp only [b, hw, blendMetric_zero]
  refine ⟨R, fun z => sphericalMetricFactor z • b z, hR,
    contDiff_sphericalMetricFactor.smul hb,
    fun z => (hbPD z).smul (sphericalMetricFactor_pos z), ?_, ?_, ?_⟩
  · filter_upwards [hbcore] with z hz
    rw [hz]
  · intro z hz
    have hzout : z ∈ (ball 0 R)ᶜ := fun hh => hz (ball_subset_closedBall hh)
    simp only [b, hzero.self_of_nhdsSet z hzout, blendMetric_zero]
  · rw [hdiff] at henergy
    have heq : (∫ z in Q \ K, matrixEnergy (fieldGram v n z)
        (sphericalMetricFactor z • b z)) =
        ∫ z in Q \ K, matrixEnergy (fieldGram v n z) (g₀ z) := by
      apply setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.measurableSet)
      intro z hz
      change matrixEnergy (fieldGram v n z) (sphericalMetricFactor z • b z) =
        matrixEnergy (fieldGram v n z) (g₀ z)
      rw [matrixEnergy_pos_smul _ (hbPD z) (sphericalMetricFactor_pos z), heqQ hz.1]
    exact heq.trans_lt henergy

/-- Extend a local covector field across the inactive side of a mask.
No global scalar primitive is introduced. -/
theorem exists_smooth_masked_covector
    {Ω Q K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {v : (ℝ × ℝ) → ℝ × ℝ} (hv : ContDiffOn ℝ ∞ v (Ω ∩ interior M)) :
    ∃ V : (ℝ × ℝ) → ℝ × ℝ, ContDiff ℝ ∞ V ∧
      ∀ z ∈ Q \ K, V z = M.indicator v z := by
  let A := (Q ∩ (interior K)ᶜ) ∩ M
  have hA : IsClosed A := (hQ.isClosed.inter isOpen_interior.isClosed_compl).inter hM
  have hAU : A ⊆ Ω ∩ interior M := by
    intro z hz
    exact ⟨hQΩ hz.1.1, (mem_interior_iff_notMem_frontier hz.2).mpr
      (fun hb => hz.1.2 (hboundary hb))⟩
  obtain ⟨vx, hvx, hex, hzx⟩ := exists_smooth_collar_extension
    (hΩ.inter isOpen_interior) hA hAU hv.fst 0
  obtain ⟨vy, hvy, hey, hzy⟩ := exists_smooth_collar_extension
    (hΩ.inter isOpen_interior) hA hAU hv.snd 0
  refine ⟨fun z => (vx z, vy z), hvx.prodMk hvy, ?_⟩
  intro z hz
  change (vx z, vy z) = M.indicator v z
  by_cases hzM : z ∈ M
  · have hzA : z ∈ A := ⟨⟨hz.1, fun hi => hz.2 (interior_subset hi)⟩, hzM⟩
    rw [indicator_of_mem hzM, hex.self_of_nhdsSet hzA, hey.self_of_nhdsSet hzA]
  · have hzU : z ∉ Ω ∩ interior M := fun h => hzM (interior_subset h.2)
    simp only [indicator_of_notMem hzM, hzx z hzU, hzy z hzU, Prod.mk_zero_zero]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
