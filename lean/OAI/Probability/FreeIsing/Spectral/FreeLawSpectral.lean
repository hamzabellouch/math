import OAI.Probability.FreeIsing.Energy.FreeLawLocalCovariance
import OAI.Probability.FreeIsing.Trees.LawDecay

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem HasFreeIsingLaw.local_koopman_far_decay {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → IsingSpin) → ℝ)
    (hF : Measurable F) (hf : f =ᵐ[μ] fun x => F (fun i => x i))
    (hzero : ∫ x, f x ∂μ = 0) :
    ∃ N : ℕ, ∀ g : TreeAut d, N < (g.toEquiv TreeEscape.root).val.length →
      |inner ℝ f (koopmanL2 (relabel g) (hμ.measurePreserving_relabel g) f)| ≤
        ‖f‖^2 * theta^((g.toEquiv TreeEscape.root).val.length - N) := by
  let R := s.sup (fun v => v.val.length)
  have hR : ∀ i : s, i.val.val.length ≤ R := fun i =>
    Finset.le_sup (f := fun v : TreeVertex d => v.val.length) i.property
  let f0 : (TreeVertex d → IsingSpin) → ℝ := fun x => F (fun i => x i)
  have hf0 : MemLp f0 2 μ := (memLp_congr_ae hf).mp (Lp.memLp f)
  have hz : ∫ x, f0 x ∂μ = 0 := (integral_congr_ae hf).symm.trans hzero
  have hn : (∫ x, (f0 x)^2 ∂μ) = ‖f‖^2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    simp [hx, f0, pow_two]
  refine ⟨R + R, fun g hg => ?_⟩
  have hdepth : (g.symm.toEquiv TreeEscape.root).val.length =
      (g.toEquiv TreeEscape.root).val.length := TreeEscape.symm_root_depth g
  have hgz : ∫ x, f0 (relabel g x) ∂μ = 0 :=
    (hμ.integral_relabel g f0).trans hz
  have hgn : (∫ x, (f0 (relabel g x))^2 ∂μ) = ‖f‖^2 :=
    (hμ.integral_relabel g (fun x => (f0 x)^2)).trans hn
  have hgf : MemLp (fun x => f0 (relabel g x)) 2 μ :=
    hf0.comp_measurePreserving (hμ.measurePreserving_relabel g)
  have hb := hμ.abs_correlation_separated_local_blocks h0 h1
    (fun i : s => i.val) (fun i : s => i.val) R hR hR g.symm
    (hdepth ▸ hg) F F hF hF hz hgz hf0 hgf
  rw [TreeLawKoopman.inner_koopman_eq_integral_of_local μ
    hμ.measurePreserving_relabel s f F hf g]
  change |∫ x, f0 x * f0 (relabel g x) ∂μ| ≤ _
  change |∫ x, f0 x * f0 (relabel g x) ∂μ| ≤
    Real.sqrt (∫ x, (f0 x)^2 ∂μ) * Real.sqrt (∫ x, (f0 (relabel g x))^2 ∂μ) *
      theta ^ ((g.symm.toEquiv TreeEscape.root).val.length - (R + R)) at hb
  simpa only [hn, hgn, Real.sqrt_sq_eq_abs, abs_norm, ← pow_two, hdepth] using hb

theorem HasFreeIsingLaw.localCriticalDecay {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    TreeLawKoopman.LocalCriticalDecay μ hμ.measurePreserving_relabel := by
  apply TreeLawKoopman.localCriticalDecay_of_far_decay μ hμ.measurePreserving_relabel
    hd h0 hthreshold
  intro s f F hF hf hzero
  exact hμ.local_koopman_far_decay h0 h1 s f F hF hf hzero

theorem HasFreeIsingLaw.centeredAverage_norm_le_critical {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    ‖TreeLawKoopman.centeredAverage μ hμ.measurePreserving_relabel‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d :=
  TreeLawKoopman.centeredAverage_norm_le μ hμ.measurePreserving_relabel hd
    (hμ.localCriticalDecay hd h0 h1 hthreshold)

end Problem367

end

end OAI
