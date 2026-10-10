import OAI.Analysis.KadisonKastler.ScalarWeakLimit

namespace OAI

/-! # Weak closure of the nonsingular pullback graph

Pullback need not be a bounded operator on L2. Its graph is nonetheless
closed: norm-convergent pairs have subsequences converging pointwise, and
nonsingularity transports the first almost-everywhere limit. Linearity then
makes this graph weakly closed. This suffices for the boundary averages.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)

def scalarL2PullbackGraph : Set (Lp ℂ 2 μ × Lp ℂ 2 μ) :=
  {p | ∀ᵐ x ∂μ, p.2 x = p.1 (T x)}

include hT in
theorem isClosed_scalarL2PullbackGraph : IsClosed (scalarL2PullbackGraph (μ := μ) T) := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns, hns, hn⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (continuous_fst.tendsto g |>.comp hfg)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hm⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      ((continuous_snd.tendsto g |>.comp hfg).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hf, hT.ae hn, hm] with x hx hnx hmx
  apply tendsto_nhds_unique hmx
  have he : (fun k => (f (ns (ms k))).2 x) = fun k => (f (ns (ms k))).1 (T x) := by
    funext k
    exact hx (ns (ms k))
  change Tendsto (fun k => (f (ns (ms k))).2 x) atTop (𝓝 (g.1 (T x)))
  rw [he]
  exact hnx.comp hms.tendsto_atTop

include hT in
theorem convex_scalarL2PullbackGraph : Convex ℝ (scalarL2PullbackGraph (μ := μ) T) := by
  intro f hf g hg a b _ha _hb _hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f.2) (b • g.2),
    Lp.coeFn_smul a f.2, Lp.coeFn_smul b g.2,
    hT.ae (Lp.coeFn_add (a • f.1) (b • g.1)),
    hT.ae (Lp.coeFn_smul a f.1), hT.ae (Lp.coeFn_smul b g.1)]
    with x hfx hgx hadd hfa hgb htadd htfa htgb
  change (a • f.2 + b • g.2) x = (a • f.1 + b • g.1) (T x)
  simp only [Pi.add_apply, Pi.smul_apply] at hadd hfa hgb htadd htfa htgb
  rw [hadd, hfa, hgb, htadd, htfa, htgb, hfx, hgx]

include hT in
theorem scalarL2PullbackGraph_of_inner_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (f g : ι → Lp ℂ 2 μ) (a b : Lp ℂ 2 μ)
    (hfg : ∀ i, ∀ᵐ x ∂μ, g i x = f i (T x))
    (hf : ∀ y, Tendsto (fun i => inner ℂ y (f i)) l (𝓝 (inner ℂ y a)))
    (hg : ∀ y, Tendsto (fun i => inner ℂ y (g i)) l (𝓝 (inner ℂ y b))) :
    ∀ᵐ x ∂μ, b x = a (T x) :=
  mem_closed_convex_of_pair_inner_tendsto (isClosed_scalarL2PullbackGraph T hT)
    (convex_scalarL2PullbackGraph T hT) f g a b hfg hf hg

variable [IsProbabilityMeasure μ]

theorem scalarInfinityPullback_of_weak_limits
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (f g : ι → ScalarLInfinity μ) (a b : ScalarLInfinity μ)
    (hfg : ∀ i, scalarInfinityPullback T hT (f i) = g i)
    (hf : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 a))))
    (hg : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (g i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 b)))) :
    scalarInfinityPullback T hT a = b := by
  have hgraph (i : ι) : ∀ᵐ x ∂μ,
      scalarInfinityToL2 (g i) x = scalarInfinityToL2 (f i) (T x) := by
    have he := scalarInfinityPullback_ae T hT (f i)
    rw [hfg i] at he
    filter_upwards [scalarInfinityToL2_ae (g i), hT.ae (scalarInfinityToL2_ae (f i)), he]
      with x hgx hfx hex
    exact hgx.trans (hex.trans hfx.symm)
  have he := scalarL2PullbackGraph_of_inner_tendsto T hT
    (fun i => scalarInfinityToL2 (f i)) (fun i => scalarInfinityToL2 (g i))
    (scalarInfinityToL2 a) (scalarInfinityToL2 b) hgraph hf hg
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae T hT a, scalarInfinityToL2_ae b,
    hT.ae (scalarInfinityToL2_ae a), he] with x hax hbx htax hex
  exact hax.trans (htax.symm.trans (hex.symm.trans hbx))

end

end KadisonKastler

end OAI
