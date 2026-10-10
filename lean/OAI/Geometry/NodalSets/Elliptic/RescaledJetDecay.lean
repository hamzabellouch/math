import OAI.Geometry.NodalSets.Elliptic.MainAmplitude
import OAI.Geometry.NodalSets.Elliptic.RescaledHigherJets
import OAI.Geometry.NodalSets.Elliptic.RescaledPhase

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

omit [CompactSpace T] in
lemma phase_smoothOn_target (t : T × Fin 3) :
    ContDiffOn ℝ ∞ (b.phase t) (b.F t).target :=
  (reval_contDiff _).comp_contDiffOn (b.chart_domain t).2.2

omit [CompactSpace T] in
lemma amplitude_smoothOn_target (N : ℝ) (t : T × Fin 3) :
    ContDiffOn ℝ ∞ (b.amplitude N t) (b.F t).target :=
  (finiteAmplitude_contDiff _ _ _).comp_contDiffOn (b.chart_domain t).2.2

theorem uniform_rescaled_factor_jets (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (d0 : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ t x s, 1 ≤ s →
      sourceEuclideanNorm (x-y t.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      ∀ v : Coord, ‖v‖ ≤ R →
      let E := rescaledPhaseDefect (b.phase t)
        (frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))) n s x
      let A := rescaledAmplitudeRatio (b.amplitude n t) n s x
      ContDiffAt ℝ ∞ E v ∧ ContDiffAt ℝ ∞ A v ∧
      ∀ k, k ≤ d0 → ‖iteratedFDeriv ℝ k E v‖ ≤ e ∧
        ‖iteratedFDeriv ℝ k (fun z ↦ A z-1) v‖ ≤ e := by
  obtain ⟨delta,hd,C,hC,D,hD,hb⟩ := b.uniform_spatial_bounds hg hp hy d0
  obtain ⟨da,hda,Ca,hCa,Da,hDa,hab⟩ := b.uniform_amplitude_bounds hg hp hy
  filter_upwards [b.uniform_rescaled_phase_first hg hp hS hy hp0 R hR e he,
    b.uniform_main_amplitude_ratio hg hp hy R e he,eventually_shifted_main_distance R,
    eventually_nat_frequency (main_scale_eventually 2 1 (min delta da) (lt_min hd hda)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2*C/e))]
    with n hfirst har hshift hn hlarge
  intro t x s hs hnear v hv
  have hN0 : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hn.1
  have hr : 0 < (n:ℝ)^(-5/12:ℝ) := Real.rpow_pos_of_pos hN0 _
  have hx := (norm_le_sourceEuclideanNorm _).trans hnear
  have hz := hshift s hs x (y t.1) v hv hnear
  have hzb := hb t _ (hz.trans (hn.2.1.trans (min_le_left _ _)))
  have hxa : ‖x-y t.1‖ ≤ da := by linarith [hn.2.1,min_le_right delta da]
  have hax := (hab t x hxa).2.2.2 n hn.1
  have hce : 2*C/(n:ℝ) ≤ e := (div_le_iff₀ hN0).mpr (by
    have := (div_le_iff₀ he).mp hlarge
    nlinarith)
  let E := rescaledPhaseDefect (b.phase t)
    (frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))) n s x
  let A := rescaledAmplitudeRatio (b.amplitude n t) n s x
  have hEs : ContDiffAt ℝ ∞ E v := rescaledPhaseDefect_smooth _ _ _ _ _ _ hzb.2.1
  have hAs : ContDiffAt ℝ ∞ A v := by
    dsimp [A,rescaledAmplitudeRatio]
    exact ((hzb.2.2.1 n).comp v (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt).div_const _
  refine ⟨hEs,hAs,?_⟩
  intro k hk
  constructor
  · by_cases hk0 : k = 0
    · subst k
      simpa only [norm_iteratedFDeriv_zero] using (hfirst t x s hs hnear v hv).1
    by_cases hk1 : k = 1
    · subst k
      simpa only [norm_iteratedFDeriv_one] using (hfirst t x s hs hnear v hv).2
    have hh := rescaledPhaseDefect_high_bound (b.F t).open_target (b.phase t)
      (b.phase_smoothOn_target t)
      (frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))) hn.1 hs x v hzb.1 (by omega : 2 ≤ k) hC.le
      (hzb.2.2.2.1 k hk)
    exact hh.trans ((div_le_div_of_nonneg_right (by linarith : C ≤ 2*C) hN0.le).trans hce)
  · by_cases hk0 : k = 0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,rescaledAmplitudeRatio] using (har t x s hs hnear v hv).2.1
    have hkf : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
    change ‖iteratedFDeriv ℝ k (A - fun _ ↦ 1) v‖ ≤ e
    rw [iteratedFDeriv_sub_apply (hAs.of_le hkf) (contDiffAt_const.of_le hkf),
      iteratedFDeriv_const_of_ne hk0]
    simp only [Pi.zero_apply,sub_zero]
    exact (rescaledAmplitudeRatio_high_bound (b.F t).open_target (b.amplitude n t)
      (b.amplitude_smoothOn_target n t) hn.1 hs x v hzb.1 hax.2.2.1
      (by omega : 1 ≤ k) hC.le (hzb.2.2.2.2.1 n hn.1 k hk)).trans hce

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
