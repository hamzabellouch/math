import OAI.Geometry.SurfaceImmersion.Correction.CoordinateModelGerm
import OAI.Geometry.SurfaceImmersion.Whitney.SupportedRuledInterior
import OAI.Geometry.SurfaceImmersion.Atlas.IntervalInteriorCutoff

namespace OAI

/-! A supported replacement on the actual surface makes any prescribed
compact inner subarc ruled, preserving all singularities and endpoint germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.surface_ruled_interior (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {c d : ℝ} (hac : A.arc.start < c) (hdb : d < A.arc.finish) :
    ∃ (g : M → ProjectionTarget 3) (K : Set M) (G : Base → ProjectionTarget 3),
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧ IsCompact K ∧ K ⊆ S.chart.source ∧
      ContDiff ℝ ∞ G ∧ EqOn G (g ∘ S.chart.symm) S.domain ∧
      (∀ t, G (crosscapAxis t) = S.model (crosscapAxis t) ∧
        fderiv ℝ G (crosscapAxis t) = fderiv ℝ S.model (crosscapAxis t) ∧
        axisDirectionJet G (crosscapAxis t) = axisDirectionJet S.model (crosscapAxis t)) ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      (∀ x ∉ K, g =ᶠ[𝓝 x] f) ∧ g =ᶠ[𝓝 p] f ∧ g =ᶠ[𝓝 q] f ∧
      ∀ t ∈ Icc c d, G =ᶠ[𝓝 (crosscapAxis t)] transverseRuling S.model ∧
        g =ᶠ[𝓝 (A.arc.curve t)] (transverseRuling S.model) ∘ S.chart := by
  obtain ⟨η,hη,hc,hs,h1⟩ := interval_interior_cutoff hac hdb
  obtain ⟨Q,hQ,hQc,hQD,_hb,hflat,hrel,hruled,hfixed⟩ :=
    S.supported_ruled_interior hη hc hs (by norm_num : (0 : ℝ) < 1)
  obtain ⟨g,hg,hreg,hout,hin⟩ := coordinate_regular_replacement S.chart
    S.chart_smooth S.inverse_smooth hf hQ hQc S.domain_open S.domain_target hQD
    S.model_eq (fun x _ => hrel x)
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish,
      A.arc.curve t ∈ S.chart.source ∧ S.chart (A.arc.curve t) = crosscapAxis t := by
    intro t ht
    exact ⟨(S.axis t ht).1,(S.axis t ht).2.trans (crosscapAxis_apply t).symm⟩
  have hdom : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ S.domain := by
    intro t ht
    rw [crosscapAxis_apply]
    apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
    constructor <;> linarith [ht.1,ht.2,S.width_pos]
  have hgerm : ∀ t ∈ Icc A.arc.start A.arc.finish,
      g =ᶠ[𝓝 (A.arc.curve t)] (S.model+Q) ∘ S.chart := by
    intro t ht
    apply hin _ (haxis t ht).1
    rw [(haxis t ht).2]
    exact hdom t ht
  have hfix : ∀ t ∈ Icc A.arc.start A.arc.finish, t ∉ tsupport η →
      g =ᶠ[𝓝 (A.arc.curve t)] f := by
    intro t ht hn
    have he := hfixed t hn
    rw [← (haxis t ht).2] at he
    exact (hgerm t ht).trans ((coordinate_replacement_germ S.chart (haxis t ht).1 he).trans
      (coordinate_model_germ S.chart S.domain_open S.model_eq (haxis t ht).1
        ((haxis t ht).2 ▸ hdom t ht)))
  let K := S.chart.symm '' tsupport Q
  have hK : IsCompact K := hQc.image_of_continuousOn
    (S.chart.continuousOn_symm.mono (hQD.trans S.domain_target))
  have hmodel : EqOn (S.model+Q) (g ∘ S.chart.symm) S.domain := by
    intro x hx
    have hxt := S.domain_target hx
    have he := (hin (S.chart.symm x) (S.chart.map_target hxt) (by rwa [S.chart.right_inv hxt])).self_of_nhds
    simpa only [Function.comp_apply,S.chart.right_inv hxt] using he.symm
  have hjets : ∀ t, (S.model+Q) (crosscapAxis t) = S.model (crosscapAxis t) ∧
      fderiv ℝ (S.model+Q) (crosscapAxis t) = fderiv ℝ S.model (crosscapAxis t) ∧
      axisDirectionJet (S.model+Q) (crosscapAxis t) = axisDirectionJet S.model (crosscapAxis t) := by
    intro t
    exact ⟨by simp only [Pi.add_apply,(hflat t).1,add_zero],
      axis_flat_add_first S.model_smooth hQ (fun t => (hflat t).2) t,
      axis_flat_add_direction S.model_smooth hQ (fun t => (hflat t).2) t⟩
  refine ⟨g,K,S.model+Q,hg,hK,?_,S.model_smooth.add hQ,hmodel,hjets,hreg,hout,?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact S.chart.map_target (S.domain_target (hQD hy))
  · have he := hfix A.arc.start (left_mem_Icc.mpr A.arc.start_lt_finish.le)
      (fun ht => (hs ht).1.false)
    simpa only [A.source] using he
  · have he := hfix A.arc.finish (right_mem_Icc.mpr A.arc.start_lt_finish.le)
      (fun ht => (hs ht).2.false)
    simpa only [A.target] using he
  · intro t ht
    have htab : t ∈ Icc A.arc.start A.arc.finish :=
      ⟨hac.le.trans ht.1,ht.2.trans hdb.le⟩
    have he := hruled t (h1 t ht)
    refine ⟨he,?_⟩
    rw [← (haxis t htab).2] at he
    exact (hgerm t htab).trans (coordinate_replacement_germ S.chart (haxis t htab).1 he)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
