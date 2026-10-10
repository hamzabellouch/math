import Mathlib
import OAI.Geometry.CubicTorus.Regularity.SurfaceH1Tangency

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma restricted_L2_extension {F : Type*} [NormedAddCommGroup F]
    {S : Set Plane} (hS : MeasurableSet S) (u : Lp F 2 (volume.restrict S)) :
    ∃ U : Lp F 2 (volume : Measure Plane),
      (U : Plane → F) =ᵐ[volume.restrict S] (u : Plane → F) := by
  have hm : MemLp (S.indicator (u : Plane → F)) 2 (volume : Measure Plane) :=
    (memLp_indicator_iff_restrict hS).mpr (Lp.memLp u)
  refine ⟨hm.toLp _, ?_⟩
  filter_upwards [ae_restrict_of_ae hm.coeFn_toLp, ae_restrict_mem hS] with y hy hys
  exact hy.trans (indicator_of_mem hys _)

theorem PlaneWeakGradientOn.cmc_classical_near
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (G y))) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    HolderJet 1 f 0 ∧ LinearCMCEquationNear f p (fun _ => 0) := by
  obtain ⟨U,hU⟩ := restricted_L2_extension measurableSet_ball u
  obtain ⟨V,hV⟩ := restricted_L2_extension measurableSet_ball G
  have hUV := hw.toWeakGradient.local_congr measurableSet_ball hU hV
  have hVD : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (V y))) = 0 := by
    intro ψ hψ hc hs
    rw [← hd ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hV] with y hy
    by_cases hys : y ∈ Metric.ball (0 : Plane) R
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (hs hh))]
      rfl
  obtain ⟨H,s,K,β,hs,hsR,hK,hβ,hβ1,hHc,hHe,hHp⟩ :=
    cmc_linearized_holder_gradient hp hpb hR hα hα1 hD hHolder U V hUV hVD
  have hsub : Metric.ball (0 : Plane) s ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hfu' : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (u : Plane → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hsub hfu
  have hU' : (U : Plane → ℝ) =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (u : Plane → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hsub hU
  have hwf : PlaneWeakGradient (Metric.ball 0 s) f H :=
    (hUV.mono hsub).local_congr measurableSet_ball
      (hfu'.trans hU'.symm) hHe
  obtain ⟨hfc,hfd⟩ := hwf.holder_C1 hs (hf.mono hsub) hHc hHp
  have hdr (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) (s / 4)) :
      gradient f y = H y := by
    have ht := hwf.continuous_hasFDerivAt hs (hf.mono hsub) hHc hy
    simp only [gradient, ht.fderiv, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨⟨hfc.contDiffAt (Metric.ball_mem_nhds _ (by positivity)),
    s / 4, β, K, by positivity, hβ, hβ1, hK, hfd⟩, s / 4, by positivity, ?_⟩
  intro ψ hψ hc ht
  have hss : Metric.ball (0 : Plane) (s/4) ⊆ Metric.ball 0 s :=
    Metric.ball_subset_ball (by linarith)
  rw [← hVD ψ hψ hc (ht.trans (hss.trans hsub))]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hHe] with y hy
  by_cases hys : y ∈ Metric.ball (0 : Plane) (s/4)
  · simp only [hdr y hys, hy (hss hys), sub_zero]
  · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (ht hh))]
    rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradientOn.cmc_smoothAt
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (G y))) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) f 0 := by
  obtain ⟨hfc,heq⟩ := hw.cmc_classical_near hp hpb hR hα hα1 hD hHolder hd hf hfu
  apply contDiffAt_infty.mpr
  intro n
  have hpJ : HolderJet (n+1) p 0 := ContDiffAt.holderJet (hpc.of_le (by
    exact_mod_cast (show (n+2 : ℕ∞) ≤ ⊤ from le_top)))
  exact (heq.schauder hpb hfc hpJ (HolderJet.const 0)).contDiffAt.of_le (by norm_cast; omega)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_memLp_top_ball {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (hf : Continuous f) (R : ℝ) :
    MemLp f ∞ (volume.restrict (Metric.ball (0 : Plane) R)) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Plane) R).exists_bound_of_continuousOn hf.continuousOn
  exact memLp_top_of_bound hf.aestronglyMeasurable C
    ((ae_restrict_mem measurableSet_ball).mono fun y hy => hC y (Metric.ball_subset_closedBall hy))

theorem PlaneWeakGradientOn.weighted_L2 {R : ℝ}
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ∃ (v : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R)))
      (J : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))),
      (v =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] fun y => q y * u y) ∧
      (J =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
        fun y => q y • G y + u y • gradient q y) ∧
      PlaneWeakGradientOn (Metric.ball 0 R) v J := by
  have hqL := continuous_memLp_top_ball hq.continuous R
  have hdL := continuous_memLp_top_ball (plane_gradient_contDiff hq).continuous R
  have hv : MemLp (fun y => q y * u y) 2 (volume.restrict (Metric.ball (0 : Plane) R)) :=
    hqL.mul (Lp.memLp u)
  have hJ : MemLp (fun y => q y • G y + u y • gradient q y) 2
      (volume.restrict (Metric.ball (0 : Plane) R)) :=
    (hqL.smul (Lp.memLp G)).add ((Lp.memLp u).smul hdL)
  refine ⟨hv.toLp _,hJ.toLp _,hv.coeFn_toLp,hJ.coeFn_toLp,?_⟩
  exact (hw.mul_smooth hq).congr hv.coeFn_toLp hJ.coeFn_toLp

theorem PlaneWeakGradientOn.jacobi_smoothAt
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpe : ∀ y ∈ Metric.ball (0 : Plane) R, p y = gradient g y)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hJ : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
      (∫ y in Metric.ball (0 : Plane) R, (cmcWeight (gradient g y))^2 *
        ⟪G y, cmcJacobian (gradient g y) (gradient ψ y)⟫ -
        cmcWeight (gradient g y) * graphSquaredSecondFundamentalForm g y * u y * ψ y) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) f 0 := by
  let q : Plane → ℝ := fun y => cmcWeight (gradient g y)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  obtain ⟨v,J,hv,hJv,hwJ⟩ := hw.weighted_L2 hq
  have hde := weak_cmc_graph_jacobi_linearization Metric.isOpen_ball hw hg hlin hJ
  have hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (J y))) = 0 := by
    intro ψ hψ hc hs
    rw [← hde ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hJv] with y hy
    by_cases hys : y ∈ Metric.ball (0 : Plane) R
    · rw [hy hys, hpe y hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (hs hh))]
      rfl
  have hvf : (fun y => q y * f y) =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      (v : Plane → ℝ) := by
    filter_upwards [hv,hfu] with y hyv hyf
    rw [hyv,hyf]
  have hsm := hwJ.cmc_smoothAt hp hpb hR hα hα1 hD hHolder hpc hd
    (hq.continuous.continuousOn.mul hf) hvf
  have heq : f = fun y => (q y * f y)/q y := by
    funext y
    rw [mul_div_cancel_left₀ _ (cmcWeight_pos _).ne']
  rw [heq]
  exact hsm.div hq.contDiffAt (cmcWeight_pos _).ne'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_jacobi_graph_smoothAt
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ, surfaceJacobiB μ q u z=0)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφb : ∀ x, φ x∈Icc 0 1)
    (hφO : tsupport φ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ, φ x=1)
    {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) R, χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖≤1)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    (hpe : ∀ y∈Metric.ball (0 : Plane) R, p y=gradient g y)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R, ∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    (hqp : (fun y => q (actualNormalGraphChart a hn g y))
      =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] graphSquaredSecondFundamentalForm g)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => u.1 (actualNormalGraphChart a hn g y)) :
    ContDiffAt ℝ (⊤ : ℕ∞) f 0 := by
  have hφunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm measurableSet_ball hφunit
  have hcell (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) (i : Fin 3) :
      (a+normalGraph n g y) i∈Icc 0 1 := by
    have hz : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hφunit y hy]; exact one_ne_zero)
    exact ⟨(hφO hz i).1.le,(hφO hz i).2.le⟩
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  let v := lpPullbackLE hchart hd u.1
  let w := lpPullbackLE hchart hd u.2
  let G := graphCovectorLp hn hgL w
  have hv := lpPullbackLE_ae hchart hd u.1
  have hG : G =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => graphCovector n g y (u.2 (actualNormalGraphChart a hn g y)) := by
    filter_upwards [graphCovectorLp_ae hn hgL w,lpPullbackLE_ae hchart hd u.2] with y hy hz
    change G y=graphCovector n g y (w y) at hy
    change w y=u.2 (actualNormalGraphChart a hn g y) at hz
    rw [hy,hz]
  have hw := surfaceH1_chart_weak_gradient μ a hn hgL Metric.isOpen_ball
    (hg.of_le (by simp)).contDiffOn hcell hd hu
  apply hw.jacobi_smoothAt hp hpb hR hα hα1 hD hHolder hpc hg hpe hlin
  · intro ψ hψ hψc hs
    have he := surfaceJacobiB_chart_form μ q u a hn hg.continuous hφ
      (fun x => (hφb x).1) hφO hm (fun y _ => hg.differentiable (by simp) y)
      hχ hc hχO hφχ Metric.isOpen_ball hunit hψ hs
    rw [hhom _ (subset_closure (LinearMap.mem_range_self _ _))] at he
    refine Eq.trans ?_ he.symm
    apply integral_congr_ae
    filter_upwards [hv,hG,hqp] with y hy hz hqz
    change v y=u.1 (actualNormalGraphChart a hn g y) at hy
    rw [hy,hz,hqz]
  · exact hf
  · exact hfu.trans hv.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma reverseNormal_reverseNormal (z : NormalBundle) :
    reverseNormal (reverseNormal z)=z := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext; simp [reverseNormal]

lemma reverseNormal_measurePreserving (μ : FiniteMeasure NormalBundle) :
    MeasurePreserving reverseNormal (μ : Measure NormalBundle)
      (μ.map reverseNormal : Measure NormalBundle) := ⟨continuous_reverseNormal.measurable,rfl⟩

lemma reverseNormal_measurePreserving_back (μ : FiniteMeasure NormalBundle) :
    MeasurePreserving reverseNormal (μ.map reverseNormal : Measure NormalBundle)
      (μ : Measure NormalBundle) := by
  refine ⟨continuous_reverseNormal.measurable,?_⟩
  change Measure.map reverseNormal (Measure.map reverseNormal (μ : Measure NormalBundle))=_
  rw [Measure.map_map continuous_reverseNormal.measurable continuous_reverseNormal.measurable]
  simp only [Function.comp_def,reverseNormal_reverseNormal,Measure.map_id']

def normalReverseLp (μ : FiniteMeasure NormalBundle) (p : ℝ≥0∞) [Fact (1≤p)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F p (μ : Measure NormalBundle) →ₗᵢ[ℝ]
      Lp F p (μ.map reverseNormal : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ reverseNormal (reverseNormal_measurePreserving_back μ)

lemma normalReverseLp_ae (μ : FiniteMeasure NormalBundle) (p : ℝ≥0∞) [Fact (1≤p)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Lp F p (μ : Measure NormalBundle)) :
    normalReverseLp μ p u =ᵐ[(μ.map reverseNormal : Measure NormalBundle)] u ∘ reverseNormal :=
  Lp.coeFn_compMeasurePreserving u (reverseNormal_measurePreserving_back μ)

lemma smoothScalarValue_reverse (f : smoothPeriodicScalars) (z : NormalBundle) :
    smoothScalarValue f (reverseNormal z)=smoothScalarValue f z := rfl

lemma smoothScalarGradient_reverse (f : smoothPeriodicScalars) (z : NormalBundle) :
    smoothScalarGradient f (reverseNormal z)=smoothScalarGradient f z := by
  change gradient f.val z.1-⟪-(z.2 : Cover),gradient f.val z.1⟫ • -(z.2 : Cover)=_
  rw [inner_neg_left,neg_smul,smul_neg,neg_neg]
  rfl

def surfaceJetReverse (μ : FiniteMeasure NormalBundle) :
    SurfaceJet μ →L[ℝ] SurfaceJet (μ.map reverseNormal) :=
  (normalReverseLp μ 2).toContinuousLinearMap.prodMap
    (normalReverseLp μ 2).toContinuousLinearMap

lemma surfaceJetReverse_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceJetReverse μ (surfaceSmoothJet μ f)=surfaceSmoothJet (μ.map reverseNormal) f := by
  apply Prod.ext
  · apply Lp.ext
    have ha := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle))
    filter_upwards [normalReverseLp_ae μ 2 (surfaceSmoothJet μ f).1,ha,
      (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map reverseNormal : Measure NormalBundle)] with z hz ha hb
    change (surfaceJetReverse μ (surfaceSmoothJet μ f)).1 z=_ at hz
    change (surfaceSmoothJet μ f).1 (reverseNormal z)=smoothScalarValue f (reverseNormal z) at ha
    change (surfaceSmoothJet (μ.map reverseNormal) f).1 z=smoothScalarValue f z at hb
    exact hz.trans (ha.trans hb.symm)
  · apply Lp.ext
    have ha := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle))
    filter_upwards [normalReverseLp_ae μ 2 (surfaceSmoothJet μ f).2,ha,
      (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map reverseNormal : Measure NormalBundle)] with z hz ha hb
    change (surfaceJetReverse μ (surfaceSmoothJet μ f)).2 z=_ at hz
    change (surfaceSmoothJet μ f).2 (reverseNormal z)=smoothScalarGradient f (reverseNormal z) at ha
    change (surfaceSmoothJet (μ.map reverseNormal) f).2 z=smoothScalarGradient f z at hb
    exact hz.trans (ha.trans ((smoothScalarGradient_reverse f z).trans hb.symm))

theorem surfaceH1_reverse (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) : surfaceJetReverse μ u∈surfaceH1 (μ.map reverseNormal) := by
  apply map_mem_closure (surfaceJetReverse μ).continuous hu
  rintro _ ⟨f,rfl⟩
  exact ⟨f,(surfaceJetReverse_smooth μ f).symm⟩

lemma surfaceMultiplier_reverse (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : Lp ℝ 2 (μ : Measure NormalBundle)) :
    surfaceMultiplier (μ.map reverseNormal) (normalReverseLp μ ∞ q) (normalReverseLp μ 2 u)=
      normalReverseLp μ 2 (surfaceMultiplier μ q u) := by
  apply Lp.ext
  have hm := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_lpSMul (r := 2) q u)
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (normalReverseLp μ ∞ q) (normalReverseLp μ 2 u),
    normalReverseLp_ae μ ∞ q,normalReverseLp_ae μ 2 u,
    normalReverseLp_ae μ 2 (surfaceMultiplier μ q u),hm] with z hz hq hu hv hm
  change (surfaceMultiplier (μ.map reverseNormal) (normalReverseLp μ ∞ q)
    (normalReverseLp μ 2 u)) z=_ at hz
  change surfaceMultiplier μ q u (reverseNormal z)=_ at hm
  simp only [Function.comp_apply,smul_eq_mul,Pi.mul_apply] at hz hq hu hv hm
  rw [hz,hq,hu,hv,hm]

lemma surfaceJacobiB_reverse (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) :
    surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
      (surfaceJetReverse μ u) (surfaceJetReverse μ v)=surfaceJacobiB μ q u v := by
  change ⟪normalReverseLp μ 2 u.2,normalReverseLp μ 2 v.2⟫-
    ⟪surfaceMultiplier (μ.map reverseNormal) (normalReverseLp μ ∞ q)
      (normalReverseLp μ 2 u.1),normalReverseLp μ 2 v.1⟫=_
  rw [surfaceMultiplier_reverse,
    (normalReverseLp μ 2 (F := Cover)).inner_map_map u.2 v.2,
    (normalReverseLp μ 2 (F := ℝ)).inner_map_map (surfaceMultiplier μ q u.1) v.1]
  rfl

lemma surfaceJacobi_homogeneous_of_smooth (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (h : ∀ f : smoothPeriodicScalars,surfaceJacobiB μ q u (surfaceSmoothJet μ f)=0) :
    ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0 := by
  have hc : Continuous (fun v : SurfaceJet μ => surfaceJacobiB μ q u v) :=
    (surfaceJacobiB_continuous μ q).comp (continuous_const.prodMk continuous_id)
  have hr : Set.range (surfaceSmoothJet μ) ⊆ {v | surfaceJacobiB μ q u v=0} := by
    rintro _ ⟨f,rfl⟩
    exact h f
  exact fun v hv => closure_minimal hr (isClosed_eq hc continuous_const) hv

theorem surfaceJacobi_homogeneous_reverse (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hh : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0) :
    ∀ v∈surfaceH1 (μ.map reverseNormal),
      surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
        (surfaceJetReverse μ u) v=0 := by
  apply surfaceJacobi_homogeneous_of_smooth
  intro f
  calc
    _ = surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
        (surfaceJetReverse μ u) (surfaceJetReverse μ (surfaceSmoothJet μ f)) :=
      congrArg (surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
        (surfaceJetReverse μ u)) (surfaceJetReverse_smooth μ f).symm
    _ = surfaceJacobiB μ q u (surfaceSmoothJet μ f) := surfaceJacobiB_reverse μ q u _
    _ = 0 := hh _ (subset_closure (LinearMap.mem_range_self _ _))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_graph_extension_compact {g : Plane → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (K : ℝ≥0),ContDiff ℝ (⊤ : ℕ∞) f ∧
      HasCompactSupport f ∧ LipschitzWith K f ∧ EqOn f g (Metric.ball 0 (R/2)) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f : Plane → ℝ := fun y => b y*g y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_local_vector_cutoff Metric.isOpen_ball hg b.contDiff hs
  have hfc : HasCompactSupport f := b.hasCompactSupport.mul_right
  obtain ⟨K,hK⟩ := compact_C1_lipschitz (hf.of_le (by simp)) hfc
  refine ⟨f,K,hf,hfc,hK,?_⟩
  intro y hy
  change b y*g y=g y
  rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]

lemma smooth_graph_symbol_extension {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hK : (K : ℝ)≤1) {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ (p : Plane → Plane) (D : ℝ),ContDiff ℝ (⊤ : ℕ∞) p ∧
      (∀ y,‖p y‖≤1) ∧ 0≤D ∧ EqOn p (gradient g) (Metric.ball 0 (R/2)) ∧
      ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hgD : ContDiffOn ℝ (⊤ : ℕ∞) (gradient g) (Metric.ball 0 R) := by
    intro y hy
    have hd := (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hy)).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)
    exact ((InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
      y hd).contDiffWithinAt
  let p : Plane → Plane := fun y => b y • gradient g y
  have hp : ContDiff ℝ (⊤ : ℕ∞) p :=
    contDiff_local_vector_cutoff Metric.isOpen_ball hgD b.contDiff hs
  have hpc : HasCompactSupport p := b.hasCompactSupport.smul_right
  obtain ⟨C,hC⟩ := compact_C1_lipschitz (hp.of_le (by simp)) hpc
  have hpb (y : Plane) : ‖p y‖≤1 := by
    have hgrad : ‖gradient g y‖≤K := by
      simpa only [gradient,LinearIsometryEquiv.norm_map] using
        norm_fderiv_le_of_lipschitz ℝ hgL (x₀ := y)
    change ‖b y • gradient g y‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg (x := y))]
    exact ((mul_le_mul_of_nonneg_right (b.le_one (x := y)) (norm_nonneg _)).trans
      (by simpa using hgrad)).trans hK
  obtain ⟨L,hL,hLip⟩ := cmcJacobian_uniform_lipschitz
  refine ⟨p,L*C,hp,hpb,mul_nonneg hL C.coe_nonneg,?_,?_⟩
  · intro y hy
    change b y • gradient g y=gradient g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]
  · intro x y
    calc
      _ ≤ L*‖p x-p y‖ := hLip _ _ (hpb x) (hpb y)
      _ ≤ L*(C*dist x y) := mul_le_mul_of_nonneg_left
        (by simpa only [← dist_eq_norm] using hC.dist_le_mul x y) hL
      _ = _ := by ring

theorem WeakCMCGraph.smooth_jacobi_data {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hK : (K : ℝ)≤1) {R H : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (Kf : ℝ≥0) (p : Plane → Plane) (r D : ℝ),
      0<r ∧ r≤R/2 ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      LipschitzWith Kf f ∧ EqOn f g (Metric.ball 0 (R/2)) ∧
      ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ y,‖p y‖≤1) ∧ 0≤D ∧
      EqOn p (gradient f) (Metric.ball 0 r) ∧
      (∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y) ∧
      ∀ i : Fin 2,LinearCMCEquation
        (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
        (fun _ => 0) (Metric.ball 0 r) := by
  obtain ⟨f,Kf,hf,hfc,hfL,hfg⟩ := smooth_graph_extension_compact hR hg
  obtain ⟨p,D,hp,hpb,hD,hpg,hpD⟩ := smooth_graph_symbol_extension hgL hK hR hg
  obtain ⟨f₀,r₀,hr₀,_,hf₀,hf₀g,hlin,_⟩ := hw.coordinate_jacobi_chart hgL hK hR hg
  let r := min (R/2) r₀
  have hr : 0<r := lt_min (half_pos hR) hr₀
  have hrR : r≤R/2 := min_le_left _ _
  have hr0 : r≤r₀ := min_le_right _ _
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : f=ᶠ[𝓝 y]g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hrR hy)] with z hz
    exact hfg hz
  have he0 (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : f=ᶠ[𝓝 y]f₀ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact (hfg (Metric.ball_subset_ball hrR hz)).trans
      (hf₀g (Metric.ball_subset_ball hr0 hz)).symm
  refine ⟨f,Kf,p,r,D,hr,hrR,hf,hfc,hfL,hfg,hp,hpb,hD,?_,hpD,?_⟩
  · intro y hy
    rw [hpg (Metric.ball_subset_ball hrR hy)]
    simp only [gradient,(he y hy).fderiv_eq]
  · intro i
    apply LinearCMCEquation.congr Metric.isOpen_ball
      ((hlin i).mono (Metric.ball_subset_ball hr0))
    · intro y hy
      exact congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (he0 y hy).fderiv_eq
    · intro y hy
      simp only [gradient,(he0 y hy).fderiv_eq]
    · intro y hy; rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceCurvatureLp_graph_ae (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=σ • (z.2 : Cover))
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {S : Set Plane} (hS : IsOpen S)
    (hcell : ∀ y∈S,∀ i,(a+normalGraph n g y) i∈Icc 0 1)
    (hd : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S)≤μ)
    (hu : ∀ y∈S,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1) :
    (fun y => surfaceCurvatureLp μ N hN (actualNormalGraphChart a hn g y))
      =ᵐ[volume.restrict S] graphSquaredSecondFundamentalForm g := by
  let Φ : Plane → Cover := fun y => a+normalGraph n g y
  have hΦ : Continuous Φ := continuous_const.add
    ((normalPlaneLinearIsometry n).continuous.add (hg.continuous.smul continuous_const))
  have hmp : Measure.QuasiMeasurePreserving (actualNormalGraphChart a hn g)
      (volume.restrict S) (μ : Measure NormalBundle) :=
    ⟨actualNormalGraphChart_measurable a hn hg.continuous,Measure.absolutelyContinuous_of_le hd⟩
  have hmatchae : (fun y => N (Φ y)) =ᵐ[volume.restrict S]
      fun y => σ • graphSlopeNormal n (gradient g y) := by
    filter_upwards [hmp.ae_eq_comp hae,ae_restrict_mem hS.measurableSet] with y hy hys
    change N (actualNormalGraphChart a hn g y).1=σ •
      ((actualNormalGraphChart a hn g y).2 : Cover) at hy
    rw [actualNormalGraphChart_position a hn g (hcell y hys),actualNormalGraphChart_normal] at hy
    exact hy
  have hmatch : EqOn (fun y => N (Φ y))
      (fun y => σ • graphSlopeNormal n (gradient g y)) S :=
    Measure.eqOn_open_of_ae_eq hmatchae hS (hN.continuous.comp hΦ).continuousOn
      (((graphSlopeNormal_contDiff hn).continuous.comp
        (plane_gradient_contDiff hg).continuous).const_smul σ).continuousOn
  have hq := hmp.ae_eq_comp
    ((show C(NormalBundle,ℝ) from ⟨_,
      (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
      (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle))
  filter_upwards [hq,ae_restrict_mem hS.measurableSet] with y hy hys
  change surfaceCurvatureLp μ N hN (actualNormalGraphChart a hn g y)=
    coverTrace ((fderiv ℝ N (actualNormalGraphChart a hn g y).1).comp
      (fderiv ℝ N (actualNormalGraphChart a hn g y).1)) at hy
  rw [hy,actualNormalGraphChart_position a hn g (hcell y hys)]
  apply graph_normal_extension_curvature a hn hg y hσ hN (hu y hys)
  filter_upwards [hS.mem_nhds hys] with z hz
  exact hmatch hz

lemma surfaceCurvatureLp_reverse (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    normalReverseLp μ ∞ (surfaceCurvatureLp μ N hN)=
      surfaceCurvatureLp (μ.map reverseNormal) N hN := by
  apply Lp.ext
  let Q : C(NormalBundle,ℝ) := ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩
  have hq := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
    (Q.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle))
  filter_upwards [normalReverseLp_ae μ ∞ (surfaceCurvatureLp μ N hN),hq,
    Q.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ.map reverseNormal : Measure NormalBundle)] with z hz hq hr
  exact hz.trans (hq.trans hr.symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_H1_jacobi_graph_smoothAt {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=σ • (z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgraph : ∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {s D : ℝ} (hs : 0<s) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
    (hpe : EqOn p (gradient g) (Metric.ball 0 s))
    (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 s))
    (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
    (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (a+normalGraph n g y))) 0 := by
  have hm := normalMeasure_graph_area_measure hE hμ a hn hgL
    (fun y _ => ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.continuousAt (x := y)))
    hgraph hφ hsφ hφU hφO hφR hφb
  have hφunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm measurableSet_ball hφunit
  have hcell (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) (i : Fin 3) :
      (a+normalGraph n g y) i∈Icc 0 1 := by
    have hz : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hφunit y hy]; exact one_ne_zero)
    exact ⟨(hφO hz i).1.le,(hφO hz i).2.le⟩
  have hq := surfaceCurvatureLp_graph_ae μ N hN hσ hae a hn hg Metric.isOpen_ball hcell hd hNu
  apply surfaceH1_jacobi_graph_smoothAt μ (surfaceCurvatureLp μ N hN) hu hhom a hn hgL hg
    hφ.continuous.measurable hφb hφO hm hχ hsχ hχO hφχ hs
    (α := 1) (by norm_num) (by norm_num) hD hunit hp.continuous hpb hp.contDiffAt
    (fun y hy => hpe hy) (fun x _ y _ => by simpa only [Real.rpow_one] using hpD x y) hlin hq
  · apply hF.comp
    · exact (continuous_quotientMap.comp
        (continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
          (hg.continuous.smul continuous_const)))).continuousOn
    · exact hS
  · have hmp : Measure.QuasiMeasurePreserving (actualNormalGraphChart a hn g)
        (volume.restrict (Metric.ball (0 : Plane) s)) (μ : Measure NormalBundle) :=
      ⟨actualNormalGraphChart_measurable a hn hg.continuous,Measure.absolutelyContinuous_of_le hd⟩
    filter_upwards [hmp.ae_eq_comp hFu,ae_restrict_mem measurableSet_ball] with y hy hys
    change u.1 (actualNormalGraphChart a hn g y)=
      F (quotientMap (actualNormalGraphChart a hn g y).1) at hy
    rw [actualNormalGraphChart_position a hn g (hcell y hys)] at hy
    exact hy.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_H1_jacobi_signed_graph_smoothAt {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgraph : (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {s D : ℝ} (hs : 0<s) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
    (hpe : EqOn p (gradient g) (Metric.ball 0 s))
    (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 s))
    (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
    (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (a+normalGraph n g y))) 0 := by
  rcases hgraph with hphase | hphase
  · have hgph : ∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x) := by
      simpa only [graphSignedHeight,sub_neg] using hphase
    have hn' : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(1 : ℝ) • (z.2 : Cover) := by
      simpa only [one_smul] using hae
    exact normalMeasure_H1_jacobi_graph_smoothAt hE hμ N hN (Or.inl rfl) hn' hu hhom
      a hn hgL hg hgph hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ hs hD hunit
      hp hpb hpe hpD hlin hNu hF hS hFu
  · have hgph : ∀ᵐ x : Cover ∂volume,x∈U →
        (x∈quotientMap ⁻¹' E ↔ graphHeightExtension a n g x<⟪n,x-a⟫) := by
      simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
    have hcph := graph_superlevel_compl_ae a hn hg.continuous hgph
    have hn' : ∀ᵐ z ∂(μ.map reverseNormal : Measure NormalBundle),
        N z.1=(-1 : ℝ) • (z.2 : Cover) := by
      have hh := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp hae
      filter_upwards [hh] with z hz
      simpa only [Function.comp_apply,reverseNormal,neg_one_smul] using hz
    have hf' : ((surfaceJetReverse μ u).1 : NormalBundle → ℝ)
        =ᵐ[(μ.map reverseNormal : Measure NormalBundle)] F ∘ normalProjection := by
      have hh := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp hFu
      filter_upwards [normalReverseLp_ae μ 2 u.1,hh] with z hz hh
      exact hz.trans hh
    have hh := surfaceJacobi_homogeneous_reverse μ (surfaceCurvatureLp μ N hN) hhom
    rw [surfaceCurvatureLp_reverse] at hh
    exact normalMeasure_H1_jacobi_graph_smoothAt hE.compl (isNormalMeasure_compl hE hμ)
      N hN (Or.inr rfl) hn' (surfaceH1_reverse μ hu) hh
      a hn hgL hg hcph hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ hs hD hunit
      hp hpb hpe hpD hlin hNu hF hS hf'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_H1_jacobi_smooth {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    ∃ (n : Cover) (f : Plane → ℝ) (s : ℝ),‖n‖=1 ∧ 0<s ∧ f 0=0 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ y∈Metric.ball (0 : Plane) s,
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) s,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n f (normalPlaneCoordinates n x)=x) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (cubeCenter+normalGraph n f y))) 0 := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,hw,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,Kf,p,rj,D,hrj,hrjr,hf,hfc,hfL,hfg,hp,hpb,hD,hpf,hpD,hlin⟩ :=
    hw.smooth_jacobi_data hg (by norm_num) hr hgc
  have hf0 : f 0=0 := (hfg (Metric.mem_ball_self (half_pos hr))).trans hg0
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x (Metric.ball_subset_ball (by linarith) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (half_pos hr)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  have hext (x : Cover) (hx : x∈U) :
      graphSignedHeight cubeCenter n f x=graphSignedHeight cubeCenter n g x := by
    have hy : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      have hz : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR hx
      simpa only [Metric.mem_ball,dist_zero_right] using
        (normalPlaneCoordinates_norm_le n (x-cubeCenter)).trans_lt (hz.trans hRr)
    simp only [graphSignedHeight,graphHeightExtension,hfg hy]
  have hphasef : (∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ graphSignedHeight cubeCenter n f x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n f x)) := by
    rcases hphase with hphase|hphase
    · left; filter_upwards [hphase] with x hx hxu
      rw [hext x hxu]; exact hx hxu
    · right; filter_upwards [hphase] with x hx hxu
      rw [hext x hxu]; exact hx hxu
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  let χ := radialHeightCutoff cubeCenter (ρ/4)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := radialDensityWeight_contDiff _ _ _
  have hsχ : HasCompactSupport χ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hχs : tsupport χ⊆Metric.closedBall cubeCenter (ρ/2) := by
    have hh := radialDensityWeight_tsupport (a := cubeCenter)
      (by positivity : 0≤2*(ρ/4)) (by positivity : 0<3*(ρ/4)^2)
    convert hh using 1 <;> congr 1
    ring
  have hφχ (x : Cover) (hx : x∈tsupport χ) : φ x=1 :=
    radialHeightCutoff_one hρ (Metric.closedBall_subset_closedBall (by linarith) (hχs hx))
  have hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1} :=
    hχs.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans (hρU.trans hUO))
  have hΦ : Continuous (fun y => cubeCenter+normalGraph n f y) :=
    continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
      (hf.continuous.smul continuous_const))
  have hΦ0 : cubeCenter+normalGraph n f 0=cubeCenter := by
    simp only [normalGraph,hf0,zero_smul,add_zero]
    change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
    rw [map_zero,add_zero]
  have hnb : ∀ᶠ y in 𝓝 (0 : Plane),
      cubeCenter+normalGraph n f y∈Metric.ball cubeCenter (ρ/4) := by
    apply hΦ.continuousAt
    change Metric.ball cubeCenter (ρ/4)∈𝓝 (cubeCenter+normalGraph n f 0)
    rw [hΦ0]
    exact Metric.ball_mem_nhds _ (by positivity)
  obtain ⟨t,ht,htb⟩ := Metric.mem_nhds_iff.mp hnb
  let s := min rj t
  have hs : 0<s := lt_min hrj ht
  have hsj : s≤rj := min_le_left _ _
  have hsr : s≤r/2 := hsj.trans hrjr
  have hunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :
      χ (cubeCenter+normalGraph n f y)=1 :=
    radialHeightCutoff_one (by positivity)
      (Metric.ball_subset_closedBall (htb (Metric.ball_subset_ball (min_le_right _ _) hy)))
  have hin (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :
      quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
    have hy' := Metric.ball_subset_ball hsr hy
    simp only [normalGraph,hfg hy',quotientMap_add]
    exact hi y (Metric.ball_subset_ball (by linarith) hy')
  refine ⟨n,f,s,hn,hs,hf0,hf,hin,?_,?_⟩
  · intro x hx
    have hx' := Metric.ball_subset_ball hsr hx
    have hp' : normalPlaneCoordinates n x∈Metric.ball (0 : Plane) (r/2) := by
      simpa only [Metric.mem_ball,dist_zero_right] using
        (normalPlaneCoordinates_norm_le n x).trans_lt
          (show ‖x‖<r/2 from by simpa only [Metric.mem_ball,dist_zero_right] using hx')
    simpa only [normalGraph,hfg hp'] using hcover' x hx'
  · exact normalMeasure_H1_jacobi_signed_graph_smoothAt hE hμ N hN hae hu hhom
      cubeCenter hn hfL hf hphasef hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ
      hs hD hunit hp hpb (hpf.mono (Metric.ball_subset_ball hsj)) hpD
      (fun i => (hlin i).mono (Metric.ball_subset_ball hsj))
      (fun y hy => hNu _ (hin y hy)) hF hin hFu

end CubicTorus

end
end

end OAI
