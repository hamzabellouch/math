import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapEndpointSmoothArc
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcReverse
import OAI.Geometry.SurfaceImmersion.Geometry.RegularCurveGerms

namespace OAI

/-! Choose disjoint initial and terminal smooth pieces of the actual
crosscap-connecting arc, retaining genuine double-locus germs at their inner ends. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_end_arcs_regular (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ (a b : ℝ) (P Q : SmoothCompactArc (planeModel.prod planeModel) (M × M)),
      0 < a ∧ a < b ∧ b < 1 ∧
      P.curve '' Icc P.start P.finish = Γ '' {t : I | (t:ℝ) ≤ a} ∧
      Q.curve '' Icc Q.start Q.finish = Γ '' {t : I | b ≤ (t:ℝ)} ∧
      P.curve P.start = (p,p) ∧ Q.curve Q.finish = (q,q) ∧
      (∀ u : I, (u:ℝ) = a → P.curve P.finish = Γ u) ∧
      (∀ u : I, (u:ℝ) = b → Q.curve Q.start = Γ u) ∧
      (∀ᶠ t in 𝓝 P.finish, P.curve t ∈ surfaceDoublePairs f) ∧
      (∀ᶠ t in 𝓝 Q.start, Q.curve t ∈ surfaceDoublePairs f) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (P.curve t).1) P.start) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (Q.curve t).1) Q.finish) := by
  obtain ⟨a,P,ha,ha3,hPstart,hPi,hP0,hPa,hPg,hPreg⟩ :=
    crosscap_endpoint_smooth_arc cp hΓ hinj hzero heq hne
  have hrev : Continuous (Γ ∘ unitInterval.symm) := hΓ.comp continuous_symm
  have hrevInj : Function.Injective (Γ ∘ unitInterval.symm) := hinj.comp symm_bijective.injective
  have hrev0 : (Γ ∘ unitInterval.symm) 0 = (q,q) := by simpa using hone
  have hrevEq : ∀ t, f ((Γ ∘ unitInterval.symm) t).1 = f ((Γ ∘ unitInterval.symm) t).2 :=
    fun t => heq (unitInterval.symm t)
  have hrevNe : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 →
      ((Γ ∘ unitInterval.symm) t).1 ≠ ((Γ ∘ unitInterval.symm) t).2 := by
    intro t ht0 ht1
    apply hne
    · change 0 < 1-(t:ℝ)
      linarith
    · change 1-(t:ℝ) < 1
      linarith
  obtain ⟨d,R,hd,hd3,hRstart,hRi,hR0,hRd,hRg,hRreg⟩ :=
    crosscap_endpoint_smooth_arc cq hrev hrevInj hrev0 hrevEq hrevNe
  obtain ⟨Q,hQs,hQf,hQdom,hQc,hQi⟩ := R.reverse_arc
  have hQimage : Q.curve '' Icc Q.start Q.finish = Γ '' {t : I | 1-d ≤ (t:ℝ)} := by
    rw [hQi,hRi]
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨unitInterval.symm t,?_,rfl⟩
      change (t:ℝ) ≤ d at ht
      change 1-d ≤ 1-(t:ℝ)
      linarith
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨unitInterval.symm t,?_,?_⟩
      · change 1-d ≤ (t:ℝ) at ht
        change 1-(t:ℝ) ≤ d
        linarith
      · change Γ (unitInterval.symm (unitInterval.symm t)) = Γ t
        rw [symm_symm]
  have hQend : Q.curve Q.finish = (q,q) := by
    rw [hQc,hQf]
    dsimp only
    rw [neg_neg]
    exact hR0
  have hQbegin : ∀ u : I, (u:ℝ) = 1-d → Q.curve Q.start = Γ u := by
    intro u hu
    rw [hQc,hQs]
    dsimp only
    rw [neg_neg]
    have hd' : (unitInterval.symm u : ℝ) = d := by change 1-(u:ℝ) = d; linarith
    have hh := hRd (unitInterval.symm u) hd'
    simpa only [Function.comp_apply,symm_symm] using hh
  have hPgood : ∀ᶠ t in 𝓝 P.finish, P.curve t ∈ surfaceDoublePairs f := by
    filter_upwards [P.domain_open.mem_nhds (P.interval_subset (right_mem_Icc.mpr P.start_lt_finish.le)),
      eventually_ne_nhds (ne_of_gt P.start_lt_finish)] with t ht htn
    exact hPg t ht htn
  have hRgood : ∀ᶠ t in 𝓝 R.finish, R.curve t ∈ surfaceDoublePairs f := by
    filter_upwards [R.domain_open.mem_nhds (R.interval_subset (right_mem_Icc.mpr R.start_lt_finish.le)),
      eventually_ne_nhds (ne_of_gt R.start_lt_finish)] with t ht htn
    exact hRg t ht htn
  have hQgood : ∀ᶠ t in 𝓝 Q.start, Q.curve t ∈ surfaceDoublePairs f := by
    rw [hQc,hQs]
    have ht : Tendsto (fun t : ℝ => -t) (𝓝 (-R.finish)) (𝓝 R.finish) := by
      simpa only [ContinuousAt,neg_neg] using (continuous_neg.continuousAt (x := -R.finish))
    exact ht.eventually hRgood
  refine ⟨a,1-d,P,Q,ha,by linarith,by linarith,hPi,hQimage,hP0,hQend,hPa,hQbegin,hPgood,hQgood,?_,?_⟩
  · exact (hPreg _ (P.interval_subset (left_mem_Icc.mpr P.start_lt_finish.le))).1
  · have hfun : (fun t => (Q.curve t).1) = (fun t => (R.curve t).1) ∘ Homeomorph.neg ℝ := by
      funext t
      rw [hQc]
      rfl
    rw [hfun,hQf]
    have ht := R.interval_subset (left_mem_Icc.mpr R.start_lt_finish.le)
    apply regular_curve_reparameterization (Homeomorph.neg ℝ) contDiff_neg contDiff_neg
    · change ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (R.curve t).1) (- -R.start)
      rw [neg_neg]
      exact contMDiffAt_fst.comp R.start (R.smooth.contMDiffAt (R.domain_open.mem_nhds ht))
    · change Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (R.curve t).1) (- -R.start))
      rw [neg_neg]
      exact (hRreg R.start ht).1

theorem crosscap_end_arcs (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ (a b : ℝ) (P Q : SmoothCompactArc (planeModel.prod planeModel) (M × M)),
      0 < a ∧ a < b ∧ b < 1 ∧
      P.curve '' Icc P.start P.finish = Γ '' {t : I | (t:ℝ) ≤ a} ∧
      Q.curve '' Icc Q.start Q.finish = Γ '' {t : I | b ≤ (t:ℝ)} ∧
      P.curve P.start = (p,p) ∧ Q.curve Q.finish = (q,q) ∧
      (∀ u : I, (u:ℝ) = a → P.curve P.finish = Γ u) ∧
      (∀ u : I, (u:ℝ) = b → Q.curve Q.start = Γ u) ∧
      (∀ᶠ t in 𝓝 P.finish, P.curve t ∈ surfaceDoublePairs f) ∧
      (∀ᶠ t in 𝓝 Q.start, Q.curve t ∈ surfaceDoublePairs f) := by
  obtain ⟨a,b,P,Q,ha,hab,hb,hPi,hQi,hP0,hQ1,hPa,hQb,hPg,hQg,_,_⟩ :=
    crosscap_end_arcs_regular cp cq hΓ hinj hzero hone heq hne
  exact ⟨a,b,P,Q,ha,hab,hb,hPi,hQi,hP0,hQ1,hPa,hQb,hPg,hQg⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
