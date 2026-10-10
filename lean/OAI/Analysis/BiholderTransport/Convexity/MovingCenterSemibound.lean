import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateMatrices
import OAI.Analysis.BiholderTransport.Regularity.JointMovingPrefix
import OAI.Analysis.BiholderTransport.Convexity.ShortPullbackSemibound

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MovingCenterSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [Nonempty M] in
lemma moving_energy_hessian_tendsto {a : M} {q : Model n}
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) {bj qj : ℕ → Model n} {tj : ℕ → ℝ}
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
    : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 (extChartAt 𝓘(ℝ,Model n) a a))) q)) := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  have hb0 : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hp0 : (1:ℝ) • chartFiberInverse a b q∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    rw [chartFiberInverse_at_center]
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
    change (1:ℝ) • (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a
    rw [one_smul]
    exact hq
  let f : (ℝ×Model n) → Model n → ℝ := fun z r=>movingPrefixEnergy a z.1 z.2 r
  have henergy : ContDiffAt ℝ ∞ (Function.uncurry f) ((1,b),q) :=
    joint_movingPrefixEnergy_contDiffAt hb0 one_ne_zero hp0
  have hd : ContDiffAt ℝ ∞ (fun z:(ℝ×Model n)×Model n=>fderiv ℝ (fderiv ℝ (f z.1)) z.2) ((1,b),q) :=
    ContDiffAt.partial_snd_fderiv_two (f := f) (q := (1,b)) (h := q) henergy
  have harg : Tendsto (fun i=>((tj i,bj i),qj i)) atTop (𝓝 ((1,b),q)) :=
    (ht.prodMk_nhds hb).prodMk_nhds hqq
  have H := hd.continuousAt.tendsto.comp harg
  exact H

omit [Nonempty M] in
lemma moving_energy_sequential_lower {a : M} {q : Model n}
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) {bj qj : ℕ → Model n} {tj : ℕ → ℝ}
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in atTop,∀ d : Model n,
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d-ε*‖d‖^2≤
        fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i) d d := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  have hElim := moving_energy_hessian_tendsto hq hb hqq ht
  have hEsmall := ((Metric.tendsto_nhds (α := Model n →L[ℝ] Model n →L[ℝ] ℝ)).mp hElim) ε hε
  filter_upwards [hEsmall] with i hei
  intro d
  have HE := (abs_le.mp (bilinear_diag_sub_bound
    (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i))
    (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q) d)).1
  rw [movingPrefixEnergy_hessian_at_center hq] at HE
  have hei' : ‖(fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i))-
    (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q)‖<ε := by
    exact (dist_eq_norm (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i))
      (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q)).symm ▸ hei
  have HM := mul_le_mul_of_nonneg_right hei'.le (sq_nonneg ‖d‖)
  linarith only [HE,HM]

omit [Nonempty M] [CompleteSpace P] in
lemma moving_chart_support_jet {a c : M} {ψ : P×Model n → ℝ} {p : P} {x q : Model n}
    (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    (he : extChartAt 𝓘(ℝ,Model n) c (riemannianExp a q)=x)
    (hc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source) (d : Model n) :
    let g := movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)
    secondJetPullback (fderiv ℝ (fun w=>ψ (p,w)) x)
      (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x)
      (fderiv ℝ g q) (fderiv ℝ (fderiv ℝ g) q) d d=
      fderiv ℝ (fderiv ℝ (fun r=>ψ (p,extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)))) q d d := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  let g := movingPrefixChart a c 1 b
  have hb0 : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc : movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simpa only [b,movingPrefix_at_center,one_smul] using hc
  have hg : ContDiffAt ℝ ∞ (fun z:(ℝ×Model n)×Model n=>movingPrefixChart a c z.1.1 z.1.2 z.2) ((1,b),q) :=
    joint_movingPrefixChart_contDiffAt hb0 hgc
  have hgb : ContDiffAt ℝ 2 g q :=
    (hg.comp q (contDiffAt_const.prodMk contDiffAt_id)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hge : g q=x := by
    simpa only [g,movingPrefixChart,b,movingPrefix_at_center,one_smul] using he
  have hψb : ContDiffAt ℝ 2 (fun w=>ψ (p,w)) (g q) := by
    rw [hge]
    exact (hψ.comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change secondJetPullback _ _ (fderiv ℝ g q) (fderiv ℝ (fderiv ℝ g) q) d d=_
  rw [←hge,secondJetPullback_apply,←second_fderiv_comp_with_acceleration hψb hgb]
  have hgfun : g=(fun r : Model n=>extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)) := by
    funext r
    simp only [g,movingPrefixChart,b,movingPrefix_at_center,one_smul]
  rw [hgfun]
  rfl

lemma moving_center_sequential_semibound {a c : M} {ψ : P×Model n → ℝ}
    {p : P} {x q : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) (he : extChartAt 𝓘(ℝ,Model n) c (riemannianExp a q)=x)
    (hc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {pj : ℕ → P} {xj bj qj : ℕ → Model n} {tj τj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
    (hτ : Tendsto τj atTop (𝓝 0)) (hτpos : ∀ᶠ i in atTop,0<τj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
    (hz : ∀ᶠ i in atTop,movingPrefixChart a c (tj i) (bj i) (qj i)=
      parametricShortForward c ψ ((pj i,τj i),xj i))
    (hjet : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),DifferentiableAt ℝ
        (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
          (movingPrefixChart a c (tj i) (bj i) (qj i)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in atTop,∀ d : Model n,
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d+
        fderiv ℝ (fderiv ℝ (fun r=>ψ (p,extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)))) q d d-
          ε*‖d‖^2 ≤ coordinateCenterMatrix a (tj i) (hopfLax (τj i) (f i)) (bj i) (qj i) d d := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  let g := fun (t:ℝ×Model n) (r:Model n)=>movingPrefixChart a c t.1 t.2 r
  have hb0 : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc : movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simpa only [b,movingPrefix_at_center,one_smul] using hc
  have hg : ContDiffAt ℝ ∞ (Function.uncurry g) ((1,b),q) :=
    joint_movingPrefixChart_contDiffAt hb0 hgc
  have harg := (ht.prodMk_nhds hb).prodMk_nhds hqq
  have hm := (ContDiffAt.partial_snd_fderiv hg).continuousAt.tendsto.comp harg
  have hr := (ContDiffAt.partial_snd_fderiv_two hg).continuousAt.tendsto.comp harg
  have hgj : ∀ᶠ i in atTop,ContDiffAt ℝ 2 (g (tj i,bj i)) (qj i) := by
    have hg2 := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    filter_upwards [harg.eventually (hg2.eventually (by norm_num))] with i hi
    exact hi.comp (qj i) (contDiffAt_const.prodMk contDiffAt_id)
  have H := parametric_short_pullback_semibound L hx hψ hp hxx hτ hτpos hlip hbelow htouch
    hz ((hjet.and hgj).mono (fun i hi=>⟨hi.1.1,hi.1.2,hi.2⟩)) hm hr (half_pos hε)
  have HE := moving_energy_sequential_lower hq hb hqq ht (half_pos hε)
  have hpull := moving_chart_support_jet hψ he hc
  have hbjt := hb.eventually ((isOpen_extChartAt_target a).mem_nhds hb0)
  have hcjt : ∀ᶠ i in atTop,movingPrefix a (tj i) (bj i) (qj i)∈(extChartAt 𝓘(ℝ,Model n) c).source :=
    ((joint_movingPrefix_contMDiffAt hb0).continuousAt.tendsto.comp harg).eventually
      ((isOpen_extChartAt_source _).mem_nhds hgc)
  filter_upwards [H,HE,hbjt,hcjt] with i hi hei hbi hci
  intro d
  have HD := hi d
  rw [hpull d] at HD
  have HD2 := hei d
  rw [coordinateCenterMatrix_chart hbi hci,add_apply,add_apply]
  linarith only [HD,HD2]

end MovingCenterSemibound
end WeakMTWTransport

end
end

end OAI
