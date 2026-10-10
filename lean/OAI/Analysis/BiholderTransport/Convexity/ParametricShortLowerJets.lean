import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.HopfApproximation
import OAI.Analysis.BiholderTransport.Regularity.UniformShortMinima
import OAI.Analysis.BiholderTransport.Calculus.ShortPoleIdentities

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma exists_parametric_short_lower_jets {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∃ r>0, ∃ (B : (P×ℝ)×Model n → Model n) (U : (P×ℝ)×Model n → ℝ),
      ContDiffAt ℝ ∞ B ((p,0),x) ∧ ContDiffAt ℝ ∞ U ((p,0),x) ∧ B ((p,0),x)=x ∧
      (∀ᶠ q in 𝓝 ((p,0),x),parametricShortForward a ψ (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),B (q.1,parametricShortForward a ψ q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),0<q.1.2 → ∀ f : M → ℝ, LipschitzWith L f →
        (∀ w∈Metric.closedBall x r,ψ (q.1.1,w)≤f ((extChartAt 𝓘(ℝ,Model n) a).symm w)) →
        U q≤hopfLax q.1.2 f ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) ∧
        (f ((extChartAt 𝓘(ℝ,Model n) a).symm (B q))=ψ (q.1.1,B q) →
          U q=hopfLax q.1.2 f ((extChartAt 𝓘(ℝ,Model n) a).symm q.2))) ∧
      Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fun y => U (q.1,y)) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fun y => ψ (p,y)) x)) ∧
      Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fderiv ℝ (fun y => U (q.1,y))) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fderiv ℝ (fun y => ψ (p,y))) x)) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨B,U,hB,hU,hBx,hBZ,hZB,hUE,hUH⟩ := geometric_parametric_short_family hx hψ
  obtain ⟨r,hr,V,hV,hmin⟩ := exists_parametric_short_action_local_minima hx hψ
  have hBmap : ContinuousAt (fun q : (P×ℝ)×Model n => (q.1,B q)) ((p,0),x) :=
    continuousAt_fst.prodMk hB.continuousAt
  have hBreg := hBmap.eventually (show ∀ᶠ q in 𝓝 ((p,0),B ((p,0),x)),
      q.2∈χ.target ∧ chartGradientVector a q.2 (q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈
        injectivityDomain (χ.symm q.2) ∧
      coordinateBackward a (-1,q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈χ.source by
    rw [hBx]; exact parametricShortForward_regular_near hx hψ)
  have hPsib : ∀ᶠ q in 𝓝 ((p,(0:ℝ)),x), ContDiffAt ℝ 1 (fun y => ψ (q.1.1,y)) (B q) := by
    have hc : ContinuousAt (fun q : (P×ℝ)×Model n => (q.1.1,B q)) ((p,0),x) :=
      continuousAt_fst.fst.prodMk hB.continuousAt
    have H := hc.eventually (show ∀ᶠ v in 𝓝 (p,B ((p,0),x)),ContDiffAt ℝ 1 ψ v by
      rw [hBx]; exact (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).eventually (by simp))
    filter_upwards [H] with q hq
    exact hq.comp (B q) (contDiffAt_const.prodMk contDiffAt_id)
  have hBr : ∀ᶠ q in 𝓝 ((p,(0:ℝ)),x), B q∈Metric.closedBall x r := by
    have H := hB.continuousAt.preimage_mem_nhds (show Metric.ball x r∈𝓝 (B ((p,0),x)) by
      rw [hBx]; exact Metric.ball_mem_nhds x hr)
    exact Filter.Eventually.mono H fun _ hy => Metric.ball_subset_closedBall hy
  have hcx : χ.symm x∈χ.source := χ.map_target hx
  have hcm : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ (χ.symm x) :=
    contMDiffAt_extChartAt' (by simpa only [χ,extChartAt_source] using hcx)
  have hWM : χ.source ∩ χ ⁻¹' Metric.ball x r∈𝓝 (χ.symm x) :=
    Filter.inter_mem ((isOpen_extChartAt_source a).mem_nhds hcx)
      (hcm.continuousAt.preimage_mem_nhds (by rw [χ.right_inv hx]; exact Metric.ball_mem_nhds x hr))
  have hi : ContinuousAt χ.symm x := continuousAt_extChartAt_symm'' hx
  have hloc := (continuousAt_fst.snd.prodMk (hi.comp (x := ((p,(0:ℝ)),x)) continuousAt_snd)).eventually
    (uniform_hopfLax_minimizers_eventually_in L hWM)
  refine ⟨r,hr,B,U,hB,hU,hBx,hBZ,hZB,?_,short_family_first_jet_limit hx hU hZB hUE,hUH⟩
  filter_upwards [hBreg,hPsib,hBr,hloc,hBZ,hV] with q hreg hps hbr hlocq hz hq
  intro ht f hf hs
  have he : coordinateBackward a (-1,B q,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) (B q))=χ.symm q.2 := by
    calc
      _=χ.symm (χ (coordinateBackward a (-1,B q,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) (B q)))) :=
        (χ.left_inv hreg.2.2).symm
      _=χ.symm q.2 := congrArg χ.symm hz
  obtain ⟨ha,hd⟩ := shortForward_action (a := a) (ψ := fun y => ψ (q.1.1,y))
    (q := (q.1.2,B q)) hreg.1 hreg.2.1
  rw [he] at ha hd
  have hstat : fderiv ℝ (fun w => q.1.2*ψ (q.1.1,w)+chartCost a (χ.symm q.2) w) (B q)=0 := by
    have H := ((hps.differentiableAt (by simp)).hasFDerivAt.const_mul q.1.2).add hd
    convert! H.fderiv using 1
    simp only [add_neg_cancel]
  have heU : U q=ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2)/q.1.2 := by
    rw [hUE,ha]
    dsimp only [parametricShortEnergy]
    congr 1
    field_simp
  have hlo : U q≤hopfLax q.1.2 f (χ.symm q.2) := by
    obtain ⟨y,hy,_⟩ := exists_hopfLax_minimizer hf.continuous q.1.2 (χ.symm q.2)
    obtain ⟨hys,hyw⟩ := hlocq ht f hf y hy
    have hh := hmin q hq (B q) hbr hstat (χ y) (Metric.ball_subset_closedBall hyw)
    have hyy : χ.symm (χ y)=y := χ.left_inv hys
    have hysup := hs (χ y) (Metric.ball_subset_closedBall hyw)
    change q.1.2*ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2)≤
      q.1.2*ψ (q.1.1,χ y)+cost (χ.symm (χ y)) (χ.symm q.2) at hh
    rw [hyy] at hh hysup
    rw [heU,hy]
    apply (mul_le_mul_iff_left₀ ht).mp
    have hd1 : (ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2)/q.1.2)*q.1.2=
        q.1.2*ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2) := by field_simp
    have hd2 : (f y+cost y (χ.symm q.2)/q.1.2)*q.1.2=q.1.2*f y+cost y (χ.symm q.2) := by field_simp
    rw [hd1,hd2]
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hysup ht.le) le_rfl)
  refine ⟨hlo,fun hc => hlo.antisymm ?_⟩
  rw [heU,←hc]
  exact hopfLax_le hf.continuous q.1.2 (χ.symm q.2) (χ.symm (B q))

end WeakMTWTransport

end

end OAI
