import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.UniformFixedCrossing
import OAI.Analysis.BiholderTransport.Regularity.MaximumFamily
import OAI.Analysis.BiholderTransport.Regularity.OuterTemplatePrimitive
import OAI.Analysis.BiholderTransport.Calculus.UniformCostTaylor
import OAI.Analysis.BiholderTransport.Calculus.ScalarFamilyBounds
import OAI.Analysis.BiholderTransport.Regularity.ActualSmallPlateau
import OAI.Analysis.BiholderTransport.Oscillation.SwitchToExcess
import OAI.Analysis.BiholderTransport.Oscillation.SwitchNumerics
import OAI.Analysis.BiholderTransport.Regularity.FamilyGlobal
import OAI.Analysis.BiholderTransport.Regularity.SmallEpsilon

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric MeasureTheory
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section NonpowerMaximum
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.nonpower_maximum (hmtw:WeakMTW (n:=n) (M:=M))
    {lam cap:ℝ} {x0:M} (hc:(densityDualClass (metricVolume n) lam cap x0).Nonempty)
    (hno:¬HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0))
    {M0 K eta C θ:ℝ} (hM:2 ≤ M0) (hK:1 ≤ K) (heta:0 < eta) (heta1:eta ≤ 1/128)
    (hetasmall:eta ≤ templateEps/(24*(128*(M0+3)*(K+1))))
    (hC:0 ≤ C) (hder:∀s,|deriv (outerTemplate M0 K eta) s| ≤ C) (hθ:0 < θ) :
    ∃uv∈densityDualClass (metricVolume n) lam cap x0,∃α D bm bp:ℝ,
      0 < D ∧ 0 < bm ∧ 0 < bp ∧ bp ≤ θ*D ∧ bp/D*centerGamma ≤ 1 ∧ bp/D*C ≤ 1/2 ∧
      (∀z:M,sectionOscillation uv.1 uv.2 z ((2*M0+10)*bp) ≤ (1+eta)*D) ∧
      2*(2*M0+10)*bp ≤ eta*D ∧
      Nonempty (MaximumFamily (n:=n) uv.2 α D bm bp centerTemplate (outerTemplate M0 K eta)) := by
  classical
  let H:ℝ:=2*M0+8
  have hH:0 ≤ H:=by dsimp [H]; linarith only [hM]
  let P:ℝ:=Metric.diam (univ:Set M)
  have hP:0 ≤ P:=Metric.diam_nonneg
  have hγ:=centerGamma_pos
  obtain ⟨Cg,hCg,d,hd,hTaylor⟩:=exists_uniform_cost_upper_taylor (n:=n) (M:=M)
  let S:Finset ℝ:={eta,1/(2^40),1/(H+100),1/(16*H+1000),
    1/(1048576*(Cg+1)*(P^2+1)),d/(16*(P+1)),eta/(2*(H+2)),1/(H+2),θ,
    1/centerGamma,1/(2*(C+1))}
  have hS:∀a∈S,0 < a:=by
    intro a ha
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> positivity
  obtain ⟨e,he,hse⟩:=exists_small_positive S hS
  have heeta:e ≤ eta:=hse _ (by simp [S])
  have he40:e ≤ 1/(2^40):=hse _ (by simp [S])
  have heR:e*(H+100) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heD:e*(16*H+1000) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heQ:e*(1048576*(Cg+1)*(P^2+1)) ≤ 1:=
    (le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have hed:e*(16*(P+1)) ≤ d:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heη:e*(2*(H+2)) ≤ eta:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heHR:e*(H+2) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heθ:e ≤ θ:=hse _ (by simp [S])
  have heγ:e*centerGamma ≤ 1:=(le_div_iff₀ hγ).mp (hse _ (by simp [S]))
  have heC:e*(2*(C+1)) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have he1:e ≤ 1:=by norm_num at he40; linarith only [he40]
  obtain ⟨r,R,bm,bp,hr,hR,hbm,hbp,uv,huv,x,y0,y1,hy0,hy1,hlo,hhi,hsec,hD,hglobal,
    hrbm,hbmbp,hbpR,hbpPow⟩:=exists_actual_small_plateau hc hno he
  let D:=uv.2 y1-uv.2 y0
  change 0 < D at hD
  change sectionOscillation uv.1 uv.2 x r = D at hsec
  let α:=uv.2 y0
  let b:ℝ:=bp/8192
  have hb:0 < b:=div_pos hbp (by norm_num)
  have hbbp:b ≤ bp:=by dsimp [b]; linarith only [hbp]
  have hbpD:bp ≤ e*D:=by simpa only [pow_one] using hbpPow 1 (by norm_num)
  have hbD':b ≤ e*D:=hbbp.trans hbpD
  have hbpD2:bp ≤ e*D^2:=hbpPow 2 le_rfl
  have hbmle:bm ≤ bp:=hbmbp.trans (by nlinarith only [he1,hbp])
  have hrbp:r ≤ e*bp:=hrbm.trans (mul_le_mul_of_nonneg_left hbmle he.le)
  have hrb:r ≤ b/2048:=by
    have HH:=mul_le_mul_of_nonneg_right he40 hbp.le
    dsimp [b]
    norm_num at HH
    linarith only [hrbp,HH,hbp]
  have hsmallbm:bm ≤ bp/(64*1024^2):=by
    have HH:=mul_le_mul_of_nonneg_right he40 hbp.le
    norm_num at HH ⊢
    linarith only [hbmbp,HH,hbp]
  have hbR:b*(H+100) ≤ R:=by
    simpa only [one_mul] using ratio_mul_le (hbbp.trans hbpR) (by positivity) hR.le heR
  have hbDb:b*(16*H+1000) ≤ D:=by
    simpa only [one_mul] using ratio_mul_le hbD' (by positivity) hD.le heD
  obtain ⟨p,hp,hep⟩:=exists_minimizing_vector (n:=n) x y0
  obtain ⟨q,hq,heq⟩:=exists_minimizing_vector (n:=n) x y1
  have hpP:‖p‖ ≤ P:=minimizing_norm_le_diam hp
  have hpP2:‖p‖^2 ≤ P^2:=sq_le_sq₀ (norm_nonneg _) hP |>.mpr hpP
  have hbQuad:b*(Cg+1)*(‖p‖^2+1) ≤ D^2/1048576:=by
    have hh:=ratio_mul_le (hbbp.trans hbpD2) (by positivity) (sq_nonneg D) heQ
    rw [one_mul] at hh
    have hmul:=mul_le_mul_of_nonneg_left (add_le_add_right hpP2 1) (show 0 ≤ b*(Cg+1) by positivity)
    nlinarith only [hh,hmul]
  obtain ⟨hrb4,hbD16,hanchor,hlower,hlower',hnorm,herror⟩:=switch_numerical_errors hb hD hr.le hCg.le hH
    (sq_nonneg ‖p‖) heta1 hrb hbR hbDb hbQuad
  have hsdisp:‖(8*b/D:ℝ) • p‖ < d:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 8*b/D)]
    have hratio:b/D ≤ e:=(div_le_iff₀ hD).mpr hbD'
    have hh:=mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8*‖p‖ by positivity)
    have hhP:=mul_le_mul_of_nonneg_left hpP (show 0 ≤ 8*e by positivity)
    calc
      (8*b/D)*‖p‖ = (b/D)*(8*‖p‖) := by ring
      _ ≤ e*(8*‖p‖) := hh
      _ = 8*e*‖p‖ := by ring
      _ ≤ 8*e*P := hhP
      _ < d := by nlinarith only [hed,he,mul_nonneg he.le hP]
  have hdual:=densityDualClass_isDual huv
  have ha:uv.2 (riemannianExp x p)=α:=by rw [hep]
  have ha1:uv.2 (riemannianExp x q)=α+D:=by rw [heq]; dsimp [α,D]; ring
  have hpsec:p∈liftedGapSection uv.1 uv.2 x r:=mem_liftedGapSection_iff.mpr ⟨hp,by rwa [hep]⟩
  have hqsec:q∈liftedGapSection uv.1 uv.2 x r:=mem_liftedGapSection_iff.mpr ⟨hq,by rwa [heq]⟩
  have hangle:‖p‖^2-inner ℝ p q ≤ 6*D:=
    (hmtw.section_initial_logs uv.1.continuous uv.2.continuous hdual hr.le
      (by linarith only [hrb4,hbD16,hD]) hpsec hqsec ha ha1 hsec.le).2.2.1
  have hosc (z:M):sectionOscillation uv.1 uv.2 z R ≤ (1+eta)*D:=by
    apply (sectionOscillation_le_classOscillation huv z hR.le).trans
    exact hglobal.trans (mul_le_mul_of_nonneg_right (add_le_add_right heeta 1) hD.le)
  let Bo:=outerTemplate M0 K eta
  have hBo:ContDiff ℝ ∞ Bo:=outerTemplate_smooth _ _ _
  have hob (s):0 ≤ Bo s ∧ Bo s ≤ H:=⟨outerTemplate_nonneg hM hK heta heta1 hetasmall,
    outerTemplate_upper hM hK heta heta1 hetasmall⟩
  obtain ⟨y,hy⟩:=hmtw.switch_to_positive_excess uv.1.continuous uv.2.continuous hdual hp hq hBo.continuous
    ha ha1 hb hD hr.le hR.le hCg.le (mem_liftedGapSection_iff.mp hpsec).2 (mem_liftedGapSection_iff.mp hqsec).2 hangle heta.le heta1 hrb4 hbD16 hob
    (by dsimp [Bo]; rw [outerTemplate_zero_level heta heta1,templateEps_eq]; norm_num)
    (outerTemplate_zero heta le_rfl)
    (fun s hs=>outerTemplate_lower hM hK heta heta1 hetasmall (by linarith only [hs,heta1]))
    (fun s hs=>outerTemplate_barrier hM hK heta heta1 hs.1 hs.2)
    (fun s=>(centerTemplate_bounds s).1.le) (fun s hs=>by simpa only [templateEps_eq] using centerTemplate_left hs)
    hsdisp hanchor hosc hlower hlower' hnorm herror hTaylor
  have hγsmall:bp/D*centerGamma ≤ 1:=by
    have hh:=ratio_mul_le hbpD hγ.le hD.le heγ
    rw [one_mul] at hh
    calc bp/D*centerGamma = (bp*centerGamma)/D := by ring
         _ ≤ 1 := (div_le_iff₀ hD).mpr (by simpa only [one_mul] using hh)
  have hCsmall:bp/D*C ≤ 1/2:=by
    have heC':e*C ≤ 1/2:=by nlinarith only [heC,he]
    have hh:=ratio_mul_le hbpD hC hD.le heC'
    calc bp/D*C = (bp*C)/D := by ring
         _ ≤ 1/2 := (div_le_iff₀ hD).mpr hh
  have hsCenter (s:ℝ) (hs:s∈Icc bm bp):s/D*(centerGamma/2) ≤ 1/2:=by
    have hh:=mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hs.2) hγ.le
    nlinarith only [hh,hγsmall]
  have hmono (s:ℝ) (hs:s∈Icc bm bp):Monotone (fun t=>modifiedScalar α D centerTemplate (s,t)):=
    (modifiedScalar_strictMono centerTemplate_smooth (by positivity) hD (hbm.le.trans hs.1)
      (hsCenter s hs) exact_center_deriv_abs α).monotone
  have hLipφ (s:ℝ) (hs:s∈Icc bm bp):LipschitzWith 2 (fun t=>modifiedScalar α D centerTemplate (s,t)):=
    modifiedScalar_lipschitz centerTemplate_smooth (by positivity) hD (hbm.le.trans hs.1)
      (hsCenter s hs) exact_center_deriv_abs α
  let Lv:ℝ≥0:=⟨P,hP⟩
  have hvL:LipschitzWith Lv (uv.2:M → ℝ):=by
    rw [hdual.2]
    exact cTransform_lipschitz uv.1.continuous (fun x y=>Metric.dist_le_diam_of_mem
      isCompact_univ.isBounded (mem_univ x) (mem_univ y))
  obtain ⟨A,hA⟩:=isCompact_univ.exists_bound_of_continuousOn uv.2.continuous.continuousOn
  have hrange:∀y:M,cTransform uv.1 y∈Icc (-A) A:=by
    intro y
    rw [←hdual.2]
    exact abs_le.mp (hA y (mem_univ y))
  obtain ⟨δ,hδ,hreg⟩:=uniform_family_short_mdifferentiable (n:=n) (M:=M)
    (modifiedScalar_contDiff centerTemplate_smooth α D) isCompact_Icc hmono hLipφ (-A) A
  have hL:∀s∈Icc bm bp,LipschitzWith (2*Lv) (modifiedDatum uv.2 α D s centerTemplate):=
    fun s hs=>(hLipφ s hs).comp hvL
  have hreg':∀s∈Icc bm bp,∀τ:ℝ,0 < τ → τ < δ →
      MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (modifiedDatum uv.2 α D s centerTemplate)):=by
    intro s hs τ hτ hτδ
    change MDifferentiable _ _ (hopfLax τ (fun y=>uv.2 y+s*centerTemplate ((uv.2 y-α)/D)))
    simpa only [←hdual.2,modifiedScalar] using hreg s hs uv.1 uv.1.continuous hrange τ hτ hτδ
  have hF:=hmtw.exists_maximum_family uv.2.continuous centerTemplate_smooth.continuous hBo.continuous hob
    hbp hbm.le hsmallbm
    (fun s hs z=>modified_excess_upper uv.1.continuous uv.2.continuous hdual hBo.continuous
      (hbm.le.trans hs.1) (fun t=>(hob t).1) (fun t=>(centerTemplate_bounds t).2.le) z)
    (show ∃y,bp/(8*1024^2) ≤ modifiedExcess uv.2 α D (bp/(8*1024)) centerTemplate Bo y from by
      refine ⟨y,?_⟩
      simpa only [b,show (8192:ℝ)=8*1024 by norm_num,div_div,pow_two,mul_assoc] using hy)
    hL hδ hreg'
  refine ⟨uv,huv,α,D,bm,bp,hD,hbm,hbp,hbpD.trans (mul_le_mul_of_nonneg_right heθ hD.le),
    hγsmall,hCsmall,?_,?_,hF⟩
  · intro z
    apply le_trans (sectionOscillation_mono uv.2.continuous hdual z (by positivity) ?_) (hosc z)
    have hh:=ratio_mul_le hbpR (show 0 ≤ H+2 by positivity) hR.le heHR
    dsimp [H] at hh
    nlinarith only [hh]
  · have hh:=ratio_mul_le hbpD (show 0 ≤ 2*(H+2) by positivity) hD.le heη
    dsimp [H] at hh
    nlinarith only [hh]

end NonpowerMaximum
end WeakMTWTransport

end
end

end OAI
