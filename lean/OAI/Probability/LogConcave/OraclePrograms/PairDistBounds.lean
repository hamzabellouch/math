import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.CircuitParameters
import OAI.Probability.LogConcave.OraclePrograms.MeanTreeBase
import OAI.Probability.LogConcave.OraclePrograms.CalibratedMeanCircuit
import OAI.Probability.LogConcave.Numerics.BaseVariationCenters
import OAI.Probability.LogConcave.Numerics.EvalLipschitz

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma pair_dist_bounds (z w : Point d × Point d) :
    ‖z.1-w.1‖≤dist z w ∧ ‖z.2-w.2‖≤dist z w := by
  change ‖z.1-w.1‖≤ max (dist z.1 w.1) (dist z.2 w.2) ∧
    ‖z.2-w.2‖≤ max (dist z.1 w.1) (dist z.2 w.2)
  simp only [dist_eq_norm]
  exact ⟨le_max_left _ _,le_max_right _ _⟩

lemma meanTree_anchorVariation {r σ : ℝ} (hr : 0≤r) (x : Point d) (z w : Point d × Point d) :
    BaseVariation ((2*r+|σ/2|)*dist z w) (x,z) (x,w) (C.meanTree r σ) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint
  have hd := pair_dist_bounds z w
  apply baseVariation_of_centers
  · rw [C.meanTree_base]
    simp only [←smul_sub,norm_smul,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hd.2 (abs_nonneg (σ/2)),mul_nonneg hr (dist_nonneg (x:=z) (y:=w))]
  · exact centers_mono _ (fun r' b hb => by
      have he := hb.variation hr C.T_upper.le (x,z) (x,w)
      simp only [sub_self,norm_zero,zero_add] at he
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hd.1 hd.2) hr,
        mul_nonneg (abs_nonneg (σ/2)) (dist_nonneg (x:=z) (y:=w))]) hg.2

lemma sampleTree_anchorVariation {r η : ℝ} (hr : 0≤r) (hη : 0<η) (hη1 : η≤1)
    (x z w : Point d) :
    BaseVariation ((r+|(sampleCorrelation η)⁻¹|)*dist z w) (x,z) (x,w)
      (C.sampleTree r η hη hη1) := by
  have hp := sampleCorrelation_properties hη hη1
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)
  apply baseVariation_of_centers
  · unfold sampleTree
    rw [hg.1]
    simp only [←smul_sub,norm_smul,Real.norm_eq_abs,dist_eq_norm]
    nlinarith [mul_nonneg hr (norm_nonneg (z-w))]
  · exact centers_mono _ (fun r' b hb => by
      have he := hb.variation hr hp.2.1.le (x,z) (x,w)
      simp only [sub_self,norm_zero,zero_add,add_zero] at he
      rw [dist_eq_norm]
      nlinarith [mul_nonneg (abs_nonneg ((sampleCorrelation η)⁻¹)) (norm_nonneg (z-w))]) hg.2

lemma meanTree_anchor_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r σ : ℝ} (hr : 0<r) (hl : (lam:ℝ)*r^2≤1/4) (x : Point d) :
    ∃K : ℝ≥0,LipschitzWith K (fun z : Point d × Point d => (C.meanTree r σ).eval F (x,z)) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint
  apply eval_exists_lipschitz hF (C.meanTree r σ) (fun z => (x,z))
  · rw [C.meanTree_base]
    exact ⟨_,(lipschitzWith_smul (σ/2)).comp LipschitzWith.prod_snd⟩
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    have hr' := hb.radius_pos hr (by linarith [C.T_lower]) C.T_upper
    have hb' := hb.radius hr.le (by linarith [C.T_lower]) C.T_upper
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hb'.2 2) lam.coe_nonneg
    refine ⟨hr',hs.trans hl,?_⟩
    obtain ⟨ρ,hρ,θ,hθ,he,rfl⟩ := hb
    exact ⟨_,(LipschitzWith.const x).add ((lipschitzWith_smul (r*ρ)).comp
      (((lipschitzWith_smul (Real.cos θ)).comp LipschitzWith.prod_fst).add
      ((lipschitzWith_smul (Real.sin θ)).comp LipschitzWith.prod_snd)))⟩

lemma sampleTree_anchor_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r η : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1) (hl : (lam:ℝ)*r^2≤1/4) (x : Point d) :
    ∃K : ℝ≥0,LipschitzWith K (fun z : Point d => (C.sampleTree r η hη hη1).eval F (x,z)) := by
  have hp := sampleCorrelation_properties hη hη1
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)
  apply eval_exists_lipschitz hF (C.sampleTree r η hη hη1) (fun z => (x,z))
  · unfold sampleTree
    rw [hg.1]
    exact ⟨_,lipschitzWith_smul ((sampleCorrelation η)⁻¹)⟩
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    have hr' := hb.radius_pos hr (by linarith [hp.1]) hp.2.1
    have hb' := hb.radius hr.le (by linarith [hp.1]) hp.2.1
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hb'.2 2) lam.coe_nonneg
    refine ⟨hr',hs.trans hl,?_⟩
    obtain ⟨ρ,hρ,θ,hθ,he,rfl⟩ := hb
    exact ⟨_,(LipschitzWith.const x).add ((lipschitzWith_smul (r*ρ)).comp
      ((lipschitzWith_smul (Real.cos θ)).add ((lipschitzWith_smul (Real.sin θ)).comp (LipschitzWith.const 0))))⟩

lemma meanCompiled_anchor_lipschitz {r σ Lf Li : ℝ} (hr : 0<r) (hσ : 0<σ)
    (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.meanCenterBudget r σ≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.meanCenterBudget r σ) C.Af
      (P true) (P false) (C.meanTree (d:=d) r σ) n) (x : Point d) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af
      (M true) (M false) (C.meanTree (d:=d) r σ) n
    ∃K : ℝ,0≤K ∧ ∀z w g,‖E.eval V (x,z) g-E.eval V (x,w) g‖≤K*dist z w := by
  have hw := C.meanTree_actual_weights (d:=d) hr hσ hψ
  rw [←hAf,←hA] at hw
  have hAf0 : 0≤C.Af := by rw [hAf]; exact C.actualAf_pos.le
  let b := 2*r+|σ/2|
  refine ⟨C.Af*Lf*(depth (C.meanTree (d:=d) r σ):ℝ)*b+b,by dsimp [b]; positivity,?_⟩
  intro z w g
  have hv := C.meanTree_anchorVariation (σ:=σ) hr.le x z w
  have hb : ‖base (C.meanTree r σ) (x,z)-base (C.meanTree r σ) (x,w)‖≤b*dist z w := by
    generalize C.meanTree (d:=d) r σ=E at hv ⊢
    cases E
    exact hv.1
  have he := compileDeclaredRoot_variation hLf hLi (show 0≤b*dist z w by dsimp [b]; positivity)
    hsmall V P M hm hmi (C.meanTree r σ) n (x,z) (x,w) hv hb hw.1 hw.2 hready g
  convert he using 1
  dsimp [b]
  ring

lemma sampleCompiled_anchor_lipschitz {r η Lf Li : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.sampleCenterBudget r≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (P true) (P false) (C.sampleTree (d:=d) r η hη hη1) n) (x : Point d) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (M true) (M false) (C.sampleTree (d:=d) r η hη hη1) n
    ∃K : ℝ,0≤K ∧ ∀z w g,‖E.eval V (x,z) g-E.eval V (x,w) g‖≤K*dist z w := by
  have hw := C.sampleTree_actual_weights (d:=d) hr hη hη1
  rw [←hAf,←hA] at hw
  have hAf0 : 0≤C.sampleFinalBudget r := by unfold sampleFinalBudget; rw [hAf]; positivity [C.actualAf_pos]
  let b := r+|(sampleCorrelation η)⁻¹|
  refine ⟨C.sampleFinalBudget r*Lf*(depth (C.sampleTree (d:=d) r η hη hη1):ℝ)*b+b,by dsimp [b]; positivity,?_⟩
  intro z w g
  have hv := C.sampleTree_anchorVariation hr.le hη hη1 x z w
  have hb : ‖base (C.sampleTree r η hη hη1) (x,z)-base (C.sampleTree r η hη hη1) (x,w)‖≤b*dist z w := by
    generalize C.sampleTree (d:=d) r η hη hη1=E at hv ⊢
    cases E
    exact hv.1
  have he := compileDeclaredRoot_variation hLf hLi (show 0≤b*dist z w by dsimp [b]; positivity)
    hsmall V P M hm hmi (C.sampleTree r η hη hη1) n (x,z) (x,w) hv hb hw.1 hw.2 hready g
  convert he using 1 <;> (try simp only [sampleFinalBudget])
  dsimp [b]
  ring

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeasureTheory ProbabilityTheory MeanTree Quadrature Function
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma meanTree_eval {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r σ : ℝ) (x : Point d) (y : Point d × Point d) :
    (C.meanTree r σ).eval F (x,y)=
      centeringMeanCircuit F x r C.T C.h C.ψ (σ/2) C.n C.m C.N C.nc C.Nc C.meanEndpoint
        ((productPointEquiv d d).symm y) := by
  unfold meanTree literalMean
  rw [eval_meanCircuit hF (by linarith [C.T_lower]) C.T_upper C.h_pos]
  simp only [eval_anchor]

lemma sampleTree_eval {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r η : ℝ) (hη : 0<η) (hη1 : η≤1) (x Y : Point d) :
    (C.sampleTree r η hη hη1).eval F (x,Y)=
      sampleMeanCircuit F x r (sampleCorrelation η) C.h (C.n+1) C.N (C.sampleEndpoint η hη hη1) Y := by
  unfold sampleTree literalSample
  rw [eval_scale,eval_forward hF (Nat.succ_pos C.n)
    (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos]
  simp only [eval_anchor,sampleMeanCircuit]

theorem meanTree_numerical {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r σ err : ℝ} (hr : 0<r) (hl : (lam:ℝ)*r^2≤1/4)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (hcert : CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hr (by linarith : (lam:ℝ)*r^2≤1/2) (by linarith [C.T_lower]) C.T_upper
      C.h_pos C.n C.N err) :
    ∃w : Point d × Point d → Point d,Measurable w ∧
      ((interpolationLaw F x r C.T).prod (stdGaussian (Point d))).map w=
        (stdGaussian (Point d)).map (fun z => primitiveExpectedField F x r+(σ/2) • z) ∧
      Integrable (fun z => ‖(C.meanTree r σ).eval F (x,z)-w z‖^2)
        ((interpolationLaw F x r C.T).prod (stdGaussian (Point d))) ∧
      (∫z,‖(C.meanTree r σ).eval F (x,z)-w z‖^2
        ∂(interpolationLaw F x r C.T).prod (stdGaussian (Point d)))≤
          ((σ/2)*circuitD F x)^2*err := by
  obtain ⟨X,hsi,hsb,hw,hlaw,hi,hnum⟩ := hcert
  let w₀ := stationaryMeanTarget hF x hr (by linarith : (lam:ℝ)*r^2≤1/2)
    (by linarith [C.T_lower] : 0≤C.T) C.T_upper X
  let w : Point d × Point d → Point d := fun z => w₀ ((productPointEquiv d d).symm z)
  have hw' : Measurable w := hw.comp (productPointEquiv d d).symm.continuous.measurable
  have hjoint := centering_joint_law hF x hr.le (by linarith : (lam:ℝ)*r^2≤1/2)
    (by linarith [C.T_lower]) C.T_upper
  obtain ⟨K,hK⟩ := C.meanTree_anchor_lipschitz hF hr hl x
  have hg : Measurable (fun z => (C.meanTree r σ).eval F (x,z)) := hK.continuous.measurable
  have hid : ∀y : Point (d+d),
      (C.meanTree r σ).eval F (x,productPointEquiv d d y)-w (productPointEquiv d d y)=
      centeringMeanCircuit F x r C.T C.h C.ψ (σ/2) C.n C.n C.N C.n C.N C.meanEndpoint y-w₀ y := by
    intro y
    rw [C.meanTree_eval hF]
    simp only [hm,hnc,hNc,w,ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨w,hw',?_,?_,?_⟩
  · rw [←hjoint,Measure.map_map hw' (productPointEquiv d d).continuous.measurable]
    simpa only [comp_def,w,ContinuousLinearEquiv.symm_apply_apply] using hlaw
  · rw [←hjoint]
    apply (integrable_map_measure (by fun_prop) (productPointEquiv d d).continuous.measurable.aemeasurable).mpr
    simpa only [hid,comp_def,meanEndpoint,w₀] using hi
  · rw [←hjoint,integral_map (productPointEquiv d d).continuous.measurable.aemeasurable (by fun_prop)]
    simpa only [hid,meanEndpoint,w₀] using hnum

lemma meanTree_numerical_noisy {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r σ err : ℝ} (hr : 0<r) (hl : (lam:ℝ)*r^2≤1/4)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (hcert : CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hr (by linarith : (lam:ℝ)*r^2≤1/2) (by linarith [C.T_lower]) C.T_upper
      C.h_pos C.n C.N err) :
    ∃w : Point d × Point d → Point d,Measurable w ∧
      (((interpolationLaw F x r C.T).prod (stdGaussian (Point d))).prod (stdGaussian (Point d))).map
        (fun z => w z.1+(Real.sqrt 3*σ/2) • z.2)=
        (stdGaussian (Point d)).map (fun z => primitiveExpectedField F x r+σ • z) ∧
      Integrable (fun z => ‖(C.meanTree r σ).eval F (x,z)-w z‖^2)
        ((interpolationLaw F x r C.T).prod (stdGaussian (Point d))) ∧
      (∫z,‖(C.meanTree r σ).eval F (x,z)-w z‖^2
        ∂(interpolationLaw F x r C.T).prod (stdGaussian (Point d)))≤
          ((σ/2)*circuitD F x)^2*err := by
  obtain ⟨w,hw,hlaw,hi,hnum⟩ := C.meanTree_numerical hF x hr hl hm hnc hNc hcert
  let := interpolationLaw_probability hF x hr.le (by linarith : (lam:ℝ)*r^2<1) C.T
  refine ⟨w,hw,?_,hi,hnum⟩
  apply law_add_gaussian _ w hw (primitiveExpectedField F x r) (σ/2) (Real.sqrt 3*σ/2) σ _ hlaw
  rw [div_pow,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  ring
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
