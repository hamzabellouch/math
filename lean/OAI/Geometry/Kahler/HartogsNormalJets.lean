import OAI.Geometry.Kahler.HartogsGauge

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma _root_.OAI.ContDiffAt.hartogs_dzBase {f : Base → ℂ} {p : Base} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 2) :
    ContDiffAt ℝ m (fun q => dzBase f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dzBase
  exact ((hd.clm_apply contDiffAt_const).sub
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma dz_dz_lift_base {f : Base → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p.1)
    (a c : Fin 3) :
    dz (fun q => dz (fun r : Ambient => f r.1) q c) p a =
      !![dzBase (fun z => dzBase f z 0) p.1 0, dzBase (fun z => dzBase f z 1) p.1 0, 0;
         dzBase (fun z => dzBase f z 0) p.1 1, dzBase (fun z => dzBase f z 1) p.1 1, 0;
         0,0,0] a c := by
  have he : (fun q => dz (fun r : Ambient => f r.1) q c) =ᶠ[𝓝 p]
      (fun q => ![dzBase f q.1 0, dzBase f q.1 1, 0] c) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with q hq
    change ContDiffAt ℝ 2 f q.1 at hq
    exact dz_lift_base (hq.differentiableAt (by norm_num)) c
  rw [dz_congr he]
  have hd (i : Fin 2) := (_root_.OAI.ContDiffAt.hartogs_dzBase hf (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  fin_cases a <;> fin_cases c
  all_goals first
    | exact dz_lift_base (hd 0) _
    | exact dz_lift_base (hd 1) _
    | simp [dz]

lemma dz_gaugePolynomial_vertical (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (p : Ambient) :
    dz (gaugePolynomial a B) p 2 = 0 := by
  rw [dz_gaugePolynomial]
  simp [Fin.sum_univ_two]

lemma dz_dz_gaugePolynomial_vertical_right (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (p : Ambient) (i : Fin 3) : dz (fun q => dz (gaugePolynomial a B) q 2) p i = 0 := by
  simp only [dz_gaugePolynomial_vertical]
  simp [dz]

lemma dz_dz_gaugePolynomial_vertical_left (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (p : Ambient) (i : Fin 3) : dz (fun q => dz (gaugePolynomial a B) q i) p 2 = 0 := by
  rw [dz_dz_comm ((gaugePolynomial_analytic a B p (mem_univ p)).contDiffAt.restrict_scalars ℝ)]
  exact dz_dz_gaugePolynomial_vertical_right a B p i

lemma dz_dz_gaugePolynomial_all (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (hB : ∀ i k, B i k = B k i) (p : Ambient) (i k : Fin 3) :
    dz (fun q => dz (gaugePolynomial a B) q k) p i =
      !![B 0 0, B 0 1, 0; B 1 0, B 1 1, 0; 0,0,0] i k := by
  fin_cases i <;> fin_cases k
  · exact dz_dz_gaugePolynomial a B hB p 0 0
  · exact dz_dz_gaugePolynomial a B hB p 0 1
  · exact dz_dz_gaugePolynomial_vertical_right a B p 0
  · exact dz_dz_gaugePolynomial a B hB p 1 0
  · exact dz_dz_gaugePolynomial a B hB p 1 1
  · exact dz_dz_gaugePolynomial_vertical_right a B p 1
  · exact dz_dz_gaugePolynomial_vertical_left a B p 0
  · exact dz_dz_gaugePolynomial_vertical_left a B p 1
  · exact dz_dz_gaugePolynomial_vertical_right a B p 2

def baseGaugePolynomial (f : Base → ℝ) (w : ℂ) : Ambient → ℂ :=
  gaugePolynomial (firstGaugeJet (fun q => f q.1) (0,w))
    (secondGaugeJet (fun q => f q.1) (0,w))

def normalLogWeight (f : Base → ℝ) (w : ℂ) (q : Ambient) : ℝ :=
  f q.1 - 2 * (baseGaugePolynomial f w q - q.2).re

lemma baseGaugePolynomial_analytic (f : Base → ℝ) (w : ℂ) (q : Ambient) :
    AnalyticAt ℂ (baseGaugePolynomial f w) q := gaugePolynomial_analytic _ _ q (mem_univ _)

lemma normalLogWeight_contDiffAt {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ ∞ f q.1) (w : ℂ) : ContDiffAt ℝ ∞ (normalLogWeight f w) q := by
  have hP : AnalyticAt ℂ (fun q => baseGaugePolynomial f w q - q.2) q :=
    (baseGaugePolynomial_analytic f w q).sub ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt q)
  exact (hf.comp q contDiffAt_fst).sub
    (contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp q (hP.contDiffAt.restrict_scalars ℝ)))

lemma normalLogWeight_hessian {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (w : ℂ) :
    complexHessian (normalLogWeight f w) q = complexHessian (fun q : Ambient => f q.1) q :=
  complexHessian_gauge (hf.comp q contDiffAt_fst)
    ((baseGaugePolynomial_analytic f w q).sub ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt q))

lemma normalLogWeight_first {f : Base → ℝ} (hf : ContDiffAt ℝ 2 f 0) (w : ℂ) (i : Fin 3) :
    dz (fun q => (normalLogWeight f w q : ℂ)) (0,w) i = if i = 2 then 1 else 0 := by
  have hP := (baseGaugePolynomial_analytic f w (0,w)).differentiableAt
  have hv := (ContinuousLinearMap.snd ℂ Base ℂ).differentiableAt (x := (0,w))
  have hf' : DifferentiableAt ℝ (fun q : Ambient => f q.1) (0,w) :=
    (hf.differentiableAt (by norm_num)).comp (0,w) differentiableAt_fst
  unfold normalLogWeight
  erw [dz_gauge hf' (hP.sub hv), dz_sub (hP.restrictScalars ℝ) (hv.restrictScalars ℝ), dz_fiber]
  change dz (fun q : Ambient => (f q.1 : ℂ)) (0,w) i -
    (dz (gaugePolynomial _ _) (0,w) i - (if i = 2 then 1 else 0)) = _
  fin_cases i
  · erw [dz_gaugePolynomial_center _ _ w 0]
    simp [firstGaugeJet]
  · erw [dz_gaugePolynomial_center _ _ w 1]
    simp [firstGaugeJet]
  · have hfc : DifferentiableAt ℝ (fun z => (f z : ℂ)) (0,w).1 :=
      Complex.ofRealCLM.differentiableAt.comp 0 (hf.differentiableAt (by norm_num))
    rw [dz_lift_base hfc, dz_gaugePolynomial]
    simp [Fin.sum_univ_two]

lemma normalLogWeight_pureSecond {f : Base → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (w : ℂ) (i k : Fin 3) :
    dz (fun q => dz (fun r => (normalLogWeight f w r : ℂ)) q k) (0,w) i = 0 := by
  have hL : ContDiffAt ℝ 2 (fun q : Ambient => f q.1) (0,w) := hf.comp (0,w) contDiffAt_fst
  have hP := baseGaugePolynomial_analytic f w (0,w)
  have hv : AnalyticAt ℂ (fun q : Ambient => q.2) (0,w) :=
    (ContinuousLinearMap.snd ℂ Base ℂ).analyticAt _
  have he : (fun q => dz (fun r => baseGaugePolynomial f w r - r.2) q k) =
      (fun q => dz (baseGaugePolynomial f w) q k - if k = 2 then 1 else 0) := by
    funext q
    erw [dz_sub ((baseGaugePolynomial_analytic f w q).differentiableAt.restrictScalars ℝ)
      (ContinuousLinearMap.snd ℝ Base ℂ).differentiableAt, dz_fiber]
  unfold normalLogWeight
  erw [dz_dz_gauge hL (hP.sub hv), he,
    dz_sub ((dz_analyticAt hP k).differentiableAt.restrictScalars ℝ) (differentiableAt_const _)]
  have hc : dz (fun _ : Ambient => if k = 2 then (1 : ℂ) else 0) (0,w) i = 0 := by simp [dz]
  rw [hc, sub_zero]
  change dz (fun q => dz (fun r : Ambient => (f r.1 : ℂ)) q k) (0,w) i -
    dz (fun q => dz (baseGaugePolynomial f w) q k) (0,w) i = 0
  rw [baseGaugePolynomial, dz_dz_gaugePolynomial_all _ _ (secondGaugeJet_symm hL)]
  have hfc : ContDiffAt ℝ 2 (fun z => (f z : ℂ)) 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hf
  have hdd (a c : Fin 3) := dz_dz_lift_base (p := (0,w)) hfc a c
  simp only [secondGaugeJet, hdd]
  fin_cases i <;> fin_cases k <;> simp

lemma normalLogWeight_hessian_eventually {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (w : ℂ) :
    complexHessian (normalLogWeight f w) =ᶠ[𝓝 (0,w)] complexHessian (fun q : Ambient => f q.1) := by
  have he : ∀ᶠ z in 𝓝 (0 : Base), ContDiffAt ℝ 2 f z := (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)
  filter_upwards [continuousAt_fst.preimage_mem_nhds he] with q hq
  change ContDiffAt ℝ 2 f q.1 at hq
  exact normalLogWeight_hessian hq w

lemma dbar_dz_dz_real {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 3 s p) (a b c : Fin 3) :
    dbar (fun q => dz (fun r => dz (fun t => (s t : ℂ)) r c) q a) p b =
      dz (fun q => complexHessian s q c b) p a := by
  rw [← dz_dbar_comm (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) c)]
  apply dz_congr
  filter_upwards [hs.eventually (by norm_num)] with q hq
  exact dbar_dz_real_eq_hessian (hq.of_le (by norm_num)) c b

lemma dbar_dbar_real {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 2 s p) (a b : Fin 3) :
    dbar (fun q => dbar (fun r => (s r : ℂ)) q a) p b =
      star (dz (fun q => dz (fun r => (s r : ℂ)) q a) p b) := by
  have he : (fun q => dbar (fun r => (s r : ℂ)) q a) =ᶠ[𝓝 p]
      (fun q => star (dz (fun r => (s r : ℂ)) q a)) := by
    filter_upwards [hs.eventually (by norm_num)] with q hq
    exact dbar_eq_star_dz_real (hq.differentiableAt (by norm_num)) a
  rw [dbar_congr he]
  exact dbar_conj ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) a).differentiableAt (by norm_num)) b

lemma normalLogWeight_barFirst {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (i : Fin 3) :
    dbar (fun q => (normalLogWeight f w q : ℂ)) (0,w) i = if i = 2 then 1 else 0 := by
  rw [dbar_eq_star_dz_real ((normalLogWeight_contDiffAt hf w).differentiableAt (by simp)),
    normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  split_ifs <;> simp

lemma normalLogWeight_pureBarSecond {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (i k : Fin 3) :
    dbar (fun q => dbar (fun r => (normalLogWeight f w r : ℂ)) q k) (0,w) i = 0 := by
  rw [dbar_dbar_real ((normalLogWeight_contDiffAt hf w).of_le (WithTop.coe_le_coe.mpr le_top)),
    normalLogWeight_pureSecond (hf.of_le (WithTop.coe_le_coe.mpr le_top)), star_zero]

end PinchedHartogs

end

end OAI
