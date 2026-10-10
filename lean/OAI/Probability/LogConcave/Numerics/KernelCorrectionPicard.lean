import Mathlib
import OAI.Probability.LogConcave.Complexity.ProbabilityRmsBudget

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory
open scoped NNReal

variable {Ω E H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [SecondCountableTopology E] in
lemma lipschitz_error_sq {f g : Ω → E} (hf : Measurable f) (hg : Measurable g)
    {Q : E → H} {K : ℝ≥0} (hQ : LipschitzWith K Q)
    (hi : Integrable (fun y => ‖f y-g y‖^2) μ)
    {B : ℝ} (hB : (∫y,‖f y-g y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖Q (f y)-Q (g y)‖^2) μ ∧
    (∫y,‖Q (f y)-Q (g y)‖^2 ∂μ)≤(K:ℝ)^2*B := by
  have hpt (y : Ω) : ‖Q (f y)-Q (g y)‖^2≤(K:ℝ)^2*‖f y-g y‖^2 := by
    simpa only [dist_eq_norm,mul_pow] using pow_le_pow_left₀ (dist_nonneg)
      (hQ.dist_le_mul (f y) (g y)) 2
  have hs : Integrable (fun y => ‖Q (f y)-Q (g y)‖^2) μ :=
    (hi.const_mul ((K:ℝ)^2)).mono'
      (((hQ.continuous.measurable.comp hf).sub (hQ.continuous.measurable.comp hg)).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs,abs_sq] using hpt y))
  refine ⟨hs,?_⟩
  have hb := integral_mono hs (hi.const_mul ((K:ℝ)^2)) hpt
  rw [integral_const_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hB (sq_nonneg _))

lemma add_error_sq {f g k : Ω → E} (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hfg : Integrable (fun y => ‖f y-g y‖^2) μ)
    (hgk : Integrable (fun y => ‖g y-k y‖^2) μ)
    {A B : ℝ} (hA : (∫y,‖f y-g y‖^2 ∂μ)≤A) (hB : (∫y,‖g y-k y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖f y-k y‖^2) μ ∧ (∫y,‖f y-k y‖^2 ∂μ)≤2*A+2*B := by
  have he (y : Ω) : f y-k y=(f y-g y)-(k y-g y) := by abel
  have hi : Integrable (fun y => ‖k y-g y‖^2) μ := by simpa only [norm_sub_rev] using hgk
  have hb : (∫y,‖k y-g y‖^2 ∂μ)≤B := by simpa only [norm_sub_rev] using hB
  simp_rw [he]
  exact sub_sq_bound (hf.sub hg).aestronglyMeasurable (hk.sub hg).aestronglyMeasurable hfg hi hA hb

omit [SecondCountableTopology E] in
lemma compose_error_sq {f g : Ω → E} {k : Ω → H}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    {Q : E → H} {K : ℝ≥0} (hQ : LipschitzWith K Q)
    (hfg : Integrable (fun y => ‖f y-g y‖^2) μ)
    (hgk : Integrable (fun y => ‖Q (g y)-k y‖^2) μ)
    {A B : ℝ} (hA : (∫y,‖f y-g y‖^2 ∂μ)≤A) (hB : (∫y,‖Q (g y)-k y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖Q (f y)-k y‖^2) μ ∧
      (∫y,‖Q (f y)-k y‖^2 ∂μ)≤2*(K:ℝ)^2*A+2*B := by
  have hh := lipschitz_error_sq hf hg hQ hfg hA
  simpa only [Function.comp_def,mul_assoc] using add_error_sq (hQ.continuous.measurable.comp hf) (hQ.continuous.measurable.comp hg) hk
    hh.1 hgk hh.2 hB
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral
open scoped Classical NNReal

def kernelCorrectionPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h z : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (p : Point d × Point d) : Point d :=
  let b := probabilityAnchoredPicard F x r T h n N e p.1 s
  let w := harmonicPicard F x r (probabilityNodeTime T h n s) z n N (b,p.2) (Fin.last n)
  probabilityAnchoredPicard F x r T h n (N+1) s w e-w

def harmonicRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam A : ℝ≥0) (r R t z C : ℝ) (n N : ℕ) : ℝ :=
  2*(r*t)*Real.sqrt (4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
    ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))+
    (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(r*t)*Real.sqrt (harmonicStationaryMoment F x r t)

theorem kernelCorrectionPicard_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0<r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      ∀R : ℝ,0<R → R^2≤1-(S:ℝ)^2 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y)) → (∀y,Ξ y 0=y) →
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r S) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,μ.map (fun y => Ξ y v)=μ) →
      ∀z : ℝ,0≤z → z≤1 →
      let w := fun y => (productPointEquiv d d (Ξ y z)).1
      let err := fun y => kernelCorrectionPicard F x r T h z n N s e
        (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-(fw (w y)-w y)
      Integrable (fun y => ‖err y‖^2) μ ∧
      (∫y,‖err y‖^2 ∂μ)≤
        2*(2*(Lp*probabilityMeanLipschitz lam r):ℝ≥0)^2*
          (32*(probabilityRmsBudget F x lam Ap r h C k n N)^2+
            2*(harmonicRmsBudget F x lam Ah r R S z J n N)^2)+
          2*(probabilityRmsBudget F x lam Ap r h C k n (N+1))^2 := by
  obtain ⟨Ap,C,hC,k,hP⟩ := kernel_probability_errors n hn
  obtain ⟨Ah,J,hJ,hH⟩ := harmonicPicard_stationary_rms n hn
  obtain ⟨Lp,hLp⟩ := probabilityAnchored_lipschitz n hn
  obtain ⟨Lh,hLh⟩ := harmonicPicard_lipschitz n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  intro R hR hRT Ξ hc hinit hder hm hlaw z hz hz1
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  let mom := fun y : Point (d+d) => (productPointEquiv d d y).2
  let b := fun y => probabilityAnchoredPicard F x r T h n N e (fw (pos y)) s
  let H := fun p => harmonicPicard F x r S z n N p (Fin.last n)
  let Q := fun v => probabilityAnchoredPicard F x r T h n (N+1) s v e-v
  let w := fun y => pos (Ξ y z)
  let u := fun y => H (b y,mom y)
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hmom : Measurable mom := (productPointEquiv d d).continuous.measurable.snd
  have hfw : Continuous fw := probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E
  have hb : Measurable b := (probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn N e s).measurable.comp
    (hfw.measurable.comp hpos)
  have hW : Measurable w := hpos.comp (hm.comp (measurable_const.prodMk measurable_id))
  have hHL : LipschitzWith 4 H := by
    have he := (LipschitzWith.eval (Fin.last n)).comp
      (hLh hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1) hz hz1 hqlh N).1
    convert he using 1 <;> first | rfl | simp only [one_mul]
  have hQL : LipschitzWith (2*(Lp*probabilityMeanLipschitz lam r)) Q := by
    have he := (LipschitzWith.eval e).comp (hLp hF x hr.le hl hT0 hT1 hh hqlp N s).2
    convert he using 1 <;> first | rfl | simp only [one_mul]
  have hu : Measurable u := hHL.continuous.measurable.comp (hb.prodMk hmom)
  have hprob := hP hF x hr hlam hl hd hT0 hT1 hh hsmall hqp N s e
  have hnorm (y : Point (d+d)) : ‖(b y,mom y)-(pos y,mom y)‖^2=‖b y-pos y‖^2 := by
    simp only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)]
  have hi : Integrable (fun y => ‖(b y,mom y)-(pos y,mom y)‖^2) μ := by
    simpa only [hnorm] using hprob.1.1
  have hbnd : (∫y,‖(b y,mom y)-(pos y,mom y)‖^2 ∂μ)≤
      (probabilityRmsBudget F x lam Ap r h C k n N)^2 := by
    simpa only [hnorm] using hprob.1.2
  have hnum := lipschitz_error_sq (hb.prodMk hmom) (hpos.prodMk hmom) hHL hi hbnd
  have hlast : probabilityNodes n (Fin.last n)=1 := by
    change (n:ℝ)/(n:ℝ)=1
    exact div_self (by exact_mod_cast hn.ne')
  have hharm := hH hF x hr hlam hl hR hRT S.2.1 (S.2.2.trans_lt hT1)
    Ξ hc hinit hder hm hlaw z hz hz1 hqh N (Fin.last n)
  rw [hlast,mul_one] at hharm
  have hharm' : Integrable (fun y => ‖H (pos y,mom y)-w y‖^2) μ ∧
      (∫y,‖H (pos y,mom y)-w y‖^2 ∂μ)≤(harmonicRmsBudget F x lam Ah r R S z J n N)^2 := hharm
  have hstate := add_error_sq hu (hHL.continuous.measurable.comp (hpos.prodMk hmom)) hW
    hnum.1 hharm'.1 hnum.2 hharm'.2
  have hstate' : Integrable (fun y => ‖u y-w y‖^2) μ ∧
      (∫y,‖u y-w y‖^2 ∂μ)≤32*(probabilityRmsBudget F x lam Ap r h C k n N)^2+
        2*(harmonicRmsBudget F x lam Ah r R S z J n N)^2 := by
    simpa only [NNReal.coe_ofNat,show (4:ℝ)^2=16 by norm_num,show (2:ℝ)*16=32 by norm_num,←mul_assoc] using hstate
  have hforward := hprob.2 (fun y => Ξ y z) (hm.comp (measurable_const.prodMk measurable_id)) (hlaw z ⟨hz,hz1⟩)
  have hcancel (y : Point (d+d)) : Q (w y)-(fw (w y)-w y)=
      probabilityAnchoredPicard F x r T h n (N+1) s (w y) e-fw (w y) := by dsimp [Q]; abel
  have hforw' : Integrable (fun y => ‖Q (w y)-(fw (w y)-w y)‖^2) μ ∧
      (∫y,‖Q (w y)-(fw (w y)-w y)‖^2 ∂μ)≤(probabilityRmsBudget F x lam Ap r h C k n (N+1))^2 := by
    simpa only [hcancel] using hforward
  exact compose_error_sq hu hW ((hfw.measurable.comp hW).sub hW) hQL
    hstate'.1 hforw'.1 hstate'.2 hforw'.2

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set
open scoped NNReal

lemma harmonicPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (z : ℝ) (n N : ℕ) (i : Fin (n+1)) :
    Continuous (fun p => harmonicPicard F x r ρ z n N p i) := by
  apply (continuous_apply i).comp
  apply FinitePicard.nodes_continuous
  · exact fun _ => (harmonicMeanVelocity_lipschitz hF x hr hl hρ0 hρ1).continuous
  · exact (harmonicFree_lipschitz n z).continuous

lemma kernelCorrectionPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (z : ℝ) (n : ℕ) (hn : 0<n) (N : ℕ) (s e : ProbabilityNode T h n) :
    Continuous (kernelCorrectionPicard F x r T h z n N s e) := by
  have hb : Continuous (fun p : Point d × Point d => probabilityAnchoredPicard F x r T h n N e p.1 s) :=
    (probabilityAnchored_continuous hF x hr hl hT0 hT1 hh n hn N e s).comp continuous_fst
  have ht := probabilityNodeTime_mem hT0 hT1 hh hn s
  have hw := (harmonicPicard_continuous hF x hr hl ht.1 (ht.2.trans_lt hT1) z n N (Fin.last n)).comp
    (hb.prodMk continuous_snd)
  exact ((probabilityAnchored_continuous hF x hr hl hT0 hT1 hh n hn (N+1) s e).comp hw).sub hw
end LogConcaveSampling

end

end

end

end OAI
