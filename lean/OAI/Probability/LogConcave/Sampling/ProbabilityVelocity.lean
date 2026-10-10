import Mathlib
import OAI.Probability.LogConcave.Sampling.InterpolationResidual
import OAI.Probability.LogConcave.Dynamics.Curve

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open Function Set
open scoped Topology

def probabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : Point d := -r • conditionalFieldMean F x r ρ y

lemma probabilityVelocity_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (uncurry (probabilityVelocity F x r)) p := by
  change ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => (-r) • conditionalFieldMean F x r q.1 q.2) p
  exact (contDiffAt_const (c:=(-r:ℝ))).smul (conditionalFieldMean_joint_smooth hF x hr hl p hp)

lemma probabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ∈Icc 0 T) (hT : T<1) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (probabilityVelocity F x r ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change ‖-r • conditionalFieldMean F x r ρ u- -r • conditionalFieldMean F x r ρ v‖≤((Real.pi^2/2)*(lam:ℝ)*r^2)*dist u v
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr]
  have hh := (conditionalFieldMean_lipschitz hF x hr hl hρ.1 (hρ.2.trans_lt hT)).dist_le_mul u v
  rw [dist_eq_norm] at hh
  calc
    _ ≤ r*((Real.pi^2/2)*ρ*((lam:ℝ)*r)*dist u v) := mul_le_mul_of_nonneg_left hh hr
    _ ≤ r*((Real.pi^2/2)*1*((lam:ℝ)*r)*dist u v) := by gcongr; exact hρ.2.trans hT.le
    _ = _ := by ring

theorem exists_probability_trajectory {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (t₀ : Icc (0:ℝ) T) (y : Point d) :
    ∃ α : ℝ → Point d, Continuous α ∧ α t₀=y ∧
      ContDiffOn ℝ (⊤:ℕ∞) α (Icc 0 T) ∧
      ∀ t∈Icc 0 T, HasDerivWithinAt α (probabilityVelocity F x r t (α t)) (Icc 0 T) t := by
  let c : ℝ → ℝ := fun t => projIcc 0 T hT0 t
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcm (t : ℝ) : c t∈Icc 0 T := (projIcc 0 T hT0 t).2
  have hce (t : ℝ) (ht : t∈Icc 0 T) : c t=t := by simp [c,projIcc_of_mem _ ht]
  let f : ℝ → Point d → Point d := fun t z => probabilityVelocity F x r (c t) z
  have hf : Continuous (uncurry f) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp : (c p.1)^2<1 := by
      have hh := (probability_time (hcm p.1).1 ((hcm p.1).2.trans_lt hT1)).1
      linarith
    exact ((probabilityVelocity_joint_smooth hF x hr (by linarith) (c p.1,p.2) hp).continuousAt).comp (f:=fun q : ℝ × Point d => (c q.1,q.2))
      ((hc.comp continuous_fst).continuousAt.prodMk continuous_snd.continuousAt)
  have hL : ∀ t∈Icc 0 T,LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (f t) := by
    intro t _
    exact probabilityVelocity_lipschitz hF x hr hl (hcm t) hT1
  obtain ⟨α,hα,hi,hd⟩ := GlobalODE.exists_curve t₀ hf hL y
  have hd' : ∀ t∈Icc 0 T,HasDerivWithinAt α (probabilityVelocity F x r t (α t)) (Icc 0 T) t := by
    intro t ht
    simpa [f,hce t ht] using hd t ht
  refine ⟨α,hα,hi,?_,hd'⟩
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (u:=univ) _ hd' (fun _ _ => mem_univ _)
  intro p hp
  exact (probabilityVelocity_joint_smooth hF x hr (by linarith) p
    (by have hh := (probability_time hp.1.1 (hp.1.2.trans_lt hT1)).1; linarith)).contDiffWithinAt
end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory Filter
open scoped Topology

def clampedProbabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (hT : 0≤T) (t : ℝ) (z : Point d) : Point d :=
  probabilityVelocity F x r (projIcc 0 T hT t) z

def clampedProbabilityDerivative {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (hT : 0≤T) (t : ℝ) (z : Point d) : Point d →L[ℝ] Point d :=
  (fderiv ℝ (uncurry (probabilityVelocity F x r)) ((projIcc 0 T hT t:ℝ),z)).comp
    (ContinuousLinearMap.inr ℝ ℝ (Point d))

lemma clampedProbabilityVelocity_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (uncurry (clampedProbabilityVelocity F x r T hT0)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcm := (projIcc 0 T hT0 p.1).2
  have hp : (projIcc 0 T hT0 p.1:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  exact (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,p.2) hp).continuousAt.comp (f:=fun q : ℝ × Point d => ((projIcc 0 T hT0 q.1:ℝ),q.2))
    ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).continuousAt.prodMk
      continuous_snd.continuousAt)

lemma clampedProbabilityDerivative_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (uncurry (clampedProbabilityDerivative F x r T hT0)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcm := (projIcc 0 T hT0 p.1).2
  have hp : (projIcc 0 T hT0 p.1:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  have hh := (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,p.2) hp).continuousAt_fderiv
    (by simp)
  exact (hh.comp (f:=fun q : ℝ × Point d => ((projIcc 0 T hT0 q.1:ℝ),q.2)) ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).continuousAt.prodMk
    continuous_snd.continuousAt)).clm_comp continuousAt_const

lemma clampedProbabilityVelocity_hasFDerivAt {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) (z : Point d) :
    HasFDerivAt (clampedProbabilityVelocity F x r T hT0 t)
      (clampedProbabilityDerivative F x r T hT0 t z) z := by
  have hcm := (projIcc 0 T hT0 t).2
  have hp : (projIcc 0 T hT0 t:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  have hh := (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,z) hp).differentiableAt
    (by simp)
  convert! hh.hasFDerivAt.comp z ((hasFDerivAt_const (projIcc 0 T hT0 t:ℝ) z).prodMk
    (hasFDerivAt_id z)) using 1

lemma clampedProbabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩
      (clampedProbabilityVelocity F x r T hT0 t) :=
  probabilityVelocity_lipschitz hF x hr hl (projIcc 0 T hT0 t).2 hT1

lemma clampedProbabilityVelocity_eq {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T : ℝ) (hT : 0≤T) {t : ℝ} (ht : t∈Icc 0 T) (z : Point d) :
    clampedProbabilityVelocity F x r T hT t z=probabilityVelocity F x r t z := by
  simp [clampedProbabilityVelocity,projIcc_of_mem _ ht]
end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Topology

def interpolationPath {d : ℕ} (t : ℝ) (p : Point d × Point d) : Point d :=
  t • p.1+Real.sqrt (1-t^2) • p.2

def interpolationPathDerivative {d : ℕ} (t : ℝ) (p : Point d × Point d) : Point d :=
  p.1-(t/Real.sqrt (1-t^2)) • p.2

lemma interpolationPath_continuous {d : ℕ} (p : Point d × Point d) :
    Continuous (fun t => interpolationPath t p) := by unfold interpolationPath; fun_prop

lemma interpolationPath_measurable {d : ℕ} (t : ℝ) :
    Measurable (interpolationPath (d:=d) t) := by unfold interpolationPath; fun_prop

lemma interpolationPathDerivative_measurable {d : ℕ} (t : ℝ) :
    Measurable (interpolationPathDerivative (d:=d) t) := by unfold interpolationPathDerivative; fun_prop

lemma interpolationPath_hasDerivAt {d : ℕ} {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    HasDerivAt (fun t => interpolationPath t p) (interpolationPathDerivative t p) t := by
  have hs₀ : HasDerivAt (fun t : ℝ => 1-t^2) (-2*t) t := by
    convert! (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2) using 1; simp
  have hs := hs₀.sqrt (show 1-t^2≠0 by linarith)
  have hh := ((hasDerivAt_id t).smul_const p.1).add (hs.smul_const p.2)
  convert! hh using 1
  simp only [one_smul,interpolationPathDerivative]
  rw [sub_eq_add_neg,←neg_smul]
  congr 1
  congr 1
  ring

lemma interpolationPath_norm_le {d : ℕ} {t T : ℝ} (hT : T≤1) (ht : t∈Icc 0 T)
    (p : Point d × Point d) : ‖interpolationPath t p‖≤‖p.1‖+‖p.2‖ := by
  have ht1 := ht.2.trans hT
  have hs0 := Real.sqrt_nonneg (1-t^2)
  have hs1 : Real.sqrt (1-t^2)≤1 := by
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg t]
  calc
    _ ≤ ‖t • p.1‖+‖Real.sqrt (1-t^2) • p.2‖ := norm_add_le _ _
    _ = t*‖p.1‖+Real.sqrt (1-t^2)*‖p.2‖ := by
      simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,abs_of_nonneg hs0]
    _ ≤ _ := by nlinarith [norm_nonneg p.1,norm_nonneg p.2]

lemma interpolationPathDerivative_norm_le {d : ℕ} {t T : ℝ} (hT0 : 0≤T) (hT1 : T<1)
    (ht : t∈Icc 0 T) (p : Point d × Point d) :
    ‖interpolationPathDerivative t p‖≤‖p.1‖+(1/Real.sqrt (1-T^2))*‖p.2‖ := by
  have hT : 0<1-T^2 := by nlinarith
  have hs : Real.sqrt (1-T^2)≤Real.sqrt (1-t^2) := by apply Real.sqrt_le_sqrt; nlinarith [ht.1,ht.2]
  have hdiv : t/Real.sqrt (1-t^2)≤1/Real.sqrt (1-T^2) := by
    calc
      _ ≤ 1/Real.sqrt (1-t^2) := div_le_div_of_nonneg_right (ht.2.trans hT1.le) (Real.sqrt_nonneg _)
      _ ≤ _ := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hT) hs
  calc
    _ ≤ ‖p.1‖+‖(t/Real.sqrt (1-t^2)) • p.2‖ := norm_sub_le _ _
    _ = ‖p.1‖+(t/Real.sqrt (1-t^2))*‖p.2‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ht.1 (Real.sqrt_nonneg _))]
    _ ≤ _ := by gcongr

lemma interpolationPath_residual {d : ℕ} {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    interpolationPathDerivative t p=(1/(1-t^2)) • (p.1-t • interpolationPath t p) := by
  have ha : 1-t^2≠0 := by linarith
  have hs : Real.sqrt (1-t^2)≠0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have he₁ : 1/(1-t^2)-(1/(1-t^2))*t*t=1 := by field_simp
  have he₂ : (1/(1-t^2))*t*Real.sqrt (1-t^2)=t/Real.sqrt (1-t^2) := by
    field_simp
    rw [Real.sq_sqrt (show 0≤1-t^2 by linarith)]
  unfold interpolationPathDerivative interpolationPath
  simp only [smul_add,smul_sub,smul_smul]
  rw [sub_add_eq_sub_sub,←mul_assoc,←mul_assoc,←sub_smul,he₁,one_smul,he₂]
end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

lemma interpolationPath_defect {d : ℕ} {F : Point d → ℝ} (x : Point d) (r : ℝ)
    {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    interpolationPathDerivative t p-probabilityVelocity F x r t (interpolationPath t p)=
      interpolationResidual F x r t (p.1,interpolationPath t p) := by
  rw [interpolationPath_residual ht]
  simp [probabilityVelocity,interpolationResidual,sub_eq_add_neg]

lemma interpolationPath_flux {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht0 : 0≤t) (ht1 : t<1)
    {S : Point d → Point d →L[ℝ] ℝ} (hS : Measurable S)
    {C : ℝ} (hC : ∀ y,‖S y‖≤C) :
    (∫ p,S (interpolationPath t p)
      (interpolationPathDerivative t p-probabilityVelocity F x r t (interpolationPath t p))
      ∂(gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))=0 := by
  have ht : t^2<1 := by have hh := (probability_time ht0 ht1).1; linarith
  simp_rw [interpolationPath_defect x r ht]
  have hM := conditionalFieldMean_lipschitz hF x hr hl ht0 ht1
  have hc : Continuous (interpolationResidual F x r t) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul t)).const_smul (1/(1-t^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  have hm : Measurable (fun p : Point d × Point d => S p.2 (interpolationResidual F x r t p)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hS.comp measurable_snd).prodMk hc.measurable)
  have hh := interpolation_flux_zero hF x hr hl ht0 ht1 hS hC
  rw [jointInterpolationLaw,integral_map (by fun_prop) hm.aestronglyMeasurable] at hh
  exact hh

lemma interpolationPath_defect_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∃ g : Point d × Point d → ℝ,
      Integrable g ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))) ∧
      ∀ t∈Icc 0 T,∀ p,‖interpolationPathDerivative t p-
        clampedProbabilityVelocity F x r T hT0 t (interpolationPath t p)‖≤g p := by
  let f := clampedProbabilityVelocity F x r T hT0
  let K : ℝ≥0 := ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩
  have hc := clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1
  have hL : ∀ t,LipschitzWith K (f t) := clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hc.comp (continuous_id.prodMk continuous_const)).continuousOn : ContinuousOn (fun t => f t 0) (Icc 0 T))
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hz : Integrable (fun p : Point d × Point d => ‖p.1‖) (μ.prod ν) :=
    ((primitive_identity_integrable hF x hr (by linarith)).comp_fst ν).norm
  have hg : Integrable (fun p : Point d × Point d => ‖p.2‖) (μ.prod ν) :=
    ((IsGaussian.integrable_id (μ:=ν)).comp_snd μ).norm
  let g : Point d × Point d → ℝ := fun p =>
    ‖p.1‖+(1/Real.sqrt (1-T^2))*‖p.2‖+C+(K:ℝ)*(‖p.1‖+‖p.2‖)
  refine ⟨g,((hz.add (hg.const_mul _)).add (integrable_const C)).add ((hz.add hg).const_mul _),?_⟩
  intro t ht p
  have hfl := (hL t).dist_le_mul (interpolationPath t p) 0
  rw [dist_eq_norm,dist_zero_right] at hfl
  have hfb : ‖f t (interpolationPath t p)‖≤C+(K:ℝ)*(‖p.1‖+‖p.2‖) := by
    exact (norm_le_norm_add_norm_sub' _ _).trans
      (add_le_add (hC t ht) (hfl.trans (mul_le_mul_of_nonneg_left
        (interpolationPath_norm_le hT1.le ht p) K.coe_nonneg)))
  exact (norm_sub_le _ _).trans (add_le_add
    (interpolationPathDerivative_norm_le hT0 hT1 ht p) hfb) |>.trans_eq (by dsimp [g]; ring)

def probabilityFlow {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (z : Point d) : Point d :=
  GlobalODE.flow (fun t _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 t)
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1) ⟨0,le_rfl,hT0⟩ z T

lemma probabilityFlow_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (probabilityFlow hF x hr hl hT0 hT1) :=
  (GlobalODE.flow_lipschitz _ _ ⟨0,le_rfl,hT0⟩ ⟨T,hT0,le_rfl⟩).continuous
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
