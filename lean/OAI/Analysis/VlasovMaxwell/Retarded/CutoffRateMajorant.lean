import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.BranchCutoffStateContinuous

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def cutoffRateMajorant (r : ℝ) (a u n vy vx : Vec) : ℝ :=
  let ρ := (1-dot n u)/(1-dot n a)
  |r| *‖vy‖+(‖coneMotion a u n‖+|r| *‖vy‖)/(2*(1-dot n u))+
    (‖coneMotion a u n‖+|r| *‖ρ • vx‖)/(2*(1-dot n a))+|ρ-1|

lemma cutoffRateMajorant_eq {r : ℝ} (hr : 0<r) (a u n vy vx : Vec) :
    cutoffRateMajorant r a u n vy vx =
    r*(‖vy‖+(‖r⁻¹ • coneMotion a u n‖+‖vy‖)/(2*(1-dot n u))+
      (‖r⁻¹ • coneMotion a u n‖+‖((1-dot n u)/(1-dot n a)) • vx‖)/(2*(1-dot n a))+
        |(1-dot n u)/(1-dot n a)-1|/r) := by
  simp only [cutoffRateMajorant,abs_of_pos hr,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  field_simp [hr.ne']

lemma PhaseFlowOn.branchSelectedRate_coarse_bound {s : Solution} {T σ C : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1)
    (Q : Set (Fin 4→ℕ)) (hC0 : 0≤C)
    (hC : ∀ n : ℕ,∀ x : ℝ,|x*deriv (dyadicFactor n) x|≤C) :
    let τ := branchTime F.flow zX zY T σ
    (τ-σ)*|branchSelectedRate s.E s.B F.flow T zX zY Q σ| ≤
      (5:ℝ)^4*C*cutoffRateMajorant (τ-σ) (velocity (F.flow zX τ).2)
        (velocity (F.flow zY σ).2) (branchDirection F.flow zX zY T σ)
        (lorentzField s.E s.B (σ,F.flow zY σ)).2
        (lorentzField s.E s.B (τ,F.flow zX τ)).2 := by
  dsimp only
  have hr : 0<branchTime F.flow zX zY T σ-σ :=
    sub_pos.mpr (F.branch_time_mem zX zY hσ hne).1
  have hn := F.branchDirection_norm zX zY hσ hne
  have hχ := ((contDiffAt_stateCutoff T Q
    (z:=branchCutoffState F.flow T zX zY σ) hr hn).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt σ
      (F.branchCutoffState_hasDerivAt zX zY hσ hne)
  have hχeq : deriv (fun r=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY r)) σ=
      branchSelectedRate s.E s.B F.flow T zX zY Q σ := hχ.deriv
  have hb := selectedDyadicCutoff_uniform_log_bound hC0 hC
    (fun i=>(F.actualCutoffCoordinates_contDiffAt hs zX zY hσ hne i).differentiableAt one_ne_zero)
    (F.actualCutoffCoordinates_pos zX zY hσ hne) Q
  rw [hχeq] at hb
  have hY := ((F.ode zY σ (Ioo_subset_Icc_self hσ.1)).hasDerivAt
    (Icc_mem_nhds hσ.1.1 hσ.1.2)).snd
  have hX := F.retardedMomentum_hasDerivAt zX zY hσ hne
  have hN := F.branchDirection_hasDerivAt zX zY hσ hne
  have hR := (F.branch_differential zX zY hσ hne).2.sub (hasDerivAt_id σ)
  have hsumb := physical_cutoff_coarse_rates (T:=T)
    (R:=fun t=>branchTime F.flow zX zY T t-t) hn hr hY hX hN hR
  change ∑ i : Fin 4,|deriv (fun r=>actualCutoffCoordinates F.flow T zX zY r i) σ /
      actualCutoffCoordinates F.flow T zX zY σ i| ≤ _ at hsumb
  rw [cutoffRateMajorant_eq hr]
  simp only [Fintype.card_fin] at hb
  have hm := mul_le_mul_of_nonneg_left (hb.trans
    (mul_le_mul_of_nonneg_left hsumb (by positivity))) hr.le
  rw [mul_left_comm (5^4*C)]
  exact hm

lemma retardedPrimitive_eq_inverse_smul (r : ℝ) (a u n : Vec) :
    retardedPrimitive r a u n=r⁻¹ • normalisedPrimitive 1 a u n := by
  simp only [retardedPrimitive,normalisedPrimitive,smul_smul,one_div,mul_inv]

lemma cutoff_primitive_norm_bound {r c B : ℝ} (hr : 0<r) (a u n : Vec)
    (hb : r*|c|≤B) :
    ‖c • retardedPrimitive r a u n‖≤r⁻¹^2*‖B • normalisedPrimitive 1 a u n‖ := by
  have hB : 0≤B := (mul_nonneg hr.le (abs_nonneg _)).trans hb
  rw [retardedPrimitive_eq_inverse_smul,norm_smul,norm_smul,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),norm_smul,Real.norm_eq_abs,abs_of_nonneg hB]
  calc
    |c| * (r⁻¹ * ‖normalisedPrimitive 1 a u n‖) =
        (r*|c|)*(r⁻¹^2*‖normalisedPrimitive 1 a u n‖) := by
      field_simp [ne_of_gt hr]
    _ ≤ B*(r⁻¹^2*‖normalisedPrimitive 1 a u n‖) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = r⁻¹^2*(B*‖normalisedPrimitive 1 a u n‖) := by ring

lemma continuousOn_cutoffRateMajorant {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n vy vx : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hvy : ContinuousOn vy S) (hvx : ContinuousOn vx S)
    (hd : ∀p∈S,1-dot (n p) (u p)≠0) (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>cutoffRateMajorant (r p) (a p) (u p) (n p) (vy p) (vx p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  have hdc := (continuousOn_const (c:=(1:ℝ))).sub (hdot hn hu)
  have hDc := (continuousOn_const (c:=(1:ℝ))).sub (hdot hn ha)
  have hρ := hdc.div hDc hD
  have hm : ContinuousOn (fun p=>coneMotion (a p) (u p) (n p)) S :=
    ((hρ.smul (ha.sub hn)).add hn).sub hu
  exact (((hr.abs.mul hvy.norm).add
    ((hm.norm.add (hr.abs.mul hvy.norm)).div (continuousOn_const.mul hdc)
      (fun p hp=>mul_ne_zero (by norm_num) (hd p hp)))).add
    ((hm.norm.add (hr.abs.mul (hρ.smul hvx).norm)).div (continuousOn_const.mul hDc)
      (fun p hp=>mul_ne_zero (by norm_num) (hD p hp)))).add
        (hρ.sub continuousOn_const).abs

lemma EnergyPrefix.continuousOn_momentumForce {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) :
    ContinuousOn (fun p : ℝ×Phase=>(lorentzField s.E s.B p).2)
      (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hp : Continuous (fun p : ℝ×Phase=>(p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have hE : ContinuousOn (fun p : ℝ×Phase=>s.E (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.E_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hB : ContinuousOn (fun p : ℝ×Phase=>s.B (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.B_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hu := (contDiff_velocity (k:=1)).continuous.comp (continuous_snd.snd : Continuous (fun p : ℝ×Phase=>p.2.2))
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hB))

def normalisedCutoffPrimitive (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (K : ℝ) (p : ConeKernelState) : Vec :=
  (K*cutoffRateMajorant (p.1.1-p.1.2) (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1
    (lorentzField s.E s.B (p.1.2,p.2.2)).2 (lorentzField s.E s.B (p.1.1,α zX p.1.1)).2) •
    normalisedPrimitive 1 (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1

lemma PhaseFlowOn.normalisedCutoffPrimitive_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (K : ℝ) :
    ContinuousOn (normalisedCutoffPrimitive s F.flow zX K) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hvy : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.2,p.2.2)).2)
      (coneKernelDomain T) := hs.continuousOn_momentumForce.comp
        (continuous_fst.snd.prodMk continuous_snd.snd).continuousOn (fun _ hp=>⟨hp.1.2,mem_univ _⟩)
  have hvx : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.1,F.flow zX p.1.1)).2)
      (coneKernelDomain T) := (F.momentumForce_continuousOn_closed hs zX).comp
        continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)
  have hd : ∀p∈coneKernelDomain T,1-dot p.2.1 (velocity p.2.2.2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  have hD : ∀p∈coneKernelDomain T,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  exact (continuousOn_const.mul (continuousOn_cutoffRateMajorant
    (continuous_fst.fst.sub continuous_fst.snd).continuousOn ha hu.continuousOn hn.continuousOn hvy hvx hd hD)).smul
      (continuousOn_normalisedPrimitive continuousOn_const ha hu.continuousOn hn.continuousOn hd hD)

end RVM

end

end OAI
