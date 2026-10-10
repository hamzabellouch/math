import Mathlib
import OAI.Analysis.CoulombRadii.Variational.CorrectionDensity
import OAI.Analysis.CoulombRadii.ThomasFermi.TfExtendNonneg
import OAI.Analysis.CoulombRadii.RadialBounds.InteriorBarrier

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_nonneg_of_nonneg {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (x : Space) :
    0 ≤ tfPotential f x := by
  apply integral_nonneg_of_ae
  filter_upwards [tfExtend_nonneg hΩ hf] with y hy
  exact mul_nonneg (coulombKernel_nonneg _) hy

lemma tfDensity_bound_of_minimizes {c F : ℝ} (hc : 0<c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume, tfDensity Ω f x ≤ (F/(c*(5/3:ℝ)))^(3/2:ℝ) := by
  have ha : 0<c*(5/3:ℝ) := by positivity
  have hlocal : ∀ᵐ x ∂volume.restrict Ω, f x≤(F/(c*(5/3:ℝ)))^(3/2:ℝ) := by
    filter_upwards [tfEuler_equation hΩ hc W hf hm,hW] with x hx hw
    rw [hx.1]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ ha.le
    exact max_le (by linarith [tfPotential_nonneg_of_nonneg hΩ hf x]) hF
  filter_upwards [(ae_restrict_iff' hΩ).mp hlocal,tfDensity_ae_tfExtend hΩ hf] with x hx he
  rw [he]
  by_cases hs : x∈Ω
  · simpa only [tfExtend,indicator_of_mem hs] using hx hs
  · simp only [tfExtend,indicator_of_notMem hs]
    exact Real.rpow_nonneg (div_nonneg hF ha.le) _

lemma tfPotential_continuous_of_minimizes {c F : ℝ} (hc : 0<c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    Continuous (tfPotential f) := by
  let L := (F/(c*(5/3:ℝ)))^(3/2:ℝ)
  let ρ : Space → ℝ := fun x => min (tfDensity Ω f x) L
  have hL : 0≤L := Real.rpow_nonneg (by positivity) _
  have hρ : ρ =ᵐ[volume] tfExtend Ω f := by
    filter_upwards [tfDensity_bound_of_minimizes hΩ hc hF W hW hf hm,
      tfDensity_ae_tfExtend hΩ hf] with x hx he
    exact (min_eq_left hx).trans he
  have hi : Integrable ρ := (tfExtend_integrable hΩ f).congr hρ.symm
  have hp (x) : 0≤ρ x := le_min (tfDensity_nonneg _ _) hL
  have hb (x) : ρ x≤L := min_le_right _ _
  have he : tfPotential f = NeutralAtom.potentialOf ρ := by
    funext x
    apply integral_congr_ae
    filter_upwards [hρ] with y hy
    change coulombKernel (x-y)*tfExtend Ω f y=coulombKernel (x-y)*ρ y
    rw [hy]
  rw [he]
  exact NeutralAtom.potentialOf_continuous hi hp hb

lemma tfScreened_weak_equation {c F : ℝ} (hc : 0<c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0)) :
    NeutralAtom.HasWeakLaplacian (fun x => Φ x-tfPotential f x) Ω
      (fun x => (4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ)*(max (Φ x-tfPotential f x) 0)^(3/2:ℝ)) := by
  intro φ hφ hφc ht
  have hL := NeutralAtom.continuous_coordinateLaplacian
    (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := NeutralAtom.hasCompactSupport_coordinateLaplacian hφc
  have hts : tsupport (NeutralAtom.coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hiΦ : Integrable (fun x => Φ x*NeutralAtom.coordinateLaplacian φ x) :=
    NeutralAtom.integrable_mul_compact_of_continuousAt
      (fun x hx => hΦ.continuousAt (ho.mem_nhds (ht (hts hx)))) hL hLc
  have hiP : Integrable (fun x => tfPotential f x*NeutralAtom.coordinateLaplacian φ x) :=
    NeutralAtom.integrable_mul_compact_of_continuousAt
      (fun x _ => (tfPotential_continuous_of_minimizes hΩ hc hF W hW hf hm).continuousAt) hL hLc
  have hP := NeutralAtom.potentialOf_weakLaplacian (tfExtend_integrable hΩ f) φ hφ hφc (subset_univ _)
  change (∫ x, tfPotential f x*NeutralAtom.coordinateLaplacian φ x) = _ at hP
  simp_rw [sub_mul]
  rw [integral_sub hiΦ hiP,hh φ hφ hφc ht,hP]
  simp only [zero_mul,integral_zero,zero_sub,←integral_neg,neg_mul,neg_neg]
  apply integral_congr_ae
  have hE := (ae_restrict_iff' hΩ).mp (tfEuler_equation hΩ hc W hf hm)
  have hWe := (ae_restrict_iff' hΩ).mp he
  filter_upwards [hE,hWe] with x hx hw
  by_cases hs : x∈Ω
  · simp only [tfExtend,indicator_of_mem hs]
    rw [(hx hs).1,hw hs,Real.div_rpow (le_max_right _ _) (by positivity)]
    ring
  · have hpz : φ x=0 := image_eq_zero_of_notMem_tsupport (fun h => hs (ht h))
    simp only [hpz,mul_zero]

theorem tfScreened_interior_upper {c F : ℝ} (hc : 0<c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0))
    {y : Space} {s : ℝ} (hs : 0<s) (hball : Metric.closedBall y s⊆Ω)
    {z : Space} (hz : z∈Metric.ball y s) :
    Φ z-tfPotential f z ≤
      (80/((4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ)))^2*s^4/(s^2-‖z-y‖^2)^4 := by
  have hcc : 0<(4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ) := by positivity
  apply NeutralAtom.weak_power_interior_upper hs hcc
    ((hΦ.mono hball).sub ((tfPotential_continuous_of_minimizes hΩ hc hF W hW hf hm).continuousOn))
    ((tfScreened_weak_equation hΩ hc hF W hW hf hm hΦ ho he hh).mono
      (Metric.ball_subset_closedBall.trans hball)) hz

def tfInteriorConstant (c : ℝ) : ℝ :=
  256*(80/((4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ)))^2

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfInteriorConstant_nonneg (c : ℝ) : 0≤tfInteriorConstant c := by
  unfold tfInteriorConstant; positivity

lemma tfScreened_three_quarters {c F : ℝ} (hc : 0<c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0))
    {y : Space} {a : ℝ} (ha : 0<a) (hball : Metric.closedBall y (4*a)⊆Ω)
    {z : Space} (hz : z∈Metric.closedBall y (3*a)) :
    Φ z-tfPotential f z ≤ tfInteriorConstant c/a^4 := by
  have hz' : ‖z-y‖≤3*a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hz4 : z∈Metric.ball y (4*a) := by
    simp only [Metric.mem_ball,dist_eq_norm]; linarith
  have H := tfScreened_interior_upper hΩ hc hF W hW hf hm hΦ ho he hh
    (by positivity : 0<4*a) hball hz4
  have hD : a^2 ≤ (4*a)^2-‖z-y‖^2 := by
    nlinarith [sq_le_sq₀ (norm_nonneg (z-y)) (by positivity : 0≤3*a) |>.mpr hz']
  have hD0 : 0<(4*a)^2-‖z-y‖^2 := (sq_pos_of_pos ha).trans_le hD
  apply H.trans
  have hd4 : a^8 ≤ ((4*a)^2-‖z-y‖^2)^4 := by
    simpa only [←pow_mul,show 2*4=8 by norm_num] using pow_le_pow_left₀ (sq_nonneg a) hD 4
  apply (div_le_div_iff₀ (pow_pos hD0 4) (pow_pos ha 4)).mpr
  have hc0 := tfInteriorConstant_nonneg c
  have Hm := mul_le_mul_of_nonneg_left hd4 hc0
  calc
    _ = tfInteriorConstant c*a^8 := by dsimp [tfInteriorConstant]; ring
    _ ≤ _ := Hm

lemma tfDensity_interior_bound {c F : ℝ} (hc : 0<c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0))
    {y : Space} {a : ℝ} (ha : 0<a) (hball : Metric.closedBall y (4*a)⊆Ω) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall y (3*a)), tfDensity Ω f z ≤
      (tfInteriorConstant c/(c*(5/3:ℝ)))^(3/2:ℝ)/a^6 := by
  have hsub : Metric.closedBall y (3*a)⊆Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have he' := (ae_restrict_iff' hΩ).mp he
  have hE := (ae_restrict_iff' hΩ).mp (tfEuler_equation hΩ hc W hf hm)
  apply (ae_restrict_iff' measurableSet_closedBall).mpr
  filter_upwards [he',hE,tfDensity_ae_tfExtend hΩ hf] with z hze hzE hden
  intro hz
  have hzΩ := hsub hz
  rw [hden,tfExtend,indicator_of_mem hzΩ,(hzE hzΩ).1,hze hzΩ]
  have H := tfScreened_three_quarters hΩ hc hF W hW hf hm hΦ ho he hh ha hball hz
  have Hb : max (Φ z-tfPotential f z) 0 ≤ tfInteriorConstant c/a^4 :=
    max_le H (div_nonneg (tfInteriorConstant_nonneg c) (by positivity))
  have HH := Real.rpow_le_rpow (by positivity : 0 ≤ max (Φ z-tfPotential f z) 0/(c*(5/3:ℝ)))
    (div_le_div_of_nonneg_right Hb (by positivity : 0≤c*(5/3:ℝ))) (by norm_num : (0:ℝ)≤3/2)
  apply HH.trans_eq
  rw [show tfInteriorConstant c/a^4/(c*(5/3:ℝ))=(tfInteriorConstant c/(c*(5/3:ℝ)))/a^4 by ring,
    Real.div_rpow (div_nonneg (tfInteriorConstant_nonneg c) (by positivity)) (by positivity),←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

end Coulomb

end

end
end

end OAI
