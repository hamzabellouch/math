import OAI.Probability.FirstPassage.MainTheorem

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

def HasC1CurveChart (S : Set Plane) (v : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧ v ∈ S ∧ ∃ γ : ℝ → Plane, ∃ θ : Plane → ℝ,
    ContDiff ℝ 1 γ ∧ ContinuousOn θ U ∧
    (∀ t, γ t ∈ S ∩ U) ∧ (∀ t, θ (γ t)=t) ∧
    (∀ z ∈ S ∩ U, γ (θ z)=z) ∧
    (∀ t, ∃ d : Plane, HasDerivAt γ d t ∧ d ≠ 0)

lemma contDiff_direction : ContDiff ℝ 1 direction := by
  have hh : ContDiff ℝ 1 (fun t : ℝ => direction 0+t • transverseUnit) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have he : (fun t : ℝ => direction 0+t • transverseUnit)=direction := by
    funext t; ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  rwa [he] at hh

noncomputable def sphereChart (μ : Plane → ℝ) (c t : ℝ) : Plane :=
  (c/μ (direction t)) • direction t
noncomputable def directionRatio (v : Plane) : ℝ := v 1/v 0

lemma sphereChart_coordinates (μ : Plane → ℝ) (c t : ℝ) :
    sphereChart μ c t 0=c/μ (direction t) ∧ sphereChart μ c t 1=(c/μ (direction t))*t := by
  simp [sphereChart,direction,PiLp.smul_apply]

lemma sphereChart_ratio (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    directionRatio (sphereChart μ c t)=t := by
  obtain ⟨h0,h1⟩ := sphereChart_coordinates μ c t
  unfold directionRatio
  rw [h0,h1]
  have hp := norm_direction_pos μ hμ t
  field_simp

lemma sphereChart_mem (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : |c|=1) (t : ℝ) :
    μ (sphereChart μ c t)=1 ∧ 0 < c*sphereChart μ c t 0 := by
  have hp := norm_direction_pos μ hμ t
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  constructor
  · rw [sphereChart,hμ.homogeneous,abs_div,hc,abs_of_pos hp]
    field_simp
  · rw [(sphereChart_coordinates μ c t).1]
    have hcs : 0 < c*c := mul_self_pos.mpr hc0
    exact (div_pos hcs hp).trans_eq (by ring)

lemma sphereChart_reconstruct (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (c : ℝ) (hc : |c|=1) (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) :
    sphereChart μ c (directionRatio v)=v := by
  have hx : v 0 ≠ 0 := by intro he; rw [he,mul_zero] at hsign; exact lt_irrefl _ hsign
  have hrep := plane_direction_representation v hx
  change v 0 • direction (directionRatio v)=v at hrep
  have hnorm : |v 0| *μ (direction (directionRatio v))=1 := by
    rw [← hμ.homogeneous,hrep,hv]
  have hcx : c*|v 0|=v 0 := by
    rcases eq_or_eq_neg_of_abs_eq hc with hc | hc
    · rw [hc] at hsign ⊢
      simp only [one_mul] at hsign ⊢
      exact abs_of_pos hsign
    · rw [hc] at hsign ⊢
      have hvneg : v 0 < 0 := by linarith
      rw [abs_of_neg hvneg]
      ring
  have he : c/μ (direction (directionRatio v))=v 0 := by
    apply (div_eq_iff (ne_of_gt (norm_direction_pos μ hμ _))).mpr
    rw [← hcx,mul_assoc,hnorm,mul_one]
  rw [sphereChart,he]
  exact hrep

lemma sphereChart_contDiff (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) :
    ContDiff ℝ 1 (sphereChart μ c) :=
  (contDiff_const.div hφ (fun t => ne_of_gt (norm_direction_pos μ hμ t))).smul contDiff_direction

lemma sphereChart_regular (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    ∃ d : Plane, HasDerivAt (sphereChart μ c) d t ∧ d ≠ 0 := by
  have hg := ((sphereChart_contDiff μ hμ hφ c).differentiable (by norm_num) t).hasDerivAt
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hx : sphereChart μ c t 0 ≠ 0 := by
    rw [(sphereChart_coordinates μ c t).1]
    exact div_ne_zero hc (ne_of_gt (norm_direction_pos μ hμ t))
  have hyc : ContDiffAt ℝ 1 (fun z : Plane => z 1) (sphereChart μ c t) := y.contDiff.contDiffAt
  have hxc : ContDiffAt ℝ 1 (fun z : Plane => z 0) (sphereChart μ c t) := xCoord.contDiff.contDiffAt
  have hr : DifferentiableAt ℝ directionRatio (sphereChart μ c t) :=
    (hyc.div hxc hx).differentiableAt (by norm_num)
  have hchain := hr.hasFDerivAt.comp_hasDerivAt t hg
  have he : (directionRatio ∘ sphereChart μ c)=id := funext (sphereChart_ratio μ hμ c hc)
  rw [he] at hchain
  have hid := hchain.unique (hasDerivAt_id t)
  refine ⟨_,hg,?_⟩
  intro hz
  rw [hz,map_zero] at hid
  norm_num at hid

lemma sphere_horizontal_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : |c|=1)
    (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) : HasC1CurveChart {z | μ z=1} v := by
  let U : Set Plane := {z | 0 < c*z 0}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.mul xCoord.continuous)
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hθ : ContinuousOn directionRatio U := y.continuous.continuousOn.div xCoord.continuous.continuousOn
    (fun z hz => by intro he; change 0<c*z 0 at hz; rw [he,mul_zero] at hz; exact lt_irrefl _ hz)
  exact ⟨U,hU,hsign,hv,sphereChart μ c,directionRatio,sphereChart_contDiff μ hμ hφ c,hθ,
    sphereChart_mem μ hμ c hc,sphereChart_ratio μ hμ c hc0,
    fun z hz => sphereChart_reconstruct μ hμ c hc z hz.1 hz.2,sphereChart_regular μ hμ hφ c hc0⟩

end PlanarFPP

end OAI
