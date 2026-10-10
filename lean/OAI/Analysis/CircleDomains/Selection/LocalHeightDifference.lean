import OAI.Analysis.CircleDomains.Selection.FlattenedHeightError
import OAI.Analysis.CircleDomains.Sobolev.VerticalWeakConstant
import OAI.Analysis.CircleDomains.Sobolev.CompactCutoffEnergy

namespace OAI

/-! The flattened height minus the genuine vertical coordinate has an
explicit local weak gradient and a controlled compact cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def subtractSobolevWitness {U : Set EuclideanPlane} {u v : EuclideanPlane → ℝ}
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U) :
    DeGiorgi.MemW1pWitness 2 (fun x => u x-v x) U :=
  (Wu.add (Wv.smul (-1))).congr_ae (Eventually.of_forall (fun x => by ring))

 theorem subtractSobolevWitness_gradient {U : Set EuclideanPlane} {u v : EuclideanPlane → ℝ}
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U) (x : EuclideanPlane) :
    (subtractSobolevWitness Wu Wv).weakGrad x = Wu.weakGrad x-Wv.weakGrad x := by
  simp only [subtractSobolevWitness, DeGiorgi.MemW1pWitness.congr_ae,
    DeGiorgi.MemW1pWitness.add, DeGiorgi.MemW1pWitness.smul, neg_one_smul, sub_eq_add_neg]

 def verticalLocalWitness (A : ℝ) :
    DeGiorgi.MemW1pWitness 2 (fun x : EuclideanPlane => x 1) (ball 0 A) where
  memLp := continuous_memLp_ball verticalLinear.continuous A
  weakGrad := fun _ => EuclideanSpace.single (1 : Fin 2) 1
  weakGrad_component_memLp := by
    intro i
    let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) A)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact memLp_const _
  isWeakGrad := by
    intro i
    have h := weakPartial_of_smooth_on (U := ball (0 : EuclideanPlane) A) isOpen_ball verticalLinear.contDiff.contDiffOn i
    convert h using 1
    · funext x
      fin_cases i <;> simp [ContinuousLinearMap.fderiv, verticalLinear_apply]
    · rfl

 theorem ControlledHeight.compact_flattened_error_energy {R d : ℝ} (H : ControlledHeight R d)
    (A : ℝ) (T : ℝ → ℝ)
    (W : DeGiorgi.MemW1pWitness 2 (fun x => T (H.height (complexPlaneCoordinates x))) (ball 0 A))
    {ε δ ζ C₀ C₁ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (he : (∫⁻ x in ball 0 A,
      ENNReal.ofReal (‖W.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε)
    (hT : ∀ t, |T t-t| ≤ ζ)
    (hclose : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ δ)
    (η : EuclideanPlane → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hsub : tsupport η ⊆ ball 0 A)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hηb : ∀ x, |η x| ≤ C₀) (hηd : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    ∃ V : DeGiorgi.MemW1pWitness 2
        (fun x => η x*(T (H.height (complexPlaneCoordinates x))-x 1)) univ,
      (∫ x, ‖V.weakGrad x‖^2) ≤
        2*C₀^2*(2*ε+4*Real.pi*d)+4*C₁^2*(ζ+δ)^2*(volume (ball (0 : EuclideanPlane) A)).toReal := by
  let E := subtractSobolevWitness W (verticalLocalWitness A)
  have hbound : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |T (H.height (complexPlaneCoordinates x))-x 1| ≤ ζ+δ := by
    intro x hx
    calc
      _ ≤ |T (H.height (complexPlaneCoordinates x))-H.height (complexPlaneCoordinates x)|+
          |H.height (complexPlaneCoordinates x)-x 1| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hT _) (hclose x hx)
  obtain ⟨V, hV⟩ := compact_cutoff_energy_bound isOpen_ball measure_ball_lt_top.ne E hη hs hsub
    hC₀ hC₁ (add_nonneg hζ hδ) hηb hηd hbound
  have hE : (∫ x in ball 0 A, ‖E.weakGrad x‖^2) < 2*ε+4*Real.pi*d := by
    convert H.flattened_energy_error A W hε he using 1
    congr 1
    funext x
    rw [subtractSobolevWitness_gradient]
    rfl
  refine ⟨V, hV.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hE.le (show 0 ≤ 2*C₀^2 by positivity)
  exact add_le_add hm le_rfl

end CircleDomainRigidity

end

end OAI
