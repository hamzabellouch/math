import OAI.Probability.PosteriorReplicas.Gaussian.GaussianFiber

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

instance matrixRealMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℝ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℝ))

instance matrixRealBorelSpace (m n : Type*) [Countable m] [Countable n] :
    BorelSpace (Matrix m n ℝ) := inferInstanceAs (BorelSpace (m → n → ℝ))

attribute [fun_prop] measurable_labels

@[fun_prop] lemma measurable_matrix_inv_real (n : ℕ) :
    Measurable (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

@[fun_prop] lemma continuous_rowGram {d k : ℕ} : Continuous (@rowGram d k) := by
  unfold rowGram
  fun_prop

@[fun_prop] lemma measurable_liftLabel {d k : ℕ} :
    Measurable (fun z : Rows d k × Labels k => liftLabel z.1 z.2) := by
  unfold liftLabel Matrix.mulVec dotProduct
  fun_prop

@[fun_prop] lemma continuous_liftLabel {d k : ℕ} (A : Rows d k) :
    Continuous (liftLabel A) := continuous_pairingLift A

@[fun_prop] lemma measurable_kernelComponent {d k : ℕ} :
    Measurable (fun z : Rows d k × Vec d => kernelComponent z.1 z.2) := by
  unfold kernelComponent
  fun_prop

lemma liftLabel_eq_pairingLift {d k : ℕ} (A : Rows d k) : liftLabel A = pairingLift A := rfl
lemma rowGram_eq_gram {d k : ℕ} (A : Rows d k) : rowGram A = Matrix.gram ℝ A := rfl

lemma kernelComponent_eq_starProjection {d k : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (x : Vec d) :
    kernelComponent A x = (Submodule.span ℝ (Set.range A))ᗮ.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val, starProjection_eq_pairingLift hA]
  rfl

lemma labels_liftLabel {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A) (y : Labels k) :
    labels A (liftLabel A y) = y := pairings_pairingLift hA y

lemma labels_kernelComponent {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A) (x : Vec d) :
    labels A (kernelComponent A x) = 0 := by
  unfold kernelComponent
  ext i
  change ⟪A i, x - liftLabel A (labels A x)⟫ = 0
  rw [inner_sub_right]
  change labels A x i - labels A (liftLabel A (labels A x)) i = 0
  rw [labels_liftLabel hA, sub_self]

def basePoint {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) (x : Vec d) : Vec d :=
  match base with
  | .gaussian => liftLabel A y + kernelComponent A x
  | .spherical => liftLabel A y +
      (Real.sqrt (1 - ‖liftLabel A y‖ ^ 2) / ‖kernelComponent A x‖) • kernelComponent A x

@[fun_prop] lemma measurable_basePoint {d k : ℕ} (base : BaseLaw) :
    Measurable (fun z : (Rows d k × Labels k) × Vec d => basePoint base z.1.1 z.1.2 z.2) := by
  cases base <;> unfold basePoint <;> fun_prop

lemma baseFiber_eq_map {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    baseFiber base A y = (stdGaussian (Vec d)).map (basePoint base A y) := by
  cases base <;> rfl

@[fun_prop] lemma measurable_basePoint_fixed {d k : ℕ} (base : BaseLaw)
    (A : Rows d k) (y : Labels k) : Measurable (basePoint base A y) := by
  have h := (measurable_basePoint (d := d) (k := k) base).comp
    (show Measurable (fun x : Vec d => ((A, y), x)) from measurable_const.prodMk measurable_id)
  exact h

instance {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    IsProbabilityMeasure (baseFiber base A y) := by
  rw [baseFiber_eq_map]
  infer_instance

lemma labels_basePoint {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (base : BaseLaw) (y : Labels k) (x : Vec d) : labels A (basePoint base A y x) = y := by
  have h₁ := labels_liftLabel hA y
  have h₂ := labels_kernelComponent hA x
  cases base <;> ext i <;>
    simp only [basePoint, labels, inner_add_right, inner_smul_right,
      show ⟪A i, liftLabel A y⟫ = y i from congrFun h₁ i,
      show ⟪A i, kernelComponent A x⟫ = 0 from congrFun h₂ i, mul_zero, add_zero]

lemma measurable_parametric_map {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [SFinite μ] {F : Z × X → Y} (hF : Measurable F) :
    Measurable (fun z => μ.map (fun x => F (z, x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he : (fun z => μ.map (fun x => F (z, x)) s) =
      (fun z => μ ((Prod.mk z) ⁻¹' (F ⁻¹' s))) := by
    funext z
    exact Measure.map_apply (hF.comp (measurable_const.prodMk measurable_id)) hs
  rw [he]
  exact measurable_measure_prodMk_left (hF hs)

@[fun_prop] lemma measurable_baseFiber {d k : ℕ} (base : BaseLaw) :
    Measurable (fun z : Rows d k × Labels k => baseFiber base z.1 z.2) := by
  simp_rw [baseFiber_eq_map]
  exact measurable_parametric_map _ (measurable_basePoint base)

def baseKernel {d k : ℕ} (base : BaseLaw) : Kernel (Rows d k × Labels k) (Vec d) where
  toFun z := baseFiber base z.1 z.2
  measurable' := measurable_baseFiber base

instance {d k : ℕ} (base : BaseLaw) : IsMarkovKernel (@baseKernel d k base) where
  isProbabilityMeasure _ := by dsimp [baseKernel]; infer_instance

@[fun_prop] lemma measurable_tiltMass {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun z : Rows d k × Labels k => tiltMass base f z.1 z.2) := by
  unfold tiltMass
  exact hf.lintegral_kernel (κ := baseKernel base)

end PosteriorReplicas
end

end OAI
