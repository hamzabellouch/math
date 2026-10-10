import OAI.MathematicalPhysics.Boltzmann.Branching.IncomingLossRate
import OAI.MathematicalPhysics.Boltzmann.Collision.SphereIsometryMeasure
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod

namespace OAI

section

/-! # The actual normal-angle gain kernel for measurable cold partner measures -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def normalChild (left : Bool) (z : (X × Velocity) × (Velocity × Sphere)) : Velocity :=
  if left then scatterLeft z.2.1 z.1.2 z.2.2 else scatterRight z.2.1 z.1.2 z.2.2

theorem normalChild_measurable (left : Bool) : Measurable (normalChild (X := X) left) := by
  cases left <;> unfold normalChild scatterLeft scatterRight normalComponent <;> dsimp <;> fun_prop

def normalParameters (K : Kernel X Velocity) : Kernel (X × Velocity) (Velocity × Sphere) :=
  (K.comap Prod.fst measurable_fst) ×ₖ Kernel.const _ sphereArea

def normalRate (z : (X × Velocity) × (Velocity × Sphere)) : ℝ≥0∞ :=
  ENNReal.ofReal (collisionKernel z.2.1 z.1.2 z.2.2)

theorem normalRate_measurable : Measurable (normalRate (X := X)) := by
  unfold normalRate collisionKernel normalComponent
  fun_prop

def normalChildKernel (K : Kernel X Velocity) (left : Bool) : Kernel (X × Velocity) Velocity :=
  (Kernel.withDensity (Kernel.id ×ₖ normalParameters K)
    (fun _ z => normalRate z)).map (normalChild left)

instance normalParameters_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (normalParameters K) := by unfold normalParameters; infer_instance

instance normalChildKernel_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] (left : Bool) :
    IsSFiniteKernel (normalChildKernel K left) := by
  have : IsSFiniteKernel (Kernel.withDensity (Kernel.id ×ₖ normalParameters K)
      (fun _ z => normalRate z)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold normalChildKernel
  infer_instance

theorem normalChildKernel_lintegral (K : Kernel X Velocity) [IsSFiniteKernel K]
    (left : Bool) (z : X × Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v, f v ∂normalChildKernel K left z) =
      ∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*
        f (normalChild left (z,w,ω)) ∂sphereArea ∂K z.1 := by
  have hd : Measurable (Function.uncurry (fun (_ : X × Velocity)
      (q : (X × Velocity) × (Velocity × Sphere)) => normalRate q)) :=
    normalRate_measurable.comp measurable_snd
  have hc : Measurable (fun q => f (normalChild (X := X) left q)) :=
    hf.comp (normalChild_measurable (X := X) left)
  have hi : Measurable (fun q : (X × Velocity) × (Velocity × Sphere) => normalRate q*f (normalChild left q)) :=
    normalRate_measurable.mul hc
  rw [normalChildKernel,Kernel.lintegral_map _ (normalChild_measurable left) z hf,
    Kernel.lintegral_withDensity _ hd z hc,Kernel.lintegral_id_prod hi]
  have hip : Measurable (fun q : Velocity × Sphere =>
      ENNReal.ofReal (collisionKernel q.1 z.2 q.2)*f (normalChild left (z,q))) := by
    simpa only [normalRate,Function.comp_def,id_eq] using
      hi.comp (measurable_const.prodMk measurable_id)
  rw [normalParameters,Kernel.prod_apply,Kernel.comap_apply,Kernel.const_apply]
  exact lintegral_prod _ hip.aemeasurable

def normalGainKernel (K : Kernel X Velocity) : Kernel (X × Velocity) Velocity :=
  normalChildKernel K true+normalChildKernel K false

instance normalGainKernel_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (normalGainKernel K) := by unfold normalGainKernel; infer_instance

theorem normalGainKernel_lintegral (K : Kernel X Velocity) [IsSFiniteKernel K]
    (z : X × Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v, f v ∂normalGainKernel K z) =
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (scatterLeft w z.2 ω)
        ∂sphereArea ∂K z.1)+
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (scatterRight w z.2 ω)
        ∂sphereArea ∂K z.1) := by
  rw [normalGainKernel,add_apply,lintegral_add_measure,
    normalChildKernel_lintegral K true z hf,normalChildKernel_lintegral K false z hf]
  rfl

end BoltzmannNonuniqueness

end

end

section

/-! # The physical gain kernel, retaining the collision's spacetime location -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def normalPhaseGainKernel (K : Kernel X Velocity) : Kernel (X × Velocity) (X × Velocity) :=
  (Kernel.id ×ₖ normalGainKernel K).map (fun z => (z.1.1,z.2))

instance normalPhaseGainKernel_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (normalPhaseGainKernel K) := by
  unfold normalPhaseGainKernel
  infer_instance

theorem normalPhaseGainKernel_lintegral (K : Kernel X Velocity) [IsSFiniteKernel K]
    (z : X × Velocity) {f : X × Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂normalPhaseGainKernel K z) =
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (z.1,scatterLeft w z.2 ω)
        ∂sphereArea ∂K z.1)+
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (z.1,scatterRight w z.2 ω)
        ∂sphereArea ∂K z.1) := by
  have hp : Measurable (fun p : (X × Velocity) × Velocity => (p.1.1,p.2)) := by fun_prop
  have hc : Measurable (fun p : (X × Velocity) × Velocity => f (p.1.1,p.2)) := hf.comp hp
  rw [normalPhaseGainKernel,Kernel.lintegral_map _ hp z hf,
    Kernel.lintegral_id_prod hc]
  simpa only [Function.comp_def] using normalGainKernel_lintegral K z
    (hf.comp (show Measurable (fun v : Velocity => (z.1,v)) from
      measurable_const.prodMk measurable_id))

end BoltzmannNonuniqueness

end

end

section

/-! # Rotation covariance of the weighted normal-reflection law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem normalReflectionVector_isometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) (g n : Velocity) :
    R (normalReflectionVector g n) = normalReflectionVector (R g) (R n) := by
  unfold normalReflectionVector
  rw [R.map_sub,R.map_smul,R.inner_map_map]

theorem normalReflection_isometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) (e n : Sphere) :
    sphereIsometry R (normalReflection e n) =
      normalReflection (sphereIsometry R e) (sphereIsometry R n) := by
  apply Subtype.ext
  exact normalReflectionVector_isometry R e.1 n.1

def normalReflectionLaw (e : Sphere) : Measure Sphere :=
  (sphereArea.withDensity (fun n : Sphere => ENNReal.ofReal |inner ℝ e.1 n.1|)).map
    (normalReflection e)

theorem normalReflectionLaw_lintegral (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n, f n ∂normalReflectionLaw e) =
      ∫⁻ n : Sphere, ENNReal.ofReal |inner ℝ e.1 n.1| * f (normalReflection e n) ∂sphereArea := by
  rw [normalReflectionLaw,lintegral_map hf (normalReflection_measurable e),
    lintegral_withDensity_eq_lintegral_mul _ (g := fun n => f (normalReflection e n)) (by fun_prop)
      (hf.comp (normalReflection_measurable e))]
  rfl

theorem normalReflectionLaw_isometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) (e : Sphere) :
    (normalReflectionLaw e).map (sphereIsometry R) = normalReflectionLaw (sphereIsometry R e) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (sphereIsometry R).measurable,
    normalReflectionLaw_lintegral e (f := fun n => f (sphereIsometry R n)) (hf.comp (sphereIsometry R).measurable),
    normalReflectionLaw_lintegral (sphereIsometry R e) hf]
  let g : Sphere → ℝ≥0∞ := fun n => ENNReal.ofReal |inner ℝ (sphereIsometry R e).1 n.1| *
    f (normalReflection (sphereIsometry R e) n)
  have hg : Measurable g := by
    exact (show Measurable (fun n : Sphere => ENNReal.ofReal |inner ℝ (sphereIsometry R e).1 n.1|) by
      fun_prop).mul (hf.comp (normalReflection_measurable _))
  calc
    _ = ∫⁻ n, g (sphereIsometry R n) ∂sphereArea := by
      apply lintegral_congr
      intro n
      dsimp only [g]
      rw [← normalReflection_isometry]
      congr 2
      change |inner ℝ e.1 n.1| = |inner ℝ (R e.1) (R n.1)|
      rw [R.inner_map_map]
    _ = ∫⁻ n, g n ∂sphereArea.map (sphereIsometry R) :=
      (lintegral_map hg (sphereIsometry R).measurable).symm
    _ = _ := by rw [(sphereIsometry_measurePreserving R).map_eq]

end BoltzmannNonuniqueness

end

end

section

/-! # Collision gain as a kernel applied to the incoming hot measure -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingCollisionMeasure_lintegral (μ : Measure (X × (Velocity × Velocity)))
    [SFinite μ] {f : (X × (Velocity × Velocity)) × Sphere → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂incomingCollisionMeasure μ) =
      ∫⁻ p, ∫⁻ ω, ENNReal.ofReal (collisionKernel p.2.1 p.2.2 ω)*f (p,ω)
        ∂sphereArea ∂μ := by
  have hd : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  rw [incomingCollisionMeasure,lintegral_withDensity_eq_lintegral_mul _ hd hf]
  exact lintegral_prod _ (hd.mul hf).aemeasurable

theorem normalPhaseGain_comp (μ : Measure X) [SFinite μ]
    (K H : Kernel X Velocity) [IsSFiniteKernel K] [IsSFiniteKernel H] :
    normalPhaseGainKernel K ∘ₘ (μ ⊗ₘ H) =
      (incomingCollisionMeasure (μ ⊗ₘ (K ×ₖ H))).map incomingLeft+
      (incomingCollisionMeasure (μ ⊗ₘ (K ×ₖ H))).map incomingRight := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    Measure.lintegral_compProd (hf.lintegral_kernel),lintegral_add_measure,
    lintegral_map hf incomingLeft_measurable,
    lintegral_map hf incomingRight_measurable,
    incomingCollisionMeasure_lintegral _ (f := fun z => f (incomingLeft z))
      (hf.comp incomingLeft_measurable),
    incomingCollisionMeasure_lintegral _ (f := fun z => f (incomingRight z))
      (hf.comp incomingRight_measurable)]
  have hr : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  have hL : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*f (incomingLeft z)) := by
    exact hr.mul (hf.comp incomingLeft_measurable)
  have hR : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*f (incomingRight z)) := by
    exact hr.mul (hf.comp incomingRight_measurable)
  rw [Measure.lintegral_compProd (hL.lintegral_prod_right' (ν := sphereArea)),
    Measure.lintegral_compProd (hR.lintegral_prod_right' (ν := sphereArea)),
    ← lintegral_add_left ((hL.lintegral_prod_right' (ν := sphereArea)).lintegral_kernel_prod_right' (κ := K ×ₖ H))]
  apply lintegral_congr
  intro x
  simp_rw [normalPhaseGainKernel_lintegral K _ hf]
  rw [lintegral_add_left]
  · congr 1
    · rw [Kernel.prod_apply,lintegral_prod_symm]
      · rfl
      · exact ((hL.lintegral_prod_right' (ν := sphereArea)).comp (measurable_const.prodMk measurable_id)).aemeasurable
    · rw [Kernel.prod_apply,lintegral_prod_symm]
      · rfl
      · exact ((hR.lintegral_prod_right' (ν := sphereArea)).comp (measurable_const.prodMk measurable_id)).aemeasurable
  · exact (((hL.lintegral_prod_right' (ν := sphereArea)).comp (measurable_const.prodMk
      (measurable_snd.prodMk measurable_fst))).lintegral_prod_right' (ν := K x))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The normal-angle gain is linear in an arbitrary incoming partner measure -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalGainKernel_eq_smul_of_measure_eq
    (K : Kernel X Velocity) (L : Kernel Y Velocity) [IsSFiniteKernel K] [IsSFiniteKernel L]
    (x : X) (y : Y) (v : Velocity) (c : ℝ≥0∞) (h : K x = c • L y) :
    normalGainKernel K (x,v) = c • normalGainKernel L (y,v) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [normalGainKernel_lintegral K (x,v) hf,lintegral_smul_measure,
    normalGainKernel_lintegral L (y,v) hf,h]
  simp only [lintegral_smul_measure,smul_eq_mul,mul_add]

theorem normalPhaseGainKernel_lintegral_gain
    (K : Kernel X Velocity) [IsSFiniteKernel K] (z : X × Velocity)
    {f : X × Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂normalPhaseGainKernel K z) =
      ∫⁻ v, f (z.1,v) ∂normalGainKernel K z := by
  rw [normalPhaseGainKernel_lintegral K z hf,
    normalGainKernel_lintegral K z (f := fun v => f (z.1,v)) (hf.comp (measurable_const.prodMk measurable_id))]

end BoltzmannNonuniqueness

end

end

end OAI
