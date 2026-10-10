import OAI.Analysis.CircleDomains.Topology.SphereCoefficient
import OAI.Analysis.CircleDomains.Reflection.ReflectionCoefficientExtension

namespace OAI

/-! The actual norm-preserving coefficient transport for circular reflection. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def roundReflectionCoefficient (c : ℂ) (p : Sphere) (a : ℂ) : ℂ :=
  sphereReflectionPhase c p * starRingEnd ℂ a

lemma roundReflectionCoefficient_zero (c : ℂ) (p : Sphere) :
    roundReflectionCoefficient c p 0=0 := by simp [roundReflectionCoefficient]

lemma roundReflectionCoefficient_norm (c : ℂ) (p : Sphere) (a : ℂ) :
    ‖roundReflectionCoefficient c p a‖=‖a‖ := by
  rw [roundReflectionCoefficient,norm_mul,sphereReflectionPhase_norm,one_mul,Complex.norm_conj]

lemma roundReflectionCoefficient_measurable (c : ℂ) :
    Measurable (fun p : Sphere × ℂ => roundReflectionCoefficient c p.1 p.2) :=
  ((sphereReflectionPhase_measurable c).comp measurable_fst).mul (Complex.continuous_conj.measurable.comp measurable_snd)

lemma roundReflectionCoefficient_involutive (c : ℂ) {r : ℝ} (hr : 0<r)
    (p : Sphere) (a : ℂ) :
    roundReflectionCoefficient c p
      (roundReflectionCoefficient c (roundDiskReflection c r hr p) a)=a := by
  simp only [roundReflectionCoefficient,map_mul,sphereReflectionPhase_reflection,Complex.conj_conj]
  have hphase : sphereReflectionPhase c p * starRingEnd ℂ (sphereReflectionPhase c p)=1 := by
    rw [Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq,sphereReflectionPhase_norm,one_pow,Complex.ofReal_one]
  rw [←mul_assoc,hphase,one_mul]

lemma exists_round_reflection_coefficient {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0<r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c j) (r j))))
    (f : Sphere → ℂ) (hf : Measurable f) {k : ℝ} (hk : 0≤k) (hb : ∀p,‖f p‖≤k) :
    ∃E : Sphere → ℂ,Measurable E ∧ (∀p,‖E p‖≤k) ∧
      EqOn E f (⋃i,((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))ᶜ ∧
      ∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p)) := by
  classical
  let R := fun i => roundDiskReflection (c i) (r i) (hr i)
  let K := fun i => ((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i)
  let U := fun i => ((↑) : ℂ → Sphere) '' Metric.ball (c i) (r i)
  have hK : ∀i,IsClosed (K i) := fun i =>
    ((isCompact_closedBall (c i) (r i)).image OnePoint.continuous_coe).isClosed
  have hbase : IsOpen (⋃i,K i)ᶜ := (isClosed_iUnion_of_finite hK).isOpen_compl
  have htm : ∀w : List I,MeasurableSet (reflectionTile R K w) := by
    intro w
    exact ((reflectionWord R w).isOpenMap _ hbase).measurableSet
  obtain ⟨E,hEm,hEb,hEf,_hEz,hEinv⟩ := exists_reflection_coefficient_extension R
    (fun i => roundDiskReflection_involutive (c i) (hr i)) K U
    (fun _ => image_mono Metric.ball_subset_closedBall) hd
    (fun i => (roundDiskReflection_outer_image (c i) (hr i)).subset) htm
    (fun i => roundReflectionCoefficient (c i))
    (fun i => roundReflectionCoefficient_involutive (c i) (hr i))
    (fun i => roundReflectionCoefficient_zero (c i))
    (fun i => roundReflectionCoefficient_norm (c i))
    (fun i => roundReflectionCoefficient_measurable (c i)) f hf hk hb
  exact ⟨E,hEm,hEb,hEf,hEinv⟩

end CircleDomainRigidity

end

end OAI
