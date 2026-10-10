import OAI.Geometry.Relativity.CKS.PhysicalMomentumNorm

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

lemma physical_acceleration_components {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a : Fin 2) :
    (frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).B a =
      ∑ b : Fin 2, (D (CKSRealizedRound.basis b.succ) U x / U x) *
        angularFrame (U x) (γ x) (s x) a b := by
  have h := leaf_frame_acceleration hU hγ hs h0 hp a
  fin_cases a <;> exact h

theorem physical_acceleration_norm {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    CKSFrame.accelNormSq (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
        (D (CKSRealizedRound.basis i.succ) U x / U x) *
        (D (CKSRealizedRound.basis j.succ) U x / U x) := by
  have he : CKSFrame.accelNormSq (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      ∑ a : Fin 2, ((frameConnectionField
        (fun y => foliationMetric (U y) (γ y) (s y))
        (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).B a)^2 := by
    simp only [CKSFrame.accelNormSq,Fin.sum_univ_two]
  rw [he]
  simp_rw [physical_acceleration_components hU hγ hs h0 hp]
  exact angular_covector_frame_square _ h0.ne' hp.self_of_nhds

end
end CKSAngularGeometry

end

end OAI
