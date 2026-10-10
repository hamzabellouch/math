import Mathlib
import OAI.Probability.Perceptron.Interpolation.ArrayGeometry
import OAI.Probability.Perceptron.Variational.TangentConsistency

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

lemma compact_other_edge_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (F : CompactBlock K 2→ᵇℝ) (g : K→ᵇℝ),compactGGDefect μ 2 0 F g=0)
    (he : MeasurePreserving (compactRelabel (K:=K) (Equiv.swap 0 1)) (μ : Measure _) (μ : Measure _))
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray K)),Q 1 0=Q 0 1) :
    (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 1 2))=
      (1/2:ℝ≥0) • (((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)))+
      (1/2:ℝ≥0) • ((μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 1))) := by
  have h := congrArg (Measure.map (fun Q : CompactArray K=>(Q 0 1,Q 0 2))) he.map_eq
  rw [Measure.map_map (by fun_prop) he.measurable] at h
  have h' : (μ : Measure (CompactArray K)).map (fun Q=>(Q 1 0,Q 1 2))=
      (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 2)) := by
    simpa [Function.comp_def,compactRelabel,Equiv.swap_apply_def] using h
  have hm : (μ : Measure (CompactArray K)).map (fun Q=>(Q 1 0,Q 1 2))=
      (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 1 2)) :=
    Measure.map_congr (hsy.mono (fun Q hQ=>by dsimp only; rw [hQ]))
  rw [←hm,h',compact_two_edge_law μ hGG]

lemma array_tangent_self_consistency (μ : ProbabilityMeasure (CompactArray Time))
    (hGG : ∀ (F : CompactBlock Time 2→ᵇℝ) (g : Time→ᵇℝ),compactGGDefect μ 2 0 F g=0)
    (he : MeasurePreserving (compactRelabel (K:=Time) (Equiv.swap 0 1)) (μ : Measure _) (μ : Measure _))
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),∀ i j,Q i j=Q j i)
    (hul : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),∀ i j k,min (Q i j:ℝ) (Q i k:ℝ)≤(Q j k:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,0≤a x ∧ a x≤A)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ Q : CompactArray Time,G (Q 0 1)*((Q 0 1:ℝ)-a (Q 0 1)*(1-(Q 0 1:ℝ)^2)+
        2*a (Q 0 2)*((Q 1 2:ℝ)-(Q 0 1:ℝ)*(Q 0 2:ℝ))) ∂(μ : Measure _))=0) :
    (∀ᵐ x : Time ∂((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
      a x=∫ y in 0..(x:ℝ),(realTail ((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)) y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),(x:ℝ)≤A/(1+A) := by
  let ν := (μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hd : ν.map (fun x=>(x,x))=(μ : Measure (CompactArray Time)).map (fun Q=>(Q 0 1,Q 0 1)) := by
    change ((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)).map (fun x=>(x,x))=_
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  apply tangent_sphere_self_consistency (μ : Measure (CompactArray Time)) ν (fun Q=>Q 0 1) (fun Q=>Q 0 2) (fun Q=>Q 1 2)
    (by fun_prop) (by fun_prop) (by fun_prop) rfl
    (by rw [hd]; exact compact_two_edge_law μ hGG)
    (by rw [hd]; exact compact_other_edge_law μ hGG he (hsy.mono (fun Q hQ=>hQ 1 0)))
    _ a ha hA hab hT
  filter_upwards [hsy,hul] with Q hS hU
  refine ⟨hU 0 1 2,?_,?_⟩
  · have h := hU 1 0 2
    simpa only [hS 1 0] using h
  · have h := hU 2 0 1
    simpa only [hS 2 0,hS 2 1] using h

end SphericalPerceptronFreeEnergy
end

end OAI
