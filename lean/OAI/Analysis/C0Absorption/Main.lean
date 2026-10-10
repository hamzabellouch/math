import OAI.Analysis.C0Absorption.Aharoni

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section

theorem BiLip.comp {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {g : Y → Z} {f : X → Y} (hg : BiLip g) (hf : BiLip f) : BiLip (g ∘ f) := by
  obtain ⟨cg,Cg,hcg,hcgC,hg⟩ := hg
  obtain ⟨cf,Cf,hcf,hcfC,hf⟩ := hf
  have hCg : 0≤Cg := hcg.le.trans hcgC
  have hCf : 0≤Cf := hcf.le.trans hcfC
  refine ⟨cg*cf,Cg*Cf,mul_pos hcg hcf,mul_le_mul hcgC hcfC hcf.le hCg,fun x y => ⟨?_,?_⟩⟩
  · calc
      cg*cf*dist x y = cg*(cf*dist x y) := mul_assoc _ _ _
      _ ≤ cg*dist (f x) (f y) := mul_le_mul_of_nonneg_left (hf x y).1 hcg.le
      _ ≤ dist ((g ∘ f) x) ((g ∘ f) y) := (hg _ _).1
  · calc
      dist ((g ∘ f) x) ((g ∘ f) y) ≤ Cg*dist (f x) (f y) := (hg _ _).2
      _ ≤ Cg*(Cf*dist x y) := mul_le_mul_of_nonneg_left (hf x y).2 hCg
      _ = Cg*Cf*dist x y := (mul_assoc _ _ _).symm

theorem concrete_metricUniversal : MetricUniversal ConcreteSpace := by
  intro M instM instSep
  obtain ⟨f,hf⟩ := c0_metricUniversal M
  exact ⟨concreteC0Embedding ∘ f,concreteC0Embedding_bilip.comp hf⟩

theorem main_result : MainConclusion := by
  refine ⟨ConcreteSpace,inferInstance,inferInstance,inferInstance,inferInstance,
    concrete_noLinearC0,⟨concreteAbsorption,concreteAbsorption_surjective,concreteAbsorption_bilip⟩,
    ⟨concreteC0Embedding,concreteC0Embedding_bilip⟩,concrete_metricUniversal,
    concrete_not_linearly_isomorphic⟩

end
end C0Absorption

end OAI
