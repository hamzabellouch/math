import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ActualRadial
import OAI.Analysis.BiholderTransport.Coordinates.Prefix

namespace OAI

section

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology BigOperators

namespace WeakMTWTransport

lemma symmetric_bilinear_eq_of_diagonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ u v, A u v = A v u) (hB : ∀ u v, B u v = B v u)
    (hd : ∀ u, A u u = B u u) : A = B := by
  ext u v
  have H := hd (u+v)
  simp only [map_add,add_apply,hA v u,hB v u] at H
  linarith [hd u,hd v]

section GeometryJets
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefixNormalCost_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (u : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixNormalCost x t)) (0,p) (u,0) (u,0) =
      normalHessian x (t • p) u u/t := by
  have H := iteratedDeriv_two_affine_line
    ((prefixNormalCost_contDiffAt hp).of_le (m := 2)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (u,0)
  simp only [prefixNormalCost,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,
    zero_add,smul_zero,add_zero,iteratedDeriv_div_const] at H
  rw [← H,← hessianValue_eq_normalHessian hp]
  rfl
end GeometryJets
end WeakMTWTransport

end

end

end

end OAI
