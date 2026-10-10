import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticSecondJetCoordinates
import OAI.Analysis.SymmetricDomains.ImagPartLieReal

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
namespace LieFieldJets
variable {G E ι : Type*} [LieRing G] [LieAlgebra ℂ G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : G →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)
    (hjet : ∀ X, ZeroSecondJet (F X) p → X=0)
    (hlie : ∀ X Y, F ⁅X,Y⁆=VectorField.lieBracket ℂ (F X) (F Y))
    (b : Module.Basis ι ℂ E)

include hlie
 omit [CompleteSpace E] in
 theorem centered_bracket (L : G) (A : E →L[ℂ] E)
    (hL : F L =ᶠ[𝓝 p] fun x => A (x-p)) (X : G) :
    F ⁅L,X⁆ =ᶠ[𝓝 p] VectorField.lieBracket ℂ (fun x => A (x-p)) (F X) := by
  rw [hlie]
  filter_upwards [hL.eventually_nhds] with x hx
  have he : F L =ᶠ[𝓝 x] fun y => A (y-p) := hx
  simp only [VectorField.lieBracket,he.eq_of_nhds,he.fderiv_eq]

 theorem conjugated_diagonal (c : G ≃ₗ⁅ℂ⁆ G) (L : G) (A : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p)) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) :
    ∀ X j, analyticSecondJetCoordinates F p hF b (c ⁅L,X⁆) j=
      secondJetWeight w j*analyticSecondJetCoordinates F p hF b (c X) j := by
  intro X j
  rw [c.map_lie]
  exact analyticSecondJetCoordinates_euler F p hF b A w hA
    (LieAlgebra.ad ℂ G (c L))
    (fun X => centered_bracket F p hlie (c L) A hL X) (c X) j

include hF hjet
 theorem conjugated_ad_semisimple (c : G ≃ₗ⁅ℂ⁆ G) (L : G) (A : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p)) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (s : Finset ℂ) (hs : ∀ j, secondJetWeight w j∈s) :
    (LieAlgebra.ad ℂ G L).IsSemisimple := by
  let J := (analyticSecondJetCoordinates F p hF b).comp c.toLinearEquiv.toLinearMap
  apply LinearMap.diagonal_faithful_isSemisimple (LieAlgebra.ad ℂ G L) J (secondJetWeight w)
    (conjugated_diagonal F p hF hlie b c L A hL w hA)
    ((analyticSecondJetCoordinates_injective F p hF b hjet).comp c.injective) s hs

 theorem conjugated_ad_eigenvalue (c : G ≃ₗ⁅ℂ⁆ G) (L : G) (A : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p)) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) {μ : ℂ}
    (hμ : (LieAlgebra.ad ℂ G L).HasEigenvalue μ) : ∃ j, secondJetWeight w j=μ := by
  let J := (analyticSecondJetCoordinates F p hF b).comp c.toLinearEquiv.toLinearMap
  exact LinearMap.diagonal_faithful_eigenvalue_mem (LieAlgebra.ad ℂ G L) J (secondJetWeight w)
    (conjugated_diagonal F p hF hlie b c L A hL w hA)
    ((analyticSecondJetCoordinates_injective F p hF b hjet).comp c.injective) hμ

 theorem conjugated_second_ad_relation (c : G ≃ₗ⁅ℂ⁆ G) (L H : G)
    (A B : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p))
    (hH : F (c H) =ᶠ[𝓝 p] fun x => B (x-p))
    (w v : ι → ℂ) (hA : ∀ i, A (b i)=w i • b i) (hB : ∀ i, B (b i)=v i • b i)
    (μ ν : ℂ) (hweight : ∀ j, secondJetWeight w j=μ → secondJetWeight v j=ν)
    (X : G) (hX : ⁅L,X⁆=μ • X) : ⁅H,X⁆=ν • X := by
  let J := (analyticSecondJetCoordinates F p hF b).comp c.toLinearEquiv.toLinearMap
  have hi : Function.Injective J :=
    (analyticSecondJetCoordinates_injective F p hF b hjet).comp c.injective
  apply hi
  ext j
  have he := conjugated_diagonal F p hF hlie b c L A hL w hA X j
  have hh := conjugated_diagonal F p hF hlie b c H B hH v hB X j
  change J ⁅L,X⁆ j=secondJetWeight w j*J X j at he
  change J ⁅H,X⁆ j=secondJetWeight v j*J X j at hh
  simp only [hX,map_smul,Pi.smul_apply,smul_eq_mul] at he
  change J ⁅H,X⁆ j=J (ν • X) j
  rw [hh,map_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hw : secondJetWeight w j=μ
  · rw [hweight j hw]
  · have hz : J X j=0 := by
      have hz : (secondJetWeight w j-μ)*J X j=0 := by rw [sub_mul,←he,sub_self]
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hw)
    simp [hz]
end LieFieldJets

end

end OAI
