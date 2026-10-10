import Mathlib
import OAI.Geometry.PrescribedPotential.LiteralWeakHessian
import OAI.Geometry.PrescribedPotential.GlobalSmooth

namespace OAI

/-! Sobolev Reconstruction. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma memSobolev_of_first_basis {s : ℝ} {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u)
    (hD : ∀ j, MemSobolev s 2 (∂_{stdOrthonormalBasis ℝ E j} u)) :
    MemSobolev (s+1) 2 u := by
  have hh := memSobolev_of_second_basis (hu.mono (show s-1 ≤ s by linarith))
    (fun j => (hD j).lineDerivOp (m := stdOrthonormalBasis ℝ E j))
  convert hh using 1
  ring

def lowerCoord (s t : ℝ) (hst : t ≤ s) : L2 E →L[ℂ] L2 E :=
  liftOperator s t (ContinuousLinearMap.id ℂ _) (fun _ hu => hu.mono hst)

lemma realize_lowerCoord (s t : ℝ) (hst : t ≤ s) (u : L2 E) :
    realize t (lowerCoord s t hst u) = realize s u :=
  realize_liftOperator s t _ _ u

lemma lowerCoord_schwartz (s t : ℝ) (hst : t ≤ s) (f : 𝓢(E,ℂ)) :
    lowerCoord s t hst (schwartzCoord s f) = schwartzCoord t f := by
  apply realize_injective t
  rw [realize_lowerCoord,realize_schwartzCoord,realize_schwartzCoord]

end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

def globalizeOrder (k : ℕ) (q : Fin A.count) (κ : ChartCutoff (A.euclideanChart q).target) :
    L2 (EC d) →L[ℝ] D.Sobolev (k : ℝ) :=
  ((D.embed (k : ℝ)).comp (globalize q κ)).extendOfNorm (schwartzCoordLinear (k : ℝ))

lemma globalizeOrder_schwartz (k : ℕ) (q : Fin A.count)
    (κ : ChartCutoff (A.euclideanChart q).target) (f : 𝓢(EC d,ℂ)) :
    D.globalizeOrder k q κ (schwartzCoord (k : ℝ) f) = D.embed (k : ℝ) (globalize q κ f) := by
  obtain ⟨C,hC,h⟩ := globalize_integer_bound D q κ k
  exact LinearMap.extendOfNorm_eq (schwartzCoord_dense (k : ℝ)) ⟨C,h⟩ f

lemma globalizeOrder_lower_zero (k : ℕ) (q : Fin A.count)
    (κ : ChartCutoff (A.euclideanChart q).target) (u : L2 (EC d)) :
    D.lower (k : ℝ) 0 (D.globalizeOrder k q κ u) =
      D.globalizeL2 q κ (lowerCoord (k : ℝ) 0 (Nat.cast_nonneg k) u) := by
  have hh : D.lower (k : ℝ) 0 ∘ D.globalizeOrder k q κ =
      D.globalizeL2 q κ ∘ lowerCoord (k : ℝ) 0 (Nat.cast_nonneg k) := by
    apply (schwartzCoord_dense (k : ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply,D.globalizeOrder_schwartz,D.lower_embed (Nat.cast_nonneg k),
      lowerCoord_schwartz,D.globalizeL2_schwartz]
  exact congr_fun hh u

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

 

theorem sobolev_of_local_order (k : ℕ) (u : D.localizers.Sobolev 0)
    (hu : ∀ p, MemSobolev (k : ℝ) 2 (D.localizers.distribution 0 p u)) :
    ∃ v : D.localizers.Sobolev (k : ℝ), D.localizers.lower (k : ℝ) 0 v = u := by
  choose f hf using fun p => (memSobolev_iff_realize (k : ℝ) _).mp (hu p)
  refine ⟨∑ p, D.localizers.globalizeOrder k (D.patch p).index (D.cutoff p) (f p),?_⟩
  rw [map_sum,← D.reconstruct_eq u,D.reconstruct_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [D.localizers.globalizeOrder_lower_zero]
  congr 1
  apply realize_injective 0
  rw [realize_lowerCoord,hf]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
