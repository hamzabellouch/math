import OAI.Analysis.AncientFlat.Evolution.UniformLipschitz
import OAI.Analysis.AncientFlat.Evolution.CompactDifferenceCore

namespace OAI
noncomputable section
open Set Filter
open scoped Topology ContDiff ZeroAtInfty BoundedContinuousFunction NNReal
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
lemma MovesClassically.lipschitz {Af Bf : V → ℝ} {d : C₀(V,ℂ)}
    {u : ℝ → C₀(V,ℂ)} (hu : MovesClassically Af Bf d u) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => u t x) := by
  obtain ⟨M,hM⟩ := hu.2.2.2.1 t ht 1 (by norm_num)
  have hMn : 0≤M := (norm_nonneg _).trans (hM 0)
  refine ⟨⟨M,hMn⟩,lipschitzWith_of_nnnorm_fderiv_le ((hu.2.2.1 t ht).differentiable (by norm_num)) ?_⟩
  intro x
  change ‖fderiv ℝ (fun y => u t y) x‖≤M
  simpa only [norm_iteratedFDeriv_one] using hM x
lemma TimeOneMap.lipschitz {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {P : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)} (hP : TimeOneMap Af Bf P) (d : C₀(V,ℂ)) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => P d x) := by
  obtain ⟨K,hK,S,hS0,hSb,hSc,hSa,hSm⟩ := exists_symbol_semigroup c Af Bf h
  have hP' (v : C₀(V,ℂ)) : P v=S 1 v := by
    obtain ⟨u,hu,hue⟩ := hP v
    obtain ⟨w,hw,hwe⟩ := hSm v
    ext x
    rw [hue x,hwe 1 ⟨zero_le_one,le_rfl⟩ x]
    congr 1
    exact hu.unique h hw 1 ⟨zero_le_one,le_rfl⟩
  have hhalf : S 1=(S (1/2)).comp (S (1/2)) := by
    convert hSa (1/2) (1/2) (by norm_num) (by norm_num) using 1
    norm_num
  obtain ⟨u,hu,hue⟩ := hSm (S (1/2) d)
  obtain ⟨C,hC⟩ := hu.lipschitz (t := 1/2) ⟨by norm_num,by norm_num⟩
  let L : V →L[ℝ] V := Real.exp (-(1/2:ℝ)/4) • ContinuousLinearMap.id ℝ V
  have he : (fun x => P d x)=fun x => u (1/2) (L x) := by
    funext x
    rw [hP',hhalf]
    exact hue (1/2) ⟨by norm_num,by norm_num⟩ x
  rw [he]
  exact ⟨C*‖L‖₊,hC.comp L.lipschitzWith⟩
lemma TimeOneMap.uniform_lipschitz {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {P : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)} (hP : TimeOneMap Af Bf P) :
    ∃ K : ℝ, 0≤K ∧ ∀ d : C₀(V,ℂ), ∀ x y : V,
      ‖P d x-P d y‖≤K*‖d‖*‖x-y‖ :=
  FlatCompactness.uniform_lipschitz P (hP.lipschitz h)
end FlatSimilarity

end

end OAI
