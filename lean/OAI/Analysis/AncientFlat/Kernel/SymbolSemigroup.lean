import OAI.Analysis.AncientFlat.Evolution.MovingCoefficients
import OAI.Analysis.AncientFlat.Evolution.SimilarityFamily
import OAI.Analysis.AncientFlat.Evolution.LocalExtensionContinuity

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem exists_symbol_semigroup (c : ℝ) (Af Bf : V → ℝ) (h : SymbolBounds c Af Bf) :
    ∃ K : ℝ, 0≤K ∧ ∃ S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)),
      S 0=ContinuousLinearMap.id ℂ C₀(V,ℂ) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ‖S t‖≤K) ∧
      (∀ d : C₀(V,ℂ), ContinuousOn (fun t => S t d) (Ici (0:ℝ))) ∧
      (∀ s t : ℝ, 0 ≤ s → 0≤t → S (s+t)=(S t).comp (S s)) ∧
      (∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), MovesClassically Af Bf d u ∧
        ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S t d x=u t (Real.exp (-t/4) • x)) := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  obtain ⟨α,β,C,L,B,hα,hC,hL,hB,A,b,hAe,hbe,hb,hLip,hLipb,hA,hAj⟩ := h.moving_coefficients
  obtain ⟨K,hK,U,hU0,hUb,hUc,hUE,hUa⟩ := ParametrixEvolution.exists_local_similarity_family
    α β C L B hα hC hL hB A b Af (fun x => (Bf x : ℂ)) hAe hbe hb hLip hLipb hA hAj
  have h0 : U 0=1 := hU0
  have ha : ∀ s t : ℝ, 0 ≤ s → 0≤t → s+t≤1 → U (s+t)=U s*U t := by
    intro s t hs ht hst
    rw [add_comm]
    exact hUa t s ht hs (by linarith)
  let S := LocalSemigroupExtension.extend U
  have hunit (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : S t=U t :=
    LocalSemigroupExtension.extend_unit U h0 t ht
  refine ⟨K,hK,S,?_,?_,?_,?_,?_⟩
  · rw [hunit 0 ⟨le_rfl,zero_le_one⟩,hU0]
  · intro t ht
    rw [hunit t ht]
    exact hUb t ht
  · exact LocalSemigroupExtension.extend_continuous U h0 ha K hUb hUc
  · intro s t hs ht
    change LocalSemigroupExtension.extend U (s+t)=
      LocalSemigroupExtension.extend U t*LocalSemigroupExtension.extend U s
    rw [add_comm]
    exact LocalSemigroupExtension.extend_add U h0 ha t s ht hs
  · intro d
    obtain ⟨u,hu,hue⟩ := hUE d
    refine ⟨u,⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,?_⟩,?_⟩
    · intro t ht
      obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
      refine ⟨p,hp,fun x => ?_⟩
      rw [hpe x,hAe t ⟨ht.1.le,ht.2.le⟩ x,hbe t ⟨ht.1.le,ht.2.le⟩ x]
    · intro t ht x
      rw [hunit t ht]
      exact hue t ht x
end FlatSimilarity

end

end OAI
