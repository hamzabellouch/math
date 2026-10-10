import OAI.Analysis.AncientFlat.Regularity.SourceHolderEvolution
import OAI.Analysis.AncientFlat.Evolution.SourceDuhamel

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace FlatSimilarity
open ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma MovesWithSource.fourth_holder (c : ℝ) (Af Bf : V → ℝ) (h : SymbolBounds c Af Bf)
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ)
    (d : C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ)) (hu : MovesWithSource Af Bf f d u) :
    ∀ a : ℝ, 0<a → ∃ C : ℝ, 0≤C ∧
      (∀ t∈Icc a 1, ∀ x, ‖iteratedFDeriv ℝ 4 (fun y => u t y) x‖≤C) ∧
      (∀ t∈Icc a 1, ∀ s∈Icc a 1, ∀ x y,
        ‖iteratedFDeriv ℝ 4 (fun z => u t z) x-iteratedFDeriv ℝ 4 (fun z => u s z) y‖≤
          C*(‖x-y‖^γ+|t-s|^(γ/4))) := by
  obtain ⟨α,β,C,L,B,hα,hC,hL,hB,A,b,hAe,hbe,hbound,hLip,hLipb,hA,hAj⟩ := h.moving_coefficients
  have hse : SourceEvolves A b (movingSource f) 0 1 d u := by
    refine ⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,fun t ht => ?_⟩
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    refine ⟨p,hp,fun x => ?_⟩
    rw [hAe t ⟨ht.1.le,ht.2.le⟩ x,hbe t ⟨ht.1.le,ht.2.le⟩ x,
      movingSource_apply f ⟨ht.1.le,ht.2.le⟩]
    exact hpe x
  exact hse.fourth_holder hα L B C hL hB hC A b 1 zero_le_one le_rfl hbound hLip hLipb hA hAj
    γ hγ hγ1 (movingSource f) (movingSource_holder f γ hγ.le hf) d u
end FlatSimilarity

end

end OAI
