import OAI.Analysis.AncientFlat.Evolution.MovingCoefficients
import OAI.Analysis.AncientFlat.Evolution.EvolutionUniqueness

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma MovesClassically.unique {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {d : C₀(V,ℂ)} {u v : ℝ → C₀(V,ℂ)}
    (hu : MovesClassically Af Bf d u) (hv : MovesClassically Af Bf d v) :
    ∀ t ∈ Icc (0:ℝ) 1, u t=v t := by
  obtain ⟨α,β,C,L,B,hα,hC,hL,hB,A,b,hAe,hbe,hb,hLip,hLipb,hA,hAj⟩ := h.moving_coefficients
  have he (w : ℝ → C₀(V,ℂ)) (hw : MovesClassically Af Bf d w) :
      ParametrixEvolution.Evolves A b 0 1 d w := by
    refine ⟨hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,?_⟩
    intro t ht
    obtain ⟨p,hp,hpe⟩ := hw.2.2.2.2 t ht
    refine ⟨p,hp,fun x => ?_⟩
    rw [hAe t ⟨ht.1.le,ht.2.le⟩ x,hbe t ⟨ht.1.le,ht.2.le⟩ x]
    exact hpe x
  exact (he u hu).unique (he v hv) zero_le_one hα hC hB hb (fun t ht => (hA t ht).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))) hAj
end FlatSimilarity

end

end OAI
