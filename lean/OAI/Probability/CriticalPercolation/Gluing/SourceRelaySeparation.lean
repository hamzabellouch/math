import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.RelayScales

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma source_outside_relay_collar (t z : V → ℝ) (σ e ρ P : ℝ) (L R m i : ℕ)
    (he : 0<e) (hρ : 0 ≤ ρ) (hi : i ≤ L) (hPi : 1 ≤ P+i)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {a : V} (ha : t a ≤ m*ρ-P) :
    a∉G.vertexCollar (corridorRelay t z σ e ρ L i) R := by
  intro hin
  obtain ⟨hρe,_,_,_,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  have hs := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R hin
  have hb := (G.relay_collar_bounds t z σ e ρ hρ ht hz R i hs).1
  have hi' : (i:ℝ) ≤ L := by exact_mod_cast hi
  have hile : (i+1)*e ≤ (L+1)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
  have hb' := (abs_le.mp hb).1
  nlinarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
