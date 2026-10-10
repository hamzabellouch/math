import OAI.Analysis.LipschitzHilbert.Trees.SourceCoefficientIntegrability

namespace OAI

/-! A symmetric reference cutoff is exactly three one-sided cutoffs,
including its boundary. No level-set nullity is required. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def physicalCenteredWave (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (q : Σ j, ι j) (k : κ) (z : ℝ×ℝ) : ℂ :=
  if |v z-t| ≤ d q.1 then P.physicalPacket s q.1 q.2 k z else 0

def physicalCenteredCoefficient (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (u : ι j) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun q : Σ j, ι j => P.length q.1*P.width)
    (P.physicalCenteredWave s t d v) g ⟨j,u⟩

theorem physicalCenteredWave_eq (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (q : Σ j, ι j) (k : κ) (z : ℝ×ℝ) :
    P.physicalCenteredWave s t d v q k z =
      P.physicalSelectedWave s (fun j => t+d j) v q k z+
      P.physicalSelectedWave s (fun j => d j-t) (fun z => -v z) q k z-
      P.physicalSelectedWave s (fun _ => 0) (fun _ => 0) q k z := by
  have heq : |v z-t| ≤ d q.1 ↔ v z ≤ t+d q.1 ∧ -v z ≤ d q.1-t := by
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  unfold physicalCenteredWave physicalSelectedWave
  simp only [heq]
  by_cases hu : v z ≤ t+d q.1 <;> by_cases hl : -v z ≤ d q.1-t
  · simp [hu,hl]
  · simp [hu,hl]
  · simp [hu,hl]
  · exfalso
    linarith [hd q.1]

/-- Exact coefficient identity used for symmetric frozen selectors.
All three terms have monotone thresholds whenever the original d does. -/
theorem physicalCenteredCoefficient_eq (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (u : ι j) :
    P.physicalCenteredCoefficient s t d v g j u =
      P.physicalCoefficient s (fun j => t+d j) v g j u+
      P.physicalCoefficient s (fun j => d j-t) (fun z => -v z) g j u-
      P.physicalCoefficient s (fun _ => 0) (fun _ => 0) g j u := by
  ext k
  have hU := P.physical_analyzing_integrable s (fun j => t+d j) v hv g hg hg1 ⟨j,u⟩ k
  have hD := P.physical_analyzing_integrable s (fun j => d j-t) (fun z => -v z)
    hv.neg g hg hg1 ⟨j,u⟩ k
  have hT := P.physical_analyzing_integrable s (fun _ => 0) (fun _ => 0)
    measurable_const g hg hg1 ⟨j,u⟩ k
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*conj (P.physicalCenteredWave s t d v ⟨j,u⟩ k z) ∂volume.prod volume) = _
  simp_rw [P.physicalCenteredWave_eq s t d hd v,map_sub,map_add,mul_sub,mul_add]
  have hsub := integral_sub (hU.add hD) hT
  simp only [Pi.add_apply] at hsub
  rw [hsub,integral_add hU hD]
  change _ = ((↑(P.length j*P.width):ℂ)⁻¹)*_+
    ((↑(P.length j*P.width):ℂ)⁻¹)*_-((↑(P.length j*P.width):ℂ)⁻¹)*_
  ring

theorem centered_upper_monotone (t : ℝ) {d : Fin N → ℝ} (hd : Monotone d) :
    Monotone (fun j => t+d j) := by
  intro i j h
  dsimp only
  linarith [hd h]

theorem centered_lower_monotone (t : ℝ) {d : Fin N → ℝ} (hd : Monotone d) :
    Monotone (fun j => d j-t) := fun _ _ h => sub_le_sub_right (hd h) t

end LipschitzHilbert.SourceLatticePacket

end

end OAI
