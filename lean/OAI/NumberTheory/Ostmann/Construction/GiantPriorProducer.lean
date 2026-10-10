import OAI.NumberTheory.Ostmann.Construction.GiantCellPriorIdentity
import OAI.NumberTheory.Ostmann.Construction.GiantCellSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

theorem exists_positive_giant_prior (d : Decomposition) {δ : ℝ} (hδ : 0<δ)
    (r : ℝ) (hr : 4≤r) :
    ∀ᶠ L : ℝ in atTop,
      (3/20:ℝ)*L≤(∑p∈Supply.nonsparsePrimes d δ L,(1:ℝ)/p) →
      ∃ G : ℝ, ∃ c : ℤ, ∃ P : Finset ℕ, ∃ hZ : 0<logCellMass c ∅,
        P⊆Supply.nonsparsePrimes d δ L ∧
        Real.exp ((1/20:ℝ)*L)≤G ∧ G+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
        G-2<(c:ℝ) ∧ (c:ℝ)<G+favorableBlockWidth L+2 ∧
        (∀p∈P,G≤Real.log p ∧ Real.log p<G+favorableBlockWidth L) ∧
        (δ/(320*Real.sqrt 2))<
          (logCellPrior c ∅ hZ).mean (fun p => if (p:ℕ)∈P then
            giantEmpiricalMean d (giantWindowScale r G L) p else 0) := by
  classical
  filter_upwards [exists_positive_giant_cell d hδ r hr] with L hL
  intro hmass
  obtain ⟨G,c,P,hP,hGlo,hGhi,hclo,hchi,hwin,hZ,hmean⟩ := hL hmass
  refine ⟨G,c,P,hZ,hP,hGlo,hGhi,hclo,hchi,hwin,?_⟩
  rw [giant_cell_prior_mean d (giantWindowScale r G L) c hZ P
    (fun p hp => (Finset.mem_filter.mp (hP hp)).2.1)]
  exact hmean

end Ostmann.Construction

end

end OAI
