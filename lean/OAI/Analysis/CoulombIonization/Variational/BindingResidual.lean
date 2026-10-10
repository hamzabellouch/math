import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.LipschitzResidualBase
import OAI.Analysis.CoulombIonization.Variational.WeightedMass

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  bindingTotalMultiplier graphNuclear sectorExcessOperator
  weightedMass weightedPairs weightedNuclear weightedCoreDensity

lemma energy_weighted_core_price_le {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hstep : energy Z (N+1)+lam ≤ energy Z N)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (i : Fin (N+1)) :
    (energy Z (N+1)+lam)*weightedMass F (fun x => bindingWeight R ε (x i)) ≤
      weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) := by
  have hm := weightedMass_nonneg F (fun x => (bindingWeight_pos hR hε (x i)).le)
  have hb (y : Space) : ‖bindingWeight R ε y‖ ≤ R := by
    rw [Real.norm_of_nonneg (bindingWeight_pos hR hε y).le]
    exact bindingWeight_le hR hε y
  have hi := weighted_core_coordinate F hZ i (bindingWeight R ε)
    (bindingWeight_continuous hR hε) (fun y => (bindingWeight_pos hR hε y).le) hb
  apply (mul_le_mul_of_nonneg_right hstep hm).trans
  simpa only [weightedMass,weightedCoreDensity] using hi

lemma binding_residual_cancellation {ι : Type*} [Fintype ι]
    (C V P M : ι → ℝ) (E lam Z A Mt r : ℝ)
    (hC : ∀ i, (E+lam)*M i ≤ C i) (hM : Mt=∑ i,M i)
    (hA : r=A-E*Mt) (hL : (∑ i,(C i-Z*V i+P i)) ≤ A) :
    (∑ i,P i)+lam*Mt ≤ Z*(∑ i,V i)+r := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hC i
  rw [← Finset.mul_sum,← hM] at hs
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hL
  nlinarith

lemma quantum_binding_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hstep : energy Z (N+1)+lam ≤ energy Z N)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    (∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
      lam*weightedMass F (bindingTotalMultiplier hR hε).value ≤
    Z*(∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i)))+
      (⟪(bindingTotalMultiplier hR hε).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have he := sectorExcessOperator_pair Z ((bindingTotalMultiplier hR hε).apply F) F
  have hp := FermionMultiplier.value_weighted_pairing F (bindingTotalMultiplier hR hε)
  have he' := he.trans (congrArg (fun t : ℝ =>
    (⟪(bindingTotalMultiplier hR hε).apply F,coulombFormOperator Z (N+1) F⟫_ℂ).re-
      energy Z (N+1)*t) hp)
  exact binding_residual_cancellation _ _ _ _ _ _ _ _ _ _
    (fun i => energy_weighted_core_price_le hZ F hstep hR hε i)
    (bindingTotal_mass hR hε F) he' (binding_form_lower hR hε Z F)

end CoulombAtom

end

end OAI
