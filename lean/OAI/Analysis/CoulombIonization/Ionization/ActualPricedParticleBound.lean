import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.BindingSums
import OAI.Analysis.CoulombIonization.Variational.BindingResidual

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

theorem quantum_positive_price_binding_bound {Z lam : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N : ℕ}
    (hstep : energy Z (N+1)+lam ≤ energy Z N) : (N:ℝ) ≤ 2*Z := by
  let R : ℝ := ((N:ℝ)+1)/lam
  have hR : 0 < R := div_pos (by positivity) hlam
  have hRl : R*lam = (N:ℝ)+1 := div_mul_cancel₀ _ hlam.ne'
  have htail : 2*(N:ℝ)/R ≤ 2*lam := by
    apply (div_le_iff₀ hR).mpr
    nlinarith only [hRl]
  let K : ℝ := 4*(|energy Z (N+1)|+((N+1:ℕ):ℝ)*Z^2+2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hεlim (ε : ℝ) (hε : 0 < ε) :
      ((N:ℝ)+1)*(N:ℝ) ≤ 2*Z*(((N:ℝ)+1)+ε*((N:ℝ)+2)*K) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨F,hn,hFK,hr⟩ := quantum_approximate_multiplier hZ (N+1)
      (bindingTotalMultiplier hR hε) (half_pos hδ)
    change ‖F‖^2 ≤ K at hFK
    have hp := binding_pair_sum_bound hR hε F
    have hv := binding_nuclear_sum_bound hR hε F
    have hb := quantum_binding_residual hZ F hstep hR hε
    have hm : 0 ≤ weightedMass F (bindingTotalMultiplier hR hε).value := by
      apply weightedMass_nonneg
      intro x
      rw [bindingTotalMultiplier_value]
      exact Finset.sum_nonneg fun i _ => (bindingWeight_pos hR hε (x i)).le
    have ht := mul_le_mul_of_nonneg_right htail hm
    have hkn := mul_le_mul_of_nonneg_left hFK
      (show 0 ≤ ε*((N:ℝ)+2) by positivity)
    simp only [hn,mul_one,Nat.cast_add,Nat.cast_one] at hp hv
    have hv' : (∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i))) ≤
        ((N:ℝ)+1)+ε*((N:ℝ)+2)*K := by nlinarith only [hv,hkn]
    have hzv := mul_le_mul_of_nonneg_left hv' hZ
    nlinarith only [hp,ht,hb,hr,hzv]
  have hfinal : ((N:ℝ)+1)*(N:ℝ) ≤ 2*Z*((N:ℝ)+1) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let C : ℝ := 2*Z*((N:ℝ)+2)*K
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let ε : ℝ := δ/(C+1)
    have hε : 0 < ε := div_pos hδ (by linarith)
    have he : ε*(C+1)=δ := div_mul_cancel₀ _ (by linarith : C+1 ≠ 0)
    have hh := hεlim ε hε
    have hCe : C*ε ≤ δ := by nlinarith only [he,hε]
    dsimp only [C] at hCe
    nlinarith only [hh,hCe]
  have hnpos : 0 < (N:ℝ)+1 := by positivity
  nlinarith only [hfinal,hnpos]

theorem actual_priced_particle_bound {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) : (N:ℝ) ≤ 2*Z+1 := by
  cases N with
  | zero => simp only [Nat.cast_zero]; positivity
  | succ n =>
    have hs := hN n
    simp only [Nat.cast_add,Nat.cast_one] at hs ⊢
    have hstep : energy Z (n+1)+lam ≤ energy Z n := by nlinarith only [hs]
    have hh := quantum_positive_price_binding_bound hZ hlam hstep
    linarith only [hh]

end CoulombAtom

end

end OAI
