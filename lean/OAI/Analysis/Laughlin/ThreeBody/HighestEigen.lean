import OAI.Analysis.Laughlin.Spin.WeightSlice
import OAI.Analysis.Laughlin.ThreeBody.HighestReadout
import OAI.Analysis.Laughlin.ThreeBody.SpinCovariance

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def coupledHighest (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) : PairOrbitalIndex Q → ℝ :=
  extendWeightSlice (2*Q-2) Q z (by omega) hz (fun p => highestUnit (2*Q-2) Q z p.val)

theorem threeGram_on_slice (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (p q : Fin (z+1)) :
    threeGram Q (weightSliceIndex (2*Q-2) Q z (by omega) hz p)
      (weightSliceIndex (2*Q-2) Q z (by omega) hz q) = Fock.threeBodyGramSlice Q z hz p q := by
  apply Complex.ofReal_injective
  rw [threeGram_physical Q hQ,Fock.threeBodyGramSlice_physical Q z hQ hz]
  rfl

theorem threeGram_extend_off (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (f : Fin (z+1) → ℝ) (i : PairOrbitalIndex Q) (hi : i.1.val+i.2.val ≠ z) :
    (threeGram Q *ᵥ extendWeightSlice (2*Q-2) Q z (by omega) hz f) i = 0 := by
  change (∑ j, threeGram Q i j * extendWeightSlice (2*Q-2) Q z (by omega) hz f j) = 0
  rw [sum_extendWeightSlice]
  apply Finset.sum_eq_zero
  intro p hp
  rw [threeGram_weight]
  · ring
  · dsimp [weightSliceIndex]
    omega

theorem threeGram_highest_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeGram Q *ᵥ coupledHighest Q z hQ hz =
      (1+gramEigenvalueFormula Q z) • coupledHighest Q z hQ hz := by
  let v := coupledHighest Q z hQ hz
  let g := threeGram Q *ᵥ v
  let f : Fin (z+1) → ℝ := fun p => g (weightSliceIndex (2*Q-2) Q z (by omega) hz p)
  have hv : totalRaise (2*Q-2) Q *ᵥ v = 0 := by
    apply extendWeightSlice_highest
    intro p
    exact highestUnit_raising (2*Q-2) Q z p.val (by omega) hz p.isLt
  have hg : totalRaise (2*Q-2) Q *ᵥ g = 0 := by
    dsimp [g]
    rw [Matrix.mulVec_mulVec,← threeGram_raising Q (by omega),← Matrix.mulVec_mulVec,hv,
      Matrix.mulVec_zero]
  have hf : ∀ p, raiseSlice (2*Q-2) Q z f p = 0 := by
    intro p
    have he := congrFun hg ((⟨p.val,by omega⟩,⟨z-p.val-1,by omega⟩) : PairOrbitalIndex Q)
    rw [totalRaise_below_slice (2*Q-2) Q z (by omega) hz] at he
    exact he
  obtain ⟨c,hc⟩ := (raiseSlice_kernel (2*Q-2) Q z (by omega) hz f).mp hf
  have hfirst : f ⟨0,by omega⟩ =
      (1+gramEigenvalueFormula Q z)*highestUnit (2*Q-2) Q z 0 := by
    dsimp [f,g,v,coupledHighest]
    change (∑ j,threeGram Q _ j*extendWeightSlice (2*Q-2) Q z (by omega) hz _ j) = _
    rw [sum_extendWeightSlice]
    simp_rw [threeGram_on_slice Q z hQ hz]
    exact Fock.threeBodyGram_highest_first_coordinate Q z hQ hz
  have hcz : c = 1+gramEigenvalueFormula Q z := by
    apply (mul_right_cancel₀ (highestUnit_ne_zero (2*Q-2) Q z 0 (by omega) hz (by omega)))
    exact (hc ⟨0,by omega⟩).symm.trans hfirst
  funext i
  change g i = (1+gramEigenvalueFormula Q z)*v i
  by_cases hi : i.1.val+i.2.val=z
  · let p : Fin (z+1) := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex (2*Q-2) Q z (by omega) hz p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    rw [he]
    change f p = (1+gramEigenvalueFormula Q z)*extendWeightSlice (2*Q-2) Q z (by omega) hz _ _
    rw [extendWeightSlice_at,hc p,hcz]
  · have hg₀ : g i = 0 := threeGram_extend_off Q z hQ hz _ i hi
    have hv₀ : v i = 0 := extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i hi
    rw [hg₀,hv₀,mul_zero]

theorem coupledHighest_norm (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (∑ i : PairOrbitalIndex Q, (coupledHighest Q z hQ hz i)^2) = 1 := by
  simp only [pow_two]
  unfold coupledHighest
  rw [sum_extendWeightSlice]
  simp_rw [extendWeightSlice_at,← pow_two]
  have hs := highestUnit_norm (2*Q-2) Q z (by omega) hz
  simpa only [← Fin.sum_univ_eq_sum_range] using hs

end Laughlin.Spin

end OAI
