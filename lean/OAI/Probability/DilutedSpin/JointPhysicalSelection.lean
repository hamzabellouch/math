import OAI.Probability.DilutedSpin.FullCubeConditionalContinuity
import OAI.Probability.DilutedSpin.PhysicalTreeMatrix

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

/-- ONE low-increment sequence simultaneously controls the singleton base
case AND every actual multileaf centered matrix history. This avoids separately
selected sequences at the base and inductive stages. -/
theorem joint_energy_matrix_selection (m : Fin (L+1) → ℝ)
    (M : Model p) {C H c : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, c ≤ m l) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior m direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ (d : ℕ) (hd : d < L+1) (t : ℝ), 0 < t → ∀ᶠ n in atTop,
        (2*(Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-
          (Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d,by omega⟩) *
          physicalSingletonEnergy m M C H (Ns n+1) (us n) d ≤
        ((Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-
          (Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d,by omega⟩)+t) ∧
      (∀ (S : PrescribedTree (L+1)) (a : S.Leaf) (k : ℕ), 0 < k →
        ∀ (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf),
          Tendsto (fun n => physicalTreeMatrixCovariance m S a M C H (Ns n+1) (us n) T q)
            atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hus,hinc,hshape⟩ := complete_shape_selection m M hC hH hc
    hθ hh hθi hhi hm hmono hend hε
  refine ⟨Ns,us,hNs,hus,hinc,?_,?_⟩
  · intro d hd t ht
    have hlim := hshape (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0)
      (fun n => singletonOldTest d hd (Ns n+1)) 1 (by norm_num)
      (fun n x => singletonOldTest_bound d hd (Ns n+1) x) 1 (pairSplitTest d) true
    have hsmall : ∀ᶠ n in atTop, physicalShapeCovariance m (forkAt (L+1) d hd)
        (forkAtLeaf (L+1) d hd 0) M C H (Ns n+1) (us n) (pairSplitTest d) true
        (singletonOldTest d hd (Ns n+1)) < t := (tendsto_order.1 hlim).2 t ht
    filter_upwards [hsmall] with n hn
    exact (physical_singleton_bound m (fun j => hc.le.trans (hm j)) hmono hend M C H
      (Ns n+1) (us n) d hd).trans (add_le_add le_rfl hn.le)
  · intro S a k hk T q
    let F := fun n => spatialProduct (fun _ : S.Leaf =>
      readVector (fun v x => readSpin (KernelTower.terminalState L x) v)
        (N := Ns n+1))
    have hF : ∀ n x, |F n x| ≤ 1 := fun n x => spatialProduct_bound _
      (fun _ y i => readVector_bound _ y i) x
    have h := hshape S a F 1 (by norm_num) hF k (matrixSplitTest T q) true
    have he (n : ℕ) :
        physicalShapeCovariance m S a M C H (Ns n+1) (us n) (matrixSplitTest T q) true (F n) =
          physicalTreeMatrixCovariance m S a M C H (Ns n+1) (us n) T q := by
      rw [physicalShape_matrix hk m (fun j => hc.trans_le (hm j)) hmono hend
        S a M C H _ _ T q _ (by norm_num : (0:ℝ)≤1) (hF n)]
      exact (physicalTreeMatrixCovariance_eq m S a M C H _ _ T q).symm
    simpa only [he] using h

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
