import OAI.Probability.DilutedSpin.JointPhysicalSelection

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

/-- A single grid reservoir sequence, with its regular singleton base case
and EVERY actual centered multileaf history simultaneously. -/
theorem joint_grid_selection (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ η : ℝ, 0 < η → ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
        ∀ d ∈ regularSingletonDepths L η,
          physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d ≤
            ((L+1:ℕ):ℝ)⁻¹/η+t) ∧
      (∀ (S : PrescribedTree (L+1)) (a : S.Leaf) (k : ℕ), 0 < k →
        ∀ (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf),
          Tendsto (fun n => physicalTreeMatrixCovariance (gridExponents L) S a M C H
            (Ns n+1) (us n) T q) atTop (𝓝 0)) := by
  have hδ : 0 < ((L+1:ℕ):ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))
  obtain ⟨Ns,us,hNs,hus,hinc,henergy,hmatrix⟩ := joint_energy_matrix_selection (gridExponents L) M hC hH hδ
    hθ hh hθi hhi (gridExponents_lower L) (gridExponents_mono L) (gridExponents_last L) hε
  refine ⟨Ns,us,hNs,hus,hinc,?_,hmatrix⟩
  intro η hη t ht
  apply (Filter.eventually_all_finset _).mpr
  intro d hd
  have hreg := (Finset.mem_filter.mp hd).2.1
  have hs := henergy d d.isLt (η*t) (mul_pos hη ht)
  filter_upwards [hs] with n hn
  rw [gridExponents_cons] at hn
  have hcoef : η ≤ 2*grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩ := by
    simp only [grid,Nat.zero_add,Nat.cast_add,Nat.cast_one,add_div]
    have hx : 0 ≤ (1:ℝ)/((L+1:ℕ):ℝ) := by simpa only [one_div] using hδ.le
    change η < (d.val:ℝ)/((L+1:ℕ):ℝ) at hreg
    simp only [Nat.cast_add,Nat.cast_one] at hreg hx
    linarith
  have hstep : grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩ = ((L+1:ℕ):ℝ)⁻¹ := by
    simp [grid,Nat.cast_add,add_div]
  rw [hstep] at hn
  have hen := physicalSingletonEnergy_nonneg (gridExponents L) M C H (Ns n+1) (us n) d
  have hh := mul_le_mul_of_nonneg_right hcoef hen
  have hx : η * physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d ≤
      ((L+1:ℕ):ℝ)⁻¹+η*t := hh.trans hn
  calc
    _ ≤ (((L+1:ℕ):ℝ)⁻¹+η*t)/η := (le_div_iff₀ hη).mpr (by nlinarith [hx])
    _ = _ := by rw [add_div,mul_div_cancel_left₀ t (ne_of_gt hη)]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
