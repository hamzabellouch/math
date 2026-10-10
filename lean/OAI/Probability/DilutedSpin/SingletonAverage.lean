import OAI.Probability.DilutedSpin.FullCubeConditionalContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

/-- The unnormalized regular-depth average of the actual physical singleton
covariance energy; L+1 is the physical height, not the number of RSB steps. -/
noncomputable def regularSingletonAverage (M : Model p) (C H : ℝ) (N : ℕ)
    (u : Spec L×ℕ → ℝ) (η : ℝ) : ℝ :=
  (∑ d ∈ regularSingletonDepths L η,
    physicalSingletonEnergy (gridExponents L) M C H N u d) / ((L+1:ℕ):ℝ)

lemma regularSingletonAverage_nonneg (M : Model p) (C H : ℝ) (N : ℕ)
    (u : Spec L×ℕ → ℝ) (η : ℝ) : 0 ≤ regularSingletonAverage M C H N u η := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun d _ => physicalSingletonEnergy_nonneg _ _ _ _ _ _ _)

lemma regularSingletonAverage_le (M : Model p) (C H : ℝ) (N : ℕ)
    (u : Spec L×ℕ → ℝ) (η B : ℝ) (hB : 0 ≤ B)
    (h : ∀ d ∈ regularSingletonDepths L η,
      physicalSingletonEnergy (gridExponents L) M C H N u d ≤ B) :
    regularSingletonAverage M C H N u η ≤ B := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos L))).mpr
  have hc : (regularSingletonDepths L η).card ≤ L+1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hs := Finset.sum_le_sum h
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hb := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hc) hB
  nlinarith

/-- The base case `V_(1,L)(eta) ≤ 1/(eta L)` is stated as its stronger
uniform eventual bound, without assuming existence of a covariance limit. -/
theorem singleton_average_selection (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
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
        regularSingletonAverage M C H (Ns n+1) (us n) η ≤ ((L+1:ℕ):ℝ)⁻¹/η+t) := by
  obtain ⟨Ns,us,hNs,hus,hinc,he⟩ := singleton_grid_selection M hC hH hθ hh hθi hhi hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  intro η hη t ht
  filter_upwards [he η hη t ht] with n hn
  exact regularSingletonAverage_le M C H (Ns n+1) (us n) η _ (by positivity) hn

/-- Full iterated convergence formulation for actual single-leaf covariance:
first reservoir size along the chosen physical sequence, then grid height.
No interaction positivity or factorization is needed for this base case. -/
theorem singleton_iterated_concentration (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε η ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀,
      ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
        (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
        (∀ n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns n) (us n) ≤
          liminf (pressure M) atTop+ε) ∧
        (∀ᶠ n in atTop, 0 ≤ regularSingletonAverage M C H (Ns n+1) (us n) η ∧
          regularSingletonAverage M C H (Ns n+1) (us n) η < ζ) := by
  obtain ⟨L₀,hL₀⟩ := exists_nat_gt (2/(η*ζ))
  refine ⟨L₀,?_⟩
  intro L hL
  have hD : (0:ℝ) < ((L+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos L)
  have hb : 2/(η*ζ) < ((L+1:ℕ):ℝ) :=
    hL₀.trans_le (Nat.cast_le.mpr (hL.trans (Nat.le_succ L)))
  have hb' : 2 < ((L+1:ℕ):ℝ)*(η*ζ) := (div_lt_iff₀ (mul_pos hη hζ)).mp hb
  have hrate : ((L+1:ℕ):ℝ)⁻¹/η < ζ/2 := by
    apply (div_lt_iff₀ hη).mpr
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hD).mpr
    nlinarith
  obtain ⟨Ns,us,hNs,hus,hinc,he⟩ := singleton_average_selection (L := L) M hC hH hθ hh hθi hhi hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  filter_upwards [he η hη (ζ/2) (half_pos hζ)] with n hn
  exact ⟨regularSingletonAverage_nonneg M C H (Ns n+1) (us n) η,by linarith⟩

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
