import OAI.Geometry.SurfaceImmersion.Correction.LocalPerturbedMean
import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeFamily
import OAI.Geometry.SurfaceImmersion.Atlas.ChartedUniformSeed
import OAI.Geometry.SurfaceImmersion.Geometry.UniformLocalQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedIncrementEstimate
import OAI.Geometry.SurfaceImmersion.Atlas.FastPhaseBounds

namespace OAI

/-! An actual supported increment for a polynomial perturbation of the metric.
All thresholds and derivative profiles precede the map and the slow scales. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_perturbed_local_step {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U D : Set Base} {Q : Set LowJet} (hU : IsOpen U) (hD : IsOpen D)
    (hDU : D ⊆ U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    (p : ι → ChartedMeanProfile P) {ρ R r r₀ : ℝ}
    (hρ : 0 < ρ) (hgap : r₀ < r) (q : ℕ)
    (B F M C : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m)
    (hM : ∀ m, 0 ≤ M m) (hC : ∀ m, 1 ≤ C m)
    (Cq Dq Jq Iq : QuadraticLabel ι → ℕ → ℝ)
    (hCq : ∀ l m, 0 ≤ Cq l m) (hJq : ∀ l m, 1 ≤ Jq l m)
    (hIq : ∀ l m, 1 ≤ Iq l m) :
    ∃ ν η₀ : ℝ, 0 < ν ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∃ S E : ℕ → ℝ, (∀ m, 0 ≤ S m) ∧ (∀ m, 0 ≤ E m) ∧
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ (reference H : SmallModes.Base → Tensor), ContDiff ℝ ∞ H →
      (∀ x, ‖H x - reference x‖ ≤ r₀) →
      (∀ m, WeightedBound univ s m (C m) H) →
      ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G)
        (φ : ι → Base → ℝ) (_hφ : ∀ i, ContDiff ℝ ∞ (φ i))
        (K : ι → Compacts Base) (ε τ δ : ℝ),
      0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ → δ / τ ≤ ν →
      τ / s + ε / τ ^ tensorLoss P ≤ η₀ →
      MapsTo (lowJet G) U Q →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      (∀ i m v, WeightedBound U s (m + tensorOrder P) (F m)
        (fun x => fderiv ℝ (φ i) x (coordinateVector v))) →
      (∀ i m v, ‖v‖ ≤ 1 → WeightedBound univ s m (M m)
        (SmallModes.coordDeriv v (coordinatePhase (φ i)))) →
      (∀ l, (quadraticCompacts K l : Set Base) ⊆ U) →
      ∀ (c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s)
        (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      (∀ i, (p i).Fits (d i)) →
      (∀ A, ContDiff ℝ ∞ A → InTrialBall univ reference r A →
        ∀ x ∈ planeCoordinateIsometry.symm ⁻¹' D, chartedFamilyLeading d hρ A x = A x) →
      ∀ (cq : ∀ l, PolynomialSolveData P ε G hG (quadraticFamilyPhase φ l)
        (quadraticCompacts K l) τ s),
      (∀ l, (cq l).C = Cq l) → (∀ l, (cq l).D = Dq l) → (∀ l, (cq l).J = Jq l) →
      (∀ l m j, 1 ≤ j → j ≤ m → ∀ x ∈ (cq l).e.target,
        ‖iteratedFDerivWithin ℝ j (cq l).e.symm (cq l).e.target x‖ ≤ Iq l m) →
      ∃ W : RField 4, ContDiff ℝ ∞ W ∧
        tsupport W ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) ∧
        (∀ m, WeightedBound univ τ m (S m * δ * τ) W) ∧
        (∀ m, WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
          (E m * (δ * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) + δ ^ 3 / τ))
          (coordinateMetricMap P ε (fun x => G x + W (planeCoordinateIsometry x)) -
            coordinateMetricMap P ε G - δ ^ 2 • H)) := by
  classical
  obtain ⟨β,κ,η₀,hη₀,hη₁,hm⟩ := uniform_perturbed_mean_on (hD.preimage planeCoordinateIsometry.symm.continuous)
    (R := R) p hρ hgap q q hC
  let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
  let T : ℕ → ℝ := fun m => max 1 (sizeBound L C β q (PolynomialSolveData.inputOrder (P := P) q m))
  have hT (m : ℕ) : 0 ≤ T m := zero_le_one.trans (le_max_left _ _)
  choose Xb Xe hXb hXe hx using fun m => uniform_charted_free_family_all_inputs
    (R := R) p hρ q m (T m)
  choose Ab hAb ha using fun i m => uniform_charted_seed_bound (R := R) (p i) hρ q m (T m)
  let A : ℕ → ℝ := fun m => 1 + ∑ i, Ab i (m + tensorOrder P + 1)
  have hA (m : ℕ) : 0 < A m := by
    dsimp [A]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun i _ => zero_le_one.trans (hAb i _))
  obtain ⟨Yb,Ye,hYb,hYe,hy⟩ := uniform_local_quadratic_cancellation hU isOpen_univ hQ
    (subset_univ _) P hP B F M A hB hF hM hA Cq Dq Jq Iq hCq hJq hIq q
  let Zb : ℕ → ℝ := fun m => 1 + Yb m
  have hZb (m : ℕ) : 0 < Zb m := add_pos_of_pos_of_nonneg zero_lt_one (hYb m)
  obtain ⟨ν₀,Q',hν₀,hQ',hQQ',_,hsegment⟩ :=
    free_forced_segment_margin hQ isOpen_univ (subset_univ _)
  let ν := ν₀ / (Xb 2 + Zb 2)
  have hν : 0 < ν := div_pos hν₀ (add_pos (lt_of_lt_of_le zero_lt_one (hXb 2)) (hZb 2))
  let j : ℕ → ℕ := fun m => m + tensorOrder P + 2
  choose N hN hd using fun m => perturbed_increment_estimate (ι := ι) hD hQ' P hP m
    (B m + Xb (j m) + Zb (j m)) (Xb (j m)) (Zb (j m))
    (by have := hXb (j m); have := hZb (j m); have := hB m; linarith)
    (lt_of_lt_of_le zero_lt_one (hXb (j m))) (hZb (j m))
  let E : ℕ → ℝ := fun m => Xe m + Ye m + |differenceBound L C β κ q m| + N m
  refine ⟨ν,η₀,hν,hη₀,hη₁,(fun m => Xb m + Zb m),E,?_,?_,?_⟩
  · intro m
    exact add_nonneg (zero_le_one.trans (hXb m)) (hZb m).le
  · intro m
    dsimp [E]
    exact add_nonneg (add_nonneg (add_nonneg (zero_le_one.trans (hXe m)) (hYe m))
      (abs_nonneg _)) (hN m)
  · intro s hs hs1 reference H hH hH0 hbH G hG φ hφ K ε τ δ hτ hτs hε hε1
      hδ hδτ hδν hsmall hGQ hGb hφb hφm hKU c d hfit hdecomp cq hcq hdq hjq hiq
    have hτ1 : τ ≤ 1 := hτs.trans hs1
    have hηsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1 := hsmall.trans hη₁
    have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
      add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
    obtain ⟨a,haS,haBall,haBound,haMean⟩ :=
      hm s hs hs1 reference H hH hH0 hbH d hfit hτ hτs hε hε1 hsmall hdecomp δ hδ q le_rfl
    have haT (m : ℕ) : WeightedBound univ s (PolynomialSolveData.inputOrder (P := P) q m)
        (T m) a := (haBound _).mono_const (le_max_right _ _)
    let X := chartedFreeSum d hρ δ q a
    have hXS : ContDiff ℝ ∞ X := (chartedFreeSum_smooth_support d hρ δ q a).1
    have hXsp := (chartedFreeSum_smooth_support d hρ δ q a).2
    have hx' (m : ℕ) := hx m d hfit hτ hs hτs hs1 hε hηsmall δ hδ.le a (hT m) haS haBall (haT m)
    have hAb (i : ι) (m : ℕ) : WeightedBound univ s (m + tensorOrder P + 1)
        (A m * (δ * τ)) ((d i).freeAmplitude hρ δ q a) := by
      have hh := ha i (m + tensorOrder P + 1) (d i) (hfit i) hτ hs hτs hs1 hε hηsmall
        δ hδ.le a (hT _) haS haBall (haT _)
      apply hh.mono_const
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hδ.le hτ.le)
      exact (Finset.single_le_sum (fun i _ => zero_le_one.trans (hAb i _))
        (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
    obtain ⟨Y,hYS,hYsp,hYsize,hYres⟩ := hy hG φ hφ K
      (fun i => (d i).freeAmplitude hρ δ q a) s δ τ ε hδ hτ hs hτs hs1 hε hε1 hηsmall
      hGQ hGb hAb hφb hφm hKU cq hcq hdq hjq hiq
    have hYbound (m : ℕ) : WeightedBound univ τ m (Zb m * δ ^ 2) Y := by
      apply (hYsize m).mono_const
      calc
        δ ^ 2 * Yb m = Yb m * δ ^ 2 := mul_comm _ _
        _ ≤ Zb m * δ ^ 2 := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) (sq_nonneg δ)
    have hXbound (m : ℕ) : WeightedBound univ τ m (Xb m * δ * τ) X := by
      simpa only [mul_assoc] using (hx' m).1
    have hseg := hsegment hU hG hXS hYS hGQ hτ hτ1 hδ.le hδτ
      (zero_le_one.trans (hXb 2)) (hZb 2).le
      ((mul_le_mul_of_nonneg_left hδν (add_nonneg (zero_le_one.trans (hXb 2)) (hZb 2).le)).trans
        (by dsimp [ν]; rw [mul_div_cancel₀ _ (ne_of_gt (add_pos
          (lt_of_lt_of_le zero_lt_one (hXb 2)) (hZb 2))) ]))
      (hXbound 2) (hYbound 2)
    refine ⟨X+Y,hXS.add hYS,(tsupport_add X Y).trans (union_subset hXsp hYsp),?_,?_⟩
    · intro m
      exact free_forced_size hXS hYS hτ hδ.le hδτ (hZb m).le (hXbound m) (hYbound m)
    · intro m
      have hGτ := ((hGb m).shrink_scale hτ.le hτs).restrict_open_domain hU hD hDU
      have hsegB := free_forced_lowJet_bounds hD hG hXS hYS hτ hτ1 hδ.le hδτ
        (zero_le_one.trans (hXb (j m))) (hZb (j m)).le hGτ (hXbound (j m)) (hYbound (j m))
      have hGτ' : WeightedBound D τ (m + tensorOrder P)
          (B m + Xb (j m) + Zb (j m)) (lowJet G) :=
        hGτ.mono_const (by have := hXb (j m); have := hZb (j m); linarith)
      have hlin := ((hx' m).2).restrict_open (hD.preimage planeCoordinateIsometry.symm.continuous)
      have hforced := (hYres m).restrict_open (hD.preimage planeCoordinateIsometry.symm.continuous)
      have hmean := haMean m
      have hmean' : WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
          (|differenceBound L C β κ q m| * δ ^ 2 *
            (τ / s + ε / τ ^ tensorLoss P) ^ (q+1))
          (combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q a) τ 0 - δ ^ 2 • H) := by
        apply (hmean.shrink_scale hτ.le hτs).mono_const
        calc
          _ = differenceBound L C β κ q m * δ ^ 2 *
              (τ / s + ε / τ ^ tensorLoss P) ^ (q+1) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg δ)) (pow_nonneg hη _)
      have hforced' : WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
          (Ye m * δ^2 * (τ / s + ε / τ ^ tensorLoss P) ^ (q+1))
          (coordinateFullLinearized P ε G Y +
            combinedNonzeroQuadratic P ε G φ (fun i => (d i).freeAmplitude hρ δ q a) τ) := by
        convert hforced using 1
        ring
      have hscaledH : ContDiff ℝ ∞ (δ ^ 2 • H) := by
        change ContDiff ℝ ∞ (fun x => (δ ^ 2 : ℝ) • H x)
        exact hH.const_smul (δ ^ 2 : ℝ)
      exact hd m G φ (fun i => (d i).freeAmplitude hρ δ q a) Y (δ^2 • H)
        hG hφ (fun i => ((d i).freeAmplitude hρ δ q a).contDiff) hYS
        hscaledH
        τ ε δ (τ / s + ε / τ ^ tensorLoss P) (Xe m) (Ye m)
        |differenceBound L C β κ q m| q hτ hτ1 hε hε1 hδ hδτ hη
        (zero_le_one.trans (hXe m)) (hYe m) (abs_nonneg _)
        ((le_add_of_nonneg_left (div_nonneg hτ.le hs.le)).trans hηsmall)
        (fun _ hx => hQQ' (hGQ (hDU hx))) hGτ'
        (fun t ht x hx => hseg t ht (hDU hx)) hsegB
        ((hXbound (j m)).mono_order (by dsimp [j]; omega))
        ((hYbound (j m)).mono_order (by dsimp [j]; omega)) hlin hforced' hmean'

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
