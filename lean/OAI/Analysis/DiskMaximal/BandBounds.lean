import OAI.Analysis.DiskMaximal.SpatialBudgets

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ActualLabels
open DyadicHats PhysicalCells CommonPrices ActualMarkTrees Finset FiniteLabels

def spatialPriceConstant : ℝ := 1681*packingConstant+costLimit*priceConstant
lemma spatialPriceConstant_pos : 0 < spatialPriceConstant := by
  unfold spatialPriceConstant
  have := packingConstant_pos
  have := costLimit_pos
  have := priceConstant_nonneg
  positivity

def directPriceConstant : ℝ := 1000000*1681*(576*(4097:ℝ)^2)+priceConstant
lemma directPriceConstant_pos : 0 < directPriceConstant := by
  unfold directPriceConstant
  have := priceConstant_nonneg
  positivity

lemma pointCost_total_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        (rootMass h base j (cellRoots N p)+cellPrice N base h j (cellRoots N p))) ≤
      spatialPriceConstant*(∫ y, ‖h y‖) := by
  simp only [mul_add,sum_add_distrib]
  have h1 := pointCost_mass_budget hb hR hN hh hsupp m P
  have h2 := pointCost_price_budget hb hR hN hh hsupp m P
  unfold spatialPriceConstant
  nlinarith only [h1,h2]

lemma marginal_total_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        (badPrice h base j (cellRoots N p) n+cellPrice N base h j (cellRoots N p))) ≤
      directPriceConstant*(∫ y, ‖h y‖) := by
  simp only [mul_add,sum_add_distrib]
  have h1 := marginal_bad_budget hb hR hN hh hsupp m P n
  have h2 := marginal_price_budget hb hR hN hh hsupp m P n
  unfold directPriceConstant
  nlinarith only [h1,h2]
end ActualLabels

namespace CommonPrices
open DyadicHats Finset
lemma cellPrice_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellPrice N base h j (cellRoots N p)) ≤ priceConstant*(∫ y, ‖h y‖) := by
  have hi := single_le_sum (s := range (j+1))
    (f := fun k => ∑ p ∈ P, cellPrice N base h k (cellRoots N p))
    (fun k _ => sum_nonneg (fun p _ => cellPrice_nonneg hb hR hN hh hsupp k _))
    (by simp : j ∈ range (j+1))
  exact hi.trans (cellPrice_budget hb hR hN hh hsupp j (fun _ => P))

lemma total_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, (rootMass h base j (cellRoots N p)+cellPrice N base h j (cellRoots N p))) ≤
      (1681+priceConstant)*(∫ y, ‖h y‖) := by
  rw [sum_add_distrib,add_mul]
  exact add_le_add (rootMass_cell_budget hh base j P) (cellPrice_level_budget hb hR hN hh hsupp j P)
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells FiniteLabels Finset
lemma gradient_measurable (f : ℂ → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma marginal_continuous (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) (n : Label) :
    Continuous (fun x => marginal h r k x n) := by
  induction k generalizing n with
  | zero => exact (observation_lipschitz h r 0 (hr 0) n n).continuous
  | succ k ih =>
    change Continuous (fun x => ∑ j : Label, marginal h r k x j*row h (r (k+1)) x j n)
    apply continuous_finsetSum
    intro j _
    exact (ih j).mul (observation_lipschitz h r (k+1) (hr (k+1)) j n).continuous

lemma rate_continuous (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (n : Label) :
    Continuous (fun x => rate h r x n) := by
  exact (interpolate_lipschitz hr (by norm_num : (0:ℝ) ≤ 1) (fun p => by
    rw [abs_of_nonneg (switchChance_nonneg h r n p)]
    exact switchChance_le_one h r n p)).continuous

lemma switchCost_continuous (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) :
    Continuous (fun x => switchCost h r x k) := by
  cases k with
  | zero => exact continuous_const
  | succ k =>
    change Continuous (fun x => ∑ j : Label, marginal h r k x j*rate h (r (k+1)) x j)
    exact continuous_finsetSum _ (fun j _ => (marginal_continuous h r hr k j).mul (rate_continuous h (hr (k+1)) j))

lemma derivativeCost_measurable (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) :
    Measurable (fun x => derivativeCost h r x k) := by
  cases k with
  | zero =>
    change Measurable (fun x => r 0*∑ j : Label, ‖gradient (fun y => initial h (r 0) y j) x‖)
    exact measurable_const.mul (Finset.measurable_fun_sum _ (fun j _ => (gradient_measurable _).norm))
  | succ k =>
    change Measurable (fun x => ∑ n : Label, marginal h r k x n*(r (k+1)*
      ∑ j : Label, ‖gradient (fun y => row h (r (k+1)) y n j) x‖))
    apply Finset.measurable_fun_sum
    intro n _
    exact (marginal_continuous h r hr k n).measurable.mul
      (measurable_const.mul (Finset.measurable_fun_sum _ (fun j _ => (gradient_measurable _).norm)))

lemma filt_measurable {f : ℂ → ℕ → ℝ} (hf : ∀ i, Measurable (fun x => f x i)) (k : ℕ) :
    Measurable (fun x => filt (f x) k) := by
  induction k with
  | zero => exact hf 0
  | succ k ih => exact (hf (k+1)).add (ih.div_const 2)

lemma pointCost_measurable (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (m k : ℕ) :
    Measurable (fun x => pointCost h r x m k) := by
  unfold pointCost boundaryCost
  apply Measurable.add
  · apply Measurable.add (switchCost_continuous h r hr k).measurable
    split_ifs
    · exact measurable_const
    · exact (switchCost_continuous h r hr (k+1)).measurable
  · exact filt_measurable (derivativeCost_measurable h r hr) k
end ActualLabels

namespace PhysicalCells
open Finset
lemma sum_tsum_ofReal_le {ι κ : Type*} (s : Finset ι) (B : ι → κ → ℝ)
    (hB : ∀ i ∈ s, ∀ p, 0 ≤ B i p) (A : ℝ)
    (hbudget : ∀ P : Finset κ, ∑ i ∈ s, ∑ p ∈ P, B i p ≤ A) :
    (∑ i ∈ s, ∑' p, ENNReal.ofReal (B i p)) ≤ ENNReal.ofReal A := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hB i hi _)]
  apply tsum_ofReal_le _ (fun p => sum_nonneg (fun i hi => hB i hi p))
  intro P
  rw [Finset.sum_comm]
  exact hbudget P

lemma integrated_weighted_patches {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (F : ι → (ℤ × ℤ) → ℂ → ℝ≥0∞)
    (hF : ∀ i ∈ s, ∀ p, Measurable (F i p))
    (W : ι → ℂ → ℝ≥0∞) (hW : ∀ i ∈ s, Measurable (W i))
    (A B : ι → (ℤ × ℤ) → ℝ) (hA : ∀ i ∈ s, ∀ p, 0 ≤ A i p)
    (hB : ∀ i ∈ s, ∀ p, 0 ≤ B i p)
    (hcell : ∀ i ∈ s, ∀ p, (∫⁻ x in cell (DyadicHats.point (r i) p) (r i), F i p x) ≤ ENNReal.ofReal (B i p))
    (hWB : ∀ i ∈ s, ∀ p x, x ∈ cell (DyadicHats.point (r i) p) (r i) → W i x ≤ ENNReal.ofReal (A i p))
    (C : ℝ) (hbudget : ∀ P : Finset (ℤ × ℤ), ∑ i ∈ s, ∑ p ∈ P, A i p*B i p ≤ C) :
    (∑ i ∈ s, ∫⁻ x, W i x*patch (r i) (F i) x) ≤ ENNReal.ofReal C := by
  apply le_trans (sum_le_sum (fun i hi => weighted_patch_bound (r i) (F i) (hF i hi)
    (W i) (hW i hi) (A i) (B i) (hA i hi) (hB i hi) (hcell i hi) (hWB i hi)))
  exact sum_tsum_ofReal_le s _ (fun i hi p => mul_nonneg (hA i hi p) (hB i hi p)) C hbudget
end PhysicalCells

namespace GeometricFilter
open Finset
lemma radius_convolution {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (c J : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range m, c k/r k*(∑ l ∈ Ico k m, r l*J l)) =
      ∑ l ∈ range m, filt c l*J l := by
  simp only [mul_sum]
  rw [← Nat.Ico_zero_eq_range,Finset.sum_Ico_Ico_comm]
  simp only [Nat.Ico_zero_eq_range]
  apply sum_congr rfl
  intro l _
  rw [← sum_mul]
  have he := radius_sum (r := r) (c := c) l (fun i _ => hr i) (fun i _ => (hstep i).symm)
  rw [← he]
  ring
end GeometricFilter

namespace SignedRuns
open ActualLabels FiniteLabels Finset DiskMoments PhysicalCells SignedAssembly GeometricFilter

lemma total_divergence_integrable (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) :
    Integrable (fun x => leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) m []) := by
  apply leafSum_integrable
  intro q
  obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
  apply weighted_divergence_integrable hK _ (potential_regular hg hc hr hstep q)
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x q)]
  exact weight_le_one h r old x q

lemma total_flux_integrable (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) :
    Integrable (fun x => leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x)
      (potential g r x q)) m []) := by
  apply leafSum_integrable
  intro q
  obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
  exact potential_flux_integrable hK (potential_regular hg hc hr hstep q)

lemma band_gradient_integrable {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (m : ℕ) : Integrable (gradient (runEnvelope g r 0 m)) := by
  have hab : r m ≤ 2*r 0 := by
    have hh := radius_antitone r hr hstep (Nat.zero_le m)
    linarith [hr 0]
  obtain ⟨L,hL⟩ := run_envelope_lipschitz hg hc (hr m) hab
  exact _root_.OAI.LipschitzWith.integrable_gradient hL (run_envelope_hasCompactSupport hg hc (hr m) hab)

/-- Integration of the signed master, with its actual history law. The only
remaining inputs here are actual analytic majorants and their integrals; no
unsigned sum of run gradients is introduced. -/
theorem integrated_signed_master {g : ℂ → ℝ} (h : ℂ → ℂ) {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℂ → ℝ) (J : ℕ → ℂ → ℝ)
    (hH : ∀ k n x, 0 ≤ H k n x) (hJ : ∀ k x, 0 ≤ J k x)
    (old : Label) (m : ℕ)
    (hinterior : ∀ᵐ x, ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n x)
    (hend : ∀ᵐ x, ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k x)
    (hvalue : ∀ᵐ x, ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ r k*J k x)
    (hHi : ∀ k, k ≤ m → ∀ n, Integrable (H k n))
    (hJi : ∀ k, k ≤ m → Integrable (J k)) :
    (∫ x, ‖gradient (runEnvelope g r 0 m) x‖) ≤
      12*((∑ k ∈ range (m+1), ∫ x, expect (marginal h r k x) (fun n => H k n x))+
        4*(∑ k ∈ range (m+1), ∫ x, pointCost h r x m k*J k x)) := by
  have hdi (k : ℕ) (hk : k ≤ m) :
      Integrable (fun x => expect (marginal h r k x) (fun n => H k n x)) := by
    apply integrable_finsetSum
    intro n _
    apply (hHi k hk n).bdd_mul (marginal_continuous h r hr k n).measurable.aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg ((marginal h r k x).nonneg n)]
      exact law_le_one _ _)
  have hbi (k : ℕ) (hk : k ≤ m) : Integrable (fun x => pointCost h r x m k*J k x) := by
    apply (hJi k hk).bdd_mul (pointCost_measurable h r hr m k).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pointCost_nonneg h r hr x m k)]
      exact pointCost_le h r hr x m k)
  let D := fun x => ∑ k ∈ range (m+1), expect (marginal h r k x) (fun n => H k n x)
  let B := fun x => ∑ k ∈ range (m+1), pointCost h r x m k*J k x
  have hDi : Integrable D := integrable_finsetSum _ (fun k hk => hdi k (by have := mem_range.mp hk; omega))
  have hBi : Integrable B := integrable_finsetSum _ (fun k hk => hbi k (by have := mem_range.mp hk; omega))
  let div := fun x => leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) (m+1) []
  let flux := fun x => leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) (m+1) []
  have hdivi : Integrable div := total_divergence_integrable g h r hg hc hr hstep old (m+1)
  have hfluxi : Integrable flux := total_flux_integrable g h r hg hc hr hstep old (m+1)
  have hb (x : ℂ) : (∑ k ∈ range (m+1), boundaryCost h r x m k*J k x) ≤ B x := by
    apply sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (hJ k x)
    dsimp [pointCost]
    linarith [filt_nonneg (fun i => derivativeCost_nonneg h r x i (hr i).le) k]
  have hmaster : ∀ᵐ x, ‖gradient (runEnvelope g r 0 m) x‖ ≤ 12*(div x+D x+3*B x) := by
    filter_upwards [runs_ae_diff hg hc hr hstep,hinterior,hend] with x hd hi he
    have hh := pointwise_signed_master h hg hc hr hstep (fun k n => H k n x) (fun k => J k x)
      (fun k n => hH k n x) (fun k => hJ k x) old m x hd hi he
    change ‖gradient (runEnvelope g r 0 m) x‖ ≤ 12*(div x+D x+3*_) at hh
    linarith [hb x]
  have hf : ∀ᵐ x, -flux x ≤ B x := by
    filter_upwards [observation_ae_diff h r hr,hvalue] with x hd hv
    have ht := actual_signed_flux_bound g h r hg hr hstep old x hd (fun k => r k*J k x) hv (m+1)
    rw [radius_convolution hr hstep] at ht
    have hle : (∑ k ∈ range (m+1), filt (fun i => derivativeCost h r x i) k*J k x) ≤ B x := by
      apply sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (hJ k x)
      dsimp [pointCost]
      linarith [boundaryCost_nonneg h r x m k]
    exact (neg_le_abs (flux x)).trans (ht.trans hle)
  have hi := integral_mono_ae (band_gradient_integrable hg hc hr hstep m).norm
    ((hdivi.add hDi).add (hBi.const_mul 3) |>.const_mul 12) hmaster
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (f := fun x => div x+D x) (g := fun x => 3*B x) (hdivi.add hDi) (hBi.const_mul 3),integral_add hdivi hDi,
    integral_const_mul] at hi
  have hip : (∫ x, div x) = -∫ x, flux x := history_weighted_ibp g h r hg hc hr hstep old (m+1)
  have hfi := integral_mono_ae hfluxi.neg hBi hf
  simp only [Pi.neg_apply,integral_neg] at hfi
  have hDint : (∫ x, D x) = ∑ k ∈ range (m+1), ∫ x, expect (marginal h r k x) (fun n => H k n x) :=
    integral_finsetSum _ (fun k hk => hdi k (by have := mem_range.mp hk; omega))
  have hBint : (∫ x, B x) = ∑ k ∈ range (m+1), ∫ x, pointCost h r x m k*J k x :=
    integral_finsetSum _ (fun k hk => hbi k (by have := mem_range.mp hk; omega))
  rw [hip] at hi
  rw [← hDint,← hBint]
  linarith
end SignedRuns

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

/-- Combine the two actual signed directional prices; the labels are unchanged. -/
theorem physical_unfavorable_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ) (n : Label),
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalNeighborhoodRadius g (scale r k) y t →
        ENNReal.ofReal (unfavorable n (gradient (fun z => signedAverage g z t) y)) ≤ F y := by
  obtain ⟨C,hC,hp⟩ := physical_directional_price
  refine ⟨2*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hs hd k p n
  obtain ⟨F,hFm,hFi,hFb⟩ := hp hr hR hN hg hh hs hd k p n.property (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)=-1)
  obtain ⟨G,hGm,hGi,hGb⟩ := hp hr hR hN hg hh hs hd k p n.property (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ)=-1)
  have hn : 0 ≤ C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p)) :=
    mul_nonneg hC.le (add_nonneg (badPrice_nonneg _ _ _ _ _) (cellPrice_nonneg hr hR hN hh hs k _))
  refine ⟨fun y => F y+G y,hFm.add hGm,?_,?_⟩
  · rw [lintegral_add_left hFm]
    calc
      _ ≤ ENNReal.ofReal (C*(_+_))+ENNReal.ofReal (C*(_+_)) := add_le_add hFi hGi
      _ = _ := by rw [← ENNReal.ofReal_add hn hn]; congr 1; ring
  · intro y hy t ht
    rw [unfavorable,ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
    exact add_le_add (hFb y hy t ht) (hGb y hy t ht)

/-- A single actual endpoint price pays both the gradient and the normalized
oscillation. It is introduced before any spatial supremum is taken. -/
theorem physical_joint_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ) (n : Label),
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalEndpointRadius g (scale r k) y t →
        ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t t',
        0 < t → t ≤ 4*scale r k → 0 < t' → t' ≤ 4*scale r k →
        ENNReal.ofReal (|signedAverage g y t-signedAverage g y t'|/scale r k) ≤ F y) := by
  obtain ⟨Cs,hCs,hp⟩ := physical_size_price
  obtain ⟨Cv,hCv,hq⟩ := physical_value_price
  refine ⟨Cs+Cv,add_pos hCs hCv,?_⟩
  intro N r R hr hR hN g hg hh hs hd k p n
  obtain ⟨F,hFm,hFi,hFb⟩ := hp hr hR hN hg hh hs hd k p n.property
  obtain ⟨G,hGm,hGi,hGb⟩ := hq hr hR hN hg hh hs hd k p n.property
  have hrk := scale_pos hr k
  let B := rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p)
  have hB : 0 ≤ B := add_nonneg (rootMass_nonneg _ _ _ _) (cellPrice_nonneg hr hR hN hh hs k _)
  have hG : (∫⁻ y in cell (point (scale r k) p) (scale r k), ENNReal.ofReal (scale r k)⁻¹*G y) ≤ ENNReal.ofReal (Cv*B) := by
    rw [lintegral_const_mul _ hGm]
    calc
      _ ≤ ENNReal.ofReal (scale r k)⁻¹*ENNReal.ofReal (Cv*scale r k*B) := mul_le_mul' le_rfl hGi
      _ = _ := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrk.le)]; congr 1; field_simp
  refine ⟨fun y => F y+ENNReal.ofReal (scale r k)⁻¹*G y,
    hFm.add (measurable_const.mul hGm),?_,?_,?_⟩
  · rw [lintegral_add_left hFm]
    calc
      _ ≤ ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cv*B) := add_le_add hFi hG
      _ = _ := by rw [← ENNReal.ofReal_add (mul_nonneg hCs.le hB) (mul_nonneg hCv.le hB),← add_mul]
  · intro y hy t ht
    exact (hFb y hy t ht).trans le_self_add
  · intro y hy t t' ht hb ht' hb'
    have hgg := mul_le_mul' (le_refl (ENNReal.ofReal (scale r k)⁻¹)) (hGb y hy t t' ht hb ht' hb')
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrk.le),inv_mul_eq_div] at hgg
    exact hgg.trans le_add_self
end CommonPrices

namespace PhysicalCells
open Finset

lemma real_weighted_patches {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (F : ι → (ℤ × ℤ) → ℂ → ℝ≥0∞)
    (hFi : ∀ i ∈ s, Integrable (fun x => (patch (r i) (F i) x).toReal))
    (W : ι → ℂ → ℝ) (hW : ∀ i ∈ s, Measurable (W i))
    (hW0 : ∀ i ∈ s, ∀ x, 0 ≤ W i x) (M : ℝ)
    (hWM : ∀ i ∈ s, ∀ x, W i x ≤ M) {C : ℝ} (hC : 0 ≤ C)
    (hf : (∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (W i x)*patch (r i) (F i) x) ≤ ENNReal.ofReal C) :
    (∑ i ∈ s, ∫ x, W i x*(patch (r i) (F i) x).toReal) ≤ C := by
  have hi (i : ι) (hi : i ∈ s) : Integrable (fun x => W i x*(patch (r i) (F i) x).toReal) := by
    apply (hFi i hi).bdd_mul (hW i hi).aestronglyMeasurable
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hW0 i hi x)]; exact hWM i hi x)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => integral_nonneg (fun x => mul_nonneg (hW0 i hi x) ENNReal.toReal_nonneg))]
  apply le_trans _ hf
  apply sum_le_sum
  intro i his
  rw [ofReal_integral_eq_lintegral_ofReal (hi i his) (ae_of_all _ (fun x => mul_nonneg (hW0 i his x) ENNReal.toReal_nonneg))]
  apply lintegral_mono
  intro x
  change ENNReal.ofReal (W i x * (patch (r i) (F i) x).toReal) ≤ ENNReal.ofReal (W i x) * patch (r i) (F i) x
  rw [ENNReal.ofReal_mul (hW0 i his x)]
  exact mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
end PhysicalCells

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

lemma bad_total_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) (n : Label) :
    (∑ p ∈ P, (badPrice h base j (cellRoots N p) n+cellPrice N base h j (cellRoots N p))) ≤
      (1681+priceConstant)*(∫ y, ‖h y‖) := by
  apply le_trans _ (total_level_budget hb hR hN hh hsupp j P)
  apply sum_le_sum
  intro p hp
  exact add_le_add (badPrice_le_rootMass h base j (cellRoots N p) n) le_rfl

/-- Actual full-lattice unfavorable prices, with the genuine marginal law. -/
theorem patched_unfavorable : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    ∃ H : ℕ → Label → ℂ → ℝ,
      (∀ j n x, 0 ≤ H j n x) ∧ (∀ j n, Integrable (H j n)) ∧
      (∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
        unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x) ∧
      (∀ m n, (∑ j ∈ range (m+1), ∫ x, marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) ≤
        C*(∫ y, ‖gradient g y‖)) := by
  obtain ⟨c,hc,hp⟩ := physical_unfavorable_price
  refine ⟨c*directPriceConstant,mul_pos hc directPriceConstant_pos,?_⟩
  intro N base R hb hR hN g hg hh hs hd
  choose F hFm hFi hFb using fun j n p => hp hb hR hN hg hh hs hd j p n
  let B := fun j p n => badPrice (gradient g) base j (cellRoots N p) n+cellPrice N base (gradient g) j (cellRoots N p)
  have hB (j p n) : 0 ≤ B j p n := add_nonneg (badPrice_nonneg _ _ _ _ _) (cellPrice_nonneg hb hR hN hh hs j _)
  have hpi (j n) : (∫⁻ x, patch (scale base j) (F j n) x) ≤
      ENNReal.ofReal (c*((1681+priceConstant)*(∫ y, ‖gradient g y‖))) := by
    apply lintegral_patch_budget _ _ (hFm j n) (fun p => c*B j p n) (fun p => mul_nonneg hc.le (hB j p n)) _ (hFi j n)
    intro P
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (bad_total_level_budget hb hR hN hh hs j P n) hc.le
  let H := fun j n x => (patch (scale base j) (F j n) x).toReal
  have hHi (j n) : Integrable (H j n) := patch_integrable _ _ (hFm j n) (hpi j n)
  refine ⟨H,fun _ _ _ => ENNReal.toReal_nonneg,hHi,?_,?_⟩
  · have hfin : ∀ᵐ x, ∀ j n, patch (scale base j) (F j n) x ≠ ⊤ :=
      (ae_all_iff).mpr (fun j => (ae_all_iff).mpr (fun n => patch_finite _ _ (hFm j n) (hpi j n)))
    filter_upwards [hfin] with x hx
    intro j n t ht
    exact real_le_patch (F j n) (gridIndex (scale base j) x) (mem_index_cell (scale_pos hb j) x) (hx j n)
      (hFb j n _ x (mem_index_cell (scale_pos hb j) x) t ht)
  · intro m n
    let W := fun j x => marginal (gradient g) (geometricRadii base m) (m-j) x n
    let A := fun j p => localSup (W j) (scale base j) p
    have hA (j) (hj : j ∈ range (m+1)) (p) : 0 ≤ A j p := by
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      dsimp [A,W]
      rw [← geometricRadii_reverse base hjm]
      exact marginal_localSup_nonneg _ _ _ (geometricRadii_pos hb m (m-j)) p n
    have hwm (j) : Measurable (W j) := (marginal_continuous _ _ (geometricRadii_pos hb m) (m-j) n).measurable
    have hWB (j) (hj : j ∈ range (m+1)) (p x) (hx : x ∈ cell (point (scale base j) p) (scale base j)) :
        ENNReal.ofReal (W j x) ≤ ENNReal.ofReal (A j p) := by
      apply ENNReal.ofReal_le_ofReal
      apply le_localSup p (fun y _ => law_le_one _ _)
      change DyadicHats.boxNorm (x-point (scale base j) p) ≤ 25*scale base j
      have ht := mem_cell_box (scale_pos hb j) hx
      linarith [scale_pos hb j]
    have hwt := integrated_weighted_patches (range (m+1)) (scale base) (fun j => F j n)
      (fun j _ => hFm j n) (fun j x => ENNReal.ofReal (W j x)) (fun j _ => (hwm j).ennreal_ofReal)
      A (fun j p => c*B j p n) hA (fun j _ p => mul_nonneg hc.le (hB j p n))
      (fun j _ => hFi j n) hWB (c*directPriceConstant*(∫ y, ‖gradient g y‖)) (by
        intro P
        have hbgt := mul_le_mul_of_nonneg_left (marginal_total_budget hb hR hN hh hs m (fun _ => P) n) hc.le
        simpa only [A,W,B,mul_sum,mul_assoc,mul_left_comm] using hbgt)
    exact real_weighted_patches (range (m+1)) (scale base) (fun j => F j n) (fun j _ => hHi j n)
      W (fun j _ => hwm j) (fun j _ x => (marginal _ _ _ x).nonneg n) 1 (fun j _ x => law_le_one _ _)
      (mul_nonneg (mul_nonneg hc.le directPriceConstant_pos.le) (integral_nonneg (fun y => norm_nonneg _))) hwt
end CommonPrices

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

/-- Actual endpoint/value weights charged simultaneously at every level. -/
theorem patched_joint : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    ∃ J : ℕ → ℂ → ℝ,
      (∀ j x, 0 ≤ J j x) ∧ (∀ j, Integrable (J j)) ∧
      (∀ᵐ x, ∀ j t, PhysicalEndpointRadius g (scale base j) x t →
        ‖gradient (fun y => signedAverage g y t) x‖ ≤ J j x) ∧
      (∀ᵐ x, ∀ j t t', 0 < t → t ≤ 4*scale base j → 0 < t' → t' ≤ 4*scale base j →
        |signedAverage g x t-signedAverage g x t'| ≤ scale base j*J j x) ∧
      (∀ m, (∑ j ∈ range (m+1), ∫ x, pointCost (gradient g) (geometricRadii base m) x m (m-j)*J j x) ≤
        C*(∫ y, ‖gradient g y‖)) := by
  obtain ⟨c,hc,hp⟩ := physical_joint_price
  refine ⟨c*spatialPriceConstant,mul_pos hc spatialPriceConstant_pos,?_⟩
  intro N base R hb hR hN g hg hh hs hd
  let n : Label := target (gradient g) base (0,0)
  choose F hFm hFi hFb hFv using fun j p => hp hb hR hN hg hh hs hd j p n
  let B := fun j p => rootMass (gradient g) base j (cellRoots N p)+cellPrice N base (gradient g) j (cellRoots N p)
  have hB (j p) : 0 ≤ B j p := add_nonneg (rootMass_nonneg _ _ _ _) (cellPrice_nonneg hb hR hN hh hs j _)
  have hpi (j) : (∫⁻ x, patch (scale base j) (F j) x) ≤
      ENNReal.ofReal (c*((1681+priceConstant)*(∫ y, ‖gradient g y‖))) := by
    apply lintegral_patch_budget _ _ (hFm j) (fun p => c*B j p) (fun p => mul_nonneg hc.le (hB j p)) _ (hFi j)
    intro P
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (total_level_budget hb hR hN hh hs j P) hc.le
  let J := fun j x => (patch (scale base j) (F j) x).toReal
  have hJi (j) : Integrable (J j) := patch_integrable _ _ (hFm j) (hpi j)
  have hfin : ∀ᵐ x, ∀ j, patch (scale base j) (F j) x ≠ ⊤ :=
    (ae_all_iff).mpr (fun j => patch_finite _ _ (hFm j) (hpi j))
  refine ⟨J,fun _ _ => ENNReal.toReal_nonneg,hJi,?_,?_,?_⟩
  · filter_upwards [hfin] with x hx
    intro j t ht
    exact real_le_patch (F j) (gridIndex (scale base j) x) (mem_index_cell (scale_pos hb j) x) (hx j)
      (hFb j _ x (mem_index_cell (scale_pos hb j) x) t ht)
  · filter_upwards [hfin] with x hx
    intro j t t' ht hb' ht' hb''
    have ht := real_le_patch (F j) (gridIndex (scale base j) x) (mem_index_cell (scale_pos hb j) x) (hx j)
      (hFv j _ x (mem_index_cell (scale_pos hb j) x) t t' ht hb' ht' hb'')
    exact (div_le_iff₀ (scale_pos hb j)).mp ht |>.trans_eq (mul_comm _ _)
  · intro m
    let W := fun j x => pointCost (gradient g) (geometricRadii base m) x m (m-j)
    let A := fun j p => cellSup (W j) (scale base j) p
    have hwm (j) : Measurable (W j) := pointCost_measurable _ _ (geometricRadii_pos hb m) m (m-j)
    have hw0 (j x) : 0 ≤ W j x := pointCost_nonneg _ _ (geometricRadii_pos hb m) x m (m-j)
    have hwM (j x) : W j x ≤ costLimit := pointCost_le _ _ (geometricRadii_pos hb m) x m (m-j)
    have hA (j p) : 0 ≤ A j p := cellSup_nonneg p (hw0 j) (fun x _ => hwM j x)
    have hWB (j p x) (hx : x ∈ cell (point (scale base j) p) (scale base j)) :
        ENNReal.ofReal (W j x) ≤ ENNReal.ofReal (A j p) :=
      ENNReal.ofReal_le_ofReal (le_cellSup p (fun y _ => hwM j y) hx)
    have hwt := integrated_weighted_patches (range (m+1)) (scale base) F
      (fun j _ => hFm j) (fun j x => ENNReal.ofReal (W j x)) (fun j _ => (hwm j).ennreal_ofReal)
      A (fun j p => c*B j p) (fun j _ => hA j) (fun j _ p => mul_nonneg hc.le (hB j p))
      (fun j _ => hFi j) (fun j _ => hWB j) (c*spatialPriceConstant*(∫ y, ‖gradient g y‖)) (by
        intro P
        have hbgt := mul_le_mul_of_nonneg_left (pointCost_total_budget hb hR hN hh hs m (fun _ => P)) hc.le
        simpa only [A,W,B,mul_sum,mul_assoc,mul_left_comm] using hbgt)
    exact real_weighted_patches (range (m+1)) (scale base) F (fun j _ => hJi j)
      W (fun j _ => hwm j) (fun j _ => hw0 j) costLimit (fun j _ => hwM j)
      (mul_nonneg (mul_nonneg hc.le spatialPriceConstant_pos.le) (integral_nonneg (fun y => norm_nonneg _))) hwt
end CommonPrices

namespace SignedRuns
open ActualLabels FiniteLabels Finset DiskMoments PhysicalCells SignedAssembly GeometricFilter CommonPrices DyadicHats

/-- Reverse the spatial scale index and fill unused indices with genuine global
Lipschitz bounds. Only the physical prices at indices at most m are integrated. -/
lemma master_from_patches {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {base : ℝ} (hb : 0 < base) (m : ℕ)
    (H : ℕ → Label → ℂ → ℝ) (J : ℕ → ℂ → ℝ)
    (hH : ∀ j n x, 0 ≤ H j n x) (hJ : ∀ j x, 0 ≤ J j x)
    (hHi : ∀ j n, Integrable (H j n)) (hJi : ∀ j, Integrable (J j))
    (hinterior : ∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x)
    (hend : ∀ᵐ x, ∀ j t, PhysicalEndpointRadius g (scale base j) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J j x)
    (hvalue : ∀ᵐ x, ∀ j t t', 0 < t → t ≤ 4*scale base j → 0 < t' → t' ≤ 4*scale base j →
      |signedAverage g x t-signedAverage g x t'| ≤ scale base j*J j x) :
    (∫ x, ‖gradient (runEnvelope g (geometricRadii base m) 0 m) x‖) ≤
      12*((∑ j ∈ range (m+1), ∫ x, expect (marginal (gradient g) (geometricRadii base m) (m-j) x) (fun n => H j n x))+
        4*(∑ j ∈ range (m+1), ∫ x, pointCost (gradient g) (geometricRadii base m) x m (m-j)*J j x)) := by
  classical
  let r := geometricRadii base m
  have hr := geometricRadii_pos hb m
  obtain ⟨L,hL⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hg.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hMa (y) : |g y| ≤ M := by simpa only [Real.norm_eq_abs] using hM y
  let H' := fun k n x => if k ≤ m then H (m-k) n x else 2*(L:ℝ)
  let J' := fun k x => if k ≤ m then J (m-k) x else (L:ℝ)+2*M/r k
  have hH' (k n x) : 0 ≤ H' k n x := by dsimp [H']; split_ifs; exact hH _ _ _; positivity
  have hJ' (k x) : 0 ≤ J' k x := by
    dsimp [J']; split_ifs
    · exact hJ _ _
    · exact add_nonneg L.coe_nonneg (div_nonneg (mul_nonneg (by norm_num) hM0) (hr k).le)
  have hHi' (k) (hk : k ≤ m) (n) : Integrable (H' k n) := by simpa only [H',ite_eq_left hk] using hHi (m-k) n
  have hJi' (k) (hk : k ≤ m) : Integrable (J' k) := by simpa only [J',ite_eq_left hk] using hJi (m-k)
  have hint' : ∀ᵐ x, ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H' k n x := by
    filter_upwards [hinterior] with x hx
    intro k n t ht
    dsimp [H']
    split_ifs with hk
    · apply hx
      simpa only [r,geometricRadii_eq base hk] using ht
    · exact (unfavorable_le_norm n _).trans (mul_le_mul_of_nonneg_left
        (gradient_norm_le (signedAverage_lipschitz hL ((hr k).trans_le ht.1.1)) x) (by norm_num))
  have hend' : ∀ᵐ x, ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J' k x := by
    filter_upwards [hend] with x hx
    intro k t ht
    dsimp [J']
    split_ifs with hk
    · apply hx
      simpa only [r,geometricRadii_eq base hk] using ht
    · have he := gradient_norm_le (signedAverage_lipschitz hL ((hr k).trans_le ht.1.1)) x
      have hpos : 0 ≤ 2*M/r k := div_nonneg (mul_nonneg (by norm_num) hM0) (hr k).le
      linarith
  have hval' : ∀ᵐ x, ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ r k*J' k x := by
    filter_upwards [hvalue] with x hx
    intro k t t' ht hbt ht' hbt'
    dsimp [J']
    split_ifs with hk
    · simpa only [r,geometricRadii_eq base hk] using hx (m-k) t t' ht
        (by simpa only [r,geometricRadii_eq base hk] using hbt) ht'
        (by simpa only [r,geometricRadii_eq base hk] using hbt')
    · have he := abs_sub (signedAverage g x t) (signedAverage g x t')
      have he1 := signedAverage_abs_le hMa x ht
      have he2 := signedAverage_abs_le hMa x ht'
      rw [mul_add,mul_div_cancel₀ _ (hr k).ne']
      have hp : 0 ≤ r k*(L:ℝ) := mul_nonneg (hr k).le L.coe_nonneg
      linarith
  have hi := integrated_signed_master (gradient g) hg hc hr (geometricRadii_step base m)
    H' J' hH' hJ' (target (gradient g) base (0,0)) m hint' hend' hval' hHi' hJi'
  have hd : (∑ k ∈ range (m+1), ∫ x, expect (marginal (gradient g) r k x) (fun n => H' k n x)) =
      ∑ j ∈ range (m+1), ∫ x, expect (marginal (gradient g) r (m-j) x) (fun n => H j n x) := by
    rw [← sum_range_reflect (fun k => ∫ x, expect (marginal (gradient g) r k x) (fun n => H' k n x)) (m+1)]
    apply sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by have := mem_range.mp hj; omega
    simp only [Nat.add_sub_cancel,H',ite_eq_left (Nat.sub_le m j),Nat.sub_sub_self hjm]
  have he : (∑ k ∈ range (m+1), ∫ x, pointCost (gradient g) r x m k*J' k x) =
      ∑ j ∈ range (m+1), ∫ x, pointCost (gradient g) r x m (m-j)*J j x := by
    rw [← sum_range_reflect (fun k => ∫ x, pointCost (gradient g) r x m k*J' k x) (m+1)]
    apply sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by have := mem_range.mp hj; omega
    simp only [Nat.add_sub_cancel,J',ite_eq_left (Nat.sub_le m j),Nat.sub_sub_self hjm]
  rw [hd,he] at hi
  exact hi

/-- The genuine smooth signed dyadic finite-band estimate. No probability,
common-price, local analytic estimate, or total variation bound is assumed. -/
theorem smooth_compact_dyadic_band : ∃ C : ℝ, 0 < C ∧
    ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g → HasCompactSupport g →
    ∀ {base : ℝ}, 0 < base → ∀ m : ℕ,
    (∫ x, ‖gradient (runEnvelope g (geometricRadii base m) 0 m) x‖) ≤ C*(∫ x, ‖gradient g x‖) := by
  obtain ⟨Cd,hCd,hpd⟩ := patched_unfavorable
  obtain ⟨Cj,hCj,hpj⟩ := patched_joint
  refine ⟨12*((Fintype.card Label:ℝ)*Cd+4*Cj),by positivity,?_⟩
  intro g hg hc base hb m
  have hh : Integrable (gradient g) := (continuous_gradient hg).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  obtain ⟨R0,hR0⟩ := (gradient_hasCompactSupport hc).isBounded.subset_closedBall (0:ℂ)
  let R := max 0 R0
  have hR : 0 ≤ R := le_max_left _ _
  have hs : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R := by
    intro y hy
    have he : ‖y‖ ≤ R0 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR0 (subset_tsupport (gradient g) hy)
    exact he.trans (le_max_right _ _)
  obtain ⟨N,hN⟩ := exists_nat_ge (R/base+1)
  obtain ⟨L,hL⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hd : ∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D := ⟨L,fun _ => norm_fderiv_le_of_lipschitz ℝ hL⟩
  obtain ⟨H,hH,hHi,hHd,hHb⟩ := hpd hb hR hN hg hh hs hd
  obtain ⟨J,hJ,hJi,hJe,hJv,hJb⟩ := hpj hb hR hN hg hh hs hd
  have hi := master_from_patches hg hc hb m H J hH hJ hHi hJi hHd hJe hJv
  have hdi (j : ℕ) (n : Label) : Integrable (fun x => marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) := by
    apply (hHi j n).bdd_mul (marginal_continuous _ _ (geometricRadii_pos hb m) (m-j) n).measurable.aestronglyMeasurable
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg ((marginal _ _ _ x).nonneg n)]; exact law_le_one _ _)
  have hD : (∑ j ∈ range (m+1), ∫ x, expect (marginal (gradient g) (geometricRadii base m) (m-j) x) (fun n => H j n x)) ≤
      (Fintype.card Label:ℝ)*Cd*(∫ y, ‖gradient g y‖) := by
    simp only [FiniteLabels.expect]
    simp_rw [integral_finsetSum univ (fun n _ => hdi _ n)]
    rw [Finset.sum_comm]
    have he := sum_le_sum (s := univ) (fun n _ => hHb m n)
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_assoc] using he
  have hB := hJb m
  nlinarith only [hi,hD,hB]
end SignedRuns

end

end OAI
