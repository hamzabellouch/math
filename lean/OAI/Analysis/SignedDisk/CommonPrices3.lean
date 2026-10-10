import OAI.Analysis.SignedDisk.CommonPrices2

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset

def priceConstant : ℝ := 1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))
lemma priceConstant_nonneg : 0 ≤ priceConstant := by
  unfold priceConstant
  exact mul_nonneg (by norm_num) (div_nonneg (by positivity) (by linarith [rho_lt_one]))
lemma cellPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ cellPrice N r h k S := sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
lemma rootMass_cell_budget {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ)
    (k : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, rootMass h r k (cellRoots N p)) ≤ 1681*(∫ y, ‖h y‖) := by
  exact (cellRoots_budget _ (fun q => norm_nonneg (vectorMass h (scale r k) q)) P).trans
    (mul_le_mul_of_nonneg_left (sum_scalarMass_grid_le hh _) (by norm_num))
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset ActualMarkTrees

lemma geometricRadii_reverse (base : ℝ) {m j : ℕ} (hj : j ≤ m) :
    geometricRadii base m (m-j) = scale base j := by
  rw [geometricRadii_eq base (Nat.sub_le m j),Nat.sub_sub_self hj]

lemma pointCost_mass_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        rootMass h base j (cellRoots N p)) ≤ 1681*packingConstant*(∫ y, ‖h y‖) := by
  have he : (∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q) =
      ∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (fun i => scale base (m-i)) m (m-j) q := by
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro q _
    rw [cellCost_congr h _ _ m (m-j) (Nat.sub_le m j)
      (fun i hi => geometricRadii_eq base hi)]
  calc
    _ ≤ ∑ j ∈ range (m+1), 1681*∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      have ht := pointCost_cell_budget (N := N) h (geometricRadii base m) (geometricRadii_pos hb m)
        base m (m-j) j (geometricRadii_reverse base hjm) (P j)
      simpa only [geometricRadii_reverse base hjm] using ht
    _ = 1681*(∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q) := by rw [mul_sum]
    _ ≤ _ := by
      rw [he,mul_assoc]
      exact mul_le_mul_of_nonneg_left (spatial_packing hb hR hN hh hsupp m) (by norm_num)

lemma pointCost_price_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        cellPrice N base h j (cellRoots N p)) ≤ costLimit*priceConstant*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ j ∈ range (m+1), ∑ p ∈ P j, costLimit*cellPrice N base h j (cellRoots N p) := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      apply sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (cellPrice_nonneg hb hR hN hh hsupp j _)
      rw [← geometricRadii_reverse base hjm]
      exact cellSup_pointCost_uniform h _ (geometricRadii_pos hb m) m (m-j) p
    _ = costLimit*(∑ j ∈ range (m+1), ∑ p ∈ P j, cellPrice N base h j (cellRoots N p)) := by
      simp only [mul_sum]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (cellPrice_budget hb hR hN hh hsupp m P) costLimit_pos.le

lemma marginal_bad_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        badPrice h base j (cellRoots N p) n) ≤
      (1000000*1681*(576*(4097:ℝ)^2))*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ j ∈ range (m+1), 1000000*1681*∑ q : Grid N,
        scalarMass h (scale base j) q*energy h (scale base j) q := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      calc
        _ ≤ ∑ p ∈ P j, 1000000*∑ q ∈ cellRoots N p,
            scalarMass h (scale base j) q*energy h (scale base j) q := by
          apply sum_le_sum
          intro p _
          have ht := marginal_badPrice_bound (N := N) h (geometricRadii base m) base (m-j) j
            (geometricRadii_pos hb m (m-j)) (geometricRadii_reverse base hjm) p n
          simpa only [geometricRadii_reverse base hjm] using ht
        _ ≤ _ := by
          rw [← mul_sum,mul_assoc]
          exact mul_le_mul_of_nonneg_left (cellRoots_budget _
            (fun q => mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)) (P j)) (by norm_num)
    _ ≤ _ := by
      rw [← mul_sum]
      have ht := mul_le_mul_of_nonneg_left (neighbor_energy_budget hb hR hN hh hsupp (m+1))
        (by norm_num : (0:ℝ) ≤ 1000000*1681)
      nlinarith only [ht]

lemma marginal_price_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        cellPrice N base h j (cellRoots N p)) ≤ priceConstant*(∫ y, ‖h y‖) := by
  apply le_trans _ (cellPrice_budget hb hR hN hh hsupp m P)
  apply sum_le_sum
  intro j hj
  have hjm : j ≤ m := by have := mem_range.mp hj; omega
  apply sum_le_sum
  intro p _
  have hbnd : localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p ≤ 1 := by
    rw [← geometricRadii_reverse base hjm]
    exact marginal_localSup_le_one h _ (m-j) (geometricRadii_pos hb m (m-j)) p n
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbnd (cellPrice_nonneg hb hR hN hh hsupp j _)

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
  exact SignedDisk.LipschitzWith.integrable_gradient hL (run_envelope_hasCompactSupport hg hc (hr m) hab)

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

end SignedDisk

end

end OAI
