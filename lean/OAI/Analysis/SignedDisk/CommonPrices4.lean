import OAI.Analysis.SignedDisk.CommonPrices3

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

/- Directional weak gradients and coordinate isometries on the plane. -/
namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Directional, coordinate-free distributional gradient. -/
def HasGradient (f : E → ℝ) (g : E → E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ v : E,
    (∫ x, f x * fderiv ℝ φ x v ∂μ) = -∫ x, ⟪g x,v⟫ * φ x ∂μ

lemma norm_convolution_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : E → ℝ} {g : E → F}
    (hK : Integrable K μ) (hg : Integrable g μ) :
    (∫ x, ‖(K ⋆[lsmul ℝ ℝ,μ] g) x‖ ∂μ) ≤ (∫ x, |K x| ∂μ)*(∫ x, ‖g x‖ ∂μ) := by
  have hi := hK.norm.integrable_convolution (lsmul ℝ ℝ) hg.norm
  calc
    _ ≤ ∫ x, ( (fun y => ‖K y‖) ⋆[lsmul ℝ ℝ,μ] (fun y => ‖g y‖)) x ∂μ := by
      apply integral_mono_ae (hK.integrable_convolution (lsmul ℝ ℝ) hg).norm hi
      filter_upwards [hK.norm.ae_convolution_exists (lsmul ℝ ℝ) hg.norm] with x hx
      simp only [convolution_def,lsmul_apply,smul_eq_mul] at hx ⊢
      exact norm_integral_le_of_norm_le hx (ae_of_all _ (fun y => by rw [norm_smul]))
    _ = _ := by rw [integral_convolution _ hK.norm hg.norm]; simp only [lsmul_apply,smul_eq_mul,Real.norm_eq_abs]

lemma lipschitz_hasGradient {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasGradient (μ := μ) f (gradient f) := by
  intro φ hφ hc v
  obtain ⟨K,hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  exact SignedDisk.LipschitzWith.integral_mul_fderiv_eq_neg hf hK hc v
end WeakSobolev

end SignedDisk

end

end OAI
