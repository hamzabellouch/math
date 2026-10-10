import OAI.Analysis.SignedDisk.SignedRuns2

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
open DyadicHats DirectionNeighbors Finset ConeCoordinates

lemma cellRoots_budget {N : ℕ} (B : Grid N → ℝ) (hB : ∀ q, 0 ≤ B q)
    (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, ∑ q ∈ cellRoots N p, B q) ≤ 1681*∑ q, B q := by
  simp only [cellRoots,sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply sum_le_sum
  intro q _
  have hs : P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p) ⊆ window 20 q := by
    intro p hp
    exact (mem_window_comm 20 _ _).mp (mem_filter.mp hp).2
  have hc : ((P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p)).card : ℝ) ≤ 1681 := by
    have hc := Finset.card_le_card hs
    rw [card_window] at hc
    exact_mod_cast hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc (hB q)

lemma badPrice_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    0 ≤ badPrice h r k S n := sum_nonneg (fun _ _ => norm_nonneg _)

lemma badPrice_le_rootMass {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    badPrice h r k S n ≤ rootMass h r k S := by
  classical
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)
end CommonPrices

namespace ActualLabels
open DyadicHats DirectionNeighbors FiniteLabels CommonPrices ConeCoordinates Finset

lemma marginal_localSup_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : 0 ≤ localSup (fun x => marginal h r k x n) (r k) p :=
  localSup_nonneg hr.le p (fun x => (marginal h r k x).nonneg n) (fun _ _ => law_le_one _ _)

lemma marginal_localSup_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : localSup (fun x => marginal h r k x n) (r k) p ≤ 1 :=
  localSup_le hr.le p (fun _ _ => law_le_one _ _)

lemma marginal_localSup_bad_zero {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p)
    (hE : energy h (r k) q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h (r k) q)) : localSup (fun x => marginal h r k x n) (r k) p = 0 := by
  apply le_antisymm _ (marginal_localSup_nonneg h r k hr p n)
  apply localSup_le hr.le p
  intro y hy
  have hqp : boxNorm (point (r k) p-point (r k) q) ≤ 20*r k := by
    rw [boxNorm_sub_comm]
    exact (mem_window_iff hr 20 p q).mp (mem_filter.mp hq).2
  have hb := boxNorm_add_le (y-point (r k) p) (point (r k) p-point (r k) q)
  rw [sub_add_sub_cancel] at hb
  have hy' : boxNorm (y-point (r k) p) ≤ 25*r k := hy
  rw [marginal_bad_zero h r k hr q (by linarith) hE n hn]

/-- The actual bad-root charge is paid by geometric energy, not a separately
assumed probability budget. -/
lemma marginal_badPrice_bound {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (base : ℝ)
    (k j : ℕ) (hr : 0 < r k) (hrj : r k = scale base j) (p : ℤ × ℤ) (n : Label) :
    localSup (fun x => marginal h r k x n) (r k) p*badPrice h base j (cellRoots N p) n ≤
      1000000*∑ q ∈ cellRoots N p, scalarMass h (r k) q*energy h (r k) q := by
  classical
  have hp0 := marginal_localSup_nonneg h r k hr p n
  have hp1 := marginal_localSup_le_one h r k hr p n
  unfold badPrice
  rw [mul_sum]
  calc
    _ ≤ ∑ q ∈ badRoots h base j (cellRoots N p) n,
        1000000*(scalarMass h (r k) q*energy h (r k) q) := by
      apply sum_le_sum
      intro q hq
      have hqp := (mem_filter.mp hq).1
      have hbad : ¬Good (n:ℂ) (theta h (r k) q) := by
        simpa only [hrj] using (mem_filter.mp hq).2
      rw [← hrj]
      by_cases hE : energy h (r k) q ≤ (1/1000:ℝ)^2
      · rw [marginal_localSup_bad_zero h r k hr p q hqp hE n hbad,zero_mul]
        exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _))
      · have he : 1 ≤ 1000000*energy h (r k) q := by norm_num at hE; linarith
        have hb := mul_le_mul_of_nonneg_right hp1 (norm_nonneg (vectorMass h (r k) q))
        have hc := mul_le_mul_of_nonneg_right he (norm_nonneg (vectorMass h (r k) q))
        dsimp only [scalarMass] at ⊢
        nlinarith
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ =>
        mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)))
end ActualLabels

namespace PhysicalCells
open DyadicHats Finset

/-- Measurable full-lattice patch; no choice of maximizing radius occurs. -/
def patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  ∑' p, (cell (point r p) r).indicator (F p) x

lemma patch_measurable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    Measurable (patch r F) :=
  Measurable.tsum (fun p => (hF p).indicator (cell_measurable _ _))

lemma le_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) : F p x ≤ patch r F x := by
  have he := ENNReal.le_tsum (f := fun q => (cell (point r q) r).indicator (F q) x) p
  simpa only [patch,Set.indicator_of_mem hx] using he

lemma lintegral_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    (∫⁻ x, patch r F x) = ∑' p, ∫⁻ x in cell (point r p) r, F p x := by
  simp only [patch]
  rw [lintegral_tsum (f := fun p x => (cell (point r p) r).indicator (F p) x) (fun p => ((hF p).indicator (cell_measurable _ _)).aemeasurable)]
  simp_rw [lintegral_indicator (cell_measurable _ _)]

lemma lintegral_patch_budget (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (B : (ℤ × ℤ) → ℝ) (hB : ∀ p, 0 ≤ B p) (A : ℝ)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hbudget : ∀ P : Finset (ℤ × ℤ), ∑ p ∈ P, B p ≤ A) :
    (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A := by
  rw [lintegral_patch r F hF]
  exact (ENNReal.tsum_le_tsum hcell).trans (tsum_ofReal_le B hB A hbudget)

lemma patch_finite (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    ∀ᵐ x, patch r F x ≠ ⊤ := by
  exact (ae_lt_top (patch_measurable r F hF) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)).mono
    (fun _ hx => hx.ne)

lemma patch_integrable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    Integrable (fun x => (patch r F x).toReal) :=
  integrable_toReal_of_lintegral_ne_top (patch_measurable r F hF).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)

lemma real_le_patch {r : ℝ} (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) (hf : patch r F x ≠ ⊤) {a : ℝ}
    (hb : ENNReal.ofReal a ≤ F p x) : a ≤ (patch r F x).toReal := by
  exact (le_max_left a 0).trans (by
    rw [← ENNReal.toReal_ofReal']
    exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hf).mpr (hb.trans (le_patch r F p hx)))

/-- Take the cell supremum of a weight only after the local price has been
proved. This bounds all three spatial budgets by the corresponding local prices. -/
lemma weighted_patch_bound (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (W : ℂ → ℝ≥0∞) (hW : Measurable W) (A B : (ℤ × ℤ) → ℝ)
    (hA : ∀ p, 0 ≤ A p) (_hB : ∀ p, 0 ≤ B p)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hWB : ∀ p x, x ∈ cell (point r p) r → W x ≤ ENNReal.ofReal (A p)) :
    (∫⁻ x, W x*patch r F x) ≤ ∑' p, ENNReal.ofReal (A p*B p) := by
  simp only [patch,← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun p x => W x*(cell (point r p) r).indicator (F p) x) (fun p => (hW.mul ((hF p).indicator (cell_measurable _ _))).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro p
  have he : (fun x => W x*(cell (point r p) r).indicator (F p) x) =
      (cell (point r p) r).indicator (fun x => W x*F p x) := by
    funext x
    by_cases hx : x ∈ cell (point r p) r <;> simp [hx]
  rw [he,lintegral_indicator (cell_measurable _ _)]
  calc
    _ ≤ ∫⁻ x in cell (point r p) r, ENNReal.ofReal (A p)*F p x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (cell_measurable (point r p) r)] with x hx
      exact mul_le_mul' (hWB p x hx) le_rfl
    _ = ENNReal.ofReal (A p)*(∫⁻ x in cell (point r p) r, F p x) :=
      lintegral_const_mul _ (hF p)
    _ ≤ ENNReal.ofReal (A p)*ENNReal.ofReal (B p) := mul_le_mul' le_rfl (hcell p)
    _ = _ := (ENNReal.ofReal_mul (hA p)).symm
end PhysicalCells

namespace ActualLabels
open DyadicHats FiniteLabels GeometricFilter Finset

/-- Global geometric extension of the finite descending radius grid. -/
def geometricRadii (base : ℝ) (m : ℕ) (k : ℕ) : ℝ := scale base m/(2:ℝ)^k
lemma geometricRadii_pos {base : ℝ} (hb : 0 < base) (m k : ℕ) :
    0 < geometricRadii base m k := div_pos (scale_pos hb m) (by positivity)
lemma geometricRadii_step (base : ℝ) (m k : ℕ) :
    2*geometricRadii base m (k+1) = geometricRadii base m k := by
  unfold geometricRadii
  rw [pow_succ]
  field_simp
lemma geometricRadii_eq (base : ℝ) {m k : ℕ} (hk : k ≤ m) :
    geometricRadii base m k = scale base (m-k) := by
  unfold geometricRadii scale
  rw [show m = (m-k)+k by omega,pow_add]
  field_simp
  rw [show m-k+k-k = m-k by omega]
  ring

lemma marginal_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : marginal h r k x = marginal h s k x := by
  induction k with
  | zero => simp only [marginal,hrs 0 le_rfl]
  | succ k ih =>
    simp only [marginal,hrs (k+1) le_rfl,ih (fun i hi => hrs i (by omega))]

lemma switchCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : switchCost h r x k = switchCost h s x k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [switchCost,hrs (k+1) le_rfl,marginal_congr h r s k (fun i hi => hrs i (by omega)) x]

lemma derivativeCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : derivativeCost h r x k = derivativeCost h s x k := by
  cases k with
  | zero => simp only [derivativeCost,hrs 0 le_rfl]
  | succ k =>
    simp only [derivativeCost,hrs (k+1) le_rfl,marginal_congr h r s k (fun i hi => hrs i (by omega)) x]

lemma cellCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (m l : ℕ) (hl : l ≤ m)
    (hrs : ∀ i, i ≤ m → r i = s i) (q : ℤ × ℤ) : cellCost h r m l q = cellCost h s m l q := by
  have hsw (i : ℕ) (hi : i ≤ m) : (fun x => switchCost h r x i) = fun x => switchCost h s x i := by
    funext x
    exact switchCost_congr h r s i (fun j hj => hrs j (by omega)) x
  have hdc (i : ℕ) (hi : i ≤ m) : (fun x => derivativeCost h r x i) = fun x => derivativeCost h s x i := by
    funext x
    exact derivativeCost_congr h r s i (fun j hj => hrs j (by omega)) x
  unfold cellCost
  rw [hrs l hl,hsw l hl]
  congr 1
  · split_ifs with he
    · rfl
    · rw [hsw (l+1) (by omega)]
  · rw [filt_sum,filt_sum]
    apply sum_congr rfl
    intro i hi
    rw [hdc i (by have := mem_range.mp hi; omega)]
end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels Finset DiskMoments PhysicalCells SignedAssembly

lemma run_cone_bound {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (x : ℂ) (n : Label) (p : List Label)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    ((runs (n::p)).map fun a => coneContribution a.dir (gradient (runEnvelope g r a.first a.last) x)).sum ≤
      divergence (fun y => potential g r y (n::p)) x+
      ((runs (n::p)).map fun a => J a.first).sum+
      ((runs (n::p)).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum+
      2*((runs (n::p)).map fun a => J a.first+J a.last).sum := by
  rw [potential_divergence hg hc hr (n::p) x hd]
  rw [← List.sum_map_mul_left,← List.sum_map_add,← List.sum_map_add,← List.sum_map_add]
  apply List.sum_le_sum
  intro a ha
  have hab := runs_bounds n p a ha
  have hu := run_unfavorable_bound hg hc hr hstep H J hH hJ x a.dir hab.1
    (hd _ _ hab.1) (hinterior · a.dir ·) hend
  have hb := hend a.first (r a.first) ⟨⟨le_rfl,by linarith [hr a.first]⟩,Or.inl rfl⟩
  have hi := real_inner_le_norm (a.dir:ℂ) (gradient (fun y => signedAverage g y (r a.first)) x)
  rw [label_unit,one_mul] at hi
  simp only [inner_sub_right]
  unfold coneContribution unfavorable at *
  linarith

/-- Complete pointwise signed assembly, still retaining the divergence term.
The remaining terms are exactly the direct directional and boundary costs. -/
theorem pointwise_signed_master {g : ℂ → ℝ} (h : ℂ → ℂ) {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (old : Label) (m : ℕ) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    ‖gradient (runEnvelope g r 0 m) x‖ ≤ 12*(
      leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) (m+1) []+
      (∑ k ∈ range (m+1), expect (marginal h r k x) (H k))+
      3*(∑ k ∈ range (m+1), boundaryCost h r x m k*J k)) := by
  have hh := leafSum_mono
    (fun q => weight h r old x q*((runs q).map fun a => coneContribution a.dir
      (gradient (runEnvelope g r a.first a.last) x)).sum)
    (fun q => weight h r old x q*divergence (fun y => potential g r y q) x+
      weight h r old x q*((runs q).map fun a => J a.first).sum+
      weight h r old x q*((runs q).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum+
      2*(weight h r old x q*((runs q).map fun a => J a.first+J a.last).sum)) (m+1) [] (by
        intro q hq
        cases q with
        | nil => simp at hq
        | cons n p =>
          have hh := mul_le_mul_of_nonneg_left
            (run_cone_bound hg hc hr hstep H J hH hJ x n p hd hinterior hend)
            (weight_nonneg h r old x (n::p))
          nlinarith only [hh])
  rw [leafSum_add,leafSum_add,leafSum_add,leafSum_const_mul,expected_span_sum] at hh
  have hb := expected_boundary_sum_bound h r old x J hJ m
  have hs := expected_start_sum_bound h r old x J hJ m
  have hsb : (∑ k ∈ range (m+1), switchCost h r x k*J k) ≤
      ∑ k ∈ range (m+1), boundaryCost h r x m k*J k := by
    apply sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (hJ k)
    unfold boundaryCost
    have hn : 0 ≤ if k=m then (1:ℝ) else switchCost h r x (k+1) := by
      split_ifs
      · exact zero_le_one
      · exact switchCost_nonneg h r x (k+1)
    linarith
  have hm := expected_run_master g h r hg hc hr hstep old m x hd
  linarith
end SignedRuns

namespace PhysicalCells
open DyadicHats
lemma center_mem_cell (p : ℂ) (r : ℝ) : p ∈ cell p r := by
  simp [cell,toUnit,unitCell]
noncomputable def cellSup (f : ℂ → ℝ) (r : ℝ) (p : ℤ × ℤ) : ℝ :=
  sSup (f '' cell (point r p) r)
lemma cellSup_le {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h : ∀ x ∈ cell (point r p) r, f x ≤ A) : cellSup f r p ≤ A := by
  apply csSup_le (Set.Nonempty.image f ⟨point r p,center_mem_cell _ _⟩)
  rintro z ⟨x,hx,rfl⟩
  exact h x hx
lemma le_cellSup {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h : ∀ x ∈ cell (point r p) r, f x ≤ A) {x : ℂ} (hx : x ∈ cell (point r p) r) :
    f x ≤ cellSup f r p := le_csSup ⟨A,by rintro z ⟨y,hy,rfl⟩; exact h y hy⟩ ⟨x,hx,rfl⟩
lemma cellSup_nonneg {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h0 : ∀ x, 0 ≤ f x) (h : ∀ x ∈ cell (point r p) r, f x ≤ A) : 0 ≤ cellSup f r p :=
  (h0 (point r p)).trans (le_cellSup p h (center_mem_cell _ _))
end PhysicalCells

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset

def pointCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (m k : ℕ) : ℝ :=
  boundaryCost h r x m k+filt (fun i => derivativeCost h r x i) k

def costLimit : ℝ := 2+32*(Fintype.card Label:ℝ)
lemma costLimit_pos : 0 < costLimit := by dsimp [costLimit]; positivity
lemma pointCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (x : ℂ) (m k : ℕ) :
    0 ≤ pointCost h r x m k := add_nonneg (boundaryCost_nonneg h r x m k)
      (filt_nonneg (fun i => derivativeCost_nonneg h r x i (hr i).le) k)
lemma pointCost_le (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (x : ℂ) (m k : ℕ) :
    pointCost h r x m k ≤ costLimit := by
  have hs0 := switchCost_le_one h r x k
  have hs1 := switchCost_le_one h r x (k+1)
  have ht := filt_le (by positivity : (0:ℝ) ≤ 16*(Fintype.card Label:ℝ))
    (fun i => derivativeCost_uniform h r x i (hr i)) k
  dsimp [pointCost,boundaryCost,costLimit]
  split_ifs <;> linarith

lemma pointCost_le_cellCost (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (q : ℤ × ℤ) (x : ℂ) (hx : x ∈ neighborhood (r k) q) :
    pointCost h r x m k ≤ cellCost h r m k q := by
  have hs (i : ℕ) : switchCost h r x i ≤ localSup (fun y => switchCost h r y i) (r k) q :=
    le_localSup q (fun y _ => switchCost_le_one h r y i) hx
  have ht (i : ℕ) : derivativeCost h r x i ≤ localSup (fun y => derivativeCost h r y i) (r k) q :=
    le_localSup q (fun y _ => derivativeCost_uniform h r y i (hr i)) hx
  have hf := filt_mono ht k
  dsimp [pointCost,boundaryCost,cellCost]
  split_ifs <;> linarith [hs k,hs (k+1)]

lemma cellSup_pointCost_le {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p) :
    cellSup (fun x => pointCost h r x m k) (r k) p ≤ cellCost h r m k q := by
  apply cellSup_le p
  intro x hx
  exact pointCost_le_cellCost h r hr m k q x (cell_subset_root_neighborhood (hr k) p q hq hx)

lemma cellSup_pointCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) : 0 ≤ cellSup (fun x => pointCost h r x m k) (r k) p :=
  cellSup_nonneg p (fun x => pointCost_nonneg h r hr x m k) (fun x _ => pointCost_le h r hr x m k)
lemma cellSup_pointCost_uniform (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) : cellSup (fun x => pointCost h r x m k) (r k) p ≤ costLimit :=
  cellSup_le p (fun x _ => pointCost_le h r hr x m k)

lemma pointCost_cell_budget {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (base : ℝ) (m k j : ℕ) (hrj : r k = scale base j) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellSup (fun x => pointCost h r x m k) (r k) p*
      rootMass h base j (cellRoots N p)) ≤
        1681*∑ q : Grid N, scalarMass h (r k) q*cellCost h r m k q := by
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ cellRoots N p, scalarMass h (r k) q*cellCost h r m k q := by
      apply sum_le_sum
      intro p _
      unfold rootMass
      rw [mul_sum]
      apply sum_le_sum
      intro q hq
      rw [← hrj,mul_comm]
      exact mul_le_mul_of_nonneg_left (cellSup_pointCost_le h r hr m k p q hq) (norm_nonneg _)
    _ ≤ _ := cellRoots_budget _ (fun q => mul_nonneg (norm_nonneg _) (cellCost_nonneg h r hr m k q)) P
end ActualLabels

end SignedDisk

end

end OAI
