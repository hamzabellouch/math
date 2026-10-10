import OAI.Analysis.SignedDisk.DiskMaximalTools2

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

namespace PhysicalCells
lemma derivative_majorant_integral {F : ℂ → ℝ≥0∞} {C P : ℝ} (p : ℂ) {r : ℝ}
    (hr : 0 < r) (hF : (∫⁻ X in unitCell, F X) ≤ ENNReal.ofReal (C*r⁻¹*P)) :
    (∫⁻ y in cell p r, ENNReal.ofReal r⁻¹*F (toUnit p r y)) ≤ ENNReal.ofReal (C*P) := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,cell_majorant p hr.ne']
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hF)).trans_eq
  rw [← ENNReal.ofReal_mul (sq_nonneg r),← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  field_simp

lemma value_majorant_integral {F : ℂ → ℝ≥0∞} {C P : ℝ} (p : ℂ) {r : ℝ}
    (hr : 0 < r) (hF : (∫⁻ X in unitCell, F X) ≤ ENNReal.ofReal (C*r⁻¹*P)) :
    (∫⁻ y in cell p r, F (toUnit p r y)) ≤ ENNReal.ofReal (C*r*P) := by
  rw [cell_majorant p hr.ne']
  apply (mul_le_mul' le_rfl hF).trans_eq
  rw [← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  field_simp
end PhysicalCells

namespace DiskMoments
lemma average_gradient_norm_le {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖gradient (fun y => signedAverage g y t) x‖ ≤ ‖∫ y in Metric.ball x t, gradient g y‖ := by
  have hp : 0 < Real.pi*t^2 := mul_pos Real.pi_pos (sq_pos_of_pos (by linarith))
  have h1 : 1 ≤ Real.pi*t^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (t-1)]
  rw [gradient_signedAverage hg hD x (by linarith),norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ hp).mpr h1)

lemma average_gradient_negative_le {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x n : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    max 0 (-inner ℝ n (gradient (fun y => signedAverage g y t) x)) ≤
      max 0 (-inner ℝ n (∫ y in Metric.ball x t, gradient g y)) := by
  have hp : 0 < Real.pi*t^2 := mul_pos Real.pi_pos (sq_pos_of_pos (by linarith))
  have h1 : 1 ≤ Real.pi*t^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (t-1)]
  rw [gradient_signedAverage hg hD x (by linarith),inner_smul_right,← mul_neg,
    ← mul_zero (Real.pi*t^2)⁻¹,← mul_max_of_nonneg _ _ (inv_nonneg.mpr hp.le)]
  simp only [mul_zero]
  exact mul_le_of_le_one_left (le_max_left _ _) ((inv_le_one₀ hp).mpr h1)

lemma physical_gradient_norm_majorant {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    {F : ℝ≥0∞}
    (hF : ENNReal.ofReal ‖gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X‖ ≤ F) :
    ENNReal.ofReal ‖gradient (fun y => signedAverage g y (r*t)) (p+r • X)‖ ≤
      ENNReal.ofReal r⁻¹*F := by
  have h : ENNReal.ofReal r⁻¹*_ ≤ ENNReal.ofReal r⁻¹*F := mul_le_mul' le_rfl hF
  rw [gradient_average_affine hg hD p X hr ht,norm_smul,Real.norm_eq_abs,abs_of_pos hr,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),inv_mul_cancel_left₀ hr.ne'] at h
  exact h

lemma physical_gradient_negative_majorant {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X n : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    {F : ℝ≥0∞}
    (hF : ENNReal.ofReal (max 0 (-inner ℝ n
      (gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X))) ≤ F) :
    ENNReal.ofReal (max 0 (-inner ℝ n (gradient (fun y => signedAverage g y (r*t)) (p+r • X)))) ≤
      ENNReal.ofReal r⁻¹*F := by
  have h : ENNReal.ofReal r⁻¹*_ ≤ ENNReal.ofReal r⁻¹*F := mul_le_mul' le_rfl hF
  rw [gradient_average_affine hg hD p X hr ht,inner_smul_right,← mul_neg,
    ← mul_zero r,← mul_max_of_nonneg _ _ hr.le,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),inv_mul_cancel_left₀ hr.ne'] at h
  simpa only [mul_zero] using h
end DiskMoments

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces PhysicalCells

theorem physical_directional_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ {s : ℝ}, (s = 1 ∨ s = -1) →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalNeighborhoodRadius g (scale r k) y t →
        ENNReal.ofReal (max 0 (-inner ℝ (axis n s) (gradient (fun z => signedAverage g z t) y))) ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := directional_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn s hs
  obtain ⟨D,hD⟩ := hD
  obtain ⟨D',hD'⟩ := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp k p hn hs unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => ENNReal.ofReal (scale r k)⁻¹*F (toUnit (point (scale r k) p) (scale r k) y),
    measurable_const.mul (hFm.comp (toUnit_continuous _ _).measurable),
    derivative_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t ht
  let X := toUnit (point (scale r k) p) (scale r k) y
  have hX : ‖X‖ ≤ 2 := norm_unitCell hy
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have ht' : PhysicalNeighborhoodRadius g (scale r k)
      (point (scale r k) p+scale r k • X) (scale r k*(t/scale r k)) := by
    simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using ht
  have htn := neighborhoodRadius_affine _ X (scale_pos hr k) ht'
  have hg' : ContDiff ℝ 1 (fun Z => g (point (scale r k) p+scale r k • Z)) := hg.comp (by fun_prop)
  have hb := (ENNReal.ofReal_le_ofReal (average_gradient_negative_le hg' hD' X (axis n s) htn.1.1)).trans
    (hFb X hX _ htn)
  have hf := physical_gradient_negative_majorant hg hD (point (scale r k) p) X (axis n s)
    (scale_pos hr k) (by linarith [htn.1.1]) hb
  simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using hf

theorem physical_size_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalEndpointRadius g (scale r k) y t →
        ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := size_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn
  obtain ⟨D,hD⟩ := hD
  obtain ⟨D',hD'⟩ := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp k p hn unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => ENNReal.ofReal (scale r k)⁻¹*F (toUnit (point (scale r k) p) (scale r k) y),
    measurable_const.mul (hFm.comp (toUnit_continuous _ _).measurable),
    derivative_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t ht
  let X := toUnit (point (scale r k) p) (scale r k) y
  have hX : ‖X‖ ≤ 2 := norm_unitCell hy
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have ht' : PhysicalEndpointRadius g (scale r k)
      (point (scale r k) p+scale r k • X) (scale r k*(t/scale r k)) := by
    simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using ht
  have htn := endpointRadius_affine _ X (scale_pos hr k) ht'
  have hg' : ContDiff ℝ 1 (fun Z => g (point (scale r k) p+scale r k • Z)) := hg.comp (by fun_prop)
  have hb := (ENNReal.ofReal_le_ofReal (average_gradient_norm_le hg' hD' X htn.1.1)).trans
    (hFb X hX _ htn)
  have hf := physical_gradient_norm_majorant hg hD (point (scale r k) p) X
    (scale_pos hr k) (by linarith [htn.1.1]) hb
  simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using hf

theorem physical_value_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*scale r k*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t t',
        0 < t → t ≤ 4*scale r k → 0 < t' → t' ≤ 4*scale r k →
        ENNReal.ofReal |signedAverage g y t-signedAverage g y t'| ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := value_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp hD k p hn unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => F (toUnit (point (scale r k) p) (scale r k) y),
    hFm.comp (toUnit_continuous _ _).measurable,
    value_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t t' ht hb ht' hb'
  let X := toUnit (point (scale r k) p) (scale r k) y
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have hrk := scale_pos hr k
  have hf := hFb X (norm_unitCell hy) (t/scale r k) (t'/scale r k)
    (div_pos ht hrk) ((div_le_iff₀ hrk).mpr hb) (div_pos ht' hrk) ((div_le_iff₀ hrk).mpr hb')
  simpa only [signedAverage_affine _ _ _ hrk (div_pos ht hrk),
    signedAverage_affine _ _ _ hrk (div_pos ht' hrk),he,mul_div_cancel₀ _ hrk.ne'] using hf
end CommonPrices

namespace DiskMoments
lemma signedAverage_abs_le {g : ℂ → ℝ} {M : ℝ} (hM : ∀ y, |g y| ≤ M)
    (x : ℂ) {t : ℝ} (ht : 0 < t) : |signedAverage g x t| ≤ M := by
  rw [signedAverage_fixedDomain g x ht,abs_div,abs_of_pos Real.pi_pos]
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) 1)) := ⟨by simp⟩
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (Metric.ball (0:ℂ) 1))
    (C := M) (f := fun z : ℂ => g (x+t • z)) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hM (x+t • z)))
  have hv : (volume.restrict (Metric.ball (0:ℂ) 1)).real univ = Real.pi := by
    simp [measureReal_def,Complex.volume_ball]
  rw [hv,Real.norm_eq_abs] at hi
  exact (div_le_iff₀ Real.pi_pos).mpr hi

def oscillationSet (g : ℂ → ℝ) (r : ℝ) (x : ℂ) : Set ℝ :=
  {a | ∃ t t', 0 < t ∧ t ≤ 4*r ∧ 0 < t' ∧ t' ≤ 4*r ∧ a = |signedAverage g x t-signedAverage g x t'|}
def oscillation (g : ℂ → ℝ) (r : ℝ) (x : ℂ) : ℝ := sSup (oscillationSet g r x)

lemma oscillationSet_zero (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    0 ∈ oscillationSet g r x := ⟨r,r,hr,by linarith,hr,by linarith,by simp⟩
lemma oscillationSet_bdd {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) (r : ℝ) (x : ℂ) :
    BddAbove (oscillationSet g r x) := by
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hg
  refine ⟨2*M,?_⟩
  rintro a ⟨t,t',ht,_,ht',_,rfl⟩
  have hb : ∀ y, |g y| ≤ M := by simpa only [Real.norm_eq_abs] using hM
  have h1 := signedAverage_abs_le hb x ht
  have h2 := signedAverage_abs_le hb x ht'
  linarith [abs_sub (signedAverage g x t) (signedAverage g x t')]
lemma oscillation_nonneg {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) {r : ℝ}
    (hr : 0 < r) (x : ℂ) : 0 ≤ oscillation g r x :=
  le_csSup (oscillationSet_bdd hg hc r x) (oscillationSet_zero g hr x)
lemma le_oscillation {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) {r : ℝ}
    (x : ℂ) {t t' : ℝ} (ht : 0 < t) (hb : t ≤ 4*r) (ht' : 0 < t') (hb' : t' ≤ 4*r) :
    |signedAverage g x t-signedAverage g x t'| ≤ oscillation g r x :=
  le_csSup (oscillationSet_bdd hg hc r x) ⟨t,t',ht,hb,ht',hb',rfl⟩
lemma oscillation_majorant {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (x : ℂ) {F : ℝ≥0∞}
    (hF : ∀ t t', 0 < t → t ≤ 4*r → 0 < t' → t' ≤ 4*r →
      ENNReal.ofReal |signedAverage g x t-signedAverage g x t'| ≤ F) :
    ENNReal.ofReal (oscillation g r x) ≤ F := by
  by_cases htop : F = ⊤
  · simp only [htop,le_top]
  · apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
    apply csSup_le ⟨0,oscillationSet_zero g hr x⟩
    rintro a ⟨t,t',ht,hb,ht',hb',rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp (hF t t' ht hb ht' hb')
end DiskMoments

namespace SignedRuns

section
open DiskMoments RadiusEnvelope ActualLabels Finset

variable (g : ℂ → ℝ) (r : ℕ → ℝ)
def runEnvelope (i j : ℕ) (x : ℂ) : ℝ :=
  envelope (fun t y => signedAverage g y t) (r j) (2*r i) x

lemma radius_antitone (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k) : Antitone r := by
  apply antitone_nat_of_succ_le
  intro k
  have := hr (k+1)
  linarith [hstep k]

lemma runEnvelope_attains (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) {i j : ℕ} (hij : i ≤ j) (x : ℂ) :
    ∃ t ∈ Icc (r j) (2*r i), runEnvelope g r i j x = signedAverage g x t ∧
      ∀ s ∈ Icc (r j) (2*r i), signedAverage g x s ≤ signedAverage g x t := by
  apply attains _ x (signedAverage_radius_continuousOn hg x (hr j))
  have := radius_antitone r hr hstep hij
  linarith [hr i]

lemma runEnvelope_le_next (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) {i j : ℕ} (hij : i ≤ j) (x : ℂ) :
    runEnvelope g r i j x ≤ runEnvelope g r i (j+1) x := by
  obtain ⟨t,ht,he,_⟩ := runEnvelope_attains g r hg hr hstep hij x
  rw [he]
  apply le_envelope ⟨(radius_antitone r hr hstep (Nat.le_succ j)).trans ht.1,ht.2⟩ x
    (signedAverage_radius_continuousOn hg x (hr (j+1)))

lemma runEnvelope_extension_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) {i j : ℕ} (hij : i ≤ j) (x : ℂ) {V : ℝ}
    (hV : ∀ t t', 0 < t → t ≤ 4*r (j+1) → 0 < t' → t' ≤ 4*r (j+1) →
      |signedAverage g x t-signedAverage g x t'| ≤ V) :
    |runEnvelope g r i (j+1) x-runEnvelope g r i j x| ≤ V := by
  have hV0 : 0 ≤ V := by
    have hh := hr (j+1)
    simpa using hV (r (j+1)) (r (j+1)) hh (by linarith) hh (by linarith)
  have h0 := runEnvelope_le_next g r hg hr hstep hij x
  rw [abs_of_nonneg (sub_nonneg.mpr h0)]
  obtain ⟨t,ht,he,_⟩ := runEnvelope_attains g r hg hr hstep (hij.trans (Nat.le_succ j)) x
  rw [he]
  by_cases htj : r j ≤ t
  · have hh := le_envelope (u := fun t y => signedAverage g y t) ⟨htj,ht.2⟩ x
      (signedAverage_radius_continuousOn hg x (hr j))
    change signedAverage g x t ≤ runEnvelope g r i j x at hh
    linarith
  · have hb : signedAverage g x (r j) ≤ runEnvelope g r i j x := by
      change signedAverage g x (r j) ≤ envelope (fun t y => signedAverage g y t) (r j) (2*r i) x
      apply le_envelope (u := fun t y => signedAverage g y t) (a := r j) (b := 2*r i) (r := r j) ⟨le_rfl,?_⟩ x (signedAverage_radius_continuousOn hg x (hr j))
      have := radius_antitone r hr hstep hij
      linarith [hr i]
    have hh := hV t (r j) ((hr (j+1)).trans_le ht.1)
      (by linarith [hstep j,hr (j+1)]) (hr j) (by linarith [hstep j,hr (j+1)])
    linarith [le_abs_self (signedAverage g x t-signedAverage g x (r j))]

lemma runEnvelope_new_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (j : ℕ) (x : ℂ) {V : ℝ}
    (hV : ∀ t t', 0 < t → t ≤ 4*r j → 0 < t' → t' ≤ 4*r j →
      |signedAverage g x t-signedAverage g x t'| ≤ V) :
    |runEnvelope g r j j x-signedAverage g x (r j)| ≤ V := by
  obtain ⟨t,ht,he,_⟩ := runEnvelope_attains g r hg hr hstep le_rfl x
  rw [he]
  exact hV t (r j) ((hr j).trans_le ht.1) (by linarith [hr j,ht.2]) (hr j) (by linarith [hr j])

/-- Reversed chronological histories. The active run's start is retained when
its new label agrees, and is reset to the new time at a switch. -/
def activeStart : List Label → ℕ
  | [] => 0
  | [_] => 0
  | n::old::p => if n = old then activeStart (old::p) else (old::p).length

lemma activeStart_le (n : Label) (p : List Label) : activeStart (n::p) ≤ p.length := by
  induction p generalizing n with
  | nil => simp [activeStart]
  | cons old p ih =>
    dsimp only [activeStart]
    split_ifs
    · exact (ih old).trans (by simp)
    · rfl

/-- The exact closed-prefix vector potential, updated without ever taking the
absolute size of an old large-radius envelope. -/
def potential (x : ℂ) : List Label → ℂ
  | [] => 0
  | [n] => (runEnvelope g r 0 0 x-signedAverage g x (r 0)) • (n:ℂ)
  | n::old::p => potential x (old::p)+
      (if n = old then (runEnvelope g r (activeStart (old::p)) (p.length+1) x-
        runEnvelope g r (activeStart (old::p)) p.length x) • (n:ℂ)
      else (runEnvelope g r (p.length+1) (p.length+1) x-
        signedAverage g x (r (p.length+1))) • (n:ℂ))

lemma potential_increment (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (x : ℂ) (v : ℕ → ℝ)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ v k)
    (n : Label) (p : List Label) : ‖potential g r x (n::p)-potential g r x p‖ ≤ v p.length := by
  cases p with
  | nil =>
    simp only [potential,List.length_nil,sub_zero,norm_smul,Real.norm_eq_abs,label_unit,mul_one]
    exact runEnvelope_new_bound g r hg hr hstep 0 x (hv 0)
  | cons old p =>
    simp only [potential,add_sub_cancel_left,List.length_cons]
    split_ifs
    · simp only [norm_smul,Real.norm_eq_abs,label_unit,mul_one]
      exact runEnvelope_extension_bound g r hg hr hstep (activeStart_le old p) x (hv (p.length+1))
    · simp only [norm_smul,Real.norm_eq_abs,label_unit,mul_one]
      exact runEnvelope_new_bound g r hg hr hstep (p.length+1) x (hv (p.length+1))

theorem potential_continuation_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (x : ℂ) (v : ℕ → ℝ)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ v k)
    (p q : List Label) : ‖potential g r x (q++p)-potential g r x p‖ ≤
      ∑ k ∈ Ico p.length (p.length+q.length), v k := by
  induction q with
  | nil => simp
  | cons n q ih =>
    have htri : ‖potential g r x ((n::q)++p)-potential g r x p‖ ≤
        ‖potential g r x (n::(q++p))-potential g r x (q++p)‖+
        ‖potential g r x (q++p)-potential g r x p‖ := by
      simpa only [sub_add_sub_cancel,List.cons_append] using norm_add_le
        (potential g r x (n::(q++p))-potential g r x (q++p))
        (potential g r x (q++p)-potential g r x p)
    have hi := potential_increment g r hg hr hstep x v hv n (q++p)
    apply htri.trans
    rw [List.length_cons,Nat.add_succ,sum_Ico_succ_top (by omega : p.length ≤ p.length+q.length)]
    simpa only [List.length_append,Nat.add_comm,add_comm] using add_le_add hi ih
end

open SignedAssembly FiniteLabels ActualLabels Finset

variable (g : ℂ → ℝ) (r : ℕ → ℝ) (x : ℂ)
variable (J : ℕ → Label → RowJet Label ℂ) (v : ℕ → ℝ)

/-- The actual closed-prefix potentials at the leaves, with the stochastic
row jet at every observation time. -/
def jet : ℕ → List Label → Label → JetTree Label ℂ
  | 0,p,_ => .leaf (potential g r x p)
  | d+1,p,n => .branch (J p.length n) (potential g r x p)
      (∑ k ∈ Ico p.length (p.length+d+1), v k) (fun a => jet d (a::p) a)

lemma jet_terminalBound (d : ℕ) (p : List Label) (old : Label) (c : ℂ) (B : ℝ)
    (h : ∀ q : List Label, q.length = d → ‖potential g r x (q++p)-c‖ ≤ B) :
    TerminalBound (jet g r x J v d p old) c B := by
  induction d generalizing p old with
  | zero => simpa only [jet,TerminalBound,List.nil_append] using h [] rfl
  | succ d ih =>
    intro n
    apply ih
    intro q hq
    have hh := h (q++[n]) (by simp only [List.length_append,List.length_singleton,hq])
    simpa only [List.append_assoc,List.singleton_append] using hh

lemma jet_controlled (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |DiskMoments.signedAverage g x t-DiskMoments.signedAverage g x t'| ≤ v k)
    (d : ℕ) (p : List Label) (old : Label) : Controlled (jet g r x J v d p old) := by
  induction d generalizing p old with
  | zero => trivial
  | succ d ih =>
    constructor
    · intro n
      apply jet_terminalBound
      intro q hq
      have hh := potential_continuation_bound g r hg hr hstep x v hv p (q++[n])
      simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton,hq,Nat.add_assoc] using hh
    · intro n
      exact ih (n::p) n

/-- Backward expected reward for an arbitrary time-dependent finite Markov law. -/
def rewardCost (reward : ℕ → Label → ℝ) : ℕ → ℕ → Label → ℝ
  | _,0,_ => 0
  | k,d+1,n => reward k n+expect (J k n).law (fun a => rewardCost reward (k+1) d a)

lemma jet_cost (d : ℕ) (p : List Label) (old : Label) (m : ℕ) (hm : p.length+d = m) :
    cost (jet g r x J v d p old) = rewardCost J
      (fun k n => (∑ a, ‖(J k n).grad a‖)*(∑ l ∈ Ico k m, v l)) p.length d old := by
  induction d generalizing p old with
  | zero => rfl
  | succ d ih =>
    simp only [jet,cost,rewardCost]
    have htop : p.length+d+1 = m := by omega
    rw [htop]
    congr 1
    apply sum_congr rfl
    intro a _
    rw [ih (a::p) a (by simp only [List.length_cons]; omega)]
    rfl

lemma expect_rewardCost (reward : ℕ → Label → ℝ) (μ : ℕ → Law Label)
    (hμ : ∀ k, μ (k+1) = move (μ k) (fun n => (J k n).law)) (d k : ℕ) :
    expect (μ k) (rewardCost J reward k d) =
      ∑ i ∈ Ico k (k+d), expect (μ i) (reward i) := by
  induction d generalizing k with
  | zero => simp [rewardCost,FiniteLabels.expect]
  | succ d ih =>
    change expect (μ k) (fun n => reward k n+expect (J k n).law (fun a => rewardCost J reward (k+1) d a)) = _
    rw [expect_add,← expect_move,← hμ k,ih]
    rw [sum_Ico_eq_sum_range,sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left,Nat.add_assoc,Nat.add_sub_cancel_left]
    rw [sum_range_succ']
    simp only [Nat.add_zero,Nat.add_left_comm,add_comm,Nat.add_sub_cancel_right]

/-- Signed finite-history flux with the actual run potential and the exact
forward stochastic marginal law. No old large-radius envelope is priced. -/
theorem run_signed_flux_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |DiskMoments.signedAverage g x t-DiskMoments.signedAverage g x t'| ≤ v k)
    (m : ℕ) (old : Label) (μ : ℕ → Law Label) (hμ0 : μ 0 = delta old)
    (hμ : ∀ k, μ (k+1) = move (μ k) (fun n => (J k n).law)) :
    |pathFlux (jet g r x J v m [] old) 1 0| ≤
      ∑ k ∈ range m, expect (μ k) (fun n => ∑ a, ‖(J k n).grad a‖)*
        (∑ l ∈ Ico k m, v l) := by
  have hh := signed_flux_bound _ (jet_controlled g r x J v hg hr hstep hv m [] old)
  rw [jet_cost g r x J v m [] old m (by simp)] at hh
  have he := expect_rewardCost J
    (fun k n => (∑ a, ‖(J k n).grad a‖)*(∑ l ∈ Ico k m, v l)) μ hμ m 0
  rw [hμ0,expect_delta] at he
  simp only [Nat.zero_add,Nat.Ico_zero_eq_range] at he
  simp only [List.length_nil] at hh
  rw [he] at hh
  simpa only [FiniteLabels.expect,← mul_assoc,← sum_mul] using hh
end SignedRuns

end SignedDisk

end

end OAI
