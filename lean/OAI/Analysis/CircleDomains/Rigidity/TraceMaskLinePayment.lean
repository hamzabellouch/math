import OAI.Analysis.CircleDomains.Rigidity.TracePrimitivePlateau
import OAI.Analysis.CircleDomains.Sobolev.IncrementDerivativeBound

namespace OAI

/-! The actual mask primitive inherits line payment from its scalar
cutoffs. Finite interval-length sums are dominated by the density before
passing to the infinite mask; no differentiability of minima is used. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem infiniteTracePrimitive_lipschitz {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a : ℝ) :
    LipschitzWith 1 (infiniteTracePrimitive cutoff I a x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  apply le_of_tendsto (show Tendsto (fun n =>
      dist (finiteTracePrimitive cutoff I a x s n) (finiteTracePrimitive cutoff I a x t n))
      atTop (𝓝 (dist (infiniteTracePrimitive cutoff I a x s)
        (infiniteTracePrimitive cutoff I a x t))) from
    (finiteTracePrimitive_tendsto hc hI x a s).dist (finiteTracePrimitive_tendsto hc hI x a t))
  exact Eventually.of_forall (fun n => (finiteTracePrimitive_lipschitz hc hI x n a).dist_le_mul s t)

 theorem trace_primitive_line_payment
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P : ℝ → ℝ} {L R : ℝ}
    (hg : ∀ j, IntervalIntegrable (g j) volume L R) (hP : IntervalIntegrable P volume L R)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n s, s ∈ uIcc L R →
      ∑ j ∈ Finset.range n, volume.real (I j)*g j s ≤ P s)
    (a t : ℝ) {x y : ℝ} (hx : x ∈ uIcc L R) (hy : y ∈ uIcc L R) :
    |infiniteTracePrimitive cutoff I a x t-infiniteTracePrimitive cutoff I a y t| ≤
      ∫ s in uIoc x y, P s := by
  have hsub : uIoc x y ⊆ uIoc L R :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx hy)
  have hg' (j : ℕ) : IntegrableOn (g j) (uIoc x y) volume := (hg j).def'.mono_set hsub
  have hP' : IntegrableOn P (uIoc x y) volume := hP.def'.mono_set hsub
  have hfinite (n : ℕ) :
      |finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a y t n| ≤
        ∫ s in uIoc x y, P s := by
    apply (finiteTracePrimitive_variation hc hI hIf x y a t n).trans
    calc
      _ ≤ ∑ j ∈ Finset.range n, volume.real (I j)*(∫ s in uIoc x y, g j s) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hcut j x hx y hy) (measureReal_nonneg)
      _ = ∫ s in uIoc x y, ∑ j ∈ Finset.range n, volume.real (I j)*g j s := by
        rw [integral_finsetSum _ (fun j _ => (hg' j).const_mul _)]
        exact Finset.sum_congr rfl (fun j _ => (integral_const_mul _ _).symm)
      _ ≤ ∫ s in uIoc x y, P s := by
        apply integral_mono_ae (integrable_finsetSum _ (fun j _ => (hg' j).const_mul _)) hP'
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        exact hdom n s (uIoc_subset_uIcc (hsub hs))
  exact le_of_tendsto
    (((finiteTracePrimitive_tendsto hc hI x a t).sub
      (finiteTracePrimitive_tendsto hc hI y a t)).abs)
    (Eventually.of_forall hfinite)

 theorem masked_scalar_increment
    {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (a : ℝ) (b : X → ℝ) {x y : X} {c : ℝ}
    (hfix : ∀ t, |infiniteTracePrimitive cutoff I a x t-infiniteTracePrimitive cutoff I a y t| ≤ c) :
    |infiniteTracePrimitive cutoff I a x (b x)-infiniteTracePrimitive cutoff I a y (b y)| ≤
      |b x-b y|+c := by
  calc
    _ ≤ |infiniteTracePrimitive cutoff I a x (b x)-infiniteTracePrimitive cutoff I a x (b y)|+
        |infiniteTracePrimitive cutoff I a x (b y)-infiniteTracePrimitive cutoff I a y (b y)| :=
      abs_sub_le _ _ _
    _ ≤ |b x-b y|+c := add_le_add (by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using
        (infiniteTracePrimitive_lipschitz hc hI x a).dist_le_mul (b x) (b y)) (hfix (b y))

 theorem masked_scalar_ACL_of_line_payment
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P Q b : ℝ → ℝ} {L R : ℝ}
    (hg : ∀ j, IntervalIntegrable (g j) volume L R)
    (hP : IntervalIntegrable P volume L R) (hQ : IntervalIntegrable Q volume L R)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n s, s ∈ uIcc L R →
      ∑ j ∈ Finset.range n, volume.real (I j)*g j s ≤ P s)
    (hb : ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R, |b x-b y| ≤ ∫ s in uIoc x y, Q s)
    (a : ℝ) : AbsolutelyContinuousOnInterval
      (fun x => infiniteTracePrimitive cutoff I a x (b x)) L R := by
  apply absolutelyContinuousOnInterval_of_integral_bound (hQ.add hP)
  intro x hx y hy
  rw [Real.dist_eq,integral_add (hQ.def'.mono_set
    (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx hy)))
    (hP.def'.mono_set (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx hy)))]
  exact (masked_scalar_increment hc hI a b (fun t =>
    trace_primitive_line_payment hc hI hIf hg hP hcut hdom a t hx hy)).trans
    (add_le_add (hb x hx y hy) le_rfl)

/-- The same payment bounds the actual derivative almost everywhere. -/
 theorem masked_scalar_derivative_of_line_payment
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P Q b : ℝ → ℝ} {L R : ℝ} (hLR : L ≤ R)
    (hg : ∀ j, IntervalIntegrable (g j) volume L R)
    (hP : IntervalIntegrable P volume L R) (hQ : IntervalIntegrable Q volume L R)
    (hnonneg : ∀ᵐ x ∂volume.restrict (Icc L R), 0 ≤ Q x+P x)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n s, s ∈ uIcc L R →
      ∑ j ∈ Finset.range n, volume.real (I j)*g j s ≤ P s)
    (hb : ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R, |b x-b y| ≤ ∫ s in uIoc x y, Q s)
    (a : ℝ) : ∀ᵐ x ∂volume.restrict (Icc L R),
      |deriv (fun x => infiniteTracePrimitive cutoff I a x (b x)) x| ≤ Q x+P x := by
  apply ae_abs_deriv_le_of_integral_bound hLR (hQ.add hP) hnonneg
  intro x hx y hy
  have hx' : x ∈ uIcc L R := by simpa only [uIcc_of_le hLR] using hx
  have hy' : y ∈ uIcc L R := by simpa only [uIcc_of_le hLR] using hy
  rw [integral_add (hQ.def'.mono_set
    (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx' hy')))
    (hP.def'.mono_set (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx' hy')))]
  exact (masked_scalar_increment hc hI a b (fun t =>
    trace_primitive_line_payment hc hI hIf hg hP hcut hdom a t hx' hy')).trans
    (add_le_add (hb x hx' y hy') le_rfl)

end CircleDomainRigidity

end

end OAI
