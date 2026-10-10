import OAI.Analysis.CircleDomains.Rigidity.TraceMaskLinePayment

namespace OAI

/-! Spatial payment needs only an almost-everywhere density bound. This
version applies to the actual L² sum furnished by ball synthesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem trace_primitive_line_payment_ae
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P : ℝ → ℝ} {L R : ℝ}
    (hg : ∀ j, IntervalIntegrable (g j) volume L R) (hP : IntervalIntegrable P volume L R)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n, ∀ᵐ s ∂volume.restrict (uIoc L R),
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
        exact ae_restrict_of_ae_restrict_of_subset hsub (hdom n)
  exact le_of_tendsto
    (((finiteTracePrimitive_tendsto hc hI x a t).sub
      (finiteTracePrimitive_tendsto hc hI y a t)).abs)
    (Eventually.of_forall hfinite)

 theorem masked_scalar_ACL_of_line_payment_ae
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P Q b : ℝ → ℝ} {L R : ℝ}
    (hg : ∀ j, IntervalIntegrable (g j) volume L R)
    (hP : IntervalIntegrable P volume L R) (hQ : IntervalIntegrable Q volume L R)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n, ∀ᵐ s ∂volume.restrict (uIoc L R),
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
    trace_primitive_line_payment_ae hc hI hIf hg hP hcut hdom a t hx hy)).trans
    (add_le_add (hb x hx y hy) le_rfl)

 theorem masked_scalar_derivative_of_line_payment_ae
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P Q b : ℝ → ℝ} {L R : ℝ} (hLR : L ≤ R)
    (hg : ∀ j, IntervalIntegrable (g j) volume L R)
    (hP : IntervalIntegrable P volume L R) (hQ : IntervalIntegrable Q volume L R)
    (hnonneg : ∀ᵐ x ∂volume.restrict (Icc L R), 0 ≤ Q x+P x)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n, ∀ᵐ s ∂volume.restrict (uIoc L R),
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
    trace_primitive_line_payment_ae hc hI hIf hg hP hcut hdom a t hx' hy')).trans
    (add_le_add (hb x hx' y hy') le_rfl)

end CircleDomainRigidity

end

end OAI
