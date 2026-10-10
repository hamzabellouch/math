import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshReplicaKernel

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma truncatedFreshKernel {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) (f : ℝ →ᵇ ℝ) (r n : ℕ) (xs : Fin r→S) :
    (∫ g, ∏ i, f (truncatedCountableGaussianField v L n g (xs i)) ∂countableGaussianLaw)=
      freshReplicaMatrixKernel f r (fun i j => gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
  let rows : Fin r→EuclideanSpace ℝ (Fin n) := fun i =>
    WithLp.toLp 2 (fun j => maskedGaussianCoefficient v L j.val (xs i))
  have hg : Matrix.gram ℝ rows=(fun i j => gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
    ext i j
    change (∑ l : Fin n, maskedGaussianCoefficient v L l.val (xs j)*
      maskedGaussianCoefficient v L l.val (xs i)) = _
    unfold gaussianPrefixCovariance
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [← hg,freshReplicaMatrixKernel_gram,← gaussianRows_map_stdGaussian rows,
    integral_map (gaussianRows rows).continuous.measurable.aemeasurable
      (gaussianReplicaTest f).continuous.aestronglyMeasurable]
  rw [← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hp := gaussianCoordinatePrefix_measurePreserving n
  have hmeas : AEStronglyMeasurable (fun y : Fin n→ℝ =>
      gaussianReplicaTest f (gaussianRows rows (WithLp.toLp 2 y)))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by fun_prop
  rw [← hp.map_eq] at hmeas ⊢
  rw [integral_map hp.measurable.aemeasurable hmeas]
  apply integral_congr_ae
  exact ae_of_all _ fun g => by
    simp only [gaussianReplicaTest_apply,gaussianRows_apply]
    congr 1

lemma countableFreshKernel {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) (f : ℝ →ᵇ ℝ) (r : ℕ) (xs : Fin r→S) :
    (∫ g, ∏ i, f (countableGaussianField v L g (xs i)) ∂countableGaussianLaw)=
      freshReplicaMatrixKernel f r (fun i j => countableGaussianCovariance v v L (xs i) (xs j)) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : Fin r, ∀ g,
      truncatedCountableGaussianField v L n g (xs i)=countableGaussianField v L g (xs i) :=
    Filter.eventually_all.mpr (fun i => truncatedCountableGaussianField_eventually_eq v L (xs i))
  have hc : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn,hc⟩ := (he.and hc).exists
  have h := truncatedFreshKernel v L f r n xs
  simp_rw [hn] at h
  have hm : (fun i j => gaussianPrefixCovariance v v L n (xs i) (xs j))=
      (fun i j => countableGaussianCovariance v v L (xs i) (xs j)) := by
    funext i j; exact hc i j
  exact h.trans (congrArg (freshReplicaMatrixKernel f r) hm)

theorem countableFresh_moment {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (v : ℕ→S→ℝ) (L : S→ℕ)
    (hv : ∀ i, Measurable (v i)) (hL : Measurable L) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (∫ x, f (countableGaussianField v L g x) ∂μ)^r ∂countableGaussianLaw)=
      ∫ xs : Fin r→S, freshReplicaMatrixKernel f r
        (fun i j => countableGaussianCovariance v v L (xs i) (xs j)) ∂Measure.pi (fun _ => μ) := by
  let F : (ℕ→ℝ)×(Fin r→S)→ℝ := fun p => ∏ i, f (countableGaussianField v L p.1 (p.2 i))
  have hm : Measurable F := Finset.measurable_prod _ fun i _ =>
    f.measurable.comp ((countableGaussianField_measurable hv hL).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hb (p : (ℕ→ℝ)×(Fin r→S)) : ‖F p‖≤‖f‖^r := by
    simp only [F,norm_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => f.norm_coe_le_norm _)).trans_eq
      (by simp)
  have hi : Integrable F (countableGaussianLaw.prod (Measure.pi fun _ : Fin r => μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  calc
    _ = ∫ g, ∫ xs : Fin r→S, F (g,xs) ∂Measure.pi (fun _ => μ) ∂countableGaussianLaw := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        simpa only [F,Fintype.card_fin] using
          (integral_fintype_prod_eq_pow (ι := Fin r) (fun x : S => f (countableGaussianField v L g x)) (μ := μ)).symm
    _ = ∫ xs : Fin r→S, ∫ g, F (g,xs) ∂countableGaussianLaw ∂Measure.pi (fun _ => μ) :=
      integral_integral_swap hi
    _ = _ := integral_congr_ae (ae_of_all _ fun xs => countableFreshKernel v L f r xs)

variable {S : Type} [MeasurableSpace S] {k : ℕ}

def labelProfileRow (q : Fin (k+1)→ℝ) : ℕ→S×IndexedLeaf k→ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k
    (profileGaussianRoot (fun l (_ : Fin 1) => q l))
    (profileGaussianStep (fun l (_ : Fin 1) => q l)))
    (fun _ : S => WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))

def labelProfileField (q : Fin (k+1)→ℝ) (g : ℕ→ℝ) : S×IndexedLeaf k→ℝ :=
  countableGaussianField (labelProfileRow q) (indexedGaussianRowLength (I := Fin 1) k) g

lemma labelProfile_covariance (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance (labelProfileRow q) (labelProfileRow q)
      (indexedGaussianRowLength (I := Fin 1) k) x y = q (indexedCommonDepth k y.2 x.2) := by
  simpa only [labelProfileRow,Fin.sum_univ_one,mul_one] using
    profileGaussianRow_covariance (fun l (_ : Fin 1) => q l) (fun _ => h0) (fun _ => hq)
      (fun _ : S => WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))
      (fun _ : S => WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) x y

theorem labelProfile_fresh_moment (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (μ : Measure (S×IndexedLeaf k)) [IsProbabilityMeasure μ] (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (∫ x, f (labelProfileField q g x) ∂μ)^r ∂countableGaussianLaw)=
      ∫ xs : Fin r→S×IndexedLeaf k, freshReplicaMatrixKernel f r
        (fun i j => q (indexedCommonDepth k (xs j).2 (xs i).2)) ∂Measure.pi (fun _ => μ) := by
  have h := countableFresh_moment μ (labelProfileRow q)
    (indexedGaussianRowLength (I := Fin 1) k)
    (indexedGaussianRow_measurable _ _ measurable_const)
    (indexedGaussianRowLength_measurable k) f r
  simpa only [labelProfileField,labelProfile_covariance q h0 hq] using h

lemma labelProfileField_marked_state {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) :
    labelProfileField q g x =
      inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))
        (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark
          (profileGaussianStep (fun l (_ : Fin 1) => q l) j))) k
          ((fun _ => diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l))
            (indexedGaussianDisorder k (Fin 1) g).1),
            (indexedGaussianDisorder k (Fin 1) g).2) x.2 0) :=
  indexedGaussianRow_diagonal_identity k _ _ _ g x

end SphericalPerceptronFreeEnergy
end

end OAI
