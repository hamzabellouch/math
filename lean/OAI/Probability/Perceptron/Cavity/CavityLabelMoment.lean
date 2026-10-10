import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityDiagonalKernel

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

variable {J : Type} [Fintype J] [DecidableEq J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {k : ℕ}

def cavityLabelBasis (j : J) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun i=>if i=j then (1:ℝ) else 0)

def cavityLabelRow (q : Fin (k+1)→J→ℝ) (i : ℕ) (x : IndexedLeaf k×J) : ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q))
    cavityLabelBasis i (x.2,x.1)

def cavityLabelLength (k : ℕ) (x : IndexedLeaf k×J) : ℕ :=
  indexedGaussianRowLength (I:=J) k (x.2,x.1)

lemma cavityLabelRow_measurable (q : Fin (k+1)→J→ℝ) (i : ℕ) :
    Measurable (cavityLabelRow q i) :=
  (indexedGaussianRow_measurable k _ (measurable_of_countable cavityLabelBasis) i).comp
    (measurable_snd.prodMk measurable_fst)

omit [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma cavityLabelLength_measurable [Fintype J] [DecidableEq J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (k : ℕ) : Measurable (cavityLabelLength (J:=J) k) :=
  (indexedGaussianRowLength_measurable k).comp (measurable_snd.prodMk measurable_fst)

omit [MeasurableSingletonClass J] in
lemma cavityLabel_covariance [MeasurableSingletonClass J] (q : Fin (k+1)→J→ℝ) (h0 : ∀ i,0≤q 0 i)
    (hq : ∀ i,Monotone (fun l=>q l i)) (x y : IndexedLeaf k×J) :
    countableGaussianCovariance (cavityLabelRow q) (cavityLabelRow q) (cavityLabelLength k) x y=
      if x.2=y.2 then q (indexedCommonDepth k y.1 x.1) x.2 else 0 := by
  change countableGaussianCovariance
    (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) cavityLabelBasis)
    (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) cavityLabelBasis)
    (indexedGaussianRowLength (I:=J) k) (x.2,x.1) (y.2,y.1)=_
  rw [profileGaussianRow_covariance q h0 hq]
  simp only [cavityLabelBasis,PiLp.toLp_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases h : x.2=y.2
  · simp [h]
  · simp [h,Ne.symm h]

theorem cavity_label_moment (q : Fin (k+1)→J→ℝ) (h0 : ∀ i,0≤q 0 i)
    (hq : ∀ i,Monotone (fun l=>q l i))
    (μ : Measure (IndexedLeaf k)) [IsProbabilityMeasure μ]
    (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ g,(∫ x,Ψ (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) g x) ∂μ)^r
      ∂countableGaussianLaw)=
    ∫ xs : Fin r→IndexedLeaf k,cavityMatrixKernel (cavityTestReplica Ψ r)
      (fun i j : J×Fin r=>if i.1=j.1 then q (indexedCommonDepth k (xs j.2) (xs i.2)) i.1 else 0)
      ∂Measure.pi (fun _=>μ) := by
  simpa only [cavityLabel_covariance q h0 hq] using
    cavity_countable_moment μ (cavityLabelRow q) (cavityLabelLength k)
      (cavityLabelRow_measurable q) (cavityLabelLength_measurable k) Ψ r


lemma cavity_label_completed_covariance (q : Fin (k+1)→J→ℝ)
    (h0 : ∀ i,0≤q 0 i) (hq : ∀ i,Monotone (fun l=>q l i))
    (D : J→ℝ) (hD : ∀ i,q (Fin.last k) i≤D i)
    (r : ℕ) (xs : Fin r→IndexedLeaf k) (p t : J×Fin r) :
    countableGaussianCovariance (cavityLabelRow q) (cavityLabelRow q) (cavityLabelLength k)
      (xs p.2,p.1) (xs t.2,t.1)+
      (if p=t then (Real.sqrt (D p.1-q (Fin.last k) p.1))^2 else 0)=
    if p=t then D p.1 else
      if p.1=t.1 then q (indexedCommonDepth k (xs t.2) (xs p.2)) p.1 else 0 := by
  rw [cavityLabel_covariance q h0 hq]
  by_cases h : p=t
  · subst t
    simp only [ite_true,indexedCommonDepth_self,Real.sq_sqrt (sub_nonneg.mpr (hD _))]
    ring
  · simp only [ite_eq_right h,add_zero]

theorem cavity_label_true_diagonal_moment (q : Fin (k+1)→J→ℝ)
    (h0 : ∀ i,0≤q 0 i) (hq : ∀ i,Monotone (fun l=>q l i))
    (D : J→ℝ) (hD : ∀ i,q (Fin.last k) i≤D i)
    (μ : Measure (IndexedLeaf k)) [IsProbabilityMeasure μ]
    (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ g,(∫ x,cavityDiagonalAverage (fun j=>Real.sqrt (D j-q (Fin.last k) j)) Ψ
      (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) g x) ∂μ)^r
      ∂countableGaussianLaw)=
    ∫ xs : Fin r→IndexedLeaf k,cavityMatrixKernel (cavityTestReplica Ψ r)
      (fun p t : J×Fin r=>if p=t then D p.1 else
        if p.1=t.1 then q (indexedCommonDepth k (xs t.2) (xs p.2)) p.1 else 0)
      ∂Measure.pi (fun _=>μ) := by
  simpa only [cavity_label_completed_covariance q h0 hq D hD r] using
    cavity_countable_residual_moment μ (cavityLabelRow q) (cavityLabelLength k)
      (cavityLabelRow_measurable q) (cavityLabelLength_measurable k)
      (fun j=>Real.sqrt (D j-q (Fin.last k) j)) Ψ r


omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma cavityLabelBasis_inner [MeasurableSpace J] [MeasurableSingletonClass J]
    (j : J) (x : EuclideanSpace ℝ J) :
    inner ℝ (cavityLabelBasis j) x=x j := by
  simp [cavityLabelBasis,PiLp.inner_apply]

lemma cavity_label_field_state (q : Fin (k+1)→J→ℝ) (g : ℕ→ℝ) (x : IndexedLeaf k) :
    cavityCountableField (cavityLabelRow q) (cavityLabelLength k) g x=
      indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
        ((fun _=>diagonalMark (profileGaussianRoot q) (indexedGaussianDisorder k J g).1),
          (indexedGaussianDisorder k J g).2) x 0 := by
  ext j
  change countableGaussianField (indexedGaussianRow k
    (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) cavityLabelBasis)
    (indexedGaussianRowLength (I:=J) k) g (j,x)=_
  rw [indexedGaussianRow_diagonal_identity,cavityLabelBasis_inner]


end SphericalPerceptronFreeEnergy
end

end OAI
