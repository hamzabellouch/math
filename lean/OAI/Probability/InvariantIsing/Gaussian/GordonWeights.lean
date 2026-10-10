import OAI.Probability.InvariantIsing.Gaussian.GaussianComparisonSign

namespace OAI

/-! The two finite Gibbs levels in the Gaussian minimum--maximum comparison. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordon_reference {X : Type*} [Nonempty X] : GibbsReference (fun _ : X => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one,⟨Classical.choice inferInstance,zero_lt_one⟩⟩

def gordonRow (H : U × V → ℝ) (v : V) : ℝ :=
  Real.log (finitePartition (fun _ : U => 1) (fun u => H (u,v)))

def gordonValue (H : U × V → ℝ) : ℝ :=
  -Real.log (finitePartition (fun _ : V => 1) (fun v => -gordonRow H v))

def gordonInner (H : U × V → ℝ) (u : U) (v : V) : ℝ :=
  finiteGibbs (fun _ : U => 1) (fun u => H (u,v)) u

def gordonOuter (H : U × V → ℝ) (v : V) : ℝ :=
  finiteGibbs (fun _ : V => 1) (fun v => -gordonRow H v) v

def gordonWeight (H : U × V → ℝ) (x : U × V) : ℝ :=
  gordonOuter H x.2*gordonInner H x.1 x.2

def gordonRowMean (H D : U × V → ℝ) (v : V) : ℝ :=
  ∑ u, gordonInner H u v*D (u,v)

def gordonMean (H D : U × V → ℝ) : ℝ :=
  ∑ v, gordonOuter H v*gordonRowMean H D v

lemma gordonWeight_nonneg (H : U × V → ℝ) (x : U × V) : 0 ≤ gordonWeight H x :=
  mul_nonneg (finiteGibbs_nonneg gordon_reference _ _) (finiteGibbs_nonneg gordon_reference _ _)

lemma gordonWeight_le_one (H : U × V → ℝ) (x : U × V) : gordonWeight H x ≤ 1 := by
  calc
    _ ≤ 1*1 := mul_le_mul (finiteGibbs_le_one gordon_reference _ _)
      (finiteGibbs_le_one gordon_reference _ _)
      (finiteGibbs_nonneg gordon_reference _ _) zero_le_one
    _ = _ := one_mul _

lemma gordonWeight_sum (H : U × V → ℝ) : ∑ x, gordonWeight H x = 1 := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [gordonWeight,← Finset.mul_sum,gordonInner,
    mul_one,gordonOuter,finiteGibbs_sum gordon_reference]

omit [Nonempty U] [Nonempty V] in
lemma gordonMean_eq_sum (H D : U × V → ℝ) : gordonMean H D = ∑ x, gordonWeight H x*D x := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [gordonMean,gordonRowMean,Finset.mul_sum,gordonWeight,mul_assoc]

omit [Fintype V] [Nonempty V] in
lemma gordonRow_hasDerivAt {H : ℝ → U × V → ℝ} {D : U × V → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (D x) t) (v : V) :
    HasDerivAt (fun s => gordonRow (H s) v) (gordonRowMean (H t) D v) t :=
  hasDerivAt_log_finitePartition gordon_reference (fun u => hH (u,v))

lemma gordonValue_hasDerivAt {H : ℝ → U × V → ℝ} {D : U × V → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (D x) t) :
    HasDerivAt (fun s => gordonValue (H s)) (gordonMean (H t) D) t := by
  have h := (hasDerivAt_log_finitePartition gordon_reference
    (fun v => (gordonRow_hasDerivAt hH v).neg)).neg
  convert h using 1 <;> first | rfl |
    simp only [gordonMean,gordonOuter,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib,neg_neg]

lemma gordonWeight_hasDerivAt {H : ℝ → U × V → ℝ} {D : U × V → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (D x) t) (x : U × V) :
    HasDerivAt (fun s => gordonWeight (H s) x)
      (gordonWeight (H t) x*(D x-2*gordonRowMean (H t) D x.2+gordonMean (H t) D)) t := by
  have hi := hasDerivAt_finiteGibbs gordon_reference (fun u => hH (u,x.2)) x.1
  have ho := hasDerivAt_finiteGibbs gordon_reference
    (fun v => (gordonRow_hasDerivAt hH v).neg) x.2
  convert ho.mul hi using 1
  · rfl
  simp only [gordonMean,gordonRowMean,gordonWeight,gordonInner,gordonOuter,
    Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
  ring

end InvariantIsing

end

end OAI
