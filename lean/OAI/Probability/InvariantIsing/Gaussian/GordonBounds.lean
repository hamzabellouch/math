import OAI.Probability.InvariantIsing.Gaussian.GordonWeights

namespace OAI

/-! Uniform bounds and continuity for the two-level Gaussian comparison weights. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

omit [Fintype V] [Nonempty V] in
lemma gordonRowMean_bound (H D : U × V → ℝ) (K : ℝ)
    (hD : ∀ x, |D x| ≤ K) (v : V) : |gordonRowMean H D v| ≤ K :=
  finiteGibbs_average_bound gordon_reference _ _ (fun u => hD (u,v))

lemma gordonMean_bound (H D : U × V → ℝ) (K : ℝ)
    (hD : ∀ x, |D x| ≤ K) : |gordonMean H D| ≤ K :=
  finiteGibbs_average_bound gordon_reference _ _ (gordonRowMean_bound H D K hD)

lemma gordonWeight_derivative_bound (H D : U × V → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hD : ∀ x, |D x| ≤ K) (x : U × V) :
    |gordonWeight H x*(D x-2*gordonRowMean H D x.2+gordonMean H D)| ≤ 4*K := by
  have hb : |D x-2*gordonRowMean H D x.2+gordonMean H D| ≤ 4*K := by
    calc
      _ ≤ |D x|+|2*gordonRowMean H D x.2|+|gordonMean H D| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = |D x|+2*|gordonRowMean H D x.2|+|gordonMean H D| := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 4*K := by linarith [hD x,gordonRowMean_bound H D K hD x.2,gordonMean_bound H D K hD]
  rw [abs_mul,abs_of_nonneg (gordonWeight_nonneg H x)]
  exact (mul_le_mul_of_nonneg_left hb (gordonWeight_nonneg H x)).trans
    (by nlinarith [gordonWeight_le_one H x])

omit [Fintype V] [Nonempty V] in
lemma continuous_gordonRow {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (v : V) :
    Continuous (fun s => gordonRow (H s) v) := by
  apply Continuous.log
  · exact continuous_finsetSum _ (fun u _ => (Real.continuous_exp.comp (hH (u,v))).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun u => H s (u,v))).ne'

omit [Fintype V] [Nonempty V] in
lemma continuous_gordonInner {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (u : U) (v : V) :
    Continuous (fun s => gordonInner (H s) u v) := by
  apply Continuous.div
  · exact (Real.continuous_exp.comp (hH (u,v))).const_mul 1
  · exact continuous_finsetSum _ (fun u _ => (Real.continuous_exp.comp (hH (u,v))).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun u => H s (u,v))).ne'

lemma continuous_gordonOuter {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (v : V) :
    Continuous (fun s => gordonOuter (H s) v) := by
  apply Continuous.div
  · exact (Real.continuous_exp.comp (continuous_gordonRow H hH v).neg).const_mul 1
  · exact continuous_finsetSum _ (fun v _ =>
      (Real.continuous_exp.comp (continuous_gordonRow H hH v).neg).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun v => -gordonRow (H s) v)).ne'

lemma continuous_gordonWeight {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (x : U × V) :
    Continuous (fun s => gordonWeight (H s) x) :=
  (continuous_gordonOuter H hH x.2).mul (continuous_gordonInner H hH x.1 x.2)

lemma continuous_gordonValue {S : Type*} [TopologicalSpace S] (H : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) :
    Continuous (fun s => gordonValue (H s)) := by
  apply Continuous.neg
  apply Continuous.log
  · exact continuous_finsetSum _ (fun v _ =>
      (Real.continuous_exp.comp (continuous_gordonRow H hH v).neg).const_mul 1)
  · intro s
    exact (finitePartition_pos gordon_reference (fun v => -gordonRow (H s) v)).ne'

omit [Fintype V] [Nonempty V] in
lemma continuous_gordonRowMean {S : Type*} [TopologicalSpace S] (H D : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (hD : ∀ x, Continuous (fun s => D s x)) (v : V) :
    Continuous (fun s => gordonRowMean (H s) (D s) v) :=
  continuous_finsetSum _ (fun u _ => (continuous_gordonInner H hH u v).mul (hD (u,v)))

lemma continuous_gordonMean {S : Type*} [TopologicalSpace S] (H D : S → U × V → ℝ)
    (hH : ∀ x, Continuous (fun s => H s x)) (hD : ∀ x, Continuous (fun s => D s x)) :
    Continuous (fun s => gordonMean (H s) (D s)) :=
  continuous_finsetSum _ (fun v _ =>
    (continuous_gordonOuter H hH v).mul (continuous_gordonRowMean H D hH hD v))

end InvariantIsing

end

end OAI
