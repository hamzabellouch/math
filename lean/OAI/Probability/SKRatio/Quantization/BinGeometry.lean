import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def sum (σ : ι → α) (f : ι → ℝ) (a : α) : ℝ :=
  ∑ i with σ i = a, f i

def overlap (σ : ι → α) (u z : ι → ℝ) (a : α) : ℝ :=
  sum σ (fun i => u i*z i) a

def ZeroSum (σ : ι → α) (u : ι → ℝ) : Prop := ∀ a, sum σ u a = 0

lemma sum_fibers (σ : ι → α) (f : ι → ℝ) : ∑ a, sum σ f a = ∑ i, f i := by
  classical
  simpa only [sum,Finset.mem_univ,true_and] using
    (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := σ)
      (fun _ _ => Finset.mem_univ _) f)

lemma sum_weighted (σ : ι → α) (f : ι → ℝ) (c : α → ℝ) :
    ∑ i, f i*c (σ i) = ∑ a, sum σ f a*c a := by
  rw [←sum_fibers σ (fun i => f i*c (σ i))]
  apply Finset.sum_congr rfl
  intro a _
  unfold sum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change f i*c (σ i)=f i*c a
  rw [(Finset.mem_filter.mp hi).2]

lemma zero_sum_weighted {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u) (c : α → ℝ) :
    (∑ i, u i*c (σ i)) = 0 := by
  rw [sum_weighted]
  simp only [show ∀ a, sum σ u a=0 from hu,zero_mul,Finset.sum_const_zero]

lemma zero_sum_bilinear {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u)
    (z : ι → ℝ) (K : α → α → ℝ) :
    (∑ i, ∑ j, u i*z j*K (σ i) (σ j)) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  simpa only [mul_assoc] using zero_sum_weighted hu (fun a => z j*K a (σ j))

omit [Fintype α] in
lemma overlap_symm (σ : ι → α) (u z : ι → ℝ) : overlap σ u z = overlap σ z u := by
  funext a
  simp only [overlap,mul_comm]

omit [Fintype α] in
lemma overlap_self_nonneg (σ : ι → α) (u : ι → ℝ) (a : α) : 0 ≤ overlap σ u u a := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

omit [Fintype α] in
lemma overlap_le {σ : ι → α} {u z : ι → ℝ} {s : α → ℝ}
    (hu : overlap σ u u = s) (hz : overlap σ z z = s) (a : α) :
    overlap σ u z a ≤ s a := by
  have h : 0 ≤ ∑ i with σ i=a, (u i-z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (∑ i with σ i=a, (u i-z i)^2) =
      overlap σ u u a+overlap σ z z a-2*overlap σ u z a := by
    unfold overlap sum
    simp only [Finset.mul_sum]
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hu,hz] at h
  linarith

omit [Fintype α] in
lemma overlap_abs_le {σ : ι → α} {u z : ι → ℝ} {s : α → ℝ}
    (hu : overlap σ u u = s) (hz : overlap σ z z = s) (a : α) :
    |overlap σ u z a| ≤ s a := by
  have hz' : overlap σ (fun i => -z i) (fun i => -z i) = s := by
    calc
      _ = overlap σ z z := by ext a; simp only [overlap,neg_mul_neg]
      _ = s := hz
  have hh := overlap_le hu hz' a
  have he : overlap σ u (fun i => -z i) a = -overlap σ u z a := by
    simp [overlap,sum]
  rw [he] at hh
  exact abs_le.mpr ⟨by linarith,overlap_le hu hz a⟩

omit [Fintype α] [DecidableEq α] in
lemma overlap_product_bound {s q : α → ℝ} (hq : ∀ a, q a ≤ s a) (a d : α) :
    s a*s d-q a*q d ≤ s a*(s d-q d)+s d*(s a-q a) := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr (hq a)) (sub_nonneg.mpr (hq d))]

lemma double_weighted (σ : ι → α) (f g : ι → ℝ) (K : α → α → ℝ) :
    (∑ i, ∑ j, f i*g j*K (σ i) (σ j)) =
      ∑ a, ∑ d, sum σ f a*sum σ g d*K a d := by
  simp_rw [mul_assoc,←Finset.mul_sum,sum_weighted σ g]
  rw [sum_weighted σ f (fun a => ∑ d, sum σ g d*K a d)]

lemma sum_overlap (σ : ι → α) (u z : ι → ℝ) :
    (∑ a, overlap σ u z a) = ∑ i, u i*z i := sum_fibers _ _

end SKRatio.Bins

end

end OAI
