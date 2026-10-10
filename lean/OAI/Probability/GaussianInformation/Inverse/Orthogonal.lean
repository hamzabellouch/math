import Mathlib
import OAI.Probability.GaussianInformation.Inverse.Tubes

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace

def Suborthonormal {d k : ℕ} (e : Fin k → Ambient d) : Prop :=
  Pairwise (fun i j => inner ℝ (e i) (e j)=0) ∧ ∀ j,e j=0 ∨ ‖e j‖=1

lemma Suborthonormal.inner_eq {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (i j : Fin k) : inner ℝ (e i) (e j) = if i=j then ‖e i‖^2 else 0 := by
  classical
  by_cases hij : i=j
  · subst j; simp
  · simp [hij,he.1 hij]

lemma Suborthonormal.norm_le {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (i : Fin k) : ‖e i‖ ≤ 1 := by
  rcases he.2 i with h|h <;> simp [h]

lemma orthogonal_sum_norm_sq {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (a : Fin k → ℝ) :
    ‖∑ j ∈ s,a j • e j‖^2 = ∑ j ∈ s,(a j)^2*‖e j‖^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,real_inner_smul_left,inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  simp [he.inner_eq,hi,pow_two,mul_assoc]

lemma suborthonormal_synth_contraction {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (x : Ambient k) : ‖synth e x‖ ≤ ‖x‖ := by
  have hh : ‖synth e x‖^2 ≤ ‖x‖^2 := by
    rw [synth,orthogonal_sum_norm_sq he,EuclideanSpace.real_norm_sq_eq x]
    apply Finset.sum_le_sum
    intro j _
    have hn : ‖e j‖^2 ≤ 1 := by nlinarith [he.norm_le j,norm_nonneg (e j)]
    simpa using mul_le_mul_of_nonneg_left hn (sq_nonneg (x j))
  nlinarith [norm_nonneg (synth e x),norm_nonneg x]

noncomputable def orthoResidual {d k : ℕ} (e : Fin k → Ambient d) (s : Finset (Fin k))
    (x : Ambient d) : Ambient d := x-∑ j ∈ s,(inner ℝ (e j) x) • e j

lemma suborthonormal_coeff_norm {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (x : Ambient d) (j : Fin k) : inner ℝ (e j) x * ‖e j‖^2 = inner ℝ (e j) x := by
  rcases he.2 j with h|h <;> simp [h]

lemma orthoResidual_inner {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (x : Ambient d) (j : Fin k) :
    inner ℝ (e j) (orthoResidual e s x) = if j∈s then 0 else inner ℝ (e j) x := by
  classical
  simp only [orthoResidual,inner_sub_right,inner_sum,real_inner_smul_right]
  simp_rw [he.inner_eq j]
  by_cases hj : j∈s <;> simp [hj,suborthonormal_coeff_norm he x j]

lemma orthoResidual_norm_sq {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (x : Ambient d) :
    ‖orthoResidual e s x‖^2 = ‖x‖^2-∑ j ∈ s,(inner ℝ (e j) x)^2 := by
  rw [orthoResidual,norm_sub_sq_real,orthogonal_sum_norm_sq he]
  have hinner : inner ℝ x (∑ j ∈ s,(inner ℝ (e j) x) • e j) =
      ∑ j ∈ s,(inner ℝ (e j) x)^2 := by
    simp only [inner_sum,real_inner_smul_right,real_inner_comm x,pow_two]
  have hnorm : ∑ j ∈ s,(inner ℝ (e j) x)^2*‖e j‖^2 =
      ∑ j ∈ s,(inner ℝ (e j) x)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_two,mul_assoc,suborthonormal_coeff_norm he]
  rw [hinner,hnorm]
  ring

lemma orthoResidual_norm_antitone {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    {s t : Finset (Fin k)} (hst : s⊆t) (x : Ambient d) :
    ‖orthoResidual e t x‖ ≤ ‖orthoResidual e s x‖ := by
  have hs := orthoResidual_norm_sq he s x
  have ht := orthoResidual_norm_sq he t x
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun j _ _ => sq_nonneg (inner ℝ (e j) x))
  nlinarith [norm_nonneg (orthoResidual e t x),norm_nonneg (orthoResidual e s x)]

lemma suborthonormal_bessel {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (x : Ambient d) :
    ∑ j ∈ s,(inner ℝ (e j) x)^2 ≤ ‖x‖^2 := by
  have hh := orthoResidual_norm_sq he s x
  nlinarith [sq_nonneg ‖orthoResidual e s x‖]

lemma gramSchmidtNormed_suborthonormal {d k : ℕ} (f : Fin k → Ambient d) :
    Suborthonormal (gramSchmidtNormed ℝ f) := by
  constructor
  · intro i j hij
    simp only [gramSchmidtNormed,real_inner_smul_left,real_inner_smul_right,
      gramSchmidt_orthogonal ℝ f hij,mul_zero]
  · intro j
    by_cases hj : gramSchmidtNormed ℝ f j=0
    · exact Or.inl hj
    · exact Or.inr (gramSchmidtNormed_unit_length' hj)

lemma Suborthonormal.cut {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Set (Fin k)) [DecidablePred (·∈s)] : Suborthonormal (fun j => if j∈s then e j else 0) := by
  constructor
  · intro i j hij
    by_cases hi : i∈s <;> by_cases hj : j∈s <;> simp [hi,hj,he.1 hij]
  · intro j
    by_cases hj : j∈s
    · simpa only [ite_eq_left hj] using he.2 j
    · exact Or.inl (ite_eq_right hj)

end AllScaleInverseVolume

end OAI
