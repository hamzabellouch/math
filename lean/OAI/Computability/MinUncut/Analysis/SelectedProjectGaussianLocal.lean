import Mathlib
import OAI.Computability.MinUncut.Estimates.Away

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

omit [AddCommGroup W] [Module F₂ W] in
lemma selectedProject_gaussian_local (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (x : ι) (F : Finset ι)
    (hJ : ∀ j ∈ J, ∀ y ∈ F, y≠x → j.2 y=0) (B : R → W)
    (c C : ι → ℝ) (hC : ∀ y ∉ F, c y=C y) :
    selectedProject J u B c=selectedProject J u B (Function.update C x (c x)) := by
  unfold selectedProject
  apply Finset.sum_congr rfl
  intro j hj
  simp only [maskHermite_eq,psi_localized j.2 x F (hJ j hj) c C hC]

omit [AddCommGroup W] [Module F₂ W] in
lemma selectedProject_gaussian_memLp (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (x : ι) (B : R → W) (C : ι → ℝ) :
    MemLp (fun t => selectedProject J u B (Function.update C x t)) 2 γ := by
  unfold selectedProject
  apply memLp_finsetSum
  intro j _
  simp only [maskHermite_eq]
  exact (memLp_psi_update j.2 x C).mul_const _

omit [AddCommGroup W] [Module F₂ W] in
lemma selectedProject_gaussian_mean (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (x : ι) (hJ : ∀ j ∈ J, 0<j.2 x)
    (B : R → W) (C : ι → ℝ) :
    (∫ t, selectedProject J u B (Function.update C x t) ∂γ)=0 := by
  unfold selectedProject
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j hj
    simp only [maskHermite_eq,integral_mul_const,integral_psi_update j.2 x C (hJ j hj),zero_mul]
  · intro j _
    simp only [maskHermite_eq]
    exact ((memLp_psi_update j.2 x C).mul_const _).integrable (by norm_num)
end MinUncut.RowNoise
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def freeGaussianPoints (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) :
    Finset (Point m n) := Finset.univ.filter (Subbox.InBox H)

lemma retained_zero_positive (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    (j : Finset (Row m n) × (Point m n → ℕ)) (hj : j∈retainedClass x H none J) :
    0<j.2 x := by
  have ht := Finset.mem_filter.mp hj
  have hc := Finset.mem_filter.mp ht.1
  exact (maskClass_none x j.2 j.1 (hJ j hc.1)).mp hc.2

lemma retained_gaussian_local (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k)
    (a : Option (PairClass m)) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (j : Finset (Row m n) × (Point m n → ℕ)) (hj : j∈retainedClass x H a J)
    (y : Point m n) (hy : y∈freeGaussianPoints x H) (hne : y≠x) : j.2 y=0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact (Finset.mem_filter.mp hj).2 (Or.inl ⟨y, by simpa [hermiteSupport] using hp,
    hne,(Finset.mem_filter.mp hy).2⟩)

def gaussianSlice (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C : Point m n → ℝ) (t : ℝ) : ℝ :=
  selectedProject (retainedClass x H none J) (fun B c => gradient f B σ η c x)
    B (Function.update C x t)

lemma retained_gaussian_slice (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (c C : Point m n → ℝ)
    (hC : ∀ y ∉ freeGaussianPoints x H, c y=C y) :
    selectedProject (retainedClass x H none J) (fun B c => gradient f B σ η c x) B c =
      gaussianSlice f σ η x H J B C (c x) :=
  selectedProject_gaussian_local _ _ x _ (retained_gaussian_local x H none J) B c C hC

lemma gaussianSlice_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C : Point m n → ℝ) :
    MemLp (gaussianSlice f σ η x H J B C) 2 γ :=
  selectedProject_gaussian_memLp _ _ x B C

lemma gaussianSlice_mean (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    (B : FaceArray A m n) (C : Point m n → ℝ) :
    (∫ t, gaussianSlice f σ η x H J B C t ∂γ)=0 :=
  selectedProject_gaussian_mean _ _ x (retained_zero_positive x H J hJ) B C
end MinUncut.Inner

end

end OAI
