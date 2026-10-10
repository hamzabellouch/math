import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeSupport

namespace OAI

/-! The singleton group selected from an actual tuple has the same
prime coefficient as the one-coordinate transition theorem. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]

lemma orderedConvolutionSupport_unique (S : ι → Finset Eisenstein) :
    orderedConvolutionSupport S = S default := by
  ext n
  constructor
  · intro hn
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
    simpa only [Fintype.prod_unique] using Fintype.mem_piFinset.mp hf default
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨fun _ => n,Fintype.mem_piFinset.mpr (fun i => ?_),?_⟩
    · have hi : i = default := Subsingleton.elim _ _
      simpa only [hi] using hn
    · simp only [Fintype.prod_unique]

lemma orderedConvolution_unique (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (n : Eisenstein) : orderedConvolution S w n = if n ∈ S default then w default n else 0 := by
  unfold orderedConvolution
  by_cases hn : n ∈ S default
  · rw [ite_eq_left hn,Finset.sum_eq_single (fun _ : ι => n)]
    · simp only [Fintype.prod_unique]
    · intro f hf hne
      exfalso
      apply hne
      funext i
      have hi : i = default := Subsingleton.elim _ _
      simpa only [Fintype.prod_unique,hi] using (Finset.mem_filter.mp hf).2
    · intro hf
      exfalso
      apply hf
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_),?_⟩
      · have hi : i = default := Subsingleton.elim _ _
        simpa only [hi] using hn
      · simp only [Fintype.prod_unique]
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro f hf
    obtain ⟨hf,hprod⟩ := Finset.mem_filter.mp hf
    have he : f default = n := by simpa only [Fintype.prod_unique] using hprod
    exact (hn (he ▸ Fintype.mem_piFinset.mp hf default)).elim

lemma fullSquarefreePrimeSupport_unique (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullSquarefreePrimeSupport R W X 1 = fullPrimeSupport R W X default := by
  unfold fullSquarefreePrimeSupport
  rw [orderedConvolutionSupport_unique]
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact ⟨(fullPrimeSupport_prime R W X default p hp).2.squarefree,isCoprime_one_right⟩

lemma fullPrimeCoefficient_unique {R : ℝ} {W : ι → ℝ → ℂ} {X : ι → ℝ} {p : Eisenstein}
    (hp : p ∈ fullPrimeSupport R W X default) :
    fullPrimeCoefficient R W X p = W default (norm p/X default) := by
  rw [fullPrimeCoefficient,squarefreeConvolution,
    ite_eq_left (fullPrimeSupport_prime R W X default p hp).2.squarefree]
  rw [orderedConvolution_unique,ite_eq_left hp]

end CubicFirstMoment

end

end OAI
