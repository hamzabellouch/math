import OAI.Analysis.TriangularHilbert.SelectedScale

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

def kernelOutput (B C : Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) (i j : ι) : ℂ :=
  ∑ k, (h:ℂ)*B j k*C k i*(K i j (u i+u j+u k):ℂ)

def kernelPairing (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) : ℂ :=
  ∑ i, ∑ j, (h^2:ℝ)*A 0 i j*kernelOutput (A 1) (A 2) h u K i j

lemma kernelPairing_eq (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) :
    kernelPairing A h u K = ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(K i j (u i+u j+u k):ℂ) := by
  simp only [kernelPairing,kernelOutput,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

lemma kernelPairing_add (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K L : ι → ι → ℝ → ℝ) :
    kernelPairing A h u (fun i j t => K i j t+L i j t) = kernelPairing A h u K+kernelPairing A h u L := by
  simp only [kernelPairing_eq,Complex.ofReal_add,mul_add,Finset.sum_add_distrib]

lemma kernelPairing_const_mul (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (K : ι → ι → ℝ → ℝ) (c : ℝ) :
    kernelPairing A h u (fun i j t => c*K i j t) = (c:ℂ)*kernelPairing A h u K := by
  simp only [kernelPairing_eq,Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma kernelPairing_smooth [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) :
    kernelPairing A h u (fun i j => smoothKernel (a i j) (b i j)) = selectedSum A h u a b := by
  rw [kernelPairing_eq]
  rfl
end
end TriangularHilbert.Heat
end

end OAI
