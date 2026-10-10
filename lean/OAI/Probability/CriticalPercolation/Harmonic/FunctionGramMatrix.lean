import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.GeneralizedGramSpectrum
import OAI.Probability.CriticalPercolation.Harmonic.HarmonicFunctionSpace

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {ι X : Type*} [Fintype ι]

def functionGram (F : Finset X) (v : ι → X → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ x∈F, v i x*v j x

def functionCombination (v : ι → X → ℝ) (a : ι → ℝ) : X → ℝ :=
  fun x => ∑ i, a i*v i x

omit [Fintype ι] in
lemma functionGram_hermitian (F : Finset X) (v : ι → X → ℝ) :
    (functionGram F v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial,functionGram,mul_comm]

lemma functionGram_quadratic (F : Finset X) (v : ι → X → ℝ) (a : ι → ℝ) :
    matrixQuadratic (functionGram F v) a = squareMass F (functionCombination v a) := by
  simp only [matrixQuadratic,functionGram,Matrix.mulVec,dotProduct,
    squareMass,functionCombination,pow_two,Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i, ∑ x∈F, ∑ j, a i*(v i x*v j x*a j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x∈F, ∑ i, ∑ j, a i*(v i x*v j x*a j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma functionGram_posSemidef (F : Finset X) (v : ι → X → ℝ) :
    (functionGram F v).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨functionGram_hermitian F v,?_⟩
  intro a
  simp only [star_trivial]
  change 0 ≤ matrixQuadratic (functionGram F v) a
  rw [functionGram_quadratic]
  exact squareMass_nonneg _ _

lemma functionGram_posDef (F : Finset X) (v : ι → X → ℝ)
    (hdetect : ∀ a, (∀ x∈F, functionCombination v a x=0) → a=0) :
    (functionGram F v).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨functionGram_hermitian F v,?_⟩
  intro a ha
  simp only [star_trivial]
  change 0 < matrixQuadratic (functionGram F v) a
  rw [functionGram_quadratic]
  apply lt_of_le_of_ne (squareMass_nonneg _ _)
  intro hz
  exact ha (hdetect a ((squareMass_eq_zero_iff _ _).mp hz.symm))

lemma functionGram_quadratic_mono {F H : Finset X} (hFH : F⊆H)
    (v : ι → X → ℝ) (a : ι → ℝ) :
    matrixQuadratic (functionGram F v) a ≤ matrixQuadratic (functionGram H v) a := by
  rw [functionGram_quadratic,functionGram_quadratic]
  exact squareMass_mono hFH _

lemma functionGram_det_mono {F H : Finset X} (hFH : F⊆H)
    (v : ι → X → ℝ) (hF : (functionGram F v).PosDef) :
    (functionGram F v).det ≤ (functionGram H v).det := by
  obtain ⟨μ,b,hμ,hdet,_,_⟩ := generalized_gram_spectrum
    (functionGram F v) (functionGram H v) hF (functionGram_hermitian H v)
    (functionGram_quadratic_mono hFH v)
  rw [hdet]
  have hp : (1:ℝ) ≤ ∏ i, μ i := Finset.one_le_prod₀ (fun index _ => hμ index)
  exact le_mul_of_one_le_right hF.det_pos.le hp

omit [Fintype ι] in
lemma functionGram_entry_bound (F : Finset X) (v : ι → X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ∀ i, ∀ x∈F, |v i x| ≤ M) (i j : ι) :
    |functionGram F v i j| ≤ (F.card:ℝ)*M^2 := by
  calc
    _ ≤ ∑ x∈F, |v i x*v j x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x∈F, M^2 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul,pow_two]
      exact mul_le_mul (hv i x hx) (hv j x hx) (abs_nonneg _) hM
    _ = _ := by simp

lemma functionGram_det_bound (F : Finset X) (v : ι → X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ∀ i, ∀ x∈F, |v i x| ≤ M) :
    |(functionGram F v).det| ≤ ((Fintype.card ι).factorial:ℝ)*((F.card:ℝ)*M^2)^(Fintype.card ι) := by
  have hh := Matrix.det_le (abv := AbsoluteValue.abs) (functionGram_entry_bound F v M hM hv)
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using hh

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
