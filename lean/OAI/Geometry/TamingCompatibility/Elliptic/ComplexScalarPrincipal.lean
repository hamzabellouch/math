import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.PrincipalDerivativeError
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexReal

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} [Fintype ι] {m n k : ℕ}

lemma matProduct_coefficient_apply (b : 𝓢(D,R m →L[ℝ] R k))
    (a : 𝓢(D,R n →L[ℝ] R m)) (i : Fin k) (j : Fin n) (x : D) :
    matProduct (coefficient b) (coefficient a) i j x =
      (entry i j (b x ∘L a x) : ℂ) := by
  simp only [matProduct,_root_.sum_apply,entryProduct_apply,coefficient_apply,
    ← Complex.ofReal_mul,← Complex.ofReal_sum]
  congr 1
  exact real_matrix_apply (b x) (a x (EuclideanSpace.single j 1)) i

lemma schwartz_zero_product (φ : 𝓢(D,ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(D,ℂ)) φ = 0 := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (0 : 𝓢(D,ℂ)).hasTemperateGrowth]
  simp only [_root_.zero_apply,zero_smul]

def scalarMatrix (n : ℕ) (q : 𝓢(D,ℂ)) : Fin n → Fin n → 𝓢(D,ℂ) :=
  fun i j => if i=j then q else 0

lemma multiply_scalarMatrix (q : 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (scalarMatrix n q) u = smulLeftCLM (C n) q u := by
  ext φ i
  rw [multiply_apply_component,smulLeftCLM_apply_apply]
  rw [Finset.sum_eq_single i]
  · simp only [scalarMatrix,ite_true]
  · intro j _ hji
    simp only [scalarMatrix,ite_eq_right (Ne.symm hji),schwartz_zero_product,map_zero,PiLp.zero_apply]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

variable [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

lemma symmetrized_principal (e : ι → D)
    (a : ι → ι → Fin n → Fin n → 𝓢(D,ℂ)) (g : ι → ι → 𝓢(D,ℂ))
    (ha : ∀ i j k l, a i j k l + a j i k l = scalarMatrix n (g i j + g i j) k l)
    (u : 𝓢'(D,C n)) :
    (∑ i, ∑ j, multiply (a i j) (∂_{e i} (∂_{e j} u))) =
      ∑ i, ∑ j, smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u)) := by
  let S := ∑ i, ∑ j, multiply (a i j) (∂_{e i} (∂_{e j} u))
  have hs : S = ∑ i, ∑ j, multiply (a j i) (∂_{e i} (∂_{e j} u)) := by
    dsimp only [S]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [distribution_derivatives_commute (e i) (e j)]
  have hm (i j : ι) :
      multiply (a i j) (∂_{e i} (∂_{e j} u)) + multiply (a j i) (∂_{e i} (∂_{e j} u)) =
      smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u)) +
        smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u)) := by
    rw [← multiply_add]
    have he : (fun k l => a i j k l + a j i k l) = scalarMatrix n (g i j + g i j) :=
      funext fun k => funext fun l => ha i j k l
    rw [he,multiply_scalarMatrix]
    ext φ k
    simp only [smulLeftCLM_apply_apply,_root_.add_apply,PiLp.add_apply]
    have hf : SchwartzMap.smulLeftCLM ℂ (g i j+g i j) φ =
        SchwartzMap.smulLeftCLM ℂ (g i j) φ + SchwartzMap.smulLeftCLM ℂ (g i j) φ := by
      ext x
      simp only [SchwartzMap.smulLeftCLM_apply_apply (g i j+g i j).hasTemperateGrowth,
        SchwartzMap.smulLeftCLM_apply_apply (g i j).hasTemperateGrowth,_root_.add_apply,add_smul]
    rw [hf,map_add]
    rfl
  have hsum : S+S =
      (∑ i, ∑ j, smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u))) +
      (∑ i, ∑ j, smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u))) := by
    calc
      S+S = S+(∑ i, ∑ j, multiply (a j i) (∂_{e i} (∂_{e j} u))) :=
        congrArg (fun v => S+v) hs
      _ = _ := by
        dsimp only [S]
        simp_rw [← Finset.sum_add_distrib,hm]
  have he := congrArg (fun v : 𝓢'(D,C n) => (1/2:ℂ) • v) hsum
  simpa only [← two_smul ℂ,smul_smul,div_mul_cancel₀ _ (by norm_num : (2:ℂ) ≠ 0),one_smul] using he

end TamingCompatibility.ComplexMatrix

end

end OAI
