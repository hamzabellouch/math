import Mathlib
import OAI.Analysis.Commutator.FreeRepeatedWords

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (hS : S i=f.range) (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
  (x : letterSpace t S i) (hx : ‖x‖=1)

variable (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) d‖)

def normalizedColumn (n : ℕ) : multiplicityLevel t S j 0 →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
    (repeatedOutput t S f hf hS hfree hij d x n).comp
      (repeatInsertion t S s hs n).toContinuousLinearMap).toLinearMap
  norm_map' v := by
    change ‖((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
      repeatedOutput t S f hf hS hfree hij d x n (repeatInsertion t S s hs n v)‖=‖v‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
      abs_of_nonneg (norm_nonneg _),norm_repeatedOutput,hx,one_pow,mul_one,
      (repeatInsertion t S s hs n).norm_map,←mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hr),one_mul]

lemma normalizedColumn_apply (n : ℕ) (v : multiplicityLevel t S j 0) :
    normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v=
      ((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
        repeatedOutput t S f hf hS hfree hij d x n (repeatInsertion t S s hs n v) := rfl

lemma repeatedOutput_orthogonal {n m : ℕ} (hnm : n≠m)
    (v : multiplicityLevel t S j n) (z : multiplicityLevel t S j m) :
    inner ℂ (repeatedOutput t S f hf hS hfree hij d x n v)
      (repeatedOutput t S f hf hS hfree hij d x m z)=0 := by
  exact sourceLevelEmbedding_orthogonal t f hf S i j hS hfree hij hnm _ _

lemma normalizedColumn_orthogonal : OrthogonalFamily ℂ
    (fun _ : ℕ => multiplicityLevel t S j 0)
    (normalizedColumn t S f hf hS hfree hij d s hs x hx hr) := by
  intro n m hnm v z
  simp only [normalizedColumn_apply t S f hf hS hfree hij d s hs x hx hr,inner_smul_left,inner_smul_right,
    repeatedOutput_orthogonal t S f hf hS hfree hij d x hnm,mul_zero]

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

include hB in
lemma normalizedColumn_error (n : ℕ) (v : multiplicityLevel t S j 0) :
    G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v)=
    ((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
      repeatedOutput t S f hf hS hfree hij d x n
        (B n (repeatInsertion t S s hs n v)-repeatInsertion t S s hs n (B 0 v)) := by
  simp only [normalizedColumn_apply t S f hf hS hfree hij d s hs x hx hr,map_smul,hB,map_sub,smul_sub]

include hB in
lemma normalizedColumn_error_norm (n : ℕ) (v : multiplicityLevel t S j 0) :
    ‖G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v)‖=
    ‖B n (repeatInsertion t S s hs n v)-repeatInsertion t S s hs n (B 0 v)‖ := by
  rw [normalizedColumn_error t S f hf hS hfree hij d s hs x hx hr G B hB,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    norm_repeatedOutput,hx,one_pow,mul_one,←mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hr),one_mul]

include hB in
lemma normalizedColumn_error_orthogonal {n m : ℕ} (hnm : n≠m)
    (v z : multiplicityLevel t S j 0) :
    inner ℂ (G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v))
      (G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr m z)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr m (B 0 z))=0 := by
  simp only [normalizedColumn_error t S f hf hS hfree hij d s hs x hx hr G B hB,
    inner_smul_left,inner_smul_right,
    repeatedOutput_orthogonal t S f hf hS hfree hij d x hnm,mul_zero]

include hB in
lemma norm_normalizedColumn_error_le (δ : ℝ) (hδ : 0≤δ) (n : ℕ)
    (he : ∀ v, ‖B n (repeatInsertion t S s hs n v)-repeatInsertion t S s hs n (B 0 v)‖≤δ*‖v‖) :
    ‖G.comp (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap-
      (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap.comp (B 0)‖≤δ := by
  let T := G.comp (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap-
    (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap.comp (B 0)
  change sInf {r : ℝ | 0≤r ∧ ∀ v, ‖T v‖≤r*‖v‖}≤δ
  refine csInf_le ⟨0,fun r h => h.1⟩ ⟨hδ,?_⟩
  intro v
  change ‖G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v)‖≤_
  rw [normalizedColumn_error_norm t S f hf hS hfree hij d s hs x hx hr G B hB]
  exact he v

end Kadison.FreeBlocks

end

end
end

end OAI
