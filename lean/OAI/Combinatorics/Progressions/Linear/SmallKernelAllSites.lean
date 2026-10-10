import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Estimates.AnchoredFixedCenterDomination
import OAI.Combinatorics.Progressions.Estimates.CenteredFullParameterGeometry
import OAI.Combinatorics.Progressions.Estimates.ScaledFloorPerturbation
import OAI.Combinatorics.Progressions.Sampling.SmallKernelSamplerThreshold

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem matrixSupCLM_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ) (A : Matrix ι κ ℝ) :
    matrixSupCLM (a • A) = a • matrixSupCLM A := by
  ext x i
  simp only [smul_apply, matrixSupCLM_apply, Matrix.smul_mulVec,
    Pi.smul_apply]

theorem scalar_identity_inverse_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) :
    (a • ContinuousLinearMap.id ℝ E).IsInvertible ∧
      ‖(a • ContinuousLinearMap.id ℝ E).inverse‖ ≤ 1 / a := by
  let A := a • ContinuousLinearMap.id ℝ E
  let B := a⁻¹ • ContinuousLinearMap.id ℝ E
  have hAB : A.comp B = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ne_of_gt ha]
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ne_of_gt ha]
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hAB hBA, ?_⟩
  change ‖A.inverse‖ ≤ 1 / a
  rw [ContinuousLinearMap.inverse_eq hAB hBA]
  calc
    ‖B‖ = |a⁻¹| * ‖ContinuousLinearMap.id ℝ E‖ := by
      simp only [B, norm_smul, Real.norm_eq_abs]
    _ ≤ a⁻¹ * 1 := by
      rw [abs_of_pos (inv_pos.mpr ha)]
      exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.mpr ha.le)
    _ = 1 / a := by simp only [mul_one, one_div]

theorem matrix_inverse_near_scalar_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (hentry : ∀ i j, |M i j - (a • (1 : Matrix ι ι ℝ)) i j| ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ a / 2) :
    (matrixSupCLM M).IsInvertible ∧ ‖(matrixSupCLM M).inverse‖ ≤ 2 / a := by
  have hA := scalar_identity_inverse_bound (E := ι → ℝ) ha
  have hdiff : ‖matrixSupCLM M - a • ContinuousLinearMap.id ℝ (ι → ℝ)‖ ≤
      (Fintype.card ι : ℝ) * ε := by
    rw [← matrixSupCLM_one, ← matrixSupCLM_smul, ← matrixSupCLM_sub]
    exact matrixSupCLM_norm_le _ hε hentry
  have hbound : (1 / a) * ‖matrixSupCLM M - a • ContinuousLinearMap.id ℝ (ι → ℝ)‖ ≤
      (1 / 2 : ℝ) := by
    have h := (mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 1 / a)).trans
      (mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 1 / a))
    calc
      _ ≤ (1 / a) * (a / 2) := h
      _ = 1 / 2 := by field_simp
  have h := inverse_perturbation_bound _ (matrixSupCLM M) hA.1
    (⟨1 / a, by positivity⟩ : ℝ≥0) hA.2 hbound
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ 2 * (1 / a) := h.2
    _ = 2 / a := by ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

def kernelColumnCenter {G X F : Type*} [DecidableEq X] (a : ℝ) :
    (G × X) ⊕ F → X → ℝ
  | .inl (_, j), i => if i = j then a else 0
  | .inr _, _ => 0

noncomputable def kernelSpatialAnchor {G X F : Type*} [DecidableEq X]
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (a : ℝ) :
    Option ((G × X) ⊕ F) × X → ℤ
  | (none, i) => integerBoxCenter N i
  | (some k, i) => ⌊((N i : ℝ) / T k) * kernelColumnCenter a k i⌋

noncomputable def kernelSpatialWidths {G X F : Type*}
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (η σ : ℝ) :
    Option ((G × X) ⊕ F) × X → ℝ
  | (none, i) => (N i : ℝ) / 8
  | (some (.inl (g, j)), i) => η * ((N i : ℝ) / T (.inl (g, j)))
  | (some (.inr f), i) => σ * η * ((N i : ℝ) / T (.inr f))

theorem kernelSpatialWidths_pos {G X F : Type*}
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ)
    (hT : ∀ k, 0 < T k) {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ)
    (z : Option ((G × X) ⊕ F) × X) : 0 < kernelSpatialWidths N T η σ z := by
  rcases z with ⟨k, i⟩
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  cases k with
  | none => exact div_pos hn (by norm_num)
  | some k =>
    rcases k with ⟨g,j⟩ | f
    · exact mul_pos hη (div_pos hn (hT _))
    · exact mul_pos (mul_pos hσ hη) (div_pos hn (hT _))

noncomputable def normalizedKernelBlock {G X F : Type*}
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ)
    (z : Option ((G × X) ⊕ F) × X → ℤ) (g : G) : Matrix X X ℝ :=
  fun i j => (z (some (.inl (g,j)),i) : ℝ) / ((N i : ℝ) / T (.inl (g,j)))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F] [DecidableEq X]

theorem kernelSpatial_kernel_error
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    (a η σ : ℝ) (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ η)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (kernelSpatialWidths N T η σ) 1)
    (g : G) (i j : X) :
    |normalizedKernelBlock N T (kernelSpatialAnchor N T a + u) g i j -
      (if i = j then a else 0)| ≤ 2 * η := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hs : 0 < (N i : ℝ) / T (.inl (g,j)) := div_pos hn (hT _)
  have hb := rectangularWeightIndices_zero_bound (kernelSpatialWidths N T η σ) hu
    (some (.inl (g,j)), i)
  have h := scaled_floor_perturbation_le_twice (a := if i = j then a else 0)
    hs (hscale g j i) (u (some (.inl (g,j)), i)) hb
  exact h

theorem kernelSpatial_nonkernel_bound
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    (a η σ : ℝ) {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (kernelSpatialWidths N T η σ) 1)
    (f : F) (i : X) :
    |((kernelSpatialAnchor N T a + u) (some (.inr f), i) : ℝ) /
      ((N i : ℝ) / T (.inr f))| ≤ σ * η := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hs : 0 < (N i : ℝ) / T (.inr f) := div_pos hn (hT _)
  have hb := rectangularWeightIndices_zero_bound (kernelSpatialWidths N T η σ) hu
    (some (.inr f), i)
  simp only [kernelSpatialWidths] at hb
  simpa only [Pi.add_apply, kernelSpatialAnchor, kernelColumnCenter, mul_zero,
    Int.floor_zero, zero_add, abs_div, abs_of_pos hs] using (div_le_iff₀ hs).mpr hb

theorem kernelSpatial_column_bound
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {a η σ : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) (hσ : σ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ η)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (kernelSpatialWidths N T η σ) 1)
    (k : (G × X) ⊕ F) (i : X) :
    |((kernelSpatialAnchor N T a + u) (some k, i) : ℝ) /
      ((N i : ℝ) / T k)| ≤ a + 2 * η := by
  cases k with
  | inl k =>
    rcases k with ⟨g,j⟩
    have h := kernelSpatial_kernel_error N hN T hT a η σ hscale hu g i j
    have hc : |(if i = j then a else 0 : ℝ)| ≤ a := by
      split_ifs <;> simp_all only [abs_zero, abs_of_nonneg ha, le_refl]
    have ht := abs_add_le
      (normalizedKernelBlock N T (kernelSpatialAnchor N T a + u) g i j -
        (if i = j then a else 0)) (if i = j then a else 0)
    rw [sub_add_cancel] at ht
    exact ht.trans (by linarith)
  | inr f =>
    have h := kernelSpatial_nonkernel_bound N hN T hT a η σ hu f i
    exact h.trans (by nlinarith)

theorem scaled_coordinate_product_bound {H T c v t : ℝ}
    (hH : 0 < H) (hT : 0 < T) (hv : |v / (H / T)| ≤ c) (ht : |t| ≤ T) :
    |t * v| ≤ c * H := by
  have hs : 0 < H / T := div_pos hH hT
  have hv' : |v| ≤ c * (H / T) :=
    (div_le_iff₀ hs).mp (by simpa only [abs_div, abs_of_pos hs] using hv)
  calc
    |t * v| = |t| * |v| := abs_mul _ _
    _ ≤ T * (c * (H / T)) := mul_le_mul ht hv' (abs_nonneg _) hT.le
    _ = c * H := by field_simp

theorem kernelSpatial_nonkernel_displacement
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    (a η σ : ℝ) {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (kernelSpatialWidths N T η σ) 1)
    (root : (G × X) ⊕ F → ℤ) (hroot : ∀ k, |(root k : ℝ)| ≤ T k) (i : X) :
    |∑ f : F, (root (.inr f) : ℝ) *
      ((kernelSpatialAnchor N T a + u) (some (.inr f), i) : ℝ)| ≤
      (Fintype.card F : ℝ) * (σ * η) * (N i : ℝ) := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  calc
    _ ≤ ∑ f : F, |(root (.inr f) : ℝ) *
        ((kernelSpatialAnchor N T a + u) (some (.inr f), i) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f : F, (σ * η) * (N i : ℝ) := by
      apply Finset.sum_le_sum
      intro f _
      exact scaled_coordinate_product_bound hn (hT _)
        (kernelSpatial_nonkernel_bound N hN T hT a η σ hu f i) (hroot _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F] [DecidableEq X]

theorem kernelSpatial_kernel_inverse
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {a η σ : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ η)
    (hsmall : (Fintype.card X : ℝ) * (2 * η) ≤ a / 2)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (kernelSpatialWidths N T η σ) 1) (g : G) :
    (matrixSupCLM (normalizedKernelBlock N T (kernelSpatialAnchor N T a + u) g)).IsInvertible ∧
      ‖(matrixSupCLM (normalizedKernelBlock N T (kernelSpatialAnchor N T a + u) g)).inverse‖ ≤
        2 / a := by
  apply matrix_inverse_near_scalar_identity _ ha (by positivity) _ hsmall
  intro i j
  simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite, mul_one, mul_zero] using
    kernelSpatial_kernel_error N hN T hT a η σ hscale hu g i j

theorem kernelSpatial_site_deviation
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {a η σ : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) (hσ : σ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ η)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (kernelSpatialWidths N T η σ) 1)
    (root : (G × X) ⊕ F → ℤ) (hroot : ∀ k, |(root k : ℝ)| ≤ T k) (i : X) :
    |(integerPhysicalSite root (kernelSpatialAnchor N T a + u) i : ℝ) -
      (integerBoxCenter N i : ℝ)| ≤
      (N i : ℝ) / 8 + (Fintype.card ((G × X) ⊕ F) : ℝ) * (a + 2 * η) * (N i : ℝ) := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hbase := rectangularWeightIndices_zero_bound (kernelSpatialWidths N T η σ) hu (none, i)
  change |(u (none, i) : ℝ)| ≤ (N i : ℝ) / 8 at hbase
  have hcol (k) : |(root k : ℝ) * ((kernelSpatialAnchor N T a + u) (some k, i) : ℝ)| ≤
      (a + 2 * η) * (N i : ℝ) :=
    scaled_coordinate_product_bound hn (hT k)
      (kernelSpatial_column_bound N hN T hT ha hη hσ hscale hu k i) (hroot k)
  have heq : (integerPhysicalSite root (kernelSpatialAnchor N T a + u) i : ℝ) -
      (integerBoxCenter N i : ℝ) = (u (none, i) : ℝ) +
      ∑ k, (root k : ℝ) * ((kernelSpatialAnchor N T a + u) (some k, i) : ℝ) := by
    simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul,
      Pi.add_apply, kernelSpatialAnchor]
    ring
  rw [heq]
  calc
    _ ≤ |(u (none, i) : ℝ)| +
        |∑ k, (root k : ℝ) * ((kernelSpatialAnchor N T a + u) (some k, i) : ℝ)| := abs_add_le _ _
    _ ≤ (N i : ℝ) / 8 +
        ∑ k, |(root k : ℝ) * ((kernelSpatialAnchor N T a + u) (some k, i) : ℝ)| :=
      add_le_add hbase (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (N i : ℝ) / 8 + ∑ _k : (G × X) ⊕ F, (a + 2 * η) * (N i : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun k _ => hcol k))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem kernelSpatial_site_mem_box
    (N : X → ℕ) (hN : ∀ i, 4 ≤ N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {a η σ : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) (hσ : σ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ η)
    (hfit : (Fintype.card ((G × X) ⊕ F) : ℝ) * (a + 2 * η) ≤ 1 / 8)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (kernelSpatialWidths N T η σ) 1)
    (root : (G × X) ⊕ F → ℤ) (hroot : ∀ k, |(root k : ℝ)| ≤ T k) :
    integerPhysicalSite root (kernelSpatialAnchor N T a + u) ∈ integerBox N := by
  apply (mem_integerBox N _).mpr
  intro i
  have h := kernelSpatial_site_deviation N (fun i => by have := hN i; omega)
    T hT ha hη hσ hscale hu root hroot i
  have hfit' := mul_le_mul_of_nonneg_right hfit (Nat.cast_nonneg (α := ℝ) (N i))
  have hr : 4 * |((integerPhysicalSite root (kernelSpatialAnchor N T a + u) i -
      integerBoxCenter N i : ℤ) : ℝ)| ≤ (N i : ℝ) := by
    rw [Int.cast_sub]
    linarith
  have hz : 4 * |integerPhysicalSite root (kernelSpatialAnchor N T a + u) i -
      integerBoxCenter N i| ≤ (N i : ℤ) := by exact_mod_cast hr
  have hmem := integer_center_quarter_mem (N i) (hN i) _ hz
  change 0 ≤ integerBoxCenter N i +
      (integerPhysicalSite root (kernelSpatialAnchor N T a + u) i - integerBoxCenter N i) ∧
    integerBoxCenter N i +
      (integerPhysicalSite root (kernelSpatialAnchor N T a + u) i - integerBoxCenter N i) < N i at hmem
  have heq : integerBoxCenter N i +
      (integerPhysicalSite root (kernelSpatialAnchor N T a + u) i - integerBoxCenter N i) =
      integerPhysicalSite root (kernelSpatialAnchor N T a + u) i := by abel
  simpa only [heq] using hmem

theorem translatedKernelSpatial_support
    (N : X → ℕ) (hN : ∀ i, 4 ≤ N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {a η σ : ℝ} (ha : 0 < a) (hη : 0 < η) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ η)
    (hsmall : (Fintype.card X : ℝ) * (2 * η) ≤ a / 2)
    (hfit : (Fintype.card ((G × X) ⊕ F) : ℝ) * (a + 2 * η) ≤ 1 / 8)
    (modulus : X → ℕ)
    (S : Finset (ColumnResiduePattern (Option ((G × X) ⊕ F)) X modulus))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus S (kernelSpatialWidths N T η σ) z)
    (D : (Option ((G × X) ⊕ F) × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus S (kernelSpatialWidths N T η σ)
      (fun u => D (kernelSpatialAnchor N T a + u)))
    (z : Option ((G × X) ⊕ F) × X → ℤ)
    (hz : 0 < (translatedSelectedResidueDensityPMF (kernelSpatialAnchor N T a) modulus S
      (kernelSpatialWidths N T η σ)
      (kernelSpatialWidths_pos N (fun i => by have := hN i; omega) T hT hη hσ0)
      hZ D hD0 hD z).toReal) :
    (∀ g, (matrixSupCLM (normalizedKernelBlock N T z g)).IsInvertible ∧
      ‖(matrixSupCLM (normalizedKernelBlock N T z g)).inverse‖ ≤ 2 / a) ∧
    (∀ root : (G × X) ⊕ F → ℤ, (∀ k, |(root k : ℝ)| ≤ T k) →
      integerPhysicalSite root z ∈ integerBox N) ∧
    (∀ root : (G × X) ⊕ F → ℤ, (∀ k, |(root k : ℝ)| ≤ T k) → ∀ i,
      |∑ f : F, (root (.inr f) : ℝ) * (z (some (.inr f), i) : ℝ)| ≤
        (Fintype.card F : ℝ) * (σ * η) * (N i : ℝ)) := by
  have hpositive (i) : 0 < N i := by have := hN i; omega
  have hs := (translatedSelectedResidueDensityPMF_support (kernelSpatialAnchor N T a)
    modulus S (kernelSpatialWidths N T η σ)
    (kernelSpatialWidths_pos N hpositive T hT hη hσ0) hZ D hD0 hD z hz).1
  have heq : kernelSpatialAnchor N T a + (z - kernelSpatialAnchor N T a) = z := by abel
  refine ⟨?_, ?_, ?_⟩
  · intro g
    simpa only [heq] using kernelSpatial_kernel_inverse N hpositive T hT ha hη.le hscale hsmall hs g
  · intro root hroot
    simpa only [heq] using kernelSpatial_site_mem_box N hN T hT ha.le hη.le hσ1 hscale hfit hs root hroot
  · intro root hroot i
    simpa only [heq] using kernelSpatial_nonkernel_displacement N hpositive T hT a η σ hs root hroot i

end Erdos3

end

section

namespace Erdos3

noncomputable def kernelAnchorScale (G X F : Type*) [Fintype G] [Fintype X] [Fintype F] : ℝ :=
  1 / (16 * ((Fintype.card ((G × X) ⊕ F) : ℝ) + 1))

noncomputable def kernelNoiseScale (G X F : Type*) [Fintype G] [Fintype X] [Fintype F] : ℝ :=
  kernelAnchorScale G X F / (4 * ((Fintype.card X : ℝ) + 1))

theorem kernelSpatial_scales (G X F : Type*) [Fintype G] [Fintype X] [Fintype F] :
    let a := kernelAnchorScale G X F
    let η := kernelNoiseScale G X F
    0 < a ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      (Fintype.card X : ℝ) * (2 * η) ≤ a / 2 ∧
      (Fintype.card ((G × X) ⊕ F) : ℝ) * (a + 2 * η) ≤ 1 / 8 := by
  let M : ℝ := Fintype.card ((G × X) ⊕ F)
  let n : ℝ := Fintype.card X
  let a := kernelAnchorScale G X F
  let η := kernelNoiseScale G X F
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have ha : 0 < a := by dsimp [a, kernelAnchorScale]; positivity
  have hη : 0 < η := by dsimp [η, kernelNoiseScale]; positivity
  have hma : (M + 1) * a = 1 / 16 := by
    dsimp [M, a, kernelAnchorScale]
    field_simp
  have hnη : 4 * (n + 1) * η = a := by
    dsimp [n, η, kernelNoiseScale, a]
    field_simp
  have hηa : 2 * η ≤ a := by nlinarith [mul_nonneg hn hη.le]
  have hna : n * (2 * η) ≤ a / 2 := by nlinarith
  have hMa : M * a ≤ 1 / 16 := by nlinarith
  have ha1 : a ≤ 1 / 16 := by nlinarith [mul_nonneg hM ha.le]
  have hfit : M * (a + 2 * η) ≤ 1 / 8 := by
    calc
      _ ≤ M * (2 * a) := mul_le_mul_of_nonneg_left (by linarith) hM
      _ ≤ 1 / 8 := by nlinarith
  exact ⟨ha, hη, by linarith, hna, hfit⟩

theorem kernelSpatialWidths_lower_bound {G X F : Type*}
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {L η σ : ℝ} (hL : 1 ≤ L) (hTL : ∀ k, T k ≤ L)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 8) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (z : Option ((G × X) ⊕ F) × X) :
    (σ * η / L) * (N z.2 : ℝ) ≤ kernelSpatialWidths N T η σ z := by
  have hL0 : 0 < L := by linarith
  have hρ : σ * η / L ≤ η := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  rcases z with ⟨k, i⟩
  have hN : 0 ≤ (N i : ℝ) := Nat.cast_nonneg _
  cases k with
  | none =>
    change (σ * η / L) * (N i : ℝ) ≤ (N i : ℝ) / 8
    calc
      _ ≤ η * (N i : ℝ) := mul_le_mul_of_nonneg_right hρ hN
      _ ≤ (1 / 8) * (N i : ℝ) := mul_le_mul_of_nonneg_right hη1 hN
      _ = _ := by ring
  | some k =>
    cases k with
    | inl k =>
      have hleft : σ * η / L ≤ η / T (.inl k) := by
        calc
          _ ≤ η / L := div_le_div_of_nonneg_right (by nlinarith) hL0.le
          _ ≤ _ := div_le_div_of_nonneg_left hη (hT _) (hTL _)
      change (σ * η / L) * (N i : ℝ) ≤ η * ((N i : ℝ) / T (.inl k))
      calc
        _ ≤ (η / T (.inl k)) * (N i : ℝ) := mul_le_mul_of_nonneg_right hleft hN
        _ = _ := by ring
    | inr f =>
      have hleft : σ * η / L ≤ (σ * η) / T (.inr f) :=
        div_le_div_of_nonneg_left (mul_nonneg hσ hη) (hT _) (hTL _)
      change (σ * η / L) * (N i : ℝ) ≤ (σ * η) * ((N i : ℝ) / T (.inr f))
      calc
        _ ≤ ((σ * η) / T (.inr f)) * (N i : ℝ) := mul_le_mul_of_nonneg_right hleft hN
        _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F]

theorem kernelNoiseScale_reciprocal :
    1 / kernelNoiseScale G X F =
      64 * ((Fintype.card ((G × X) ⊕ F) : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) := by
  unfold kernelNoiseScale kernelAnchorScale
  field_simp
  ring

theorem kernelNoiseScale_reciprocal_le {P : ℝ}
    (hK : (Fintype.card ((G × X) ⊕ F) : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P) :
    1 / kernelNoiseScale G X F ≤ Real.exp (2 * P + 64) := by
  have h1 : (Fintype.card ((G × X) ⊕ F) : ℝ) + 1 ≤ Real.exp P :=
    (add_le_add hK (le_refl 1)).trans (Real.add_one_le_exp P)
  have h2 : (Fintype.card X : ℝ) + 1 ≤ Real.exp P :=
    (add_le_add hX (le_refl 1)).trans (Real.add_one_le_exp P)
  have h64 : (64 : ℝ) ≤ Real.exp 64 := by linarith [Real.add_one_le_exp 64]
  rw [kernelNoiseScale_reciprocal]
  calc
    _ ≤ Real.exp 64 * Real.exp P * Real.exp P :=
      mul_le_mul (mul_le_mul h64 h1 (by positivity) (Real.exp_nonneg _)) h2
        (by positivity) (by positivity)
    _ = Real.exp (2 * P + 64) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem kernelSpatial_relative_width_budget {P Q σ L : ℝ}
    (hK : (Fintype.card ((G × X) ⊕ F) : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hσ : 0 < σ) (hσP : 1 / σ ≤ Real.exp P) (hL : 0 < L) (hLQ : L ≤ Real.exp Q) :
    0 < σ * kernelNoiseScale G X F / L ∧
      1 / (σ * kernelNoiseScale G X F / L) ≤ Real.exp (Q + 3 * P + 64) := by
  have hη : 0 < kernelNoiseScale G X F := (kernelSpatial_scales G X F).2.1
  refine ⟨by positivity, ?_⟩
  have heq : 1 / (σ * kernelNoiseScale G X F / L) =
      L * (1 / σ) * (1 / kernelNoiseScale G X F) := by field_simp
  rw [heq]
  calc
    _ ≤ Real.exp Q * Real.exp P * Real.exp (2 * P + 64) :=
      mul_le_mul (mul_le_mul hLQ hσP (by positivity) (Real.exp_nonneg _))
        (kernelNoiseScale_reciprocal_le hK hX) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem kernelSpatial_rounding_scale [DecidableEq X] {P Q L : ℝ}
    (hK : (Fintype.card ((G × X) ⊕ F) : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (_hL : 0 < L) (hLQ : L ≤ Real.exp Q)
    (N : X → ℕ) (hN : ∀ i, Real.exp (Q + 2 * P + 64) ≤ (N i : ℝ))
    (T : (G × X) ⊕ F → ℝ) (_hT : ∀ k, 0 < T k) (hTL : ∀ k, T k ≤ L)
    (g : G) (j i : X) :
    1 / ((N i : ℝ) / T (.inl (g,j))) ≤ kernelNoiseScale G X F := by
  have hη : 0 < kernelNoiseScale G X F := (kernelSpatial_scales G X F).2.1
  have hn : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
  have hlarge : L * (1 / kernelNoiseScale G X F) ≤ (N i : ℝ) := by
    calc
      _ ≤ Real.exp Q * Real.exp (2 * P + 64) :=
        mul_le_mul hLQ (kernelNoiseScale_reciprocal_le hK hX) (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (Q + 2 * P + 64) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hN i
  have hmul : L ≤ (N i : ℝ) * kernelNoiseScale G X F := by
    apply (div_le_iff₀ hη).mp
    simpa only [div_eq_mul_inv, one_div, one_mul] using hlarge
  have heq : 1 / ((N i : ℝ) / T (.inl (g,j))) = T (.inl (g,j)) / (N i : ℝ) := by field_simp
  rw [heq]
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_comm] using (hTL (.inl (g,j))).trans hmul

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F]

theorem two_div_kernelAnchorScale :
    2 / kernelAnchorScale G X F = 32 * ((Fintype.card ((G × X) ⊕ F) : ℝ) + 1) := by
  unfold kernelAnchorScale
  field_simp
  ring

theorem kernelNoiseScale_nonkernel_cap :
    (Fintype.card F : ℝ) * kernelNoiseScale G X F ≤ 1 / 16 := by
  have hs := kernelSpatial_scales G X F
  have hFM : (Fintype.card F : ℝ) ≤ (Fintype.card ((G × X) ⊕ F) : ℝ) := by
    exact_mod_cast (show Fintype.card F ≤ Fintype.card ((G × X) ⊕ F) by
      simp only [Fintype.card_sum]; omega)
  have hmul := mul_le_mul_of_nonneg_right hFM hs.2.1.le
  have hnonneg := mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card ((G × X) ⊕ F))) hs.1.le
  have hfit := hs.2.2.2.2
  nlinarith

omit [Fintype G] [Fintype X] [Fintype F] in
theorem kernelSpatial_early_widths_independent
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (η σ τ : ℝ) :
    (∀ i, kernelSpatialWidths N T η σ (none, i) = kernelSpatialWidths N T η τ (none, i)) ∧
    (∀ g j i, kernelSpatialWidths N T η σ (some (.inl (g,j)), i) =
      kernelSpatialWidths N T η τ (some (.inl (g,j)), i)) := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem canonicalKernelSpatial_support [DecidableEq X]
    (N : X → ℕ) (hN : ∀ i, 4 ≤ N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ kernelNoiseScale G X F)
    (modulus : X → ℕ)
    (S : Finset (ColumnResiduePattern (Option ((G × X) ⊕ F)) X modulus))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus S
      (kernelSpatialWidths N T (kernelNoiseScale G X F) σ) z)
    (D : (Option ((G × X) ⊕ F) × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus S
      (kernelSpatialWidths N T (kernelNoiseScale G X F) σ)
      (fun u => D (kernelSpatialAnchor N T (kernelAnchorScale G X F) + u)))
    (z : Option ((G × X) ⊕ F) × X → ℤ)
    (hz : 0 < (translatedSelectedResidueDensityPMF
      (kernelSpatialAnchor N T (kernelAnchorScale G X F)) modulus S
      (kernelSpatialWidths N T (kernelNoiseScale G X F) σ)
      (kernelSpatialWidths_pos N (fun i => by have := hN i; omega) T hT
        (kernelSpatial_scales G X F).2.1 hσ0) hZ D hD0 hD z).toReal) :
    (∀ g, (matrixSupCLM (normalizedKernelBlock N T z g)).IsInvertible ∧
      ‖(matrixSupCLM (normalizedKernelBlock N T z g)).inverse‖ ≤
        32 * ((Fintype.card ((G × X) ⊕ F) : ℝ) + 1)) ∧
    (∀ root : (G × X) ⊕ F → ℤ, (∀ k, |(root k : ℝ)| ≤ T k) →
      integerPhysicalSite root z ∈ integerBox N) ∧
    (∀ root : (G × X) ⊕ F → ℤ, (∀ k, |(root k : ℝ)| ≤ T k) → ∀ i,
      |∑ f : F, (root (.inr f) : ℝ) * (z (some (.inr f), i) : ℝ)| ≤ σ * (N i : ℝ) / 16) := by
  have hs := kernelSpatial_scales G X F
  have h := translatedKernelSpatial_support N hN T hT hs.1 hs.2.1 hσ0 hσ1 hscale
    hs.2.2.2.1 hs.2.2.2.2 modulus S hZ D hD0 hD z hz
  refine ⟨?_, h.2.1, ?_⟩
  · intro g
    simpa only [two_div_kernelAnchorScale] using h.1 g
  · intro root hroot i
    calc
      _ ≤ (Fintype.card F : ℝ) * (σ * kernelNoiseScale G X F) * (N i : ℝ) := h.2.2 root hroot i
      _ = ((Fintype.card F : ℝ) * kernelNoiseScale G X F) * (σ * (N i : ℝ)) := by ring
      _ ≤ (1 / 16) * (σ * (N i : ℝ)) :=
        mul_le_mul_of_nonneg_right kernelNoiseScale_nonkernel_cap (by positivity)
      _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F]

noncomputable def smallKernelSpatialAnchor [DecidableEq X]
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (θ : ℝ) : Option ((G × X) ⊕ F) × X → ℤ :=
  baseArrayJoin (fun k => kernelSpatialAnchor N T (θ * kernelAnchorScale G X F) (some k.1,k.2)) 0

noncomputable def smallKernelSpatialWidths
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (θ τ : ℝ) : Option ((G × X) ⊕ F) × X → ℝ :=
  fun z => θ * kernelSpatialWidths N T (kernelNoiseScale G X F) τ z

theorem smallKernelSpatialWidths_pos
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (z) :
    0 < smallKernelSpatialWidths N T θ τ z :=
  mul_pos hθ (kernelSpatialWidths_pos N hN T hT (kernelSpatial_scales G X F).2.1 hτ z)

theorem smallKernelSpatialWidths_le
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) {θ τ : ℝ} (hθ : θ ≤ 1) (z) :
    smallKernelSpatialWidths N T θ τ z ≤
      kernelSpatialWidths N T (θ * kernelNoiseScale G X F) τ z := by
  rcases z with ⟨k,i⟩
  cases k with
  | none =>
    change θ * ((N i : ℝ) / 8) ≤ (N i : ℝ) / 8
    exact mul_le_of_le_one_left (by positivity) hθ
  | some k =>
    rcases k with ⟨g,j⟩ | f
    · change θ * (kernelNoiseScale G X F * ((N i : ℝ) / T (.inl (g,j)))) ≤ _
      exact le_of_eq (by dsimp only [kernelSpatialWidths]; ring)
    · change θ * (τ * kernelNoiseScale G X F * ((N i : ℝ) / T (.inr f))) ≤ _
      exact le_of_eq (by dsimp only [kernelSpatialWidths]; ring)

theorem smallKernelSpatial_column_identity [DecidableEq X]
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (θ : ℝ)
    (u : Option ((G × X) ⊕ F) × X → ℤ) (k) (i) :
    (smallKernelSpatialAnchor N T θ + u) (some k,i) =
      (kernelSpatialAnchor N T (θ * kernelAnchorScale G X F) + u) (some k,i) := rfl

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F] [DecidableEq X]

theorem smallKernelSpatial_column_bound
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hτ1 : τ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ θ * kernelNoiseScale G X F)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (smallKernelSpatialWidths N T θ τ) 1) (k) (i) :
    |((smallKernelSpatialAnchor N T θ + u) (some k,i) : ℝ) / ((N i : ℝ) / T k)| ≤
      θ * (kernelAnchorScale G X F + 2 * kernelNoiseScale G X F) := by
  have hs := kernelSpatial_scales G X F
  have hu' := rectangularWeightIndices_zero_mono (smallKernelSpatialWidths_le N T hθ1) hu
  have h := kernelSpatial_column_bound N hN T hT (mul_nonneg hθ hs.1.le)
    (mul_nonneg hθ hs.2.1.le) hτ1 hscale hu' k i
  rw [smallKernelSpatial_column_identity]
  exact h.trans_eq (by ring)

theorem smallKernelSpatial_site_bound
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hτ1 : τ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ θ * kernelNoiseScale G X F)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (smallKernelSpatialWidths N T θ τ) 1)
    (root : (G × X) ⊕ F → ℤ) (hroot : ∀ k, |(root k : ℝ)| ≤ T k) (i : X) :
    |(integerPhysicalSite root (smallKernelSpatialAnchor N T θ + u) i : ℝ)| ≤ θ * (N i : ℝ) / 4 := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  let a := kernelAnchorScale G X F
  let η := kernelNoiseScale G X F
  have hbase := rectangularWeightIndices_zero_bound (smallKernelSpatialWidths N T θ τ) hu (none,i)
  change |(u (none,i) : ℝ)| ≤ θ * ((N i : ℝ) / 8) at hbase
  have hcol (k) : |(root k : ℝ) * ((smallKernelSpatialAnchor N T θ + u) (some k,i) : ℝ)| ≤
      (θ * (a + 2 * η)) * (N i : ℝ) :=
    scaled_coordinate_product_bound hn (hT k)
      (smallKernelSpatial_column_bound N hN T hT hθ hθ1 hτ1 hscale hu k i) (hroot k)
  have hfit := mul_le_mul_of_nonneg_right (kernelSpatial_scales G X F).2.2.2.2
    (mul_nonneg hθ hn.le)
  have heq : (integerPhysicalSite root (smallKernelSpatialAnchor N T θ + u) i : ℝ) =
      (u (none,i) : ℝ) + ∑ k, (root k : ℝ) *
        ((smallKernelSpatialAnchor N T θ + u) (some k,i) : ℝ) := by
    simp only [integerPhysicalSite, Pi.add_apply, smallKernelSpatialAnchor, baseArrayJoin,
      Pi.zero_apply, zero_add, Int.cast_add, Int.cast_sum, Int.cast_mul]
  have hraw : |(integerPhysicalSite root (smallKernelSpatialAnchor N T θ + u) i : ℝ)| ≤
      θ * ((N i : ℝ) / 8) + (Fintype.card ((G × X) ⊕ F) : ℝ) *
        (θ * (a + 2 * η)) * (N i : ℝ) := by
    rw [heq]
    calc
      _ ≤ |(u (none,i) : ℝ)| + |∑ k, (root k : ℝ) *
          ((smallKernelSpatialAnchor N T θ + u) (some k,i) : ℝ)| := abs_add_le _ _
      _ ≤ θ * ((N i : ℝ) / 8) + ∑ k, |(root k : ℝ) *
          ((smallKernelSpatialAnchor N T θ + u) (some k,i) : ℝ)| :=
        add_le_add hbase (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ θ * ((N i : ℝ) / 8) + ∑ _k : (G × X) ⊕ F,
          (θ * (a + 2 * η)) * (N i : ℝ) := add_le_add le_rfl (Finset.sum_le_sum (fun k _ => hcol k))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  dsimp only [a, η] at hraw
  nlinarith

theorem smallKernelSpatial_trim_margin
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hτ1 : τ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ θ * kernelNoiseScale G X F)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (smallKernelSpatialWidths N T θ τ) 1)
    (root : (G × X) ⊕ F → ℤ) (hroot : ∀ k, |(root k : ℝ)| ≤ T k) (i : X) :
    |integerPhysicalSite root (smallKernelSpatialAnchor N T θ + u) i| ≤
      (spatialTrimMargin θ N i : ℤ) := by
  have h := (smallKernelSpatial_site_bound N hN T hT hθ hθ1 hτ1 hscale hu root hroot i).trans
    (Nat.le_ceil (θ * (N i : ℝ) / 4))
  exact_mod_cast h

end Erdos3

end

section

namespace Erdos3

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F]

theorem smallKernelSpatialWidths_lower_bound
    (N : X → ℕ) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {L θ τ : ℝ} (hL : 1 ≤ L) (hTL : ∀ k, T k ≤ L)
    (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (z) :
    (θ * τ * kernelNoiseScale G X F / L) * (N z.2 : ℝ) ≤ smallKernelSpatialWidths N T θ τ z := by
  have hs := kernelSpatial_scales G X F
  have h := mul_le_mul_of_nonneg_left
    (kernelSpatialWidths_lower_bound N T hT hL hTL hs.2.1.le hs.2.2.1 hτ hτ1 z) hθ
  change (θ * τ * kernelNoiseScale G X F / L) * (N z.2 : ℝ) ≤
    θ * kernelSpatialWidths N T (kernelNoiseScale G X F) τ z
  calc
    _ = θ * ((τ * kernelNoiseScale G X F / L) * (N z.2 : ℝ)) := by ring
    _ ≤ _ := h

theorem smallKernelSpatial_relative_width_budget {P Q θ τ L : ℝ}
    (hK : (Fintype.card ((G × X) ⊕ F) : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hθ : 0 < θ) (hθP : 1 / θ ≤ Real.exp P) (hτ : 0 < τ) (hτP : 1 / τ ≤ Real.exp P)
    (hL : 0 < L) (hLQ : L ≤ Real.exp Q) :
    0 < θ * τ * kernelNoiseScale G X F / L ∧
      1 / (θ * τ * kernelNoiseScale G X F / L) ≤ Real.exp (Q + 4 * P + 64) := by
  have hη := (kernelSpatial_scales G X F).2.1
  have hρ := kernelSpatial_relative_width_budget hK hX hτ hτP hL hLQ
  refine ⟨by positivity, ?_⟩
  have heq : 1 / (θ * τ * kernelNoiseScale G X F / L) =
      (1 / θ) * (1 / (τ * kernelNoiseScale G X F / L)) := by field_simp
  rw [heq]
  calc
    _ ≤ Real.exp P * Real.exp (Q + 3 * P + 64) :=
      mul_le_mul hθP hρ.2 (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smallKernelSpatial_rounding_scale {P Q θ L : ℝ}
    (hK : (Fintype.card ((G × X) ⊕ F) : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hθ : 0 < θ) (hθP : 1 / θ ≤ Real.exp P) (hLQ : L ≤ Real.exp Q)
    (N : X → ℕ) (hN : ∀ i, Real.exp (Q + 3 * P + 64) ≤ (N i : ℝ))
    (T : (G × X) ⊕ F → ℝ) (hTL : ∀ k, T k ≤ L) (g : G) (j i : X) :
    1 / ((N i : ℝ) / T (.inl (g,j))) ≤ θ * kernelNoiseScale G X F := by
  have hη := (kernelSpatial_scales G X F).2.1
  have hn : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
  have hinv : 1 / (θ * kernelNoiseScale G X F) ≤ Real.exp (3 * P + 64) := by
    have heq : 1 / (θ * kernelNoiseScale G X F) =
        (1 / θ) * (1 / kernelNoiseScale G X F) := by field_simp
    rw [heq]
    calc
      _ ≤ Real.exp P * Real.exp (2 * P + 64) :=
        mul_le_mul hθP (kernelNoiseScale_reciprocal_le hK hX) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlarge : L / (θ * kernelNoiseScale G X F) ≤ (N i : ℝ) := by
    calc
      _ = L * (1 / (θ * kernelNoiseScale G X F)) := by ring
      _ ≤ Real.exp Q * Real.exp (3 * P + 64) :=
        mul_le_mul hLQ hinv (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (Q + 3 * P + 64) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hN i
  have hmul := (div_le_iff₀ (mul_pos hθ hη)).mp hlarge
  have heq : 1 / ((N i : ℝ) / T (.inl (g,j))) = T (.inl (g,j)) / (N i : ℝ) := by field_simp
  rw [heq]
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_comm] using (hTL (.inl (g,j))).trans hmul

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

variable {G X F : Type*} [Fintype G] [Fintype X] [Fintype F] [DecidableEq X]

theorem smallKernelSpatial_kernel_inverse
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ θ * kernelNoiseScale G X F)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (smallKernelSpatialWidths N T θ τ) 1)
    (base : X → ℤ) (g : G) :
    (matrixSupCLM (normalizedKernelBlock N T
      ((integerBaseTranslation base + smallKernelSpatialAnchor N T θ) + u) g)).IsInvertible ∧
      ‖(matrixSupCLM (normalizedKernelBlock N T
        ((integerBaseTranslation base + smallKernelSpatialAnchor N T θ) + u) g)).inverse‖ ≤
        (32 * ((Fintype.card ((G × X) ⊕ F) : ℝ) + 1)) / θ := by
  have hs := kernelSpatial_scales G X F
  have hu' := rectangularWeightIndices_zero_mono (smallKernelSpatialWidths_le N T hθ1) hu
  have hsmall : (Fintype.card X : ℝ) * (2 * (θ * kernelNoiseScale G X F)) ≤
      (θ * kernelAnchorScale G X F) / 2 := by
    have h := mul_le_mul_of_nonneg_left hs.2.2.2.1 hθ.le
    nlinarith
  have h := kernelSpatial_kernel_inverse N hN T hT (mul_pos hθ hs.1)
    (mul_nonneg hθ.le hs.2.1.le) hscale hsmall hu' g
  have heq : normalizedKernelBlock N T
      ((integerBaseTranslation base + smallKernelSpatialAnchor N T θ) + u) g =
        normalizedKernelBlock N T (kernelSpatialAnchor N T (θ * kernelAnchorScale G X F) + u) g := by
    ext i j
    simp only [normalizedKernelBlock, integerBaseTranslation, smallKernelSpatialAnchor,
      baseArrayJoin, Pi.add_apply, Pi.zero_apply, zero_add]
  rw [heq]
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [show 2 / (θ * kernelAnchorScale G X F) = (2 / kernelAnchorScale G X F) / θ by
    field_simp, two_div_kernelAnchorScale]

theorem smallKernelSpatial_nonkernel_displacement
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hτ : 0 ≤ τ)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (smallKernelSpatialWidths N T θ τ) 1)
    (base : X → ℤ) (root : (G × X) ⊕ F → ℤ) (hroot : ∀ k, |(root k : ℝ)| ≤ T k) (i : X) :
    |∑ f : F, (root (.inr f) : ℝ) *
      (((integerBaseTranslation base + smallKernelSpatialAnchor N T θ + u :
        Option ((G × X) ⊕ F) × X → ℤ) (some (.inr f),i)) : ℝ)| ≤
        τ * θ * (N i : ℝ) / 16 := by
  have hu' := rectangularWeightIndices_zero_mono (smallKernelSpatialWidths_le N T hθ1) hu
  have h := kernelSpatial_nonkernel_displacement N hN T hT
    (θ * kernelAnchorScale G X F) (θ * kernelNoiseScale G X F) τ hu' root hroot i
  calc
    _ ≤ (Fintype.card F : ℝ) * (τ * (θ * kernelNoiseScale G X F)) * (N i : ℝ) := by
      simpa only [Pi.add_apply, integerBaseTranslation, smallKernelSpatialAnchor, baseArrayJoin,
        kernelSpatialAnchor, kernelColumnCenter, Pi.zero_apply, mul_zero, Int.floor_zero, zero_add] using h
    _ = ((Fintype.card F : ℝ) * kernelNoiseScale G X F) * (τ * θ * (N i : ℝ)) := by ring
    _ ≤ (1 / 16) * (τ * θ * (N i : ℝ)) :=
      mul_le_mul_of_nonneg_right kernelNoiseScale_nonkernel_cap (by positivity)
    _ = _ := by ring

theorem smallKernelSpatial_base_mem_box
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1/2) (hτ1 : τ ≤ 1)
    (hsize : ∀ i, 4 ≤ θ * (N i : ℝ))
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ θ * kernelNoiseScale G X F)
    {u : Option ((G × X) ⊕ F) × X → ℤ}
    (hu : u ∈ rectangularWeightIndices 0 (smallKernelSpatialWidths N T θ τ) 1)
    {base : X → ℤ} (hb : base ∈ trimmedIntegerBox N (spatialTrimMargin θ N))
    (root : (G × X) ⊕ F → ℤ) (hroot : ∀ k, |(root k : ℝ)| ≤ T k) :
    integerPhysicalSite root ((integerBaseTranslation base + smallKernelSpatialAnchor N T θ) + u) ∈
      integerBox N := by
  rw [add_assoc, integerPhysicalSite_baseTranslation_add]
  exact trimmedIntegerBox_add_mem N (spatialTrimMargin θ N)
    (fun i => (spatialTrimMargin_proper hθhalf N hN hsize i).le) hb _
    (smallKernelSpatial_trim_margin N hN T hT hθ.le (by linarith) hτ1 hscale hu root hroot)

theorem translatedSmallKernelSpatial_support
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (T : (G × X) ⊕ F → ℝ) (hT : ∀ k, 0 < T k)
    {θ τ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1/2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hsize : ∀ i, 4 ≤ θ * (N i : ℝ))
    (hscale : ∀ g j i, 1 / ((N i : ℝ) / T (.inl (g,j))) ≤ θ * kernelNoiseScale G X F)
    {base : X → ℤ} (hb : base ∈ trimmedIntegerBox N (spatialTrimMargin θ N))
    (modulus : X → ℕ)
    (S : Finset (ColumnResiduePattern (Option ((G × X) ⊕ F)) X modulus))
    (hZ : 0 < ∑' u, selectedResidueSmoothWeight modulus S (smallKernelSpatialWidths N T θ τ) u)
    (D : (Option ((G × X) ⊕ F) × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus S (smallKernelSpatialWidths N T θ τ)
      (fun u => D ((integerBaseTranslation base + smallKernelSpatialAnchor N T θ) + u)))
    (z : Option ((G × X) ⊕ F) × X → ℤ)
    (hz : 0 < (translatedSelectedResidueDensityPMF
      (integerBaseTranslation base + smallKernelSpatialAnchor N T θ) modulus S
      (smallKernelSpatialWidths N T θ τ) (smallKernelSpatialWidths_pos N hN T hT hθ hτ)
      hZ D hD0 hD z).toReal) :
    (∀ g, (matrixSupCLM (normalizedKernelBlock N T z g)).IsInvertible ∧
      ‖(matrixSupCLM (normalizedKernelBlock N T z g)).inverse‖ ≤
        (32 * ((Fintype.card ((G × X) ⊕ F) : ℝ) + 1)) / θ) ∧
    (∀ root : (G × X) ⊕ F → ℤ, (∀ k, |(root k : ℝ)| ≤ T k) →
      integerPhysicalSite root z ∈ integerBox N) ∧
    (∀ root : (G × X) ⊕ F → ℤ, (∀ k, |(root k : ℝ)| ≤ T k) → ∀ i,
      |∑ f : F, (root (.inr f) : ℝ) * (z (some (.inr f),i) : ℝ)| ≤ τ * θ * (N i : ℝ) / 16) := by
  let anchor := integerBaseTranslation base + smallKernelSpatialAnchor N T θ
  have hu := (translatedSelectedResidueDensityPMF_support anchor modulus S
    (smallKernelSpatialWidths N T θ τ) (smallKernelSpatialWidths_pos N hN T hT hθ hτ)
    hZ D hD0 hD z hz).1
  have heq : (integerBaseTranslation base + smallKernelSpatialAnchor N T θ) + (z - anchor) = z := by
    dsimp only [anchor]
    abel
  refine ⟨?_, ?_, ?_⟩
  · intro g
    simpa only [heq] using smallKernelSpatial_kernel_inverse N hN T hT hθ (by linarith) hscale hu base g
  · intro root hroot
    simpa only [heq] using smallKernelSpatial_base_mem_box N hN T hT hθ hθhalf hτ1 hsize hscale hu hb root hroot

  · intro root hroot i
    simpa only [heq] using smallKernelSpatial_nonkernel_displacement N hN T hT hθ.le
      (by linarith) hτ.le hu base root hroot i

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_small_kernel_near_uniform_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G] [Nonempty G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables (G × X) I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (θ τ : ℝ) (_hθ : 0 < θ) (_hθhalf : θ ≤ 1/2) (_hθP : 1/θ ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hτP : 1/τ ≤ Real.exp P)
    (_hθδ : 2 * (Fintype.card X : ℝ) * θ ≤ δ)
    (root : LayerSamplerVariables (G × X) I n B → ℤ) (_hroot : root ∈ layerSamplerIntegerBox B U b
      (selectedLayerSamplerScale (G := G × X) B U b R σ hR hσ L₀))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hN : ∀ i, 0 < N i)
    (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (G × X) I n B)) X stride)) (_hT : T.Nonempty),
    let scale := selectedLayerSamplerScale (G := G × X) B U b R σ hR hσ L₀
    let sites := layerSamplerIntegerBox B U b scale
    let F := PrincipalTupleIndex B (layerSamplerDegree I n)
    let spatialSides := layerSamplerBox B U b scale
    let anchor := smallKernelSpatialAnchor N spatialSides θ
    let W := smallKernelSpatialWidths N spatialSides θ τ
    let hW := smallKernelSpatialWidths_pos N _hN spatialSides
      (fun k => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (layerSamplerBox_one_le B U b scale k)) _hθ _hτ
    let bases := trimmedIntegerBox N (spatialTrimMargin θ N)
    let D := fun center => translatedSelectedPhysicalDensity (G := G × X) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) p hm
    let Z := fun base center => selectedResidueDensityMass stride T W
      (fun u => D center ((integerBaseTranslation base + anchor) + u))
    ∃ hbase : bases.Nonempty, ∃ hparent : (integerBox N).Nonempty,
    ∃ hZ : 0 < ∑' u, selectedResidueSmoothWeight stride T W u,
    ∃ hD : ∀ base center, 0 < Z base center,
    let law := fun center => selectedAnchoredMixture bases hbase
      (fun base => integerBaseTranslation base + anchor) stride T W hW hZ (D center)
      (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) p hm) (fun base => hD base center);
      (∀ base center, |Z base center-1| ≤ 3*δ ∧ 1/2 ≤ Z base center ∧ Z base center ≤ 3/2) ∧
      (∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(𝔼 base ∈ bases,
          ∫ center, ∑' z, ((translatedSelectedResidueDensityPMF
            (integerBaseTranslation base + anchor) stride T W hW hZ (D center)
            (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) p hm) (hD base center) z).toReal : ℂ) *
              φ (physicalAffineSite root z) ∂μ) -
          𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))‖ ≤ 7*δ) ∧
      (∀ base ∈ bases, ∀ center z,
        0 < (translatedSelectedResidueDensityPMF
          (integerBaseTranslation base + anchor) stride T W hW hZ (D center)
          (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) p hm) (hD base center) z).toReal →
        (∀ g, (matrixSupCLM (normalizedKernelBlock N spatialSides z g)).IsInvertible ∧
          ‖(matrixSupCLM (normalizedKernelBlock N spatialSides z g)).inverse‖ ≤
            (32 * ((Fintype.card (LayerSamplerVariables (G × X) I n B) : ℝ) + 1)) / θ) ∧
        (∀ r : LayerSamplerVariables (G × X) I n B → ℤ,
          (∀ k, |(r k : ℝ)| ≤ spatialSides k) → integerPhysicalSite r z ∈ integerBox N) ∧
        (∀ r : LayerSamplerVariables (G × X) I n B → ℤ,
          (∀ k, |(r k : ℝ)| ≤ spatialSides k) → ∀ i,
          |∑ f : F, (r (.inr f) : ℝ) * (z (some (.inr f),i) : ℝ)| ≤ τ * θ * (N i : ℝ) / 16)) ∧
      (∀ base center,
        (∑' z, (translatedSelectedResidueDensityPMF
          (integerBaseTranslation base + anchor) stride T W hW hZ (D center)
          (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) p hm) (hD base center) z).toReal *
          noninjectivityIndicator (fun q : sites => integerPhysicalSite q.val z)) ≤ δ) ∧
      (∀ center, ∃ c : ∀ j, U j, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U (fun s => c s.1))) ∧
        ∀ base z, 0 < (translatedSelectedResidueDensityPMF
          (integerBaseTranslation base + anchor) stride T W hW hZ (D center)
          (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) p hm) (hD base center) z).toReal →
          HasQuarterAffinePolynomialLifts p (fun j => (c j).val) (fun k v => (z (k,v) : ℝ))
            (layerSamplerBox B U b scale)) ∧
      (∀ center (φ : (X → ℝ) → ℝ), (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (𝔼 base ∈ bases,
          ∑' z, (translatedSelectedResidueDensityPMF
            (integerBaseTranslation base + anchor) stride T W hW hZ (D center)
            (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) p hm) (hD base center) z).toReal *
              φ (physicalAffineSite root z)) ≤
          2 * (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) *
            (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ) ∧
      (∀ center,
        (∀ {Y : Type*} [Fintype Y] (Fobs : (X → ℝ) → Y),
        let reference := (FiniteProbabilityWeights.uniformFinset (integerBox N) hparent).fiberLaw
          (fun x => Fobs (fun i => (x.val i : ℝ)))
        let marginal := (law center).fiberLaw (fun z => Fobs (physicalAffineSite root
          ((integerBaseTranslation (K := LayerSamplerVariables (G × X) I n B) z.1.val + anchor) + z.2.val)))
        let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
        reference.excessMass marginal (2*M) ≤ 6*δ ∧
          marginal.mass (Finset.univ.filter (fun y => 4*M*reference.weight y < marginal.weight y)) ≤ 12*δ) ∧
        (let marginal := (law center).fiberLaw (fun z => integerBoxObservation N hparent
            (physicalAffineSite root
              ((integerBaseTranslation (K := LayerSamplerVariables (G × X) I n B) z.1.val + anchor) + z.2.val)));
         let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j);
         (FiniteProbabilityWeights.uniformFinset (integerBox N) hparent).excessMass marginal (2*M) ≤ 6*δ ∧
           marginal.mass (Finset.univ.filter (fun x => 4*M/(integerBox N).card < marginal.weight x)) ≤ 12*δ)) := by
  obtain ⟨aM, haM, hmixed⟩ := exists_base_and_center_mixed_selected_sampler_law m
  obtain ⟨aG, _, hgeometry⟩ := exists_centered_full_parameter_anchored_geometry m
  obtain ⟨aD, _, hdomination⟩ := exists_anchored_fixed_center_selected_sampler_box_domination m
  let a := max aM (max aG aD)
  have ha : 2 ≤ a := haM.trans (le_max_left _ _)
  obtain ⟨A, hA, hthreshold⟩ := exists_smallKernelSamplerThreshold m a
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP θ τ hθ hθhalf hθP hτ hτ1 hτP hθδ
    root hroot p hp hm stride hs Rrank S hS hSP hstride N hN hsize hrank hRrank T hT
  let scale := selectedLayerSamplerScale (G := G × X) B U b R σ hR hσ L₀
  let spatialSides := layerSamplerBox B U b scale
  let anchor := smallKernelSpatialAnchor N spatialSides θ
  let W := smallKernelSpatialWidths N spatialSides θ τ
  have hsidepos (k) : 0 < spatialSides k :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (layerSamplerBox_one_le B U b scale k)
  have hLpos : (0 : ℝ) < scale.value := by exact_mod_cast scale.positive
  have hL1 : (1 : ℝ) ≤ scale.value := by exact_mod_cast scale.positive
  have hsidele (k) : spatialSides k ≤ (scale.value : ℝ) := layerSamplerBox_le B U b scale k
  have hW := smallKernelSpatialWidths_pos N hN spatialSides hsidepos hθ hτ
  let Q := selectedFourierInputBudget m P
  let P' := smallKernelSamplerBudget m P
  have hP' : 0 ≤ P' := smallKernelSamplerBudget_nonneg m hP
  have hmono (c : ℕ) (hc : c ≤ a) : Real.exp ((P'+c)^c) ≤ Real.exp ((P'+a)^a) := by
    apply Real.exp_le_exp.mpr
    have hca : (c : ℝ) ≤ a := by exact_mod_cast hc
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P'+(c:ℝ) ≤ P'+a) c).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P'+a) hc)
  have hthresholdM := (hmono aM (le_max_left _ _)).trans (hthreshold P hP).2
  have hthresholdG := (hmono aG ((le_max_left _ _).trans (le_max_right _ _))).trans (hthreshold P hP).2
  have hthresholdD := (hmono aD ((le_max_right _ _).trans (le_max_right _ _))).trans (hthreshold P hP).2
  have hPP' : P ≤ P' := le_smallKernelSamplerBudget m hP
  have hQQ' : Q ≤ P' := by dsimp [P', smallKernelSamplerBudget, Q]; linarith
  have heP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP'
  have hL : (scale.value : ℝ) ≤ Real.exp Q :=
    selectedLayerSamplerScale_input_bound B U b R σ hR hσ L₀ hP hK hn hRP hσP hAP hL₀P
  let ρ := θ * τ * kernelNoiseScale G X (PrincipalTupleIndex B (layerSamplerDegree I n)) /
    (scale.value : ℝ)
  have hρ := smallKernelSpatial_relative_width_budget hK hX hθ hθP hτ hτP hLpos hL
  have hρP : 1 / ρ ≤ Real.exp P' := hρ.2.trans (Real.exp_le_exp.mpr (by
    dsimp [P', smallKernelSamplerBudget, Q]; linarith))
  have hwidth (z) : ρ * (N z.2 : ℝ) ≤ W z :=
    smallKernelSpatialWidths_lower_bound N spatialSides hsidepos hL1 hsidele hθ.le hτ.le hτ1 z
  have hNlarge (i) : Real.exp (Q + 3 * P + 64) ≤ (N i : ℝ) := by
    have hb' : Q + 3 * P + 64 ≤ P' := by dsimp [P', smallKernelSamplerBudget, Q]; linarith
    exact (Real.exp_le_exp.mpr hb').trans ((hthreshold P hP).1.trans (hsize i))
  have hround := smallKernelSpatial_rounding_scale hK hX hθ hθP hL N hNlarge spatialSides hsidele
  have hNθ (i) : 4 ≤ θ * (N i : ℝ) := by
    apply spatialTrimMargin_size_of_exp_size hP hθ (by simpa only [one_div] using hθP)
    have hb' : 5 * P + 128 ≤ P' := by
      dsimp [P', smallKernelSamplerBudget, Q]
      have h := le_selectedFourierInputBudget m hP
      linarith
    exact (Real.exp_le_exp.mpr hb').trans ((hthreshold P hP).1.trans (hsize i))
  have hrootSide (k) : |(root k : ℝ)| ≤ spatialSides k := layerSamplerIntegerBox_abs_bound B U b scale hroot k
  have hrootP (k) : |(root k : ℝ)| ≤ Real.exp P' :=
    (hrootSide k).trans ((hsidele k).trans (hL.trans (Real.exp_le_exp.mpr hQQ')))
  have hnoise (u) (hu : u ∈ rectangularWeightIndices 0 W 1) (i) :
      |integerPhysicalSite root (anchor + u) i| ≤ (spatialTrimMargin θ N i : ℤ) :=
    smallKernelSpatial_trim_margin N hN spatialSides hsidepos hθ.le (by linarith) hτ1 hround hu root hrootSide i
  obtain ⟨hZ, hD, hnormal, hcompare⟩ := hmixed B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP' hδ hδsmall (hδP.trans heP) (hX.trans hPP') (hK.trans hPP')
    (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
    (hAP.trans heP) (hL₀P.trans heP) (fun j => (hCP j).trans heP) (fun j => (hVP j).trans heP)
    (fun j => (hRP j).trans heP) (fun j => (hσP j).trans heP)
    anchor root hrootP p hp hm stride hs hS (hSP.trans heP) hstride hρ.1 hρP (fun i => (N i : ℝ))
    (fun i => hthresholdM.trans (hsize i)) hrank (hthresholdM.trans hRrank)
    T hT W hW hwidth N (spatialTrimMargin θ N) (spatialTrimMargin_proper hθhalf N hN hNθ) hnoise
  have hbase := trimmedIntegerBox_nonempty N (spatialTrimMargin θ N)
    (spatialTrimMargin_proper hθhalf N hN hNθ)
  have hparent : (integerBox N).Nonempty := by
    refine ⟨0, (mem_integerBox N 0).mpr ?_⟩
    intro i
    refine ⟨le_refl 0, ?_⟩
    change (0 : ℤ) < (N i : ℤ)
    exact_mod_cast hN i
  refine ⟨hbase, hparent, hZ, hD, hnormal, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ hφ
    have hc := hcompare φ hφ
    have hb' := spatialTrimMargin_error_bound N hN hNθ
    exact hc.trans (by linarith)
  · intro base hb' center z hz
    exact translatedSmallKernelSpatial_support N hN spatialSides hsidepos hθ hθhalf hτ hτ1 hNθ hround
      hb' stride T hZ _
      (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) p hm) (hD base center) z hz

  · intro base center
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcollision⟩ :=
      hgeometry B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
        hP' hδ hδsmall (hδP.trans heP) (hX.trans hPP') (hK.trans hPP')
        (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
        (hAP.trans heP) (hL₀P.trans heP) (fun j => (hCP j).trans heP) (fun j => (hVP j).trans heP)
        (fun j => (hRP j).trans heP) (fun j => (hσP j).trans heP)
        center (integerBaseTranslation base + anchor) p hp hm stride hs hS (hSP.trans heP) hstride
        hρ.1 hρP (fun i => (N i : ℝ)) (fun i => hthresholdG.trans (hsize i)) hrank
        (hthresholdG.trans hRrank) T hT W hW hwidth
    exact hcollision
  · intro center
    obtain ⟨c, hc, hlift⟩ := exists_constant_center_uniform_lifts B U b hb o R σ hR hσ L₀
      hσ1 Cinv hCinv hchart hsmall p hp hm center
    refine ⟨c, hc, ?_⟩
    intro base z hz
    have hpos := (translatedSelectedResidueDensityPMF_support
      (integerBaseTranslation base + anchor) stride T W hW hZ
      (translatedSelectedPhysicalDensity (G := G × X) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) p hm)
      (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) p hm) (hD base center) z hz).2.2
    exact hlift z (ne_of_gt hpos)
  · have hloss : (∑ i, 2 * (spatialTrimMargin θ N i : ℝ) / N i) ≤ 1/2 := by
      have h := spatialTrimMargin_error_bound N hN hNθ
      linarith
    obtain ⟨_, _, _, hbound⟩ := hdomination B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall L₀ hP' hδ hδsmall (hδP.trans heP) (hX.trans hPP') (hK.trans hPP')
      (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
      (hAP.trans heP) (hL₀P.trans heP) (fun j => (hCP j).trans heP) (fun j => (hVP j).trans heP)
      (fun j => (hRP j).trans heP) (fun j => (hσP j).trans heP)
      anchor root hrootP p hp hm stride hs hS (hSP.trans heP) hstride hρ.1 hρP (fun i => (N i : ℝ))
      (fun i => hthresholdD.trans (hsize i)) hrank (hthresholdD.trans hRrank)
      T hT W hW hwidth N (spatialTrimMargin θ N) (spatialTrimMargin_proper hθhalf N hN hNθ) hnoise hloss
    constructor
    · intro center φ hφ
      exact hbound (coefficientConstantCenter U center) φ hφ
    · intro center
      have htwice (v : ℝ) : 2 * (2*v) = 4*v := by ring
      have herror : 2 * (6*δ) = 12*δ := by ring
      constructor
      · intro Y _ Fobs
        have hexcess := selectedAnchoredMixture_physical_excess_le _ hbase
          (fun base => integerBaseTranslation base + anchor) stride T W hW hZ _
          (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) p hm) (fun base => hD base center)
          root (integerBox N) hparent (hbound (coefficientConstantCenter U center)) Fobs
        refine ⟨hexcess, ?_⟩
        have htail := FiniteProbabilityWeights.mass_above_double_cap_le_of_excess _ _ hexcess
        simpa only [htwice, herror] using htail
      · have htail := selectedAnchoredMixture_integer_box_excess_tail _ hbase
          (fun base => integerBaseTranslation base + anchor) stride T W hW hZ _
          (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) p hm) (fun base => hD base center)
          root N hparent (hbound (coefficientConstantCenter U center))
        simpa only [htwice, herror] using htail

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_small_kernel_all_sites_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G] [Nonempty G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables (G × X) I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (θ τ : ℝ) (_hθ : 0 < θ) (_hθhalf : θ ≤ 1/2) (_hθP : 1/θ ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hτP : 1/τ ≤ Real.exp P)
    (_hθδ : 2 * (Fintype.card X : ℝ) * θ ≤ δ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hN : ∀ i, 0 < N i)
    (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (G × X) I n B)) X stride)) (_hT : T.Nonempty),
    let scale := selectedLayerSamplerScale (G := G × X) B U b R σ hR hσ L₀
    let sites := layerSamplerIntegerBox B U b scale
    let F := PrincipalTupleIndex B (layerSamplerDegree I n)
    let spatialSides := layerSamplerBox B U b scale
    let anchor := smallKernelSpatialAnchor N spatialSides θ
    let W := smallKernelSpatialWidths N spatialSides θ τ
    let hW := smallKernelSpatialWidths_pos N _hN spatialSides
      (fun k => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (layerSamplerBox_one_le B U b scale k)) _hθ _hτ
    let bases := trimmedIntegerBox N (spatialTrimMargin θ N)
    let D := fun center => translatedSelectedPhysicalDensity (G := G × X) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) p hm
    let Z := fun base center => selectedResidueDensityMass stride T W
      (fun u => D center ((integerBaseTranslation base + anchor) + u))
    ∃ hsites : sites.Nonempty, ∃ hbase : bases.Nonempty, ∃ hparent : (integerBox N).Nonempty,
    ∃ hZ : 0 < ∑' u, selectedResidueSmoothWeight stride T W u,
    ∃ hD : ∀ base center, 0 < Z base center,
    letI : Nonempty sites := hsites.to_subtype;
    let frame : (bases × rectangularWeightIndices 0 W 1) →
        Option (LayerSamplerVariables (G × X) I n B) × X → ℤ :=
      fun z => (integerBaseTranslation (K := LayerSamplerVariables (G × X) I n B) z.1.val + anchor) + z.2.val
    let law := fun center => selectedAnchoredMixture bases hbase
      (fun base => integerBaseTranslation base + anchor) stride T W hW hZ (D center)
      (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) p hm) (fun base => hD base center)
    let point := fun z (root : sites) => integerBoxObservation N hparent (physicalAffineSite root.val (frame z))
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j);
      (∀ base center, |Z base center-1| ≤ 3*δ ∧ 1/2 ≤ Z base center ∧ Z base center ≤ 3/2) ∧
      (∀ center z, 0 < (law center).weight z →
        (∀ g, (matrixSupCLM (normalizedKernelBlock N spatialSides (frame z) g)).IsInvertible ∧
          ‖(matrixSupCLM (normalizedKernelBlock N spatialSides (frame z) g)).inverse‖ ≤
            (32 * ((Fintype.card (LayerSamplerVariables (G × X) I n B) : ℝ) + 1)) / θ) ∧
        (∀ r : LayerSamplerVariables (G × X) I n B → ℤ,
          (∀ k, |(r k : ℝ)| ≤ spatialSides k) → integerPhysicalSite r (frame z) ∈ integerBox N) ∧
        (∀ r : LayerSamplerVariables (G × X) I n B → ℤ,
          (∀ k, |(r k : ℝ)| ≤ spatialSides k) → ∀ i,
          |∑ f : F, (r (.inr f) : ℝ) * (frame z (some (.inr f),i) : ℝ)| ≤ τ*θ*(N i : ℝ)/16)) ∧
      (∀ center z, 0 < (law center).weight z → ∀ root : sites,
        (point z root).val = integerPhysicalSite root.val (frame z)) ∧
      (∀ center, ∃ c : ∀ j, U j, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U (fun s => c s.1))) ∧
        ∀ z, 0 < (law center).weight z →
          HasQuarterAffinePolynomialLifts p (fun j => (c j).val) (fun k v => (frame z (k,v) : ℝ)) spatialSides) ∧
      (∀ center, (law center).mean (fun z =>
        noninjectivityIndicator (fun root : sites => integerPhysicalSite root.val (frame z))) ≤ δ) ∧
      (∀ root : sites, ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(∫ center, (law center).complexMean (fun z => φ (physicalAffineSite root.val (frame z))) ∂μ) -
          𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))‖ ≤ 7*δ) ∧
      (∀ root : sites, ∀ center (φ : (X → ℝ) → ℝ), (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (law center).mean (fun z => φ (physicalAffineSite root.val (frame z))) ≤
          2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ) ∧
      (∀ center, let marginal := (law center).siteLaw point;
        (FiniteProbabilityWeights.uniformFinset (integerBox N) hparent).excessMass marginal (2*M) ≤ 6*δ ∧
          marginal.mass (Finset.univ.filter (fun x => 4*M/(integerBox N).card < marginal.weight x)) ≤ 12*δ) := by
  obtain ⟨A, hA, hcore⟩ := exists_small_kernel_near_uniform_sampler.{_, _, _, _, _, 0} m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP θ τ hθ hθhalf hθP hτ hτ1 hτP hθδ
    p hp hm stride hs Rrank S hS hSP hstride N hN hsize hrank hRrank T hT
  let scale := selectedLayerSamplerScale (G := G × X) B U b R σ hR hσ L₀
  let sites := layerSamplerIntegerBox B U b scale
  let spatialSides := layerSamplerBox B U b scale
  let anchor := smallKernelSpatialAnchor N spatialSides θ
  let W := smallKernelSpatialWidths N spatialSides θ τ
  have hsidepos (k) : 0 < spatialSides k :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (layerSamplerBox_one_le B U b scale k)
  have hW := smallKernelSpatialWidths_pos N hN spatialSides hsidepos hθ hτ
  let bases := trimmedIntegerBox N (spatialTrimMargin θ N)
  let D := fun center => translatedSelectedPhysicalDensity (G := G × X) B U b hb o R σ hR hσ L₀
    (coefficientConstantCenter U center) p hm
  let anchors := fun base : X → ℤ => (integerBaseTranslation base :
    Option (LayerSamplerVariables (G × X) I n B) × X → ℤ) + anchor
  have hsites : sites.Nonempty := layerSamplerIntegerBox_nonempty B U b scale
  let : Nonempty sites := hsites.to_subtype
  have hfamily (root : sites) := hcore B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    θ τ hθ hθhalf hθP hτ hτ1 hτP hθδ root.val root.property p hp hm stride hs
    hS hSP hstride N hN hsize hrank hRrank T hT
  obtain ⟨hbase, hparent, hZ, hD, hnormal, _, hgeometry, hcollision, hlifts, _, _⟩ :=
    hfamily (Classical.choice inferInstance)
  let frame : (bases × rectangularWeightIndices 0 W 1) →
      Option (LayerSamplerVariables (G × X) I n B) × X → ℤ :=
    fun z => anchors z.1.val + z.2.val
  let hD0 := fun center => translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
    (coefficientConstantCenter U center) p hm
  let law := fun center => selectedAnchoredMixture bases hbase anchors stride T W hW hZ
    (D center) (hD0 center) (fun base => hD base center)
  let point := fun z (root : sites) => integerBoxObservation N hparent (physicalAffineSite root.val (frame z))
  have hpositive (center) (z : bases × rectangularWeightIndices 0 W 1)
      (hz : 0 < (law center).weight z) :
      0 < (translatedSelectedResidueDensityPMF (anchors z.1.val) stride T W hW hZ
        (D center) (hD0 center) (hD z.1.val center) (frame z)).toReal :=
    (selectedAnchoredMixture_pos_iff bases hbase anchors stride T W hW hZ
      (D center) (hD0 center) (fun base => hD base center) z).mp hz
  have htest (root : sites) (center) (φ : (X → ℝ) → ℝ)
      (hφ : ∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) :
      (law center).mean (fun z => φ (physicalAffineSite root.val (frame z))) ≤
        2*(∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) *
          (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hdom, _⟩ := hfamily root
    rw [selectedAnchoredMixture_mean bases hbase anchors stride T W hW hZ
      (D center) (hD0 center) (fun base => hD base center) (fun _ z => φ (physicalAffineSite root.val z))]
    exact hdom center φ hφ
  refine ⟨hsites, hbase, hparent, hZ, hD, hnormal, ?_, ?_, ?_, ?_, ?_, htest, ?_⟩
  · intro center z hz
    exact hgeometry z.1.val z.1.property center (frame z) (hpositive center z hz)
  · intro center z hz root
    exact integerBoxObservation_physical N hparent root.val (frame z)
      ((hgeometry z.1.val z.1.property center (frame z) (hpositive center z hz)).2.1
        root.val (layerSamplerIntegerBox_abs_bound B U b scale root.property))
  · intro center
    obtain ⟨c, hc, hlift⟩ := hlifts center
    refine ⟨c, hc, ?_⟩
    intro z hz
    exact hlift z.1.val (frame z) (hpositive center z hz)
  · intro center
    rw [selectedAnchoredMixture_mean bases hbase anchors stride T W hW hZ
      (D center) (hD0 center) (fun base => hD base center)
      (fun _ z => noninjectivityIndicator (fun root : sites => integerPhysicalSite root.val z))]
    exact Finset.expect_le hbase (fun base _ => hcollision base center)
  · intro root φ hφ
    obtain ⟨_, _, _, _, _, hmix, _, _, _, _, _⟩ := hfamily root
    have hDm (z) : Measurable (fun center => D center z) :=
      (translatedSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀ p hm z).comp
        (coefficientConstantCenter_continuous U).measurable
    rw [integral_selectedAnchoredMixture_complexMean μ bases hbase anchors stride T W hW hZ D
      hDm hD0 hD (fun _ z => φ (physicalAffineSite root.val z)) (fun _ _ => hφ _)]
    exact hmix φ hφ
  · intro center
    have hexcess := FiniteProbabilityWeights.siteLaw_excess_le (law center) point
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hparent) (C :=
        2*(∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j))) (ε := 6*δ) (by
        intro root f hf
        have h := htest root center (fun v => f (integerBoxObservation N hparent v)) (fun v => hf _)
        rw [integerBoxObservation_mean] at h
        exact h)
    refine ⟨hexcess, ?_⟩
    have htail := FiniteProbabilityWeights.mass_above_double_cap_le_of_excess _ _ hexcess
    have htwice (v : ℝ) : 2*(2*v) = 4*v := by ring
    have herror : 2*(6*δ) = 12*δ := by ring
    simpa only [FiniteProbabilityWeights.uniformFinset_weight, htwice, herror, div_eq_mul_inv] using htail

end Erdos3.BooleanCubeKernel

end

end OAI
