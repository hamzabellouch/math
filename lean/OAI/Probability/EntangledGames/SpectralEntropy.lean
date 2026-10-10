import OAI.Probability.EntangledGames.Resolvent

namespace OAI

universe u_n u_α u_m u_p u_r u_J

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
namespace ThresholdParallelRepetition.Resolvent
variable {n : Type u_n} [Fintype n] [DecidableEq n]

local instance matrixContinuousENorm : ContinuousENorm (Matrix n n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ inferInstance

local instance matrixPreorder : Preorder (Matrix n n ℂ) :=
  (Matrix.instPartialOrder : PartialOrder (Matrix n n ℂ)).toPreorder

omit [DecidableEq n] in
lemma isClosed_posSemidef : IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · have heq : {A : Matrix n n ℂ | ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)} =
        ⋂ x : n → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by ext; simp
    change IsClosed {A : Matrix n n ℂ | ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)}
    rw [heq]
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

local instance matrixClosedIci : ClosedIciTopology (Matrix n n ℂ) where
  isClosed_Ici A := by
    exact isClosed_posSemidef.preimage (continuous_id.sub continuous_const)

lemma integral_matrix_nonneg {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {f : α → Matrix n n ℂ} (hf : ∀ᵐ s ∂μ, (f s).PosSemidef) :
    (∫ s, f s ∂μ).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact @integral_nonneg_of_ae α (Matrix n n ℂ) _ _ _ μ _ _ _
    matrixClosedIci f (hf.mono fun _ h => h.nonneg)

lemma integral_matrix_mono {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {f g : α → Matrix n n ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : f ≤ᵐ[μ] g) : (∫ s, f s ∂μ) ≤ ∫ s, g s ∂μ :=
  @integral_mono_ae α (Matrix n n ℂ) _ _ _ μ _ _ _ matrixClosedIci f g hf hg hfg

def spectralLinear (U : Matrix n n ℂ) : (n → ℝ) →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => U * diagonal (fun i => (v i : ℂ)) * Uᴴ
      map_add' := by
        intro v w
        simp only [Pi.add_apply, Complex.ofReal_add]
        change U * diagonal ((fun i => (v i : ℂ)) + (fun i => (w i : ℂ))) * Uᴴ = _
        erw [← Matrix.diagonal_add]
        rw [mul_add, add_mul]
      map_smul' := by
        intro c v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have hd : diagonal (fun i => ((c * v i : ℝ) : ℂ)) =
            c • diagonal (fun i => (v i : ℂ)) := by
          ext i j
          simp only [Matrix.diagonal_apply, Matrix.smul_apply, Complex.ofReal_mul,
            Complex.real_smul]
          split_ifs <;> simp
        rw [hd, Matrix.mul_smul, Matrix.smul_mul] }

lemma spectralLinear_apply (U : Matrix n n ℂ) (v : n → ℝ) :
    spectralLinear U v = U * diagonal (fun i => (v i : ℂ)) * Uᴴ := rfl

lemma cfc_eq_spectralLinear {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = spectralLinear (hA.eigenvectorUnitary : Matrix n n ℂ)
      (fun i => f (hA.eigenvalues i)) := by
  rw [hA.cfc_eq]
  rfl

lemma integrable_cfc {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : α → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun s => f s (hA.eigenvalues i)) μ) :
    Integrable (fun s => cfc (f s) A) μ := by
  simp_rw [cfc_eq_spectralLinear hA]
  exact (spectralLinear _).integrable_comp (Integrable.of_eval hf)

lemma integral_cfc {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : α → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun s => f s (hA.eigenvalues i)) μ) :
    (∫ s, cfc (f s) A ∂μ) = cfc (fun t => ∫ s, f s t ∂μ) A := by
  simp_rw [cfc_eq_spectralLinear hA]
  erw [(spectralLinear _).integral_comp_comm (Integrable.of_eval hf)]
  congr 1
  ext i
  exact eval_integral hf i

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma spectrum_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {t : ℝ} (ht : t ∈ spectrum ℝ A) : 0 ≤ t := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hA.eigenvalues_nonneg i

lemma eigenvalues_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (i : n) : hA.isHermitian.eigenvalues i ≤ 1 := by
  have h : cfc (fun t : ℝ => t) A ≤ cfc (fun _ : ℝ => (1 : ℝ)) A := by
    erw [cfc_id' ℝ A hA.isHermitian, cfc_const (1 : ℝ) A hA.isHermitian,
      map_one]
    exact hA1
  exact (cfc_le_iff (fun t : ℝ => t) (fun _ : ℝ => (1 : ℝ)) A
    (ha := hA.isHermitian)).mp h _ (hA.isHermitian.eigenvalues_mem_spectrum_real i)

lemma resolvent_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    resolvent A s = cfc (fun t : ℝ => (t + s)⁻¹) A := by
  erw [cfc_inv (fun t : ℝ => t + s) A
    (fun t ht => ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hA ht) hs))
    (ha := hA.isHermitian)]
  erw [cfc_add A (fun t : ℝ => t) (fun _ : ℝ => s),
    cfc_id' ℝ A hA.isHermitian, cfc_const s A hA.isHermitian,
    Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse]
  rfl

lemma purificationKernel_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    purificationKernel A s = cfc (fun t : ℝ => t / (t + s)) A := by
  rw [purificationKernel, resolvent_cfc hA hs]
  calc
    A * cfc (fun t : ℝ => (t + s)⁻¹) A =
        cfc (fun t : ℝ => t) A * cfc (fun t : ℝ => (t + s)⁻¹) A := by
      erw [cfc_id' ℝ A hA.isHermitian]
    _ = _ := by
      rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + s)⁻¹) A
        (hg := A.finite_real_spectrum.continuousOn _)]
      rfl

lemma purificationKernel_square_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (purificationKernel A s)ᴴ * purificationKernel A s =
      cfc (fun t : ℝ => t ^ 2 / (t + s) ^ 2) A := by
  rw [purificationKernel_cfc hA hs,
    (cfc_predicate (fun t : ℝ => t / (t + s)) A).isHermitian.eq,
    ← cfc_mul (fun t : ℝ => t / (t + s)) (fun t : ℝ => t / (t + s)) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  change t / (t + s) * (t / (t + s)) = t ^ 2 / (t + s) ^ 2
  rw [← pow_two, div_pow]

lemma kernel_square_integrable {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s)ᴴ * purificationKernel A s)
      (Ioi 0) := by
  have hi := integrable_cfc hA.isHermitian (fun (s t : ℝ) => t ^ 2 / (t + s) ^ 2)
    (fun i => (scalar_square_integral (hA.eigenvalues_nonneg i)).1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (purificationKernel_square_cfc hA hs).symm

lemma kernel_square_integral {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (∫ s : ℝ in Ioi 0, (purificationKernel A s)ᴴ * purificationKernel A s) = A := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfc (fun t : ℝ => t ^ 2 / (t + s) ^ 2) A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact purificationKernel_square_cfc hA hs
    _ = cfc (fun t : ℝ => ∫ s : ℝ in Ioi 0, t ^ 2 / (t + s) ^ 2) A :=
      integral_cfc hA.isHermitian _ (fun i => (scalar_square_integral (hA.eigenvalues_nonneg i)).1)
    _ = cfc (fun t : ℝ => t) A := by
      apply cfc_congr
      intro t ht
      exact (scalar_square_integral (spectrum_nonneg hA ht)).2
    _ = A := cfc_id' ℝ A hA.isHermitian

def effectEntropy (A : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun t : ℝ => t * Real.log t) A

def entropyIntegrand (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (1 / (1 + s) : ℝ) • A - purificationKernel A s

lemma entropyIntegrand_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    entropyIntegrand A s = cfc (fun t : ℝ => t / (1 + s) - t / (t + s)) A := by
  rw [entropyIntegrand, purificationKernel_cfc hA hs,
    cfc_sub (fun t : ℝ => t / (1 + s)) (fun t : ℝ => t / (t + s)) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  congr 1
  calc
    _ = cfc (fun t : ℝ => (1 / (1 + s)) • t) A := by
      erw [cfc_smul (1 / (1 + s) : ℝ) (fun t : ℝ => t) A,
        cfc_id' ℝ A hA.isHermitian]
    _ = _ := by apply cfc_congr; intro t _; simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma entropy_integrable {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    IntegrableOn (entropyIntegrand A) (Ioi 0) := by
  have hi := integrable_cfc hA.isHermitian
    (fun (s t : ℝ) => t / (1 + s) - t / (t + s))
    (fun i => (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (entropyIntegrand_cfc hA hs).symm

lemma entropy_integral {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    (∫ s : ℝ in Ioi 0, entropyIntegrand A s) = effectEntropy A := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfc (fun t : ℝ => t / (1 + s) - t / (t + s)) A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact entropyIntegrand_cfc hA hs
    _ = cfc (fun t : ℝ => ∫ s : ℝ in Ioi 0, t / (1 + s) - t / (t + s)) A :=
      integral_cfc hA.isHermitian _ (fun i =>
        (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).1)
    _ = effectEntropy A := by
      apply cfc_congr
      intro t ht
      rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
      obtain ⟨i, rfl⟩ := ht
      exact (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).2

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]
local instance rectContinuousENorm {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] :
    ContinuousENorm (Matrix m p ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ inferInstance

lemma scalar_kernel_memLp {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun s : ℝ => t / (t + s)) 2 (volume.restrict (Ioi 0)) := by
  have hm : Measurable (fun s : ℝ => t / (t + s)) := by fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  simpa only [IntegrableOn, div_pow] using (scalar_square_integral ht).1

lemma kernel_entry_memLp {A : Matrix n n ℂ} (hA : A.PosSemidef) (i j : n) :
    MemLp (fun s : ℝ => purificationKernel A s i j) 2 (volume.restrict (Ioi 0)) := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let t : n → ℝ := hA.isHermitian.eigenvalues
  have hf (k : n) : MemLp (fun s : ℝ => U i k * (t k / (t k + s) : ℝ) * star (U j k))
      2 (volume.restrict (Ioi 0)) :=
    (((scalar_kernel_memLp (hA.eigenvalues_nonneg k)).ofReal (K := ℂ)).const_mul
      (U i k)).mul_const (star (U j k))
  have hi := memLp_finsetSum Finset.univ (fun k _ => hf k)
  apply hi.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [purificationKernel_cfc hA hs, hA.isHermitian.cfc_eq]
  change (∑ k, U i k * (t k / (t k + s) : ℝ) * star (U j k)) =
    (U * diagonal (fun k => ((t k / (t k + s) : ℝ) : ℂ)) * Uᴴ) i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma integrable_gram {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} {r : Type u_r} [Fintype m] [Fintype p] [Fintype r]
    {f : α → Matrix r m ℂ} {g : α → Matrix r p ℂ}
    (hf : ∀ i j, MemLp (fun s => f s i j) 2 μ)
    (hg : ∀ i j, MemLp (fun s => g s i j) 2 μ) :
    Integrable (fun s => (f s)ᴴ * g s) μ := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  change Integrable (fun s => ∑ k, star (f s k i) * g s k j) μ
  apply integrable_finsetSum
  intro k _
  exact memLp_one_iff_integrable.mp ((hf k i).star.mul (hg k j))

lemma kernel_cross_integrable {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s)ᴴ * purificationKernel B s) (Ioi 0) :=
  integrable_gram (kernel_entry_memLp hA) (kernel_entry_memLp hB)

lemma kernel_distance_integrable {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s - purificationKernel B s)ᴴ *
      (purificationKernel A s - purificationKernel B s)) (Ioi 0) := by
  apply integrable_gram <;> intro i j <;>
    exact (kernel_entry_memLp hA i j).sub (kernel_entry_memLp hB i j)

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma entropy_gap_integrand_eq {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    (∑ j, w j • entropyIntegrand (A j) s) - entropyIntegrand B s =
      s • ∑ j, w j • (resolvent (A j) s - resolvent B s) := by
  have hc (c : ℝ) : ∑ j, w j • (c • A j) = c • B := by
    simp_rw [smul_comm (w _) c]
    rw [← Finset.smul_sum, hmean]
  have hone : ∑ j, w j • (1 : Matrix n n ℂ) = 1 := by
    rw [← Finset.sum_smul, hw, one_smul]
  have hr : ∑ j, w j • (s • resolvent (A j) s) = s • ∑ j, w j • resolvent (A j) s := by
    simp_rw [smul_comm (w _) s]
    rw [Finset.smul_sum]
  simp_rw [entropyIntegrand, purificationKernel_eq (hA _) hs, purificationKernel_eq hB hs,
    smul_sub, Finset.sum_sub_distrib]
  rw [hc, hone, hr, ← Finset.sum_smul, hw, one_smul]
  module

lemma weighted_distance_jensen {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (hB : B.PosSemidef) (hB1 : B ≤ 1)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B) :
    (∑ j, w j • (∫ s : ℝ in Ioi 0,
        (purificationKernel (A j) s - purificationKernel B s)ᴴ *
          (purificationKernel (A j) s - purificationKernel B s))) ≤
      (∑ j, w j • effectEntropy (A j)) - effectEntropy B := by
  have hf (j : J) := (kernel_distance_integrable (hA j) hB).smul (w j)
  have hg (j : J) := (entropy_integrable (hA j) (hA1 j)).smul (w j)
  have hleft := integrable_finsetSum Finset.univ (fun j _ => hf j)
  have hright := (integrable_finsetSum Finset.univ (fun j _ => hg j)).sub
    (entropy_integrable hB hB1)
  have hi := integral_matrix_mono hleft hright (show
      (fun s => ∑ j, w j • ((purificationKernel (A j) s - purificationKernel B s)ᴴ *
        (purificationKernel (A j) s - purificationKernel B s))) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun s => (∑ j, w j • entropyIntegrand (A j) s) - entropyIntegrand B s) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [entropy_gap_integrand_eq A w B hA hB hw hmean hs]
    exact weighted_kernel_square_le A w B hA hB hw0 hw hmean hs)
  erw [integral_finsetSum _ (fun j _ => hf j),
    integral_sub (integrable_finsetSum Finset.univ (fun j _ => hg j))
      (entropy_integrable hB hB1),
    integral_finsetSum _ (fun j _ => hg j)] at hi
  simp only [Pi.smul_apply] at hi
  simp_rw [integral_smul, entropy_integral (hA _) (hA1 _), entropy_integral hB hB1] at hi
  exact hi

end ThresholdParallelRepetition.Resolvent

end
end
end
end

end OAI
