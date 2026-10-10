import OAI.Probability.EntangledGames.SpectralBins

namespace OAI

universe u_m u_n u_p u_ι u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open ThresholdParallelRepetition.MeasurementTransport
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq n]

lemma hsSq_mul_contraction {W : Matrix m n ℂ} (hW : Wᴴ*W ≤ 1)
    {p : Type u_p} [Fintype p] (M : Matrix n p ℂ) : hsSq (W*M) ≤ hsSq M := by
  have hpos := (Matrix.le_iff.mp hW).conjTranspose_mul_mul_same M
  have ht := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at ht
  rw [hsSq_eq_trace, hsSq_eq_trace]
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using sub_nonneg.mp ht

def rightAbs (M : Matrix m n ℂ) : Matrix n n ℂ := CFC.sqrt (Mᴴ*M)
def polar (M : Matrix m n ℂ) : Matrix m n ℂ := M * supportInverse (rightAbs M)

lemma rightAbs_pos (M : Matrix m n ℂ) : (rightAbs M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
lemma rightAbs_sq (M : Matrix m n ℂ) : rightAbs M * rightAbs M = Mᴴ*M :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg

lemma supportInverse_mul_le_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    supportInverse A * A ≤ 1 := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  change cfc (fun t : ℝ => t⁻¹) A * A ≤ 1
  calc
    _ = cfc (fun t : ℝ => t⁻¹*t) A := by
      calc
        _ = cfc (fun t : ℝ => t⁻¹) A * cfc (fun t : ℝ => t) A := by rw [hid]
        _ = _ := by
          erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ ≤ 1 := cfc_le_one _ A (by intro t _; by_cases ht : t = 0 <;> simp [ht])

lemma polar_gram (M : Matrix m n ℂ) :
    (polar M)ᴴ * polar M = supportInverse (rightAbs M) * rightAbs M := by
  let A := rightAbs M
  let D := supportInverse A
  have hA : A.IsHermitian := (rightAbs_pos M).isHermitian
  have hD : Dᴴ = D := (supportInverse_isHermitian A).eq
  change (M*D)ᴴ*(M*D) = D*A
  rw [Matrix.conjTranspose_mul, hD]
  calc
    _ = D*(Mᴴ*M)*D := by simp only [Matrix.mul_assoc]
    _ = D*(A*A)*D := by rw [rightAbs_sq]
    _ = D*A*(A*D) := by simp only [Matrix.mul_assoc]
    _ = D*A*(D*A) := by rw [show A*D=D*A from (supportInverse_commute hA).symm]
    _ = (D*A*D)*A := by simp only [Matrix.mul_assoc]
    _ = D*A := by rw [supportInverse_mul_self_mul hA]

lemma polar_contraction (M : Matrix m n ℂ) : (polar M)ᴴ*polar M ≤ 1 := by
  rw [polar_gram]
  exact supportInverse_mul_le_one (rightAbs_pos M).isHermitian

lemma polar_mul_rightAbs (M : Matrix m n ℂ) : polar M * rightAbs M = M := by
  let A := rightAbs M
  let D := supportInverse A
  have hA : A.IsHermitian := (rightAbs_pos M).isHermitian
  have hzero : (Mᴴ*M)*(1-D*A) = 0 := by
    rw [← rightAbs_sq M]
    change (A*A)*(1-D*A)=0
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      self_mul_supportInverse_mul hA, sub_self, Matrix.mul_zero]
  have hz := (Matrix.conjTranspose_mul_self_mul_eq_zero M (1-D*A)).mp hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
  simpa only [polar, Matrix.mul_assoc] using hz.symm

lemma supportInverse_bin {A : Matrix n n ℂ} (hA : A.IsHermitian) (ε s : ℝ) (l : ℤ) :
    (supportInverse A*A)*binProjection A ε s l = binProjection A ε s l := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  unfold supportInverse binProjection
  calc
    _ = cfc (fun t : ℝ => t⁻¹*t*binIndicator ε s l t) A := by
      calc
        _ = cfc (fun t : ℝ => t⁻¹) A * cfc (fun t : ℝ => t) A * cfc (binIndicator ε s l) A := by rw [hid]
        _ = _ := by
          erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t⁻¹*t) (binIndicator ε s l) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by
      apply cfc_congr; intro t _
      by_cases ht : 0 < t
      · simp [ne_of_gt ht]
      · simp [binIndicator, ht]

lemma polar_gram_bin (M : Matrix m n ℂ) (ε s : ℝ) (l : ℤ) :
    ((polar M)ᴴ*polar M)*binProjection (rightAbs M) ε s l = binProjection (rightAbs M) ε s l := by
  rw [polar_gram]
  exact supportInverse_bin (rightAbs_pos M).isHermitian ε s l

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma projection_le_one {P : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P*P=P) : P ≤ 1 := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1-P)
  have he : (1-P)ᴴ*(1-P)=1-P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP, sub_self, sub_zero]
  rw [he] at h
  exact Matrix.le_iff.mpr h

def binFilter (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) : Matrix n (n × L) ℂ :=
  fun i jl => (polar M * binProjection (rightAbs M) ε s jl.2) i jl.1

lemma binFilter_gram (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) :
    (binFilter L M ε s)ᴴ * binFilter L M ε s =
      Matrix.blockDiagonal (fun l : L => binProjection (rightAbs M) ε s l) := by
  ext ⟨i,l⟩ ⟨j,k⟩
  change (((polar M * binProjection (rightAbs M) ε s l)ᴴ *
    (polar M * binProjection (rightAbs M) ε s k)) i j) = _
  rw [Matrix.conjTranspose_mul, (binProjection_hermitian _ _ _ _).eq]
  rw [show (binProjection (rightAbs M) ε s l * (polar M)ᴴ) *
      (polar M * binProjection (rightAbs M) ε s k) =
      binProjection (rightAbs M) ε s l * (((polar M)ᴴ*polar M)*binProjection (rightAbs M) ε s k)
      by simp only [Matrix.mul_assoc], polar_gram_bin]
  by_cases hlk : l = k
  · subst k
    rw [binProjection_sq (rightAbs_pos M).isHermitian]
    exact (Matrix.blockDiagonal_apply_eq (fun l : L => binProjection (rightAbs M) ε s l) i j l).symm
  · rw [binProjection_orthogonal (rightAbs_pos M).isHermitian ε s (Subtype.coe_ne_coe.mpr hlk)]
    simp only [Matrix.zero_apply, Matrix.blockDiagonal_apply, ite_eq_right hlk]

lemma binFilter_contraction (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) :
    (binFilter L M ε s)ᴴ * binFilter L M ε s ≤ 1 := by
  rw [binFilter_gram]
  apply projection_le_one
  · change (Matrix.blockDiagonal (fun l : L => binProjection (rightAbs M) ε s l))ᴴ = _
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext l
    exact (binProjection_hermitian _ _ _ _).eq
  · rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext l
    exact binProjection_sq (rightAbs_pos M).isHermitian ε s l

def roundedAbs (A : Matrix n n ℂ) (ε s : ℝ) : Matrix n n ℂ := cfc (fun a => binWeight a ε s) A

lemma roundedAbs_energy_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) : hsSq (roundedAbs A ε s) ≤ hsSq A := by
  rw [roundedAbs, hsSq_cfc_eq hA.isHermitian, hsSq_eq_sum_eigenvalues_sq hA.isHermitian]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [binWeight_le (hA.eigenvalues_nonneg i) hε s, binWeight_nonneg (hA.isHermitian.eigenvalues i) ε s]

lemma roundedAbs_error_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) : hsSq (A-roundedAbs A ε s) ≤ ε^2*hsSq A := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA.isHermitian
  have he : A-roundedAbs A ε s = cfc (fun a => a-binWeight a ε s) A := by
    erw [cfc_sub (fun t : ℝ => t) (fun a => binWeight a ε s) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    rw [hid]; rfl
  rw [he, hsSq_cfc_eq hA.isHermitian, hsSq_eq_sum_eigenvalues_sq hA.isHermitian, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 := binWeight_le (hA.eigenvalues_nonneg i) hε s
  have h2 := sub_binWeight_le (hA.eigenvalues_nonneg i) hε s
  have h3 : 0 ≤ ε * hA.isHermitian.eigenvalues i := mul_nonneg hε.le (hA.eigenvalues_nonneg i)
  nlinarith [sq_nonneg (hA.isHermitian.eigenvalues i-binWeight (hA.isHermitian.eigenvalues i) ε s-ε*hA.isHermitian.eigenvalues i)]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

lemma hsSq_neg (M : Matrix m n ℂ) : hsSq (-M) = hsSq M := by
  simp [hsSq, Complex.normSq_neg]
lemma hsSq_sub_comm (M N : Matrix m n ℂ) : hsSq (M-N) = hsSq (N-M) := by
  rw [← hsSq_neg]; congr 1; abel
lemma hsSq_smul (r : ℝ) (M : Matrix m n ℂ) : hsSq (r • M) = r^2*hsSq M := by
  simp only [hsSq, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum]
  congr 1
  ring
lemma hsSq_add_le (M N : Matrix m n ℂ) : hsSq (M+N) ≤ 2*(hsSq M+hsSq N) := by
  unfold hsSq
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  simp only [Matrix.add_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg ((M i j).re-(N i j).re), sq_nonneg ((M i j).im-(N i j).im)]

lemma hsSq_sum_orthogonal {ι : Type u_ι} [Fintype ι] [DecidableEq ι]
    (F : ι → Matrix m n ℂ) (hF : ∀ i j, i ≠ j → (F i)ᴴ*F j=0) :
    hsSq (∑ i, F i) = ∑ i, hsSq (F i) := by
  simp only [hsSq_eq_trace, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [hF j i hji, Matrix.trace_zero, Complex.zero_re]
  · simp

lemma hsSq_mul_right_contraction [DecidableEq n] {W : Matrix n p ℂ} (hW : W*Wᴴ ≤ 1)
    (M : Matrix m n ℂ) : hsSq (M*W) ≤ hsSq M := by
  rw [← hsSq_conjTranspose (M*W), Matrix.conjTranspose_mul, ← hsSq_conjTranspose M]
  exact hsSq_mul_contraction (W := Wᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hW) _

variable [DecidableEq m]
lemma hsSq_mul_projection_le {P : Matrix m m ℂ} (hP : P.IsHermitian) (hPP : P*P=P)
    (M : Matrix m n ℂ) : hsSq (P*M) ≤ hsSq M := by
  apply hsSq_mul_contraction
  rw [hP.eq, hPP]
  exact projection_le_one hP hPP

omit [DecidableEq m] in

lemma hsSq_orthogonal_projection_sum {ι : Type u_ι} [Fintype ι] [DecidableEq ι]
    (P : ι → Matrix m m ℂ) (F : ι → Matrix m n ℂ) (r : ι → ℝ)
    (hP : ∀ i, (P i).IsHermitian) (hPP : ∀ i j, i ≠ j → P i*P j=0) :
    hsSq (∑ i, r i • (P i*F i)) = ∑ i, (r i)^2*hsSq (P i*F i) := by
  rw [hsSq_sum_orthogonal]
  · simp only [hsSq_smul]
  · intro i j hij
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
      (hP i).eq, Matrix.smul_mul, Matrix.mul_smul]
    rw [show ((F i)ᴴ*P i)*(P j*F j)=(F i)ᴴ*(P i*P j)*F j by simp only [Matrix.mul_assoc],
      hPP i j hij, Matrix.mul_zero, Matrix.zero_mul, smul_zero, smul_zero]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def CoversBins (L : Finset ℤ) (A : Matrix n n ℂ) (ε s : ℝ) : Prop :=
  ∀ a ∈ spectrum ℝ A, 0 < a → ⌊Real.log a/ε+s⌋ ∈ L

lemma sum_binScale_indicator (L : Finset ℤ) (ε s a : ℝ)
    (h : 0 < a → ⌊Real.log a/ε+s⌋ ∈ L) :
    (∑ l ∈ L, binScale ε s l * binIndicator ε s l a) = binWeight a ε s := by
  by_cases ha : 0 < a
  · simp only [binIndicator, ha, true_and, binWeight, ite_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (h ha)]
    rfl
  · simp [binIndicator, binWeight, ha]

lemma roundedAbs_eq_sum (L : Finset ℤ) {A : Matrix n n ℂ} (ε s : ℝ)
    (hL : CoversBins L A ε s) :
    roundedAbs A ε s = ∑ l : L, binScale ε s l • binProjection A ε s l := by
  unfold roundedAbs binProjection
  calc
    _ = cfc (∑ l : L, fun a => binScale ε s l * binIndicator ε s l a) A := by
      apply cfc_congr; intro a ha
      simp only [Finset.sum_apply]
      rw [Finset.sum_coe_sort L (fun l => binScale ε s l * binIndicator ε s l a)]
      exact (sum_binScale_indicator L ε s a (hL a ha)).symm
    _ = _ := by
      erw [cfc_sum_univ (fun l : L => fun a => binScale ε s l * binIndicator ε s l a) A
        (fun _ => A.finite_real_spectrum.continuousOn _)]
      apply Finset.sum_congr rfl; intro l _
      exact cfc_const_mul _ _ _ (A.finite_real_spectrum.continuousOn _)

lemma exists_common_bins {ι : Type u_ι} [Fintype ι] (A : ι → Matrix n n ℂ) (ε s : ℝ) :
    ∃ L : Finset ℤ, 0 ∈ L ∧ ∀ i, CoversBins L (A i) ε s := by
  classical
  let L := insert 0 (Finset.univ.biUnion (fun i =>
    (A i).finite_real_spectrum.toFinset.image (fun a => ⌊Real.log a/ε+s⌋)))
  refine ⟨L, Finset.mem_insert_self _ _, ?_⟩
  intro i a ha _
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  exact ⟨a, ((A i).finite_real_spectrum.mem_toFinset).mpr ha, rfl⟩

def crossBins (L : Finset ℤ) (A B : Matrix n n ℂ) (ε s : ℝ) : Matrix n n ℂ :=
  ∑ l : L, binScale ε s l • (binProjection A ε s l * binProjection B ε s l)

def binMismatch (L : Finset ℤ) (A B : Matrix n n ℂ) (ε s : ℝ) : ℝ :=
  ∑ l : L, (binScale ε s l)^2 * hsSq (binProjection A ε s l-binProjection B ε s l)

lemma crossBins_error_le (L : Finset ℤ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (_hB : B.IsHermitian) (ε s : ℝ) (hL : CoversBins L A ε s) :
    hsSq (roundedAbs A ε s-crossBins L A B ε s) ≤ binMismatch L A B ε s := by
  have he : roundedAbs A ε s-crossBins L A B ε s =
      ∑ l : L, binScale ε s l • (binProjection A ε s l * (binProjection A ε s l-binProjection B ε s l)) := by
    rw [roundedAbs_eq_sum L ε s hL, crossBins, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.mul_sub, binProjection_sq hA, smul_sub]
  rw [he, hsSq_orthogonal_projection_sum _ _ _ (fun _ => binProjection_hermitian _ _ _ _)
    (fun i j hij => binProjection_orthogonal hA ε s (Subtype.coe_ne_coe.mpr hij))]
  unfold binMismatch
  apply Finset.sum_le_sum; intro l _
  exact mul_le_mul_of_nonneg_left
    (hsSq_mul_projection_le (binProjection_hermitian _ _ _ _) (binProjection_sq hA ε s l) _) (sq_nonneg _)

lemma polar_crossBins_error_le (L : Finset ℤ) (M N : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) (hL : CoversBins L (rightAbs M) ε s) :
    hsSq (M-polar M*crossBins L (rightAbs M) (rightAbs N) ε s) ≤
      2*ε^2*hsSq M + 2*binMismatch L (rightAbs M) (rightAbs N) ε s := by
  have hm : M-polar M*crossBins L (rightAbs M) (rightAbs N) ε s =
      polar M*(rightAbs M-roundedAbs (rightAbs M) ε s) +
      polar M*(roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s) := by
    simp only [Matrix.mul_sub, polar_mul_rightAbs]
    abel
  rw [hm]
  have h1 := hsSq_mul_contraction (polar_contraction M) (rightAbs M-roundedAbs (rightAbs M) ε s)
  have h2 := hsSq_mul_contraction (polar_contraction M)
    (roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s)
  have h3 := roundedAbs_error_le (rightAbs_pos M) hε s
  have h4 := crossBins_error_le L (rightAbs_pos M).isHermitian (rightAbs_pos N).isHermitian ε s hL
  have h5 : hsSq (rightAbs M) = hsSq M := hsSq_sqrt_gram M
  rw [h5] at h3
  have h6 := hsSq_add_le (polar M*(rightAbs M-roundedAbs (rightAbs M) ε s))
    (polar M*(roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s))
  linarith

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

def vec (C : Matrix m n ℂ) : m × n → ℂ := fun i => C i.1 i.2

def eval (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) : ℂ :=
  star (vec C) ⬝ᵥ ((A ⊗ₖ B) *ᵥ vec C)

def prob (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) : ℝ :=
  (eval C A B).re

lemma eval_eq_sum (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C A B = ∑ i, ∑ j, ∑ k, ∑ l, star (C i j) * (A i k * B j l) * C k l := by
  simp only [eval, vec, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]

lemma prob_nonneg {C : Matrix m n ℂ} {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ prob C A B :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg _)).1

lemma eval_add_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C (A+A') B = eval C A B + eval C A' B := by
  simp [eval, Matrix.add_kronecker, Matrix.add_mulVec, dotProduct_add]
lemma eval_add_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    eval C A (B+B') = eval C A B + eval C A B' := by
  simp [eval, Matrix.kronecker_add, Matrix.add_mulVec, dotProduct_add]
lemma prob_add_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (A+A') B = prob C A B + prob C A' B := by
  simp [prob, eval_add_left]
lemma prob_add_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    prob C A (B+B') = prob C A B + prob C A B' := by
  simp [prob, eval_add_right]

lemma eval_one [DecidableEq m] [DecidableEq n] (C : Matrix m n ℂ) :
    eval C 1 1 = (hsSq C : ℂ) := by
  simp only [eval, Matrix.one_kronecker_one, Matrix.one_mulVec, dotProduct,
    Pi.star_apply, Fintype.sum_prod_type, vec, hsSq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact Complex.normSq_eq_conj_mul_self.symm

lemma prob_one [DecidableEq m] [DecidableEq n] (C : Matrix m n ℂ) :
    prob C 1 1 = hsSq C := by simp [prob, eval_one]

lemma eval_real {C : Matrix m n ℂ} {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : eval C A B = (prob C A B : ℂ) := by
  have h := ((hA.kronecker hB).dotProduct_mulVec_nonneg (vec C))
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp h).2.symm

lemma eval_eq_trace (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    eval C A B = Matrix.trace (Cᴴ * (A * (C * Bᵀ))) := by
  simp only [eval_eq_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  simp only [star, mul_assoc, mul_comm (B j l)]

lemma eval_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (E : Matrix p p ℂ) (F : Matrix q q ℂ) :
    eval (C ⊗ₖ D) (A ⊗ₖ E) (B ⊗ₖ F) = eval C A B * eval D E F := by
  simp only [eval_eq_trace, Matrix.conjTranspose_kronecker, ← Matrix.kroneckerMap_transpose,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

lemma prob_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {E : Matrix p p ℂ} {F : Matrix q q ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hE : E.PosSemidef) (hF : F.PosSemidef) :
    prob (C ⊗ₖ D) (A ⊗ₖ E) (B ⊗ₖ F) = prob C A B * prob D E F := by
  change (eval _ _ _).re = _
  rw [eval_kronecker, eval_real hA hB, eval_real hE hF,
    ← Complex.ofReal_mul, Complex.ofReal_re]

lemma hsSq_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ) :
    hsSq (C ⊗ₖ D) = hsSq C * hsSq D := by
  classical
  simpa only [prob_one, Matrix.one_kronecker_one] using
    (prob_kronecker C D (A := 1) (B := 1) (E := 1) (F := 1)
      Matrix.PosSemidef.one Matrix.PosSemidef.one Matrix.PosSemidef.one Matrix.PosSemidef.one)

lemma eval_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    eval C (Kᴴ*A*K) (Lᴴ*B*L) = eval (K*C*Lᵀ) A B := by
  simp only [eval_eq_trace, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose,
    Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma prob_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    prob C (Kᴴ*A*K) (Lᴴ*B*L) = prob (K*C*Lᵀ) A B := by
  simp only [prob, eval_pullback]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
end

end OAI
