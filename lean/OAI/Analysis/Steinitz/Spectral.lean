import OAI.Analysis.Steinitz.MatrixEnergy

namespace OAI

/-! Real spectral calculus and noncommuting matrix inequalities. -/

namespace EuclideanSteinitz.Spectral
open Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitary_transpose_mul (U : unitaryGroup ι ℝ) :
    (U : Matrix ι ι ℝ).transpose * U = 1 := by
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self U

lemma unitary_mul_transpose (U : unitaryGroup ι ℝ) :
    (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ).transpose = 1 := by
  simpa only [Unitary.coe_star, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self U

lemma real_spectral {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) * diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose := by
  simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq, Function.comp_def]
    using hA.spectral_theorem

lemma real_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
      diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc]
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq, Function.comp_def]

lemma trace_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [real_cfc hA f, trace_mul_cycle, unitary_transpose_mul, one_mul, trace_diagonal]

lemma trace_spectral {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.trace = ∑ i, hA.eigenvalues i := by
  conv_lhs => rw [real_spectral hA]
  rw [trace_mul_cycle, unitary_transpose_mul, one_mul, trace_diagonal]

lemma trace_conjugate (U : unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    ((U : Matrix ι ι ℝ) * A * (U : Matrix ι ι ℝ).transpose).trace = A.trace := by
  rw [trace_mul_cycle, unitary_transpose_mul, one_mul]

lemma trace_transpose_conjugate (U : unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    ((U : Matrix ι ι ℝ).transpose * A * U).trace = A.trace := by
  rw [trace_mul_cycle, unitary_mul_transpose, one_mul]

lemma sum_row_squares (U : unitaryGroup ι ℝ) (i : ι) :
    ∑ j, (U i j) ^ 2 = 1 := by
  have h := congr_fun (congr_fun (unitary_mul_transpose U) i) i
  simpa only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq, sq] using h

lemma sum_col_squares (U : unitaryGroup ι ℝ) (j : ι) :
    ∑ i, (U i j) ^ 2 = 1 := by
  have h := congr_fun (congr_fun (unitary_transpose_mul U) j) j
  simpa only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq, sq] using h

lemma orthostochastic_sums (U : unitaryGroup ι ℝ) :
    (∀ i, ∑ j, (U i j) ^ 2 = 1) ∧ (∀ j, ∑ i, (U i j) ^ 2 = 1) :=
  ⟨sum_row_squares U, sum_col_squares U⟩

noncomputable def overlapBasis {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : unitaryGroup ι ℝ :=
  star hA.eigenvectorUnitary * hB.eigenvectorUnitary

lemma overlapBasis_coe {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (overlapBasis hA hB : Matrix ι ι ℝ) =
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * hB.eigenvectorUnitary := by
  simp only [overlapBasis, Submonoid.coe_mul, Unitary.coe_star, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

lemma cfc_mixed_basis {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (cfc f A - cfc g B) *
        hB.eigenvectorUnitary =
      diagonal (fun i => f (hA.eigenvalues i)) * overlapBasis hA hB -
        (overlapBasis hA hB : Matrix ι ι ℝ) * diagonal (fun j => g (hB.eigenvalues j)) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, real_cfc hA f, real_cfc hB g, overlapBasis_coe]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  simp only [Matrix.mul_assoc, unitary_transpose_mul, Matrix.mul_one]

lemma cfc_mixed_basis_apply {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) (i j : ι) :
    ((hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (cfc f A - cfc g B) *
        hB.eigenvectorUnitary) i j =
      (f (hA.eigenvalues i) - g (hB.eigenvalues j)) * overlapBasis hA hB i j := by
  rw [cfc_mixed_basis, Matrix.sub_apply, diagonal_mul, mul_diagonal]
  ring

omit [DecidableEq ι] in
lemma trace_sandwich_diagonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : Matrix ι κ ℝ) (w : κ → ℝ) :
    (D * diagonal w * D.transpose).trace = ∑ i, ∑ j, w j * (D i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [mul_apply (M := D * diagonal w), mul_diagonal, transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_weighted_basis {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : unitaryGroup ι ℝ) (V : unitaryGroup κ ℝ)
    (D : Matrix ι κ ℝ) (w : κ → ℝ) :
    (D * ((V : Matrix κ κ ℝ) * diagonal w * (V : Matrix κ κ ℝ).transpose) *
      D.transpose).trace =
      ∑ i, ∑ j, w j * ((U : Matrix ι ι ℝ).transpose * D * (V : Matrix κ κ ℝ)) i j ^ 2 := by
  rw [← trace_sandwich_diagonal, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  rw [← trace_transpose_conjugate U
    (D * ((V : Matrix κ κ ℝ) * diagonal w * (V : Matrix κ κ ℝ).transpose) *
      D.transpose)]
  simp only [Matrix.mul_assoc]

lemma weighted_cfc_distance {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g w : ℝ → ℝ) :
    ((cfc f A - cfc g B) * cfc w B * (cfc f A - cfc g B).transpose).trace =
      ∑ i, ∑ j, (overlapBasis hA hB i j) ^ 2 * w (hB.eigenvalues j) *
        (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2 := by
  rw [real_cfc hB w, trace_weighted_basis hA.eigenvectorUnitary hB.eigenvectorUnitary]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cfc_mixed_basis_apply]
  ring

lemma trace_diagonal_product (M : Matrix ι ι ℝ) (a b : ι → ℝ) :
    (diagonal a * M * diagonal b * M.transpose).trace =
      ∑ i, ∑ j, a i * b j * (M i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [mul_apply (M := diagonal a * M * diagonal b), mul_diagonal,
    diagonal_mul, transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_cfc_product {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace = ∑ i, ∑ j,
      (overlapBasis hA hB i j) ^ 2 * f (hA.eigenvalues i) * g (hB.eigenvalues j) := by
  rw [real_cfc hA f, real_cfc hB g]
  calc
    _ = (diagonal (fun i => f (hA.eigenvalues i)) *
        (overlapBasis hA hB : Matrix ι ι ℝ) *
        diagonal (fun j => g (hB.eigenvalues j)) *
        (overlapBasis hA hB : Matrix ι ι ℝ).transpose).trace := by
      rw [overlapBasis_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
      rw [trace_mul_comm (hA.eigenvectorUnitary : Matrix ι ι ℝ)]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [trace_diagonal_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma overlap_sum_left (U : unitaryGroup ι ℝ) (f : ι → ℝ) :
    (∑ i, ∑ j, (U i j) ^ 2 * f i) = ∑ i, f i := by
  simp only [← Finset.sum_mul, sum_row_squares, one_mul]

lemma overlap_sum_right (U : unitaryGroup ι ℝ) (g : ι → ℝ) :
    (∑ i, ∑ j, (U i j) ^ 2 * g j) = ∑ j, g j := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_col_squares, one_mul]

lemma trace_cfc_remainder {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f f' : ℝ → ℝ) :
    (cfc f A).trace - (cfc f B).trace - (cfc f' B * (A - B)).trace =
      ∑ i, ∑ j, (overlapBasis hA hB i j) ^ 2 *
        (f (hA.eigenvalues i) - f (hB.eigenvalues j) -
         f' (hB.eigenvalues j) * (hA.eigenvalues i - hB.eigenvalues j)) := by
  have hprod := trace_cfc_product hA hB id f'
  rw [cfc_id ℝ A hA.isSelfAdjoint] at hprod
  rw [Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm (cfc f' B) A, hprod]
  have hs : (cfc f' B * B).trace = ∑ j, f' (hB.eigenvalues j) * hB.eigenvalues j := by
    calc
      _ = (cfc f' B * cfc (id : ℝ → ℝ) B).trace := by
        rw [cfc_id ℝ B hB.isSelfAdjoint]
      _ = _ := by
        have hf : ContinuousOn f' (spectrum ℝ B) := by
          rw [continuousOn_iff_continuous_domRestrict]
          fun_prop
        rw [← cfc_mul f' id B hf continuousOn_id, trace_cfc hB]
        rfl
  rw [hs, trace_cfc hA, trace_cfc hB]
  conv_lhs =>
    arg 1
    arg 1
    rw [← overlap_sum_left (overlapBasis hA hB) (fun i => f (hA.eigenvalues i))]
  rw [← overlap_sum_right (overlapBasis hA hB) (fun j => f (hB.eigenvalues j)),
    ← overlap_sum_right (overlapBasis hA hB)
      (fun j => f' (hB.eigenvalues j) * hB.eigenvalues j)]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [id_eq]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma convex_tangent {S : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hd : HasDerivWithinAt f d S y) : d * (x - y) ≤ f x - f y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hs := hf.slope_le_of_hasDerivWithinAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    nlinarith
  · simp
  · have hs := hf.le_slope_of_hasDerivWithinAt hy hx h hd
    rwa [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs

lemma trace_tangent_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f f' : ℝ → ℝ)
    {S : Set ℝ} (hAS : ∀ i, hA.eigenvalues i ∈ S)
    (hBS : ∀ j, hB.eigenvalues j ∈ S)
    (htan : ∀ x ∈ S, ∀ y ∈ S, f' y * (x - y) ≤ f x - f y) :
    (cfc f' B * (A - B)).trace ≤ (cfc f A).trace - (cfc f B).trace := by
  apply sub_nonneg.mp
  rw [trace_cfc_remainder hA hB]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (htan _ (hAS i) _ (hBS j)))

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivWithinAt_of_tangents {p d : ℝ → ℝ} {T : Set ℝ} {t : ℝ}
    (hd : ContinuousWithinAt d T t)
    (hl : ∀ u ∈ T, d t * (u - t) ≤ p u - p t)
    (hu : ∀ u ∈ T, p u - p t ≤ d u * (u - t)) :
    HasDerivWithinAt p (d t) T t := by
  rw [hasDerivWithinAt_iff_tendsto]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun u => by positivity))
  · filter_upwards [self_mem_nhdsWithin] with u hut
    have hlo := hl u hut
    have hup := hu u hut
    have he : 0 ≤ p u - p t - (u - t) * d t := by linarith
    have he' : p u - p t - (u - t) * d t ≤ (u - t) * (d u - d t) := by nlinarith
    have hnorm : ‖p u - p t - (u - t) • d t‖ ≤ ‖u - t‖ * ‖d u - d t‖ := by
      rw [smul_eq_mul, Real.norm_of_nonneg he, ← norm_mul]
      exact he'.trans (le_abs_self _)
    calc
      _ ≤ ‖u - t‖⁻¹ * (‖u - t‖ * ‖d u - d t‖) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ ‖d u - d t‖ := by
        by_cases h : u = t
        · simp [h]
        · rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)), one_mul]
  · simpa only [sub_self, norm_zero] using (hd.tendsto.sub (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ => d t) (nhdsWithin t T) (nhds (d t)))).norm

open scoped Matrix.Norms.L2Operator in
lemma trace_cfc_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (f f' : ℝ → ℝ)
    {T S : Set ℝ} {t : ℝ} (ht : t ∈ T)
    (hS : ∀ u ∈ T, spectrum ℝ (A + u • H) ⊆ S)
    (htan : ∀ x ∈ S, ∀ y ∈ S, f' y * (x - y) ≤ f x - f y)
    (hc : ContinuousWithinAt (fun u : ℝ => cfc f' (A + u • H)) T t) :
    HasDerivWithinAt (fun u : ℝ => (cfc f (A + u • H)).trace)
      (cfc f' (A + t • H) * H).trace T t := by
  have herm (u : ℝ) : (A + u • H).IsHermitian :=
    hA.add (hH.smul (IsSelfAdjoint.all u))
  have mem (u : ℝ) (hu : u ∈ T) (i : ι) :
      (herm u).eigenvalues i ∈ S := hS u hu ((herm u).eigenvalues_mem_spectrum_real i)
  have htrace : Continuous (Matrix.trace : Matrix ι ι ℝ → ℝ) :=
    (Matrix.traceLinearMap ι ℝ ℝ).continuous_of_finiteDimensional
  have hc' : ContinuousWithinAt (fun u : ℝ => (cfc f' (A + u • H) * H).trace) T t := by
    exact htrace.continuousAt.comp_continuousWithinAt (hc.mul continuousWithinAt_const)
  apply hasDerivWithinAt_of_tangents hc'
  · intro u hu
    have h := trace_tangent_le (herm u) (herm t) f f' (mem u hu) (mem t ht) htan
    have heq : A + u • H - (A + t • H) = (u - t) • H := by module
    simpa only [heq, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm] using h
  · intro u hu
    have h := trace_tangent_le (herm t) (herm u) f f' (mem t ht) (mem u hu) htan
    have heq : A + t • H - (A + u • H) = (t - u) • H := by module
    simp only [heq, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
    nlinarith

open scoped Matrix.Norms.L2Operator in
lemma continuous_cfc_affine {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun u : ℝ => cfc f (A + u • H)) := by
  apply Continuous.cfc_of_mem_nhdsSet (s := Set.univ) f (by simp)
    (continuous_const.add (continuous_id.smul continuous_const))
    (fun u => (hA.add (hH.smul (IsSelfAdjoint.all u))).isSelfAdjoint) hf.continuousOn

open scoped Matrix.Norms.L2Operator in

lemma trace_rpow_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) {a : ℝ} (ha : 1 ≤ a)
    {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    (hpos : ∀ u ∈ T, (A + u • H).PosSemidef) :
    HasDerivWithinAt (fun u : ℝ => (cfc (fun x : ℝ => x ^ a) (A + u • H)).trace)
      (a * (cfc (fun x : ℝ => x ^ (a - 1)) (A + t • H) * H).trace) T t := by
  have hf' : Continuous (fun x : ℝ => a * x ^ (a - 1)) :=
    continuous_const.mul (Real.continuous_rpow_const (sub_nonneg.mpr ha))
  have hd := trace_cfc_affine_derivative hA hH (fun x : ℝ => x ^ a)
    (fun x : ℝ => a * x ^ (a - 1)) (S := Set.Ici 0) ht
    (fun u hu x hx => spectrum_nonneg_of_nonneg (hpos u hu).nonneg hx)
    (fun x hx y hy => convex_tangent (convexOn_rpow ha) hx hy
      (Real.hasDerivAt_rpow_const (Or.inr ha)).hasDerivWithinAt)
    (continuous_cfc_affine hA hH hf').continuousWithinAt
  simpa only [cfc_const_mul a (fun x : ℝ => x ^ (a - 1)) _
      (Real.continuous_rpow_const (sub_nonneg.mpr ha)).continuousOn,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using hd

lemma trace_psd_pairing {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hS : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have h := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
  rw [hS.eq] at h
  have ht := h.trace_nonneg
  rw [Matrix.trace_mul_cycle, ← sq, CFC.sq_sqrt A hA.nonneg] at ht
  exact ht

lemma trace_convex_monotone {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B)
    (f f' : ℝ → ℝ) {S : Set ℝ}
    (hAS : ∀ i, hA.eigenvalues i ∈ S) (hBS : ∀ i, hB.eigenvalues i ∈ S)
    (hfp : ∀ y ∈ S, 0 ≤ f' y)
    (htan : ∀ x ∈ S, ∀ y ∈ S, f' y * (x - y) ≤ f x - f y) :
    (cfc f A).trace ≤ (cfc f B).trace := by
  have hp : (cfc f' A).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply cfc_nonneg
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfp _ (hAS i)
  have h := trace_tangent_le hB hA f f' hBS hAS htan
  have h0 := trace_psd_pairing hp (Matrix.le_iff.mp hAB)
  linarith

lemma trace_rpow_monotone {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    {a : ℝ} (ha : 1 ≤ a) :
    (cfc (fun x : ℝ => x ^ a) A).trace ≤ (cfc (fun x : ℝ => x ^ a) B).trace := by
  apply trace_convex_monotone hA.1 hB.1 hAB _ (fun x => a * x ^ (a - 1))
    (S := Set.Ici 0) (fun i => hA.eigenvalues_nonneg i) (fun i => hB.eigenvalues_nonneg i)
  · intro y hy
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hy _)
  · intro x hx y hy
    exact convex_tangent (convexOn_rpow ha) hx hy
      (Real.hasDerivAt_rpow_const (Or.inr ha)).hasDerivWithinAt

lemma trace_cfc_eq_of_charpoly {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly)
    (f : ℝ → ℝ) : (cfc f A).trace = (cfc f B).trace := by
  rw [trace_cfc hA, trace_cfc hB, (hA.eigenvalues_eq_eigenvalues_iff hB).mpr h]

lemma transpose_contraction {C : Matrix ι ι ℝ} (hC : C * C.transpose ≤ 1) :
    C.transpose * C ≤ 1 := by
  have h₁ : (C * C.transpose).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_mul_conjTranspose_self C
  have h₂ : (C.transpose * C).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self C
  have heq := (h₂.eigenvalues_eq_eigenvalues_iff h₁).mpr (charpoly_mul_comm C.transpose C)
  rw [CFC.le_one_iff (R := ℝ) _ h₂.isSelfAdjoint]
  rw [CFC.le_one_iff (R := ℝ) _ h₁.isSelfAdjoint] at hC
  intro x hx
  rw [h₂.spectrum_real_eq_range_eigenvalues, heq, ← h₁.spectrum_real_eq_range_eigenvalues] at hx
  exact hC x hx

lemma trace_rpow_contraction {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) {a : ℝ} (ha : 1 ≤ a) :
    (cfc (fun x : ℝ => x ^ a) (C * A * C.transpose)).trace ≤
      (cfc (fun x : ℝ => x ^ a) A).trace := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := by simpa only [← sq] using CFC.sq_sqrt A hA.nonneg
  have hCA : (C * A * C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same C
  have hSC : (S * (C.transpose * C) * S).PosSemidef := by
    have hp : (C.transpose * C).PosSemidef := by
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
        (star_mul_self_nonneg C : (0 : Matrix ι ι ℝ) ≤ star C * C).posSemidef
    simpa only [hS.eq] using hp.conjTranspose_mul_mul_same S
  have hle : S * (C.transpose * C) * S ≤ A := by
    have hp := (Matrix.le_iff.mp (transpose_contraction hC)).conjTranspose_mul_mul_same S
    rw [hS.eq] at hp
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS] using hp
  have heq : (C * A * C.transpose).charpoly = (S * (C.transpose * C) * S).charpoly := by
    rw [← hSS]
    convert charpoly_mul_comm (C * S) (S * C.transpose) using 1 <;> simp only [Matrix.mul_assoc]
  rw [trace_cfc_eq_of_charpoly hCA.1 hSC.1 heq]
  exact trace_rpow_monotone hSC hA hle ha

end EuclideanSteinitz.Spectral

end OAI
