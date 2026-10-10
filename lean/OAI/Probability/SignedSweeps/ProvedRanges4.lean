import OAI.Probability.SignedSweeps.ProvedRanges3

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

theorem missingCellFactor_le_exp_holes {A B : Type*} [Fintype A] [Fintype B]
    (W : Finset (A × B)) :
    missingCellFactor W ≤ Real.exp ((Fintype.card A * Fintype.card B - W.card : ℕ) : ℝ) := by
  have hk (i : A) : (occupiedRow W i).card ≤ Fintype.card B := Finset.card_le_univ _
  have hcnt : W.card ≤ Fintype.card A * Fintype.card B :=
    (Finset.card_le_univ W).trans_eq (Fintype.card_prod A B)
  calc
    _ ≤ ∏ i : A, Real.exp (Fintype.card B - (occupiedRow W i).card : ℝ) := by
      apply Finset.prod_le_prod₀ (fun i _ => missingLineFactor_nonneg _ _)
      intro i hi
      exact missingLineFactor_le_exp _ _ (hk i)
    _ = Real.exp (∑ i : A, (Fintype.card B - (occupiedRow W i).card : ℝ)) :=
      (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.cast_sum, sum_occupiedRow_card, Nat.cast_sub hcnt, Nat.cast_mul]

def splitBinary (a b : ℕ) : BinaryPositions (a + b) ≃ BinaryPositions a × BinaryPositions b where
  toFun := fun x => (fun i => x (i.castAdd b), fun j => x (j.natAdd a))
  invFun := fun x => Fin.append x.1 x.2
  left_inv x := Fin.append_castAdd_natAdd
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp

def sweepBoard (a b : ℕ) : Fin (2 ^ (a + b)) ≃ Fin (2 ^ a) × Fin (2 ^ b) :=
  (positionsEquiv (a+b)).symm.trans ((splitBinary a b).trans
    (Equiv.prodCongr (positionsEquiv a) (positionsEquiv b)))

def columnGroup (a b : ℕ) : Subgroup (SymmetricGroup (2 ^ (a+b))) :=
  fiberSubgroup (fun x => (sweepBoard a b x).2)

def rowGroup (a b : ℕ) : Subgroup (SymmetricGroup (2 ^ (a+b))) :=
  fiberSubgroup (fun x => (sweepBoard a b x).1)

lemma first_layer_le_columns (a b : ℕ) (i : Fin a) :
    coordinateSubgroup (a+b) (i.castAdd b) ≤ columnGroup a b := by
  intro g hg x
  apply (positionsEquiv b).symm.injective
  
  change (positionsEquiv b).symm ((sweepBoard a b (g x)).2) =
    (positionsEquiv b).symm ((sweepBoard a b x).2)
  simp only [sweepBoard, Equiv.trans_apply, Equiv.prodCongr_apply, splitBinary,
    Equiv.coe_fn_mk, Prod.map_snd, Equiv.symm_apply_apply]
  funext j
  apply coordinateSubgroup_bit ⟨g,hg⟩ x (j.natAdd a)
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
  omega

lemma last_layer_le_rows (a b : ℕ) (j : Fin b) :
    coordinateSubgroup (a+b) (j.natAdd a) ≤ rowGroup a b := by
  intro g hg x
  apply (positionsEquiv a).symm.injective
  change (positionsEquiv a).symm ((sweepBoard a b (g x)).1) =
    (positionsEquiv a).symm ((sweepBoard a b x).1)
  simp only [sweepBoard, Equiv.trans_apply, Equiv.prodCongr_apply, splitBinary,
    Equiv.coe_fn_mk, Prod.map_fst, Equiv.symm_apply_apply]
  funext i
  apply coordinateSubgroup_bit ⟨g,hg⟩ x (i.castAdd b)
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
  omega

def columnSweep {a b : ℕ} (lam : Partition (2 ^ (a+b))) : Specht lam →ₗ[ℂ] Specht lam :=
  (List.ofFn (fun i : Fin a => layerOperator lam (i.castAdd b))).reverse.prod

def rowSweep {a b : ℕ} (lam : Partition (2 ^ (a+b))) : Specht lam →ₗ[ℂ] Specht lam :=
  (List.ofFn (fun j : Fin b => layerOperator lam (j.natAdd a))).reverse.prod

theorem sweepOperator_split {a b : ℕ} (lam : Partition (2 ^ (a+b))) :
    sweepOperator lam = rowSweep lam * columnSweep lam := by
  unfold sweepOperator rowSweep columnSweep
  rw [← Fin.append_castAdd_natAdd (f := layerOperator lam), List.ofFn_fin_append,
    List.reverse_append, List.prod_append]
  simp only [Fin.append_left, Fin.append_right]

lemma columnSweep_contraction {a b : ℕ} (lam : Partition (2 ^ (a+b))) (x : Specht lam) :
    ‖columnSweep lam x‖ ≤ ‖x‖ := by
  apply list_prod_contraction
  intro A hA y
  simp only [List.mem_reverse, List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  exact layerOperator_contraction lam (i.castAdd b) y

lemma rowSweep_contraction {a b : ℕ} (lam : Partition (2 ^ (a+b))) (x : Specht lam) :
    ‖rowSweep lam x‖ ≤ ‖x‖ := by
  apply list_prod_contraction
  intro A hA y
  simp only [List.mem_reverse, List.mem_ofFn] at hA
  obtain ⟨j, rfl⟩ := hA
  exact layerOperator_contraction lam (j.natAdd a) y

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {K E : Type*} [CommSemiring K] [AddCommMonoid E] [Module K E]

lemma trace_product_pow_cycle (A B : E →ₗ[K] E) (r : ℕ) :
    LinearMap.trace K E ((A * B) ^ r) = LinearMap.trace K E ((B * A) ^ r) := by
  cases r with
  | zero => simp
  | succ r =>
    rw [pow_succ, ← mul_assoc, mul_pow_mul, LinearMap.trace_mul_cycle K,
      ← pow_succ']

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma trace_positiveSquare_orientations (T : E →ₗ[ℂ] E) (r : ℕ) :
    LinearMap.trace ℂ E (positiveSquare T ^ r) =
      LinearMap.trace ℂ E ((T * T.adjoint) ^ r) :=
  trace_product_pow_cycle T.adjoint T r

lemma trace_positiveSquare_product (R C : E →ₗ[ℂ] E) (r : ℕ) :
    LinearMap.trace ℂ E (positiveSquare (R * C) ^ r) =
      LinearMap.trace ℂ E ((positiveSquare R * (C * C.adjoint)) ^ r) := by
  have he : positiveSquare (R * C) = C.adjoint * (positiveSquare R * C) := by
    simp only [positiveSquare, ← LinearMap.star_eq_adjoint, star_mul, mul_assoc]
  rw [he, trace_product_pow_cycle]
  simp only [mul_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

def columnSquarePower {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    Specht lam →ₗ[ℂ] Specht lam := (columnSweep lam * (columnSweep lam).adjoint) ^ r

def rowSquarePower {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    Specht lam →ₗ[ℂ] Specht lam := positiveSquare (rowSweep lam) ^ r

lemma columnSquarePower_positive {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    (columnSquarePower lam r).IsPositive := by
  apply positive_pow
  simpa only [positiveSquare, LinearMap.adjoint_adjoint] using adjoint_mul_positive (columnSweep lam).adjoint

lemma rowSquarePower_positive {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    (rowSquarePower lam r).IsPositive := positive_pow (adjoint_mul_positive _) r

lemma sweepSquare_trace_split {a b : ℕ} (lam : Partition (2 ^ (a+b))) (r : ℕ) :
    LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ r) =
      LinearMap.trace ℂ (Specht lam)
        ((positiveSquare (rowSweep lam) * (columnSweep lam * (columnSweep lam).adjoint)) ^ r) := by
  rw [sweepSquare, sweepOperator_split, trace_positiveSquare_product]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma exists_unit_eigenvector (T : E →ₗ[ℂ] E) [Nontrivial E] :
    ∃ c : ℂ, ∃ v : E, ‖v‖ = 1 ∧ T v = c • v := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.2
  refine ⟨c, (‖x‖⁻¹ : ℂ) • x, ?_, ?_⟩
  · simp [norm_smul, hn]
  · simp only [map_smul, hx.apply_eq_smul, smul_smul]
    congr 1
    ring

omit [FiniteDimensional ℂ E] in
lemma orthonormal_head_complement {v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin (finrank ℂ (ℂ ∙ v)ᗮ)) ℂ (ℂ ∙ v)ᗮ) :
    Orthonormal ℂ (Fin.cons v (fun i => (b i : E))) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [inner_self_eq_norm_sq_to_K, hv]
  · simp only [Fin.cons_zero, Fin.cons_succ, (Ne.symm (Fin.succ_ne_zero _)), ite_false]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b j).property
  · simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ite_false]
    rw [← inner_conj_symm]
    simp only [Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property, map_zero]
  · simpa only [Fin.cons_succ, Fin.succ_inj, Submodule.coe_inner] using
      orthonormal_iff_ite.mp b.orthonormal i j

theorem exists_schur_basis (T : E →ₗ[ℂ] E) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular := by
  suffices ∀ n, finrank ℂ E = n →
      ∃ b : OrthonormalBasis (Fin n) ℂ E,
        (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular by
    exact this _ rfl
  intro n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    intro hn
    by_cases h0 : n = 0
    · subst h0
      let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hn)
      refine ⟨b, ?_⟩
      intro i
      exact Fin.elim0 i
    have : Nontrivial E := (Module.finrank_pos_iff (R := ℂ)).mp (hn.symm ▸ Nat.pos_of_ne_zero h0)
    obtain ⟨c,v,hv,hTv⟩ := exists_unit_eigenvector T
    have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv
    let F : Submodule ℂ E := (ℂ ∙ v)ᗮ
    have hdim : 1 + finrank ℂ F = n := by
      simpa only [F, finrank_span_singleton hv0] using
        (Submodule.finrank_add_finrank_orthogonal (ℂ ∙ v)).trans hn
    let S : F →ₗ[ℂ] F := F.orthogonalProjectionOnto.toLinearMap ∘ₗ T ∘ₗ F.subtype
    obtain ⟨b,hb⟩ := ih (finrank ℂ F) (by omega) S rfl
    have hon := orthonormal_head_complement hv b
    let b' : OrthonormalBasis (Fin (finrank ℂ F + 1)) ℂ E :=
      OrthonormalBasis.mk hon (by
        apply le_of_eq
        symm
        apply hon.linearIndependent.span_eq_top_of_card_eq_finrank
        simpa only [Fintype.card_fin, hn] using (by omega : finrank ℂ F + 1 = n))
    have hb' (i : Fin (finrank ℂ F + 1)) : b' i = (Fin.cons v (fun i => (b i : E)) : Fin (finrank ℂ F + 1) → E) i :=
      congrFun (OrthonormalBasis.coe_mk hon _) i
    have hu : (LinearMap.toMatrix b'.toBasis b'.toBasis T).IsUpperTriangular := by
      intro i j hji
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [hb', hb']
      revert hji
      refine Fin.cases ?_ (fun i => ?_) i
      · intro h; exact False.elim (Nat.not_lt_zero _ h)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          simp only [Fin.cons_zero, Fin.cons_succ, hTv, inner_smul_right]
          rw [← inner_conj_symm, Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property]
          simp
        · intro hji
          have h := hb (Fin.succ_lt_succ_iff.mp hji)
          simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
            OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] at h
          simp only [Fin.cons_succ]
          change inner ℂ (b i : E) (T (b j : E)) = 0
          have he : inner ℂ (b i : E) (T (b j : E)) = inner ℂ (b i) (S (b j)) := by
            change _ = inner ℂ (b i : E) (F.starProjection (T (b j : E)))
            rw [← F.inner_starProjection_left_eq_right, F.starProjection_eq_self_iff.mpr (b i).property]
          exact he.trans h
    let e : Fin (finrank ℂ F + 1) ≃ Fin n := finCongr (by omega)
    refine ⟨b'.reindex e, ?_⟩
    intro i j hji
    simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.reindex_apply] using
      hu (i := e.symm i) (j := e.symm j) hji

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {I R : Type*} [Fintype I] [LinearOrder I] [Semiring R]

lemma upper_triangular_mul_diagonal (A B : Matrix I I R)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : I) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma upper_triangular_pow_diagonal (A : Matrix I I R)
    (hA : A.IsUpperTriangular) (i : I) (m : ℕ) :
    (A ^ m) i i = A i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, upper_triangular_mul_diagonal _ _ (hA.pow m) hA, ih, pow_succ]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma schur_trace_power (T : E →ₗ[ℂ] E)
    (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E)
    (hb : (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular) (m : ℕ) :
    LinearMap.trace ℂ E (T ^ m) = ∑ i, (inner ℂ (b i) (T (b i))) ^ m := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, ← LinearMap.toMatrix_pow]
  simp only [Matrix.trace, Matrix.diag, upper_triangular_pow_diagonal _ hb,
    LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]

lemma quadratic_power_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) (m : ℕ) :
    (inner ℂ x ((T ^ m) x)).re = ∑ i : Fin (finrank ℂ E),
      hT.eigenvalues rfl i ^ m * ‖inner ℂ (hT.eigenvectorBasis rfl i) x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner x ((T ^ m) x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (hT.pow m) (hT.eigenvectorBasis rfl i) x,
    power_on_eigenvector T (hT.apply_eigenvectorBasis rfl i), inner_smul_left]
  simp only [map_pow, RCLike.ofReal_eq_complex_ofReal, Complex.conj_ofReal]
  rw [show inner ℂ x (hT.eigenvectorBasis rfl i) *
      ((hT.eigenvalues rfl i : ℂ) ^ m * inner ℂ (hT.eigenvectorBasis rfl i) x) =
      (hT.eigenvalues rfl i : ℂ) ^ m * (inner ℂ (hT.eigenvectorBasis rfl i) x *
        inner ℂ x (hT.eigenvectorBasis rfl i)) by ring,
    ← inner_conj_symm x (hT.eigenvectorBasis rfl i), Complex.mul_conj]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]

lemma quadratic_power_jensen (T : E →ₗ[ℂ] E) (hT : T.IsPositive) {x : E}
    (hx : ‖x‖ = 1) (m : ℕ) :
    (inner ℂ x (T x)).re ^ m ≤ (inner ℂ x ((T ^ m) x)).re := by
  rw [quadratic_spectral T hT.isSymmetric, quadratic_power_spectral T hT.isSymmetric]
  have hw : ∑ i : Fin (finrank ℂ E),
      ‖inner ℂ (hT.isSymmetric.eigenvectorBasis rfl i) x‖ ^ 2 = 1 := by
    rw [(hT.isSymmetric.eigenvectorBasis rfl).sum_sq_norm_inner_right, hx, one_pow]
  simpa only [smul_eq_mul, mul_comm] using
    (convexOn_pow (𝕜 := ℝ) m).map_sum_le
      (t := Finset.univ)
      (w := fun i => ‖inner ℂ (hT.isSymmetric.eigenvectorBasis rfl i) x‖ ^ 2)
      (p := hT.isSymmetric.eigenvalues rfl)
      (fun _ _ => sq_nonneg _) (by simpa using hw) (fun i _ => hT.nonneg_eigenvalues rfl i)

lemma unit_diagonal_power_le (T : E →ₗ[ℂ] E) {x : E} (hx : ‖x‖ = 1) (m : ℕ) :
    ‖inner ℂ x (T x)‖ ^ (2 * m) ≤
      (inner ℂ x ((positiveSquare T ^ m) x)).re := by
  have hc : ‖inner ℂ x (T x)‖ ≤ ‖T x‖ := by
    simpa only [hx, one_mul] using norm_inner_le_norm x (T x)
  have he : (inner ℂ x (positiveSquare T x)).re = ‖T x‖ ^ 2 := by
    simp only [positiveSquare, Module.End.mul_apply, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  calc
    _ = (‖inner ℂ x (T x)‖ ^ 2) ^ m := by rw [pow_mul]
    _ ≤ (‖T x‖ ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hc 2) m
    _ ≤ _ := he ▸ quadratic_power_jensen (positiveSquare T) (adjoint_mul_positive T) hx m

theorem trace_even_power_le_square (T : E →ₗ[ℂ] E) (m : ℕ) :
    (LinearMap.trace ℂ E (T ^ (2 * m))).re ≤
      (LinearMap.trace ℂ E (positiveSquare T ^ m)).re := by
  obtain ⟨b,hb⟩ := exists_schur_basis T
  rw [schur_trace_power T b hb, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (Complex.re_le_norm _).trans ((norm_pow _ _).le.trans
    (unit_diagonal_power_le T (b.norm_eq_one i) m))

lemma trace_product_double_le (A B : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (m : ℕ) :
    (LinearMap.trace ℂ E ((A * B) ^ (2 * m))).re ≤
      (LinearMap.trace ℂ E ((A ^ 2 * B ^ 2) ^ m)).re := by
  have h := trace_even_power_le_square (A * B) m
  have he : positiveSquare (A * B) = B * (A ^ 2 * B) := by
    simp only [positiveSquare, ← LinearMap.star_eq_adjoint, star_mul]
    simp only [LinearMap.star_eq_adjoint, hA.adjoint_eq, hB.adjoint_eq, pow_two, mul_assoc]
  rw [he, trace_product_pow_cycle B, mul_assoc, ← pow_two B] at h
  exact h

theorem dyadic_trace_product_le (A B : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (j : ℕ) :
    (LinearMap.trace ℂ E ((A * B) ^ (2 ^ j))).re ≤
      (LinearMap.trace ℂ E (A ^ (2 ^ j) * B ^ (2 ^ j))).re := by
  induction j generalizing A B with
  | zero => simp
  | succ j ih =>
    rw [pow_succ']
    apply (trace_product_double_le A B hA hB (2 ^ j)).trans
    simpa only [← pow_mul] using ih (A ^ 2) (B ^ 2) (hA.pow 2) (hB.pow 2)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical

theorem sweepSquare_dyadic_trace_split {a b : ℕ} (lam : Partition (2 ^ (a+b))) (j : ℕ) :
    (LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ (2 ^ j))).re ≤
      (LinearMap.trace ℂ (Specht lam)
        (rowSquarePower lam (2 ^ j) * columnSquarePower lam (2 ^ j))).re := by
  rw [sweepSquare_trace_split]
  exact dyadic_trace_product_le _ _ (rowSquarePower_positive lam 1 |>.isSymmetric |>
    (by simpa only [rowSquarePower, pow_one] using ·))
    (columnSquarePower_positive lam 1 |>.isSymmetric |>
    (by simpa only [columnSquarePower, pow_one] using ·)) j

end SignedSweeps
end

end OAI
