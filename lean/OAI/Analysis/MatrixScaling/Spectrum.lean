import OAI.Analysis.MatrixScaling.Determinant
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-! Spectral min-max bounds, continuity, and compactness of projections. -/

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def spectralForm (b : OrthonormalBasis (Fin r) ℂ E) (e : Fin r → ℝ) (x : E) : ℝ :=
  ∑ i, e i * ‖b.repr x i‖^2

theorem basis_norm_sq (b : OrthonormalBasis (Fin r) ℂ E) (x : E) :
    ‖x‖^2 = ∑ i, ‖b.repr x i‖^2 := by
  rw [← b.repr.norm_map x]
  exact EuclideanSpace.norm_sq_eq _

/-- Two full bases have a nonzero vector in the first k+1 coordinates of
one basis and in the last r-k coordinates of the other. -/
theorem basis_intersection_vector (a b : OrthonormalBasis (Fin r) ℂ E) (k : Fin r) :
    ∃ x : E, x ≠ 0 ∧ (∀ i : Fin r, k < i → a.repr x i = 0) ∧
      (∀ i : Fin r, i < k → b.repr x i = 0) := by
  let emb : Fin (k.val+1) → Fin r := fun i => ⟨i.val, by omega⟩
  have hemb : Function.Injective emb := fun i j h => Fin.ext (congrArg (fun z : Fin r => z.val) h)
  let L : (Fin (k.val+1) → ℂ) →ₗ[ℂ] E :=
    ∑ i, (LinearMap.proj i).smulRight (a (emb i))
  have hL (v : Fin (k.val+1) → ℂ) : L v = ∑ i, v i • a (emb i) := by
    simp [L]
  have hcoord (v : Fin (k.val+1) → ℂ) (j : Fin r) :
      a.repr (L v) j = ∑ i, if emb i = j then v i else 0 := by
    rw [hL]
    simp [map_sum, map_smul, OrthonormalBasis.repr_self, Pi.single_apply, mul_ite, eq_comm]
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    funext i
    have h := hcoord v (emb i)
    rw [hv, map_zero] at h
    simpa only [PiLp.zero_apply, hemb.eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Pi.zero_apply] using h.symm
  let C : (Fin (k.val+1) → ℂ) →ₗ[ℂ] (Fin k.val → ℂ) :=
    LinearMap.pi (fun i => (b.toBasis.coord ⟨i.val, by omega⟩).comp L)
  have hnot : ¬ Function.Injective C := by
    intro h
    have hc := LinearMap.finrank_le_finrank_of_injective h
    simp only [Module.finrank_pi, Fintype.card_fin] at hc
    omega
  obtain ⟨v, hv, hv0⟩ : ∃ v, C v = 0 ∧ v ≠ 0 := by
    by_contra h
    apply hnot
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    exact h ⟨v, hv, hv0⟩
  refine ⟨L v, fun h => hv0 (hinj (h.trans L.map_zero.symm)), ?_, ?_⟩
  · intro i hi
    rw [hcoord]
    apply Finset.sum_eq_zero
    intro j _
    have hne : emb j ≠ i := by intro h; have := congrArg Fin.val h; dsimp [emb] at this; omega
    simp [hne]
  · intro i hi
    have h := congrFun hv (⟨i.val, hi⟩ : Fin k.val)
    exact h

/-- The min--max comparison, proved by a dimension intersection and
quadratic-form bounds in two orthonormal bases. -/
theorem spectralForm_eigenvalue_mono
    (a b : OrthonormalBasis (Fin r) ℂ E) (e f : Fin r → ℝ)
    (he : Antitone e) (hf : Antitone f)
    (horder : ∀ x, spectralForm a e x ≤ spectralForm b f x) (k : Fin r) : e k ≤ f k := by
  obtain ⟨x,hx,ha,hb⟩ := basis_intersection_vector a b k
  have hlo : e k * ‖x‖^2 ≤ spectralForm a e x := by
    rw [basis_norm_sq a x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ≤ k
    · exact mul_le_mul_of_nonneg_right (he hi) (sq_nonneg _)
    · simp [ha i (lt_of_not_ge hi)]
  have hhi : spectralForm b f x ≤ f k * ‖x‖^2 := by
    rw [basis_norm_sq b x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : k ≤ i
    · exact mul_le_mul_of_nonneg_right (hf hi) (sq_nonneg _)
    · simp [hb i (lt_of_not_ge hi)]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp
    (hlo.trans ((horder x).trans hhi))

theorem symmetric_spectralForm [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = r) (x : E) :
    spectralForm (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x =
      (inner ℂ x (T x)).re := by
  let b := hT.eigenvectorBasis hn
  rw [← b.repr.inner_map_map x (T x), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (∑ i, hT.eigenvalues hn i * ‖b.repr x i‖^2) =
    (∑ i, star (b.repr x i) * b.repr (T x) i).re
  have hsum := map_sum Complex.reAddGroupHom
    (fun i : Fin r => star (b.repr x i) * b.repr (T x) i) Finset.univ
  change (∑ i, star (b.repr x i) * b.repr (T x) i).re =
    ∑ i, (star (b.repr x i) * b.repr (T x) i).re at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hT.eigenvectorBasis_apply_self_apply hn x i]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im, star]
  ring

/-- Eigenvalue monotonicity for symmetric operators from quadratic-form order. -/
theorem symmetric_eigenvalues_mono [FiniteDimensional ℂ E]
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = r)
    (horder : ∀ x, (inner ℂ x (T x)).re ≤ (inner ℂ x (S x)).re) (k : Fin r) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k := by
  apply spectralForm_eigenvalue_mono (hT.eigenvectorBasis hn) (hS.eigenvectorBasis hn)
    _ _ (hT.eigenvalues_antitone hn) (hS.eigenvalues_antitone hn)
  intro x
  simpa only [symmetric_spectralForm] using horder x

theorem decreasingEigenvalues_mono {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hBA : (B-A).PosSemidef) (k : Fin r) :
    decreasingEigenvalues hA k ≤ decreasingEigenvalues hB k := by
  apply symmetric_eigenvalues_mono (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) (finrank_euclideanSpace)
  intro x
  have h := hBA.re_dotProduct_nonneg (WithLp.ofLp x)
  simp only [Matrix.sub_mulVec, dotProduct_sub] at h
  simpa only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, dotProduct_comm] using sub_nonneg.mp h

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem symmetric_eigenvalues_smul_le [FiniteDimensional ℂ E]
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = r) (c : ℝ) (hc : 0 ≤ c)
    (horder : ∀ x, c * (inner ℂ x (T x)).re ≤ (inner ℂ x (S x)).re) (k : Fin r) :
    c * hT.eigenvalues hn k ≤ hS.eigenvalues hn k := by
  apply spectralForm_eigenvalue_mono (hT.eigenvectorBasis hn) (hS.eigenvectorBasis hn)
    (fun i => c * hT.eigenvalues hn i) (hS.eigenvalues hn)
    (fun i j hij => mul_le_mul_of_nonneg_left (hT.eigenvalues_antitone hn hij) hc)
    (hS.eigenvalues_antitone hn)
  intro x
  have he : spectralForm (hT.eigenvectorBasis hn) (fun i => c * hT.eigenvalues hn i) x =
      c * spectralForm (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x := by
    simp only [spectralForm, Finset.mul_sum, mul_assoc]
  rw [he, symmetric_spectralForm, symmetric_spectralForm]
  exact horder x

theorem decreasingEigenvalues_smul_le {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (hBA : (B-c • A).PosSemidef) (k : Fin r) :
    c * decreasingEigenvalues hA k ≤ decreasingEigenvalues hB k := by
  apply symmetric_eigenvalues_smul_le (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace c hc
  intro x
  have h := hBA.re_dotProduct_nonneg (WithLp.ofLp x)
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul] at h
  simpa only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, dotProduct_comm, Complex.smul_re, smul_eq_mul] using sub_nonneg.mp h

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem quadraticForm_norm_bound (T : E →L[ℂ] E) (x : E) :
    (inner ℂ x (T x)).re ≤ ‖T‖ * ‖x‖^2 := by
  calc
    (inner ℂ x (T x)).re ≤ ‖inner ℂ x (T x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖^2 := by ring

theorem spectralForm_add_const (b : OrthonormalBasis (Fin r) ℂ E)
    (e : Fin r → ℝ) (c : ℝ) (x : E) :
    spectralForm b (fun i => e i+c) x = spectralForm b e x + c*‖x‖^2 := by
  simp only [spectralForm, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← basis_norm_sq]

theorem symmetric_eigenvalue_le_add_norm [FiniteDimensional ℂ E]
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = r) (k : Fin r) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k + ‖(T-S).toContinuousLinearMap‖ := by
  apply spectralForm_eigenvalue_mono (hT.eigenvectorBasis hn) (hS.eigenvectorBasis hn)
    (hT.eigenvalues hn) (fun i => hS.eigenvalues hn i + ‖(T-S).toContinuousLinearMap‖)
    (hT.eigenvalues_antitone hn) (fun i j hij => add_le_add (hS.eigenvalues_antitone hn hij) le_rfl)
  intro x
  rw [spectralForm_add_const, symmetric_spectralForm, symmetric_spectralForm]
  have h := quadraticForm_norm_bound (T-S).toContinuousLinearMap x
  change (inner ℂ x (T x - S x)).re ≤ _ at h
  rw [inner_sub_right, Complex.sub_re] at h
  linarith

/-- Ordered eigenvalues are 1-Lipschitz in the actual operator norm. -/
theorem decreasingEigenvalues_sub_le_norm {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin r) :
    |decreasingEigenvalues hA k - decreasingEigenvalues hB k| ≤ ‖A-B‖ := by
  have hab := symmetric_eigenvalue_le_add_norm
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace
    (Fin.cast (Fintype.card_fin r).symm k)
  have hba := symmetric_eigenvalue_le_add_norm
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace
    (Fin.cast (Fintype.card_fin r).symm k)
  rw [← map_sub] at hab hba
  change decreasingEigenvalues hA k ≤ decreasingEigenvalues hB k + ‖A-B‖ at hab
  change decreasingEigenvalues hB k ≤ decreasingEigenvalues hA k + ‖B-A‖ at hba
  rw [norm_sub_rev] at hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem lipschitz_decreasingEigenvalues (k : Fin r) :
    LipschitzWith 1 (fun A : {A : Matrix (Fin r) (Fin r) ℂ // A.IsHermitian} =>
      decreasingEigenvalues A.property k) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    decreasingEigenvalues_sub_le_norm A.property B.property k

theorem continuous_decreasingEigenvalues (k : Fin r) :
    Continuous (fun A : {A : Matrix (Fin r) (Fin r) ℂ // A.IsHermitian} =>
      decreasingEigenvalues A.property k) :=
  (lipschitz_decreasingEigenvalues k).continuous

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {d : ℕ}

theorem projection_eigenvalue_zero_or_one {p : Matrix (Fin d) (Fin d) ℂ}
    (hp : p.IsHermitian) (hpp : p*p=p) (i : Fin d) :
    hp.eigenvalues i = 0 ∨ hp.eigenvalues i = 1 := by
  have h := congrArg (Unitary.conjStarAlgAut ℂ _ (star hp.eigenvectorUnitary)) hpp
  rw [map_mul, hp.conjStarAlgAut_star_eigenvectorUnitary] at h
  have hi := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i i) h
  simp only [Matrix.diagonal_mul_diagonal, diagonal_apply_eq,
    Function.comp_apply] at hi
  have hr : hp.eigenvalues i * hp.eigenvalues i = hp.eigenvalues i := by
    exact_mod_cast hi
  have hz : hp.eigenvalues i * (hp.eigenvalues i - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem projection_trace_eq_rank {p : Matrix (Fin d) (Fin d) ℂ}
    (hp : p.IsHermitian) (hpp : p*p=p) : p.trace = (p.rank : ℂ) := by
  rw [hp.trace_eq_sum_eigenvalues, hp.rank_eq_card_non_zero_eigs]
  calc
    ∑ i, (hp.eigenvalues i : ℂ) =
        ∑ i : Fin d, if hp.eigenvalues i ≠ 0 then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases projection_eigenvalue_zero_or_one hp hpp i with h | h <;> simp [h]
    _ = _ := by rw [Fintype.card_subtype]; simp only [Finset.sum_boole]

/-- Orthogonal rank-s projections, represented by equations with continuous
left-hand sides; the trace equation is equivalent to the rank condition. -/
abbrev projectionSpace (d s : ℕ) :=
  {p : Matrix (Fin d) (Fin d) ℂ // p.IsHermitian ∧ p*p=p ∧ p.trace.re=(s : ℝ)}

theorem projectionSpace_rank {s : ℕ} (p : projectionSpace d s) : p.val.rank = s := by
  have h := congrArg Complex.re (projection_trace_eq_rank p.property.1 p.property.2.1)
  rw [p.property.2.2] at h
  simpa only [Complex.natCast_re, Nat.cast_inj] using h.symm

theorem isCompact_projectionSpace (s : ℕ) :
    IsCompact {p : Matrix (Fin d) (Fin d) ℂ |
      p.IsHermitian ∧ p*p=p ∧ p.trace.re=(s : ℝ)} := by
  have hc : IsClosed {p : Matrix (Fin d) (Fin d) ℂ |
      p.IsHermitian ∧ p*p=p ∧ p.trace.re=(s : ℝ)} := by
    apply IsClosed.inter
    · exact isClosed_eq continuous_star continuous_id
    · apply IsClosed.inter
      · exact isClosed_eq (continuous_id.mul continuous_id) continuous_id
      · exact isClosed_eq (Complex.continuous_re.comp continuous_id.matrix_trace) continuous_const
  apply (isCompact_closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1).of_isClosed_subset hc
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs : IsStarProjection p := ⟨hp.2.1, hp.1⟩
  exact hs.norm_le

instance (s : ℕ) : CompactSpace (projectionSpace d s) :=
  isCompact_iff_compactSpace.mp (isCompact_projectionSpace s)

end Kaplansky

end
end

end OAI
