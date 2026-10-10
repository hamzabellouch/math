import Mathlib
import OAI.Analysis.AffineBernstein.SupportHomogeneity
import OAI.Analysis.AffineBernstein.RadialAdjugate

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section NewtonBasis
open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orthogonalChange (b c : OrthonormalBasis ι ℝ E) : Matrix ι ι ℝ :=
  Matrix.of fun i j => inner ℝ (b i) (c j)

omit [CompleteSpace E] in
lemma orthogonalChange_transpose_mul (b c : OrthonormalBasis ι ℝ E) :
    (orthogonalChange b c)ᵀ * orthogonalChange b c = 1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,orthogonalChange,Matrix.of_apply,Matrix.one_apply]
  calc
    ∑ k, inner ℝ (b k) (c i) * inner ℝ (b k) (c j) = inner ℝ (c i) (c j) := by
      convert b.sum_inner_mul_inner (c i) (c j) using 1
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_comm (b k) (c i)]
    _ = _ := orthonormal_iff_ite.mp c.orthonormal i j

omit [CompleteSpace E] in
lemma orthogonalChange_mul_transpose (b c : OrthonormalBasis ι ℝ E) :
    orthogonalChange b c * (orthogonalChange b c)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,orthogonalChange,Matrix.of_apply,Matrix.one_apply]
  calc
    ∑ k, inner ℝ (b i) (c k) * inner ℝ (b j) (c k) = inner ℝ (b i) (b j) := by
      convert c.sum_inner_mul_inner (b i) (b j) using 1
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_comm (b j) (c k)]
    _ = _ := orthonormal_iff_ite.mp b.orthonormal i j

end NewtonBasis
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def tubeFullRadiusMatrix (H : S × E → ℝ) (q : S × E) (b : OrthonormalBasis ι ℝ E) :
    Matrix ι ι ℝ := Matrix.of fun i j =>
  fderiv ℝ (fderiv ℝ H) q (0,b i) (0,b j)

def tubeAngularDensity (H : S × E → ℝ) (q : S × E) (b : OrthonormalBasis ι ℝ E) : ℝ :=
  (tubeFullRadiusMatrix H q b).adjugate.trace

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_change (H : S × E → ℝ) (q : S × E)
    (b c : OrthonormalBasis ι ℝ E) :
    tubeFullRadiusMatrix H q c =
      (orthogonalChange b c)ᵀ * tubeFullRadiusMatrix H q b * orthogonalChange b c := by
  have hre (v : E) : ((0:S),v) = ∑ i, b.repr v i • (0,b i) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' v).symm
  ext i j
  simp only [tubeFullRadiusMatrix,Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,
    orthogonalChange,Finset.sum_mul]
  conv_lhs => rw [hre (c i),hre (c j)]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
    OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [CompleteSpace E] in
lemma tubeAngularDensity_basis_independent (H : S × E → ℝ) (q : S × E)
    (b c : OrthonormalBasis ι ℝ E) : tubeAngularDensity H q c = tubeAngularDensity H q b := by
  rw [tubeAngularDensity,tubeFullRadiusMatrix_change H q b c,
    adjugate_conjugate_orthogonal (orthogonalChange_mul_transpose b c)
      (orthogonalChange_transpose_mul b c),Matrix.trace_mul_cycle,
      orthogonalChange_mul_transpose,Matrix.one_mul]
  rfl

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_symm {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    (tubeFullRadiusMatrix H q b).IsSymm := by
  have hh := hH.isSymmSndFDerivAt (by simp)
  ext i j
  exact hh.eq _ _

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_radial {H : S × E → ℝ} {q : S × E}
    (b : OrthonormalBasis ι ℝ E)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0) :
    tubeFullRadiusMatrix H q b *ᵥ (b.repr q.2) = 0 := by
  ext i
  have hh := hr (b i)
  have he : ((0:S),q.2) = ∑ j, b.repr q.2 j • (0,b j) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' q.2).symm
  rw [he] at hh
  simp only [map_sum,map_smul,smul_eq_mul] at hh
  simpa [Matrix.mulVec,dotProduct,tubeFullRadiusMatrix,map_sum,map_smul,mul_comm] using hh

/- The full cofactor trace recovers the transverse determinant in every flat
normal chart. No unit-normal constraint is imposed away from the chart center. -/
omit [CompleteSpace E] in
lemma tubeAngularDensity_flat {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : inner ℝ q.2 (b (Sum.inr ())) = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0) :
    tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det * inner ℝ q.2 q.2 := by
  have hc : b.repr q.2 (Sum.inr ()) = 1 := by
    simpa [OrthonormalBasis.repr_apply_apply,real_inner_comm] using he
  have hh := radial_adjugate_trace (tubeFullRadiusMatrix_symm hH b)
    (b.repr q.2) hc (tubeFullRadiusMatrix_radial b hr)
  change tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det * _ at hh
  rw [← b.sum_inner_mul_inner q.2 q.2]
  simpa [OrthonormalBasis.repr_apply_apply,real_inner_comm q.2] using hh

omit [CompleteSpace E] in
lemma tubeAngularDensity_of_last_null {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,b (Sum.inr ())) = 0) :
    tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det := by
  have hs := tubeFullRadiusMatrix_symm hH b
  have hb : tubeFullRadiusMatrix H q b =
      Matrix.fromBlocks (tubeRadiusMatrix H q b) 0 0 (0 : Matrix Unit Unit ℝ) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => cases j; exact hr _
    | inr i =>
      cases i
      cases j with
      | inl j => rw [← hs.apply]; exact hr _
      | inr j => cases j; exact hr _
  rw [tubeAngularDensity,hb,adjugate_block_radial]
  simp [Matrix.trace,Fintype.sum_sum_type,Matrix.fromBlocks]

omit [Fintype ι] [DecidableEq ι] in
lemma homogeneous_tubeBaseMatrix_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : Module.Basis ι ℝ S) :
    tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      c • tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  ext i j
  have hh := homogeneous_fiber_hessian_scale hD hs hK hne hc hH hHc (b i,0) (b j,0)
  simp only [normalScale_apply,smul_zero] at hh
  simp only [tubeBaseMatrix,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,hh,mul_neg]

omit [DecidableEq ι] in
lemma homogeneous_tubeFullRadiusMatrix_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : OrthonormalBasis ι ℝ E) :
    tubeFullRadiusMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      c⁻¹ • tubeFullRadiusMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  ext i j
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have hh := homogeneous_fiber_hessian_scale hD hs hK hne hc hH hHc (0,b i) (0,b j)
  have hscale (v : E) : normalScale c ((0:S),v) = c • ((0:S),v) := by simp
  rw [hscale,hscale] at hh
  change fderiv ℝ (fderiv ℝ H) (s,c • e) (c • ((0:S),b i)) (c • ((0:S),b j)) =
    c * fderiv ℝ (fderiv ℝ H) (s,e) (0,b i) (0,b j) at hh
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  change fderiv ℝ (fderiv ℝ H) (s,c • e) (0,b i) (0,b j) =
    c⁻¹ * fderiv ℝ (fderiv ℝ H) (s,e) (0,b i) (0,b j)
  apply (mul_left_cancel₀ hc.ne')
  rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  apply (mul_left_cancel₀ hc.ne')
  exact hh

lemma homogeneous_tubeAngularDensity_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      (c⁻¹)^Fintype.card κ *
        tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  simp only [tubeAngularDensity,homogeneous_tubeFullRadiusMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.adjugate_smul,Matrix.trace_smul,smul_eq_mul,Fintype.card_sum,Fintype.card_unit,
    Nat.add_sub_cancel]

def invariantTubeF (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) (q : S × E) : ℝ :=
  δ * (Real.log (tubeBaseMatrix H q bS).det + Real.log (inner ℝ q.2 q.2) -
     Real.log (tubeAngularDensity H q b)) - Real.log (H q)

omit [CompleteSpace E] in
lemma invariantTubeF_basis_independent (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (b c : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) (q : S × E) :
    invariantTubeF H bS c δ q = invariantTubeF H bS b δ q := by
  simp only [invariantTubeF,tubeAngularDensity_basis_independent H q b c]

omit [CompleteSpace E] in
lemma invariantTubeF_eq_flat {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S)
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : inner ℝ q.2 (b (Sum.inr ())) = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0)
    (hR : (tubeRadiusMatrix H q b).det ≠ 0) (δ : ℝ) :
    invariantTubeF H bS b δ q =
      δ * (Real.log (tubeBaseMatrix H q bS).det - Real.log (tubeRadiusMatrix H q b).det) -
        Real.log (H q) := by
  have hq : q.2 ≠ 0 := by intro hz; simp [hz] at he
  have hh : inner ℝ q.2 q.2 ≠ 0 := (real_inner_self_pos.mpr hq).ne'
  rw [invariantTubeF,tubeAngularDensity_flat hH b he hr,Real.log_mul hR hh]
  ring

lemma invariantTubeF_smul {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (bS : Module.Basis ι ℝ S) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : (tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bS).det ≠ 0)
    (hQ : tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b ≠ 0)
    (hh : homogeneousSupport (K s) e ≠ 0) (he : e ≠ 0) :
    invariantTubeF (fun q : S × E => homogeneousSupport (K q.1) q.2) bS b
      (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,c • e) =
    invariantTubeF (fun q : S × E => homogeneousSupport (K q.1) q.2) bS b
      (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e) := by
  have hn : inner ℝ e e ≠ 0 := (real_inner_self_pos.mpr he).ne'
  have hden : (Fintype.card ι : ℝ)+Fintype.card κ+2 ≠ 0 := by positivity
  simp only [invariantTubeF,homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.det_smul,homogeneous_tubeAngularDensity_scale hD hs hK hne hc hH hHc]
  rw [homogeneousSupport_smul (hK s hs) (hne s hs) e hc]
  simp only [real_inner_smul_left,real_inner_smul_right]
  rw [Real.log_mul (pow_ne_zero _ hc.ne') hB,
    Real.log_mul (pow_ne_zero _ (inv_ne_zero hc.ne')) hQ,
    Real.log_mul hc.ne' hh,Real.log_mul hc.ne' (mul_ne_zero hc.ne' hn),
    Real.log_mul hc.ne' hn,Real.log_pow,Real.log_pow,Real.log_inv]
  field_simp
  ring

end AffineBernstein
end

end OAI
