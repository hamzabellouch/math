import Mathlib

namespace OAI


noncomputable section

namespace Problem355.Lattice

open Module MeasureTheory
open scoped BigOperators Matrix

theorem covolume_sq_eq_det_gram
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume L ^ 2 = (Matrix.gram ℝ (fun i => (b i : E))).det := by
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simp [Measure.real, o.volume_parallelepiped]
  have hcov := ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis
  rw [hvol, mul_one] at hcov
  rw [hcov, sq_abs, Matrix.gram_eq_conjTranspose_mul o,
    Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [Basis.det_apply, pow_two, star_trivial]
  rfl

theorem covolume_eq_sqrt_det_gram
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
  rw [← covolume_sq_eq_det_gram L b o, Real.sqrt_sq (ZLattice.covolume_pos L volume).le]

theorem normal_smul_cross_eq_det_smul
    (u v w y : Fin 3 → ℝ)
    (hu : u ⬝ᵥ y = 0) (hv : v ⬝ᵥ y = 0) :
    (y ⬝ᵥ w) • (u ⨯₃ v) = (Matrix.det ![u, v, w]) • y := by
  have hz : (u ⨯₃ v) ⨯₃ y = 0 := by
    rw [cross_cross_eq_smul_sub_smul, hu, hv, zero_smul, zero_smul, sub_self]
  have h := cross_cross_eq_smul_sub_smul (u ⨯₃ v) y w
  rw [hz] at h
  have ht : (u ⨯₃ v) ⬝ᵥ w = Matrix.det ![u, v, w] := by
    rw [dotProduct_comm, triple_product_permutation, triple_product_eq_det]
  have hzero : (Matrix.det ![u, v, w]) • y - (y ⬝ᵥ w) • (u ⨯₃ v) = 0 := by
    simpa only [map_zero, LinearMap.zero_apply, ht] using h.symm
  exact (sub_eq_zero.mp hzero).symm

theorem cross_norm_eq_abs_det_mul_norm_div
    (u v w y : Fin 3 → ℝ)
    (hu : u ⬝ᵥ y = 0) (hv : v ⬝ᵥ y = 0) (hg : y ⬝ᵥ w ≠ 0) :
    ‖WithLp.toLp 2 (u ⨯₃ v)‖ =
      |Matrix.det ![u, v, w]| * ‖WithLp.toLp 2 y‖ / |y ⬝ᵥ w| := by
  have hn := congrArg (fun z : Fin 3 → ℝ => ‖WithLp.toLp 2 z‖)
    (normal_smul_cross_eq_det_smul u v w y hu hv)
  have hnorm : |y ⬝ᵥ w| * ‖WithLp.toLp 2 (u ⨯₃ v)‖ =
      |Matrix.det ![u, v, w]| * ‖WithLp.toLp 2 y‖ := by
    simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] using hn
  apply (eq_div_iff (abs_ne_zero.mpr hg)).2
  simpa only [mul_comm] using hnorm

theorem det_gram_pair_eq_cross_norm_sq
    (u v : EuclideanSpace ℝ (Fin 3)) :
    (Matrix.gram ℝ ![u, v]).det =
      ‖WithLp.toLp 2 (u.ofLp ⨯₃ v.ofLp)‖ ^ 2 := by
  rw [Matrix.det_fin_two, ← real_inner_self_eq_norm_sq]
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [cross_dot_cross]
  rw [dotProduct_comm v.ofLp u.ofLp]

theorem covolume_eq_cross_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L) (o : OrthonormalBasis (Fin 2) ℝ E)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ZLattice.covolume L =
      ‖WithLp.toLp 2 ((f (b 0)).ofLp ⨯₃ (f (b 1)).ofLp)‖ := by
  apply (sq_eq_sq₀ (ZLattice.covolume_pos L volume).le (norm_nonneg _)).mp
  rw [covolume_sq_eq_det_gram L b o, ← det_gram_pair_eq_cross_norm_sq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.gram_apply, f.inner_map_map]

theorem covolume_eq_abs_det_mul_norm_div
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (w y : Fin 3 → ℝ)
    (h0 : (f (b 0)).ofLp ⬝ᵥ y = 0)
    (h1 : (f (b 1)).ofLp ⬝ᵥ y = 0) (hg : y ⬝ᵥ w ≠ 0) :
    ZLattice.covolume L =
      |Matrix.det ![(f (b 0)).ofLp, (f (b 1)).ofLp, w]| *
        ‖WithLp.toLp 2 y‖ / |y ⬝ᵥ w| := by
  have hdim : finrank ℝ E = 2 := by
    simpa using finrank_eq_card_basis (b.ofZLatticeBasis ℝ)
  let o := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  rw [covolume_eq_cross_norm L b o f]
  exact cross_norm_eq_abs_det_mul_norm_div _ _ w y h0 h1 hg

theorem covolume_eq_index_mul_norm_div
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (w y : Fin 3 → ℝ) (I g : ℝ)
    (h0 : (f (b 0)).ofLp ⬝ᵥ y = 0)
    (h1 : (f (b 1)).ofLp ⬝ᵥ y = 0)
    (hI : |Matrix.det ![(f (b 0)).ofLp, (f (b 1)).ofLp, w]| = I)
    (hg : y ⬝ᵥ w = g) (hgpos : 0 < g) :
    ZLattice.covolume L = I * ‖WithLp.toLp 2 y‖ / g := by
  rw [covolume_eq_abs_det_mul_norm_div L b f w y h0 h1
    (by rw [hg]; exact ne_of_gt hgpos), hI, hg, abs_of_pos hgpos]

theorem abs_det_int_basis_eq_index
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (b : Basis ι ℤ L) :
    |(Matrix.of (fun i j => ((b i : ι → ℤ) j : ℝ))).det| =
      (L.toAddSubgroup.index : ℝ) := by
  have h : L.toAddSubgroup.index =
      (Matrix.of (fun i => (b i : ι → ℤ))).det.natAbs := by
    simpa only [Pi.basisFun_det_apply] using
      AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ ι) L.toAddSubgroup b
  rw [h, Nat.cast_natAbs, Int.cast_abs, Int.cast_det]
  rfl

theorem abs_det_sum_basis_eq_index
    (L : Submodule ℤ (Fin 3 → ℤ)) (b : Basis (Fin 2 ⊕ Unit) ℤ L) :
    |(Matrix.det ![(fun j => ((b (Sum.inl 0) : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((b (Sum.inl 1) : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((b (Sum.inr ()) : Fin 3 → ℤ) j : ℝ))])| =
        (L.toAddSubgroup.index : ℝ) := by
  let e : Fin 2 ⊕ Unit ≃ Fin 3 :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
  have h := abs_det_int_basis_eq_index L (b.reindex e)
  convert h using 1
  congr 2
  ext i j
  fin_cases i <;> simp [e, Basis.reindex_apply, finSumFinEquiv, Fin.addCases]

theorem euclidean_covolume_eq_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) :
    ZLattice.covolume L = |(Matrix.of (fun i => (b i : EuclideanSpace ℝ ι).ofLp)).det| := by
  let o := EuclideanSpace.basisFun ι ℝ
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simp [Measure.real, o.volume_parallelepiped]
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis, hvol, mul_one]
  congr 1
  rw [Basis.det_apply]
  change (Matrix.of (fun i j => (b j : EuclideanSpace ℝ ι).ofLp i)).det = _
  exact Matrix.det_transpose _

end Problem355.Lattice

end

end OAI
