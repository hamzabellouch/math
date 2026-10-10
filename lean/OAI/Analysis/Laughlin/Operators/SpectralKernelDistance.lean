import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace OAI

namespace Laughlin
open scoped BigOperators InnerProductSpace

theorem spectral_kernel_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : Module.End ℂ E) (hT : T.IsSymmetric) (c : ℝ) (hc : 0 ≤ c)
    (hgap : ∀ v : E, v≠0 → ∀ a : ℝ, T v=(a : ℂ) • v → a=0 ∨ c≤a)
    (x : E) : ∃ y : E, T y=0 ∧ c*‖x-y‖^2 ≤ (inner ℂ (T x) x).re := by
  classical
  let d := Module.finrank ℂ E
  let b := hT.eigenvectorBasis (n := d) rfl
  let a := hT.eigenvalues (n := d) rfl
  let z : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (fun i => if a i=0 then b.repr x i else 0)
  let y := b.repr.symm z
  have hyrepr (i : Fin d) : b.repr y i = if a i=0 then b.repr x i else 0 := by
    simp [y,z]
  have hdiag (v : E) (i : Fin d) : b.repr (T v) i = (a i : ℂ)*b.repr v i :=
    hT.eigenvectorBasis_apply_self_apply rfl v i
  have hy : T y=0 := by
    apply b.repr.injective
    ext i
    rw [hdiag,hyrepr]
    by_cases hi : a i=0 <;> simp [hi]
  have hnorm : ‖x-y‖^2 = ∑ i : Fin d, if a i=0 then 0 else ‖b.repr x i‖^2 := by
    rw [← b.repr.norm_map,EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_sub,PiLp.sub_apply,hyrepr]
    by_cases ha : a i=0 <;> simp [ha]
  have he : (inner ℂ (T x) x).re = ∑ i : Fin d, a i*‖b.repr x i‖^2 := by
    rw [← b.repr.inner_map_map,PiLp.inner_apply,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiag]
    simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal]
    have hn : (star (b.repr x i)*b.repr x i).re = ‖b.repr x i‖^2 := by
      change (((starRingEnd ℂ) (b.repr x i))*b.repr x i).re = _
      rw [← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.ofReal_re,Complex.normSq_eq_norm_sq]
    have hh : b.repr x i * ((a i : ℂ) * star (b.repr x i)) =
        (a i : ℂ)*(star (b.repr x i)*b.repr x i) := by ring
    change (b.repr x i * ((a i : ℂ) * star (b.repr x i))).re = _
    rw [hh,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hn]
  refine ⟨y,hy,?_⟩
  rw [hnorm,he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb : b i ≠ 0 := b.orthonormal.ne_zero i
  have hgi := hgap (b i) hb (a i) (hT.apply_eigenvectorBasis rfl i)
  by_cases ha : a i=0
  · simp [ha]
  · rw [ite_eq_right ha]
    exact mul_le_mul (hgi.resolve_left ha) le_rfl (sq_nonneg _)
      (hc.trans (hgi.resolve_left ha))

end Laughlin

end OAI
