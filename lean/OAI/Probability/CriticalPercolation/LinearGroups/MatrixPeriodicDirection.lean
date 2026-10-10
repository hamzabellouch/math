import Mathlib

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma intMatrix_mahlerMeasure_eq_one (M : Matrix ι ι ℤ)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1) :
    (M.charpoly.map (Int.castRingHom ℂ)).mahlerMeasure=1 := by
  rw [←Matrix.charpoly_map,Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    (Matrix.charpoly_monic _).leadingCoeff,norm_one,one_mul]
  apply Multiset.prod_eq_one
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
  exact max_eq_left (hroots z hz)

lemma intMatrix_root_is_rootOfUnity (M : Matrix ι ι ℤ)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1)
    (z : ℂ) (hz : z∈(M.map (Int.castRingHom ℂ)).charpoly.roots) (hz0 : z≠0) :
    ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  apply Polynomial.pow_eq_one_of_mahlerMeasure_eq_one
    (intMatrix_mahlerMeasure_eq_one M hroots) hz0
  have he : Int.castRingHom ℂ = algebraMap ℤ ℂ := by ext; simp
  simpa only [Polynomial.aroots_def,Matrix.charpoly_map,he] using hz

theorem intMatrix_exists_periodic_vector [Nonempty ι] (M : Matrix ι ι ℤ)
    (hunit : IsUnit M)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1) :
    ∃ m : ℕ, 0 < m ∧ ∃ v : ι → ℤ, v≠0 ∧ (M^m).mulVec v=v := by
  let C := M.map (Int.castRingHom ℂ)
  have hcunit : IsUnit C := hunit.map (Int.castRingHom ℂ).mapMatrix
  have hdeg : C.charpoly.degree ≠ 0 := by
    apply ne_of_gt
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact Fintype.card_pos
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root C.charpoly hdeg
  have heig : Module.End.HasEigenvalue C.mulVecLin z := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    rwa [Matrix.charpoly_mulVecLin]
  have hz0 : z≠0 := by
    intro hz0
    obtain ⟨w,hw⟩ := heig.exists_hasEigenvector
    apply hw.2
    apply Matrix.mulVec_injective_iff_isUnit.mpr hcunit
    have he := hw.apply_eq_smul
    simpa [hz0] using he
  have hzmem := (Polynomial.mem_roots (Matrix.charpoly_monic C).ne_zero).mpr hz
  obtain ⟨m,hm,hmz⟩ := intMatrix_root_is_rootOfUnity M hroots z hzmem hz0
  have heigpow := heig.pow m
  rw [hmz] at heigpow
  have hroot : (C^m).charpoly.IsRoot 1 := by
    have he : (C^m).mulVecLin = C.mulVecLin^m := Matrix.toLin'_pow C m
    rw [←Matrix.charpoly_mulVecLin,he]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heigpow
  have hrootZ : (M^m).charpoly.IsRoot 1 := by
    apply Polynomial.IsRoot.of_map (f := Int.castRingHom ℂ) ?_ (Int.castRingHom ℂ).injective_int
    simpa only [map_one,←Matrix.charpoly_map,Matrix.map_pow] using hroot
  have heigZ : Module.End.HasEigenvalue (M^m).mulVecLin 1 := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    rwa [Matrix.charpoly_mulVecLin]
  obtain ⟨v,hv⟩ := heigZ.exists_hasEigenvector
  refine ⟨m,hm,v,hv.2,?_⟩
  simpa only [Matrix.mulVecLin_apply,one_smul] using hv.apply_eq_smul

end CriticalPercolation.SparseGrowth
end
end

end OAI
