import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.FormalEtale

namespace OAI


                                     
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators
open Set

variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]

def kernelPoint (p : R →ₐ[K] K) : PrimeSpectrum R :=
  ⟨RingHom.ker p, RingHom.ker_isPrime p⟩

@[instance_reducible] def rationalPointTopology : TopologicalSpace (R →ₐ[K] K) :=
  TopologicalSpace.induced (kernelPoint K R) inferInstance

lemma isOpen_eval_ne_zero (f : R) :
    @IsOpen (R →ₐ[K] K) (rationalPointTopology K R) {p | p f ≠ 0} := by
  let _ := rationalPointTopology K R
  have hc : Continuous (kernelPoint K R) := continuous_induced_dom
  have heq : {p : R →ₐ[K] K | p f ≠ 0} =
      (kernelPoint K R) ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    ext p
    simp [kernelPoint, RingHom.mem_ker]
  rw [heq]
  exact (PrimeSpectrum.basicOpen f).isOpen.preimage hc

variable {K R}

lemma injective_mulVec_iff_exists_det {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n K) :
    Function.Injective M.mulVec ↔ ∃ B : Matrix n m K, (B * M).det ≠ 0 := by
  classical
  constructor
  · intro h
    obtain ⟨f, hf⟩ := (Matrix.toLin' M).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr h)
    refine ⟨LinearMap.toMatrix' f, ?_⟩
    have heq := congrArg LinearMap.toMatrix' hf
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] at heq
    rw [heq, Matrix.det_one]
    exact one_ne_zero
  · rintro ⟨B, hB⟩
    have hinj : Function.Injective (B * M).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB))
    intro x y hxy
    apply hinj
    simp only [← Matrix.mulVec_mulVec]
    rw [hxy]

theorem isOpen_injective_evaluation {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n R) :
    @IsOpen (R →ₐ[K] K) (rationalPointTopology K R)
      {p | Function.Injective (M.map p).mulVec} := by
  classical
  let _ := rationalPointTopology K R
  have hdet (B : Matrix n m K) (p : R →ₐ[K] K) :
      p ((B.map (algebraMap K R) * M).det) = (B * M.map p).det := by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, Matrix.map_mul]
    congr 2
    ext i j
    exact p.commutes (B i j)
  have heq : {p : R →ₐ[K] K | Function.Injective (M.map p).mulVec} =
      ⋃ B : Matrix n m K, {p : R →ₐ[K] K | p ((B.map (algebraMap K R) * M).det) ≠ 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hdet, injective_mulVec_iff_exists_det]
  rw [heq]
  exact isOpen_iUnion fun B => isOpen_eval_ne_zero K R _

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators
variable {F S V ι : Type*} [Field F] [CommRing S] [Algebra F S]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite ι]

theorem isOpen_regular_linear_test (ℓ : V →ₗ[F] (ι → S)) :
    @IsOpen (S →ₐ[F] F) (rationalPointTopology F S)
      {ρ | ∀ v, (∀ i, ρ (ℓ v i) = 0) → v = 0} := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let b := Module.finBasis F V
  let M : Matrix ι (Fin (Module.finrank F V)) S := fun i j => ℓ (b j) i
  let g (ρ : S →ₐ[F] F) : V →ₗ[F] (ι → F) :=
    LinearMap.pi fun i => ρ.toLinearMap.comp ((LinearMap.proj i).comp ℓ)
  have hmat (ρ : S →ₐ[F] F) : M.map ρ =
      LinearMap.toMatrix' ((g ρ).comp b.equivFun.symm.toLinearMap) := by
    ext i j
    simp [M, g, LinearMap.toMatrix'_apply, Module.Basis.equivFun_symm_apply]
    rfl
  have heq : {ρ : S →ₐ[F] F | ∀ v, (∀ i, ρ (ℓ v i) = 0) → v = 0} =
      {ρ : S →ₐ[F] F | Function.Injective (M.map ρ).mulVec} := by
    ext ρ
    simp only [Set.mem_ofPred_eq]
    rw [hmat]
    change (∀ v, (∀ i, ρ (ℓ v i) = 0) → v = 0) ↔
      Function.Injective (Matrix.toLin' (LinearMap.toMatrix'
        ((g ρ).comp b.equivFun.symm.toLinearMap)))
    rw [Matrix.toLin'_toMatrix']
    constructor
    · intro h
      have hg : Function.Injective (g ρ) := by
        intro v w hvw
        apply sub_eq_zero.mp
        apply h (v - w)
        intro i
        have hi := congrFun hvw i
        change ρ (ℓ v i) = ρ (ℓ w i) at hi
        simpa only [map_sub, Pi.sub_apply, sub_eq_zero] using hi
      exact hg.comp b.equivFun.symm.injective
    · intro h v hv
      have hg : Function.Injective (g ρ) := by
        intro x y hxy
        have hh : b.equivFun x = b.equivFun y := h (by simpa using hxy)
        exact b.equivFun.injective hh
      apply hg
      ext i
      change ρ (ℓ v i) = (g ρ) 0 i
      rw [map_zero]
      exact hv i
  rw [heq]
  exact isOpen_injective_evaluation M

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
variable {σ F S V : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]
  [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

include σ

theorem isOpen_jet_separation (ℓ : V →ₗ[F] S) (n : ℕ) (hn : 0 < n) :
    @IsOpen (S →ₐ[F] F) (rationalPointTopology F S)
      {ρ | ∀ v, ℓ v ∈ (RingHom.ker ρ)^n → v = 0} := by
  obtain ⟨D, hD⟩ := exists_regular_jet_coeffs (σ := σ) (F := F) (S := S) n hn
  have heq : {ρ : S →ₐ[F] F | ∀ v, ℓ v ∈ (RingHom.ker ρ)^n → v = 0} =
      {ρ : S →ₐ[F] F | ∀ v, (∀ d, ρ ((D.comp ℓ) v d) = 0) → v = 0} := by
    ext ρ
    simp only [Set.mem_ofPred_eq, LinearMap.comp_apply, hD]
  rw [heq]
  exact isOpen_regular_linear_test (D.comp ℓ)

end

noncomputable section
variable {ι σ F R V : Type*} [Finite ι] [Finite σ] [Field F]
  [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra F (S i)]
  [∀ i, Algebra (MvPolynomial σ F) (S i)]
  [∀ i, IsScalarTower F (MvPolynomial σ F) (S i)]
  [∀ i, Algebra.FormallyEtale (MvPolynomial σ F) (S i)]
  [∀ i, Algebra.EssFiniteType (MvPolynomial σ F) (S i)]
include σ

theorem isOpen_multipoint_jet_separation (φ : ∀ i, S i →ₐ[F] R)
    (ℓ : ∀ i, V →ₗ[F] S i) (n : ℕ) (hn : 0 < n) :
    @IsOpen (R →ₐ[F] F) (rationalPointTopology F R)
      {ρ | ∀ v, (∀ i, ℓ i v ∈ (RingHom.ker (ρ.comp (φ i)))^n) → v = 0} := by
  classical
  choose D hD using fun i =>
    exists_regular_jet_coeffs (σ := σ) (F := F) (S := S i) n hn
  let C : V →ₗ[F] ((ι × JetIndex σ n) → R) := LinearMap.pi fun j =>
    (φ j.1).toLinearMap.comp ((LinearMap.proj j.2).comp ((D j.1).comp (ℓ j.1)))
  have heq : {ρ : R →ₐ[F] F | ∀ v,
      (∀ i, ℓ i v ∈ (RingHom.ker (ρ.comp (φ i)))^n) → v = 0} =
      {ρ : R →ₐ[F] F | ∀ v, (∀ j, ρ (C v j) = 0) → v = 0} := by
    ext ρ
    simp only [Set.mem_ofPred_eq]
    apply forall_congr'
    intro v
    apply imp_congr_left
    constructor
    · intro h j
      exact (hD j.1 (ρ.comp (φ j.1)) (ℓ j.1 v)).mp (h j.1) j.2
    · intro h i
      apply (hD i (ρ.comp (φ i)) (ℓ i v)).mpr
      exact fun d => h (i, d)
  rw [heq]
  exact isOpen_regular_linear_test C

end
end MaximalSeshadri.AlgebraicJets

end



end OAI
