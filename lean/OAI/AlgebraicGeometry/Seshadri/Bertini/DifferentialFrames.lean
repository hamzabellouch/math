import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.CriticalLocus

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.FrameBertini
noncomputable section
open KaehlerDifferential

structure DifferentialFrame (K R κ : Type*) [CommRing K] [CommRing R]
    [Algebra K R] [Fintype κ] where
  coord : Ω[R⁄K] →ₗ[R] (κ → R)
  vector : κ → Ω[R⁄K]
  sum_coord : ∀ x, ∑ j, coord x j • vector j = x

theorem exists_differentialFrame (K R : Type*) [CommRing K] [CommRing R]
    [Algebra K R] [Algebra.Smooth K R] :
    ∃ n, Nonempty (DifferentialFrame K R (Fin n)) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R Ω[R⁄K]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  refine ⟨n, ⟨s, fun j => q (Pi.single j 1), ?_⟩⟩
  intro x
  have he := LinearMap.congr_fun hs x
  change q (s x) = x at he
  calc
    _ = q (∑ j, s x j • Pi.single j 1) := by simp only [map_sum, map_smul]
    _ = q (s x) := by rw [← pi_eq_sum_univ']
    _ = x := he

variable {K R A ι κ : Type*} [CommRing K] [CommRing R] [CommRing A]
  [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
  [Fintype ι] [Fintype κ]

lemma differential_expansion (b : DifferentialFrame K R κ) (x : R) :
    D K A (algebraMap R A x) =
      ∑ j, algebraMap R A (b.coord (D K R x) j) •
        KaehlerDifferential.map K K R A (b.vector j) := by
  have h := congrArg (KaehlerDifferential.map K K R A) (b.sum_coord (D K R x))
  simpa only [map_sum, map_smul, IsScalarTower.algebraMap_smul,
    KaehlerDifferential.map_D] using h.symm

lemma critical_of_coordinates (b : DifferentialFrame K R κ)
    (v : ι → R) (a : ι → A)
    (h : ∀ j, ∑ i, a i * algebraMap R A (b.coord (D K R (v i)) j) = 0) :
    ∑ i, a i • D K A (algebraMap R A (v i)) = 0 := by
  simp_rw [differential_expansion b, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h, zero_smul, Finset.sum_const_zero]

end
noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def universalSection (v : ι → R) : MvPolynomial (Option ι) R :=
  X none + ∑ i, X (some i) * C (v i)

def universalGradient (b : DifferentialFrame K R κ) (v : ι → R)
    (j : κ) : MvPolynomial (Option ι) R :=
  ∑ i, X (some i) * C (b.coord (D K R (v i)) j)

def criticalIdeal (b : DifferentialFrame K R κ) (v : ι → R) :
    Ideal (MvPolynomial (Option ι) R) :=
  Ideal.span (insert (universalSection v) (Set.range (universalGradient b v)))

theorem universal_critical_polynomial [Algebra.FiniteType K R]
    (b : DifferentialFrame K R κ) (v : ι → R) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧
      IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial (Option ι) R)
          (MvPolynomial (Option ι) R ⧸ criticalIdeal b v) (X i)) p) := by
  let T := MvPolynomial (Option ι) R
  let A := T ⧸ criticalIdeal b v
  let a : Option ι → A := fun i => algebraMap T A (X i)
  have hC (r : R) : algebraMap T A (C r) = algebraMap R A r := rfl
  have hzero : a none + ∑ i, a (some i) * algebraMap R A (v i) = 0 := by
    have he : algebraMap T A (universalSection v) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    simpa only [universalSection, map_add, map_sum, map_mul,
      hC, a] using he
  have hgrad : ∀ j, ∑ i, a (some i) *
      algebraMap R A (b.coord (D K R (v i)) j) = 0 := by
    intro j
    have he : algebraMap T A (universalGradient b v j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j)))
    simpa only [universalGradient, map_sum, map_mul,
      hC, a] using he
  exact critical_incidence_polynomial (fun i => algebraMap R A (v i)) a hzero
    (critical_of_coordinates b v (fun i => a (some i)) hgrad)

end

noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def specializedSection (v : ι → R) (t : Option ι → K) : R :=
  algebraMap K R (t none) + ∑ i, algebraMap K R (t (some i)) * v i

def specializedGradient (b : DifferentialFrame K R κ) (v : ι → R)
    (t : Option ι → K) (j : κ) : R :=
  ∑ i, algebraMap K R (t (some i)) * b.coord (D K R (v i)) j

omit [CharZero K] in

theorem critical_specialization_eq_top
    (b : DifferentialFrame K R κ) (v : ι → R) (p : MvPolynomial (Option ι) K)
    (hp : IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial (Option ι) R)
          (MvPolynomial (Option ι) R ⧸ criticalIdeal b v) (X i)) p))
    (t : Option ι → K) (ht : MvPolynomial.aeval t p ≠ 0) :
    Ideal.span (insert (specializedSection v t)
      (Set.range (specializedGradient b v t))) = ⊤ := by
  classical
  by_contra hne
  let J := Ideal.span (insert (specializedSection v t)
    (Set.range (specializedGradient b v t)))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
  let : M.IsMaximal := hM
  let B := R ⧸ M
  let T := MvPolynomial (Option ι) R
  let A := T ⧸ criticalIdeal b v
  let φ : T →ₐ[K] B := (MvPolynomial.aeval (fun i => algebraMap K B (t i))).restrictScalars K
  have hφX (i : Option ι) : φ (X i) = algebraMap K B (t i) := MvPolynomial.aeval_X _ _
  have hφC (r : R) : φ (C r) = algebraMap R B r := MvPolynomial.aeval_C _ _
  have hφs : φ (universalSection v) = 0 := by
    have he : algebraMap R B (specializedSection v t) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJM (Ideal.subset_span (Set.mem_insert _ _)))
    simpa only [universalSection, specializedSection, map_add, map_sum, map_mul, hφX, hφC,
      IsScalarTower.algebraMap_apply K R B] using he
  have hφg (j : κ) : φ (universalGradient b v j) = 0 := by
    have he : algebraMap R B (specializedGradient b v t j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (hJM (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))))
    simpa only [universalGradient, specializedGradient, map_sum, map_mul, hφX, hφC,
      IsScalarTower.algebraMap_apply K R B] using he
  have hker : criticalIdeal b v ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro x (rfl | ⟨j, rfl⟩)
    · exact hφs
    · exact hφg j
  let ψ : A →ₐ[K] B := Ideal.Quotient.liftₐ (criticalIdeal b v) φ (fun x hx => hker hx)
  have hspec : IsNilpotent (algebraMap K B (MvPolynomial.aeval t p)) := by
    have h := hp.map ψ
    have hψ (i : Option ι) : ψ (algebraMap T A (X i)) = algebraMap K B (t i) := by
      change φ (X i) = algebraMap K B (t i)
      exact hφX i
    rw [MvPolynomial.comp_aeval_apply, show (fun i =>
      ψ (algebraMap T A (X i))) = (fun i => algebraMap K B (t i)) from funext hψ] at h
    have he := MvPolynomial.comp_aeval_apply t (Algebra.ofId K B) p
    exact he ▸ h
  exact hspec.not_isUnit ((isUnit_iff_ne_zero.mpr ht).map (algebraMap K B))

end

noncomputable section
open KaehlerDifferential TensorProduct Algebra
open MaximalSeshadri.Bertini
                                                                               
theorem formallySmooth_principal_of_gradient
    {K S ι : Type*} [CommRing K] [CommRing S] [Algebra K S] [Fintype ι]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (b : DifferentialFrame K P.Ring ι) (f : P.Ring)
    (hf : Ideal.span ({f} : Set P.Ring) = P.ker)
    (hgrad : Ideal.span (Set.range (fun i =>
      algebraMap P.Ring S (b.coord (D K P.Ring f) i))) = ⊤) :
    Algebra.FormallySmooth K S := by
  have hmem : (1 : S) ∈ Ideal.span (Set.range (fun i =>
      algebraMap P.Ring S (b.coord (D K P.Ring f) i))) := hgrad ▸ (show (1 : S) ∈ (⊤ : Ideal S) from trivial)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  let l : Ω[P.Ring⁄K] →ₗ[P.Ring] S := ∑ i, c i •
    ((Algebra.linearMap P.Ring S).comp ((LinearMap.proj i).comp b.coord))
  apply formallySmooth_principal_of_derivation P f hf (l.compDer (D K P.Ring))
  change l (D K P.Ring f) = 1
  simpa [l, LinearMap.comp_apply, LinearMap.proj_apply] using hc

theorem formallySmooth_quotient_of_gradient
    {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    [Algebra.FormallySmooth K R] (b : DifferentialFrame K R ι) (f : R)
    (hgrad : Ideal.span (insert f (Set.range (fun i => b.coord (D K R f) i))) = ⊤) :
    Algebra.FormallySmooth K (R ⧸ Ideal.span ({f} : Set R)) := by
  let I := Ideal.span ({f} : Set R)
  let S := R ⧸ I
  let P : Algebra.Extension K S := Algebra.Extension.ofSurjective
    (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mk_surjective)
  let : Algebra.FormallySmooth K P.Ring := ‹Algebra.FormallySmooth K R›
  have hker : Ideal.span ({f} : Set P.Ring) = P.ker := (Ideal.mk_ker).symm
  have hgrad' : Ideal.span (Set.range (fun i =>
      algebraMap R S (b.coord (D K R f) i))) = ⊤ := by
    have h := congrArg (Ideal.map (Ideal.Quotient.mk I)) hgrad
    have hf : Ideal.Quotient.mk I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    simpa only [S, Ideal.Quotient.algebraMap_eq, Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, Function.comp_def, hf,
      Ideal.span_insert_zero, Ideal.map_top] using h
  exact formallySmooth_principal_of_gradient P b f hker hgrad'

end

noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

omit [CharZero K] in
lemma specializedGradient_eq (b : DifferentialFrame K R κ) (v : ι → R)
    (t : Option ι → K) (j : κ) :
    b.coord (D K R (specializedSection v t)) j = specializedGradient b v t j := by
  simp only [specializedSection, specializedGradient, map_add, map_sum,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    zero_add, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]

theorem affine_bertini_smooth [Algebra.Smooth K R]
    (b : DifferentialFrame K R κ) (v : ι → R) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧
      ∀ t : Option ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨p, hp, hcrit⟩ := universal_critical_polynomial b v
  refine ⟨p, hp, fun t ht => ?_⟩
  have hgrad := critical_specialization_eq_top b v p hcrit t ht
  rw [show specializedGradient b v t = (fun j =>
    b.coord (D K R (specializedSection v t)) j) from
      funext (fun j => (specializedGradient_eq b v t j).symm)] at hgrad
  let : Algebra.FormallySmooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    formallySmooth_quotient_of_gradient b (specializedSection v t) hgrad
  let : Algebra.FinitePresentation K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

end

noncomputable section
open MvPolynomial
                                                                                
theorem affine_bertini {K R ι : Type*} [Field K] [CharZero K] [CommRing R]
    [Algebra K R] [Fintype ι] [Algebra.Smooth K R] (v : ι → R) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧
      ∀ t : Option ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨n, ⟨b⟩⟩ := exists_differentialFrame K R
  exact affine_bertini_smooth b v
end
end MaximalSeshadri.FrameBertini

end
end

end OAI
