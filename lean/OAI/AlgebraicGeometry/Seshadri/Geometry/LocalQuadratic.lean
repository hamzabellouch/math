import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.PolynomialJets

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial IsLocalRing

attribute [local instance] RingHom.ker_isPrime

lemma pair_square_eq (A : Type*) [CommRing A] (x y : A) :
    (Ideal.span ({x,y} : Set A)) ^ 2 = Ideal.span ({x^2,x*y,y^2} : Set A) := by
  rw [pow_two, Ideal.span_pair_mul_span_pair]
  congr 1
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, pow_two, mul_comm y x]
  tauto

lemma mem_pair_square {A : Type*} [CommRing A] (x y f : A)
    (hf : f ∈ (Ideal.span ({x,y} : Set A)) ^ 2) :
    ∃ a b c : A, f = a*x^2 + b*x*y + c*y^2 := by
  rw [pair_square_eq, Ideal.mem_span_insert] at hf
  obtain ⟨a, g, hg, hfg⟩ := hf
  obtain ⟨b,c,hg⟩ := Ideal.mem_span_pair.mp hg
  refine ⟨a,b,c,?_⟩
  rw [← hg] at hfg
  simpa only [mul_add, add_assoc, mul_assoc] using hfg

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [Algebra (MvPolynomial (Fin 2) K) A] [IsScalarTower K (MvPolynomial (Fin 2) K) A]

theorem etale_coordinates_generate_local [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0) :
    maximalIdeal (Localization.AtPrime (RingHom.ker ρ)) = Ideal.span
      (Set.range fun i : Fin 2 => algebraMap A (Localization.AtPrime (RingHom.ker ρ))
        (algebraMap (MvPolynomial (Fin 2) K) A (X i))) := by
  let R := MvPolynomial (Fin 2) K
  let q := RingHom.ker ρ
  let p := q.under R
  have hp : p = idealOfVars (Fin 2) K := by
    rw [MaximalSeshadri.AlgebraicJets.idealOfVars_eq_ker_constantCoeff]
    change RingHom.ker (ρ.toRingHom.comp (algebraMap R A)) = _
    have heq : ρ.toRingHom.comp (algebraMap R A) = constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, constantCoeff_C]
        change ρ (algebraMap R A (algebraMap K R c)) = c
        rw [← IsScalarTower.algebraMap_apply K R A]
        exact ρ.commutes c
      · intro i
        simp only [RingHom.comp_apply, constantCoeff_X]
        change ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0
        exact hρ i
    rw [heq]
  let Rp := Localization.AtPrime p
  let Aq := Localization.AtPrime q
  let : Algebra Rp Aq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Aq := Algebra.EssFiniteType.of_comp R Rp Aq
  let : Algebra.FormallyEtale R Aq := Algebra.FormallyEtale.comp R A Aq
  let : Algebra.FormallyEtale Rp Aq := Algebra.FormallyEtale.of_restrictScalars (R := R)
  have hmax : (maximalIdeal Rp).map (algebraMap Rp Aq) = maximalIdeal Aq :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← hmax, ← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq R Rp Aq, hp, idealOfVars, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1

theorem etale_quadratic_local [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0)
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) :
    let B := Localization.AtPrime (RingHom.ker ρ)
    let x := algebraMap A B (algebraMap (MvPolynomial (Fin 2) K) A (X 0))
    let y := algebraMap A B (algebraMap (MvPolynomial (Fin 2) K) A (X 1))
    ∃ a b c : B, algebraMap A B f = a*x^2 + b*x*y + c*y^2 := by
  dsimp only
  apply mem_pair_square
  have hm := etale_coordinates_generate_local ρ hρ
  have hr (g : Fin 2 → Localization.AtPrime (RingHom.ker ρ)) :
      Set.range g = {g 0,g 1} := by
    ext t
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hr] at hm
  rw [← hm, ← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ρ), ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hf

theorem etale_quadratic_neighborhood [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0)
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) :
    let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
    let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
    ∃ d a b c : A, ρ d ≠ 0 ∧ d*f = a*x^2 + b*x*y + c*y^2 := by
  dsimp only
  let B := Localization.AtPrime (RingHom.ker ρ)
  let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
  have hmem : algebraMap A B f ∈
      ((Ideal.span ({x,y} : Set A))^2).map (algebraMap A B) := by
    rw [Ideal.map_pow, Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
    rw [pair_square_eq, Ideal.mem_span_insert]
    obtain ⟨a,b,c,heq⟩ := etale_quadratic_local ρ hρ f hf
    refine ⟨a, b*(algebraMap A B x * algebraMap A B y) +
      c*(algebraMap A B y)^2, Ideal.mem_span_pair.mpr ⟨b,c,rfl⟩, ?_⟩
    simpa only [add_assoc, mul_assoc] using heq
  obtain ⟨d, hd, hdf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (RingHom.ker ρ).primeCompl B _ f).mp hmem
  obtain ⟨a,b,c,heq⟩ := mem_pair_square x y _ hdf
  exact ⟨d,a,b,c,hd,heq⟩

theorem etale_linear_neighborhood [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0)
    (f : A) (hf : ρ f = 0) :
    let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
    let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
    ∃ d a b : A, ρ d ≠ 0 ∧ d*f = a*x + b*y := by
  let B := Localization.AtPrime (RingHom.ker ρ)
  let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
  have heq : (Ideal.span ({x,y} : Set A)).map (algebraMap A B) = maximalIdeal B := by
    rw [etale_coordinates_generate_local ρ hρ, Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
    congr 1
    ext t
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hmem : algebraMap A B f ∈ (Ideal.span ({x,y} : Set A)).map (algebraMap A B) := by
    rw [heq, ← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ρ)]
    exact Ideal.mem_map_of_mem _ hf
  obtain ⟨d,hd,hdf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (RingHom.ker ρ).primeCompl B _ f).mp hmem
  obtain ⟨a,b,heq⟩ := Ideal.mem_span_pair.mp hdf
  exact ⟨d,a,b,hd,heq.symm⟩

end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
