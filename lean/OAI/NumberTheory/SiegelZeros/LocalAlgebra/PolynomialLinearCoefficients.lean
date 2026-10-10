import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.DerivationJet

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
noncomputable section
namespace WeightedTorusJets.Geometry
open MvPolynomial
theorem mem_vars_square_iff {σ K : Type*} [CommRing K] (p : MvPolynomial σ K) :
    p ∈ idealOfVars σ K ^ 2 ↔ p.coeff 0 = 0 ∧ ∀ i, p.coeff (Finsupp.single i 1) = 0 := by
  rw [mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact ⟨h 0 (by simp), fun i => h (Finsupp.single i 1) (by simp)⟩
  · rintro ⟨h₀, h₁⟩ d hd
    have h : d.degree = 0 ∨ d.degree = 1 := by omega
    rcases h with h | h
    · exact (Finsupp.degree_eq_zero_iff d).mp h ▸ h₀
    · obtain ⟨i, rfl⟩ := (Finsupp.range_single_one (σ := σ) ▸ h :
        d ∈ Set.range (fun i : σ => Finsupp.single i 1))
      exact h₁ i

def polynomialLinearCoefficients {σ K : Type*} [CommRing K] :
    MvPolynomial σ K →ₗ[K] (σ → K) :=
  LinearMap.pi fun i => lcoeff K (Finsupp.single i 1)

@[simp] theorem polynomialLinearCoefficients_apply {σ K : Type*} [CommRing K]
    (p : MvPolynomial σ K) (i : σ) :
    polynomialLinearCoefficients p i = p.coeff (Finsupp.single i 1) := rfl

def varsCotangentCoefficients {σ K : Type*} [CommRing K] :
    (idealOfVars σ K).Cotangent →ₗ[K] (σ → K) :=
  Ideal.Cotangent.lift
    (polynomialLinearCoefficients.comp ((idealOfVars σ K).subtype.restrictScalars K))
    fun x y => by
      ext i
      exact (mem_vars_square_iff (x * y)).mp
        (by rw [pow_two]; exact Ideal.mul_mem_mul x.property y.property) |>.2 i

@[simp] theorem varsCotangentCoefficients_toCotangent {σ K : Type*} [CommRing K]
    (p : idealOfVars σ K) (i : σ) :
    varsCotangentCoefficients ((idealOfVars σ K).toCotangent p) i =
      (p : MvPolynomial σ K).coeff (Finsupp.single i 1) := rfl

theorem varsCotangentCoefficients_injective {σ K : Type*} [CommRing K] :
    Function.Injective (varsCotangentCoefficients (σ := σ) (K := K)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := (idealOfVars σ K).toCotangent_surjective x
  apply ((idealOfVars σ K).toCotangent_eq_zero p).mpr
  rw [mem_vars_square_iff]
  refine ⟨?_, fun i => congrFun hx i⟩
  exact (mem_pow_idealOfVars_iff' 1 (p : MvPolynomial σ K)).mp
    (by simpa only [pow_one] using p.property) 0 (by simp)

theorem varsCotangentCoefficients_surjective
    {σ K : Type*} [Fintype σ] [CommRing K] :
    Function.Surjective (varsCotangentCoefficients (σ := σ) (K := K)) := by
  classical
  intro v
  let p : MvPolynomial σ K := ∑ i, v i • X i
  have hp : p ∈ idealOfVars σ K := by
    apply Ideal.sum_mem
    intro i _
    exact ((idealOfVars σ K).restrictScalars K).smul_mem (v i)
      (Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨(idealOfVars σ K).toCotangent ⟨p, hp⟩, ?_⟩
  ext i
  simp [p, coeff_X, Finsupp.single_left_inj]

def varsCotangentEquiv {σ K : Type*} [Fintype σ] [CommRing K] :
    (idealOfVars σ K).Cotangent ≃ₗ[K] (σ → K) :=
  LinearEquiv.ofBijective varsCotangentCoefficients
    ⟨varsCotangentCoefficients_injective, varsCotangentCoefficients_surjective⟩

def quotientVarsCotangentMap {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) :
    (idealOfVars σ K).Cotangent →ₗ[K]
      ((idealOfVars σ K).map (Ideal.Quotient.mk J)).Cotangent :=
  Ideal.mapCotangent _ _ (Ideal.Quotient.mkₐ K J)
    (fun _ hp => Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hp)

theorem quotientVarsCotangentMap_surjective {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) :
    Function.Surjective (quotientVarsCotangentMap J) := by
  intro x
  obtain ⟨b, rfl⟩ := ((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent_surjective x
  obtain ⟨p, hp, hpb⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective).mp b.property
  refine ⟨(idealOfVars σ K).toCotangent ⟨p, hp⟩, ?_⟩
  change ((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent
    ⟨Ideal.Quotient.mk J p, _⟩ = _
  congr 1
  exact Subtype.ext hpb

theorem quotientVarsCotangentMap_injective {σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (hJ : J ≤ idealOfVars σ K ^ 2) :
    Function.Injective (quotientVarsCotangentMap J) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := (idealOfVars σ K).toCotangent_surjective x
  change ((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent
    ⟨Ideal.Quotient.mk J p, _⟩ = 0 at hx
  have hp₂ := (((idealOfVars σ K).map (Ideal.Quotient.mk J)).toCotangent_eq_zero _).mp hx
  rw [← Ideal.map_pow] at hp₂
  obtain ⟨q, hq, hqp⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective).mp hp₂
  have hd : q - p ∈ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hqp
  apply ((idealOfVars σ K).toCotangent_eq_zero p).mpr
  simpa using (idealOfVars σ K ^ 2).sub_mem hq (hJ hd)

def polynomialQuotientCotangentEquiv {σ K : Type*} [Fintype σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (hJ : J ≤ idealOfVars σ K ^ 2) :
    ((idealOfVars σ K).map (Ideal.Quotient.mk J)).Cotangent ≃ₗ[K] (σ → K) :=
  (LinearEquiv.ofBijective (quotientVarsCotangentMap J)
    ⟨quotientVarsCotangentMap_injective J hJ, quotientVarsCotangentMap_surjective J⟩).symm.trans
      varsCotangentEquiv

@[simp] theorem polynomialQuotientCotangentEquiv_map_toCotangent
    {σ K : Type*} [Fintype σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (hJ : J ≤ idealOfVars σ K ^ 2)
    (p : idealOfVars σ K) (i : σ) :
    polynomialQuotientCotangentEquiv J hJ
      (quotientVarsCotangentMap J ((idealOfVars σ K).toCotangent p)) i =
        (p : MvPolynomial σ K).coeff (Finsupp.single i 1) := by
  let e := LinearEquiv.ofBijective (quotientVarsCotangentMap J)
    ⟨quotientVarsCotangentMap_injective J hJ, quotientVarsCotangentMap_surjective J⟩
  change varsCotangentEquiv (e.symm (e ((idealOfVars σ K).toCotangent p))) i = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem rectangularIdeal_le_vars_square {σ K : Type*} [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i) :
    Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i) ≤ idealOfVars σ K ^ 2 := by
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  have hi : (X i : MvPolynomial σ K) ∈ idealOfVars σ K := Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.pow_le_pow_right (hk i) (Ideal.pow_mem_pow hi (k i))

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

noncomputable def cotangentEquivOfEqOver (R : Type*) {A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (I J : Ideal A) (h : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent := by
  subst J
  exact LinearEquiv.refl R _

@[simp] theorem cotangentEquivOfEqOver_toCotangent (R : Type*) {A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (I J : Ideal A) (h : I = J) (p : I) :
    cotangentEquivOfEqOver R I J h (I.toCotangent p) =
      J.toCotangent ⟨p, h ▸ p.property⟩ := by
  subst J
  rfl

noncomputable def rectangularAugmentationCotangentEquiv
    {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i) :
    (RingHom.ker (rectangularAugmentation (K := K) k
      (fun i => by have := hk i; omega)).toRingHom).Cotangent ≃ₗ[K] (σ → K) :=
  (cotangentEquivOfEqOver K _ _ (ker_quotientAugmentation _ _)).trans
    (polynomialQuotientCotangentEquiv _ (rectangularIdeal_le_vars_square k hk))

theorem rectangularAugmentationCotangentEquiv_toCotangent_mk
    {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i) (p : idealOfVars σ K) (i : σ) :
    rectangularAugmentationCotangentEquiv k hk
      ((RingHom.ker (rectangularAugmentation (K := K) k
        (fun j => by have := hk j; omega)).toRingHom).toCotangent
        ⟨Ideal.Quotient.mk _ p, by
          change quotientAugmentation (K := K) _ _
            (Ideal.Quotient.mk _ (p : MvPolynomial σ K)) = 0
          rw [quotientAugmentation_mk]
          exact (congrArg (fun J : Ideal (MvPolynomial σ K) =>
            (p : MvPolynomial σ K) ∈ J) ker_constantCoeff_eq_idealOfVars).mpr p.property⟩) i =
      (p : MvPolynomial σ K).coeff (Finsupp.single i 1) := by
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range fun j => X j ^ k j)
  let h₀ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) :=
    rectangularIdeal_le_ker_constantCoeff k (fun j => by have := hk j; omega)
  let n : Ideal (MvPolynomial σ K ⧸ J) := RingHom.ker (quotientAugmentation J h₀).toRingHom
  have hp₀ : constantCoeff (p : MvPolynomial σ K) = 0 :=
    (congrArg (fun I : Ideal (MvPolynomial σ K) =>
      (p : MvPolynomial σ K) ∈ I) ker_constantCoeff_eq_idealOfVars).mpr p.property
  have hqp : Ideal.Quotient.mk J (p : MvPolynomial σ K) ∈ n := by
    change quotientAugmentation J h₀ (Ideal.Quotient.mk J p) = 0
    simpa only [quotientAugmentation_mk] using hp₀
  change polynomialQuotientCotangentEquiv J (rectangularIdeal_le_vars_square k hk)
    (cotangentEquivOfEqOver K n _ (ker_quotientAugmentation J h₀)
      (n.toCotangent ⟨Ideal.Quotient.mk J p, hqp⟩)) i = _
  rw [cotangentEquivOfEqOver_toCotangent]
  exact polynomialQuotientCotangentEquiv_map_toCotangent J _ p i

theorem rectangularAugmentation_linear_representative
    {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i)
    (b : RingHom.ker (rectangularAugmentation (K := K) k
      (fun j => by have := hk j; omega)).toRingHom) :
    (b : MvPolynomial σ K ⧸ Ideal.span (Set.range fun j => (X j : MvPolynomial σ K) ^ k j)) -
      ∑ i, (rectangularAugmentationCotangentEquiv k hk
        ((RingHom.ker (rectangularAugmentation (K := K) k
          (fun j => by have := hk j; omega)).toRingHom).toCotangent b)) i •
        Ideal.Quotient.mk _ (X i) ∈
      (RingHom.ker (rectangularAugmentation (K := K) k
        (fun j => by have := hk j; omega)).toRingHom) ^ 2 := by
  classical
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range fun j => X j ^ k j)
  let N : Ideal (MvPolynomial σ K ⧸ J) := RingHom.ker
    (rectangularAugmentation (K := K) k (fun j => by have := hk j; omega)).toRingHom
  let e := rectangularAugmentationCotangentEquiv (K := K) k hk
  let c : σ → K := e (N.toCotangent b)
  let p : MvPolynomial σ K := ∑ i, c i • X i
  have hp : p ∈ idealOfVars σ K := by
    apply Ideal.sum_mem
    intro i _
    exact ((idealOfVars σ K).restrictScalars K).smul_mem (c i)
      (Ideal.subset_span ⟨i, rfl⟩)
  have hpn : Ideal.Quotient.mk J p ∈ N := by
    change quotientAugmentation (K := K) _ _ (Ideal.Quotient.mk J p) = 0
    rw [quotientAugmentation_mk]
    exact (congrArg (fun I : Ideal (MvPolynomial σ K) => p ∈ I)
      ker_constantCoeff_eq_idealOfVars).mpr hp
  have hc : e (N.toCotangent ⟨Ideal.Quotient.mk J p, hpn⟩) = c := by
    ext i
    exact (rectangularAugmentationCotangentEquiv_toCotangent_mk k hk ⟨p, hp⟩ i).trans
      (by simp [p, coeff_X, Finsupp.single_left_inj])
  have hq : Ideal.Quotient.mk J p = ∑ i, c i • Ideal.Quotient.mk J (X i) := by
    change (Ideal.Quotient.mkₐ K J) p = _
    simp only [p, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk]
  have hdiff := N.toCotangent_eq.mp (e.injective hc.symm)
  simpa only [hq] using hdiff

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

theorem taylor_sum_sub_first_order_mem {A : Type*} [CommRing A] [Algebra ℚ A]
    (D : Derivation ℚ A A) (I : Ideal A) {u : A} (hu : u ∈ I)
    {n : ℕ} (hn : 2 ≤ n) (a : A) :
    (∑ i ∈ Finset.range n, (i.factorial : ℚ)⁻¹ • (u ^ i * (D.toLinearMap ^ i) a)) -
      (a + u * D a) ∈ I ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]
  | succ n hn ih =>
      have hu' : u ^ n ∈ I ^ 2 := Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hu n)
      have hterm : (n.factorial : ℚ)⁻¹ • (u ^ n * (D.toLinearMap ^ n) a) ∈ I ^ 2 := by
        rw [Algebra.smul_def]
        exact (I ^ 2).mul_mem_left _ ((I ^ 2).mul_mem_right _ hu')
      rw [Finset.sum_range_succ]
      convert (I ^ 2).add_mem ih hterm using 1
      ring

theorem ringHom_comp_sub_first_order_mem {A : Type*} [CommRing A]
    (I : Ideal A) (f g : A →+* A)
    (hf : ∀ x ∈ I, f x - x ∈ I ^ 2) {a : A} (hg : g a - a ∈ I) :
    f (g a) - (f a + g a - a) ∈ I ^ 2 := by
  have h := hf (g a - a) hg
  rw [map_sub] at h
  convert h using 1
  ring



variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem truncatedTaylor_sub_first_order_mem (D : Derivation ℚ A A) (I : Ideal A)
    (u : A) (hDu : D u = 0) {n : ℕ} (hun : u ^ n = 0) (hn : 2 ≤ n)
    (hu : u ∈ I) (a : A) :
    truncatedTaylor D u hDu hun a - (a + u * D a) ∈ I ^ 2 := by
  rw [truncatedTaylor_apply]
  exact taylor_sum_sub_first_order_mem D I hu hn a

theorem truncatedTaylor_sub_self_mem (D : Derivation ℚ A A) (I : Ideal A)
    (u : A) (hDu : D u = 0) {n : ℕ} (hun : u ^ n = 0) (hn : 2 ≤ n)
    (hu : u ∈ I) (a : A) :
    truncatedTaylor D u hDu hun a - a ∈ I := by
  have h := (Ideal.pow_le_self (by decide : 2 ≠ 0))
    (truncatedTaylor_sub_first_order_mem D I u hDu hun hn hu a)
  convert I.add_mem h (I.mul_mem_right (D a) hu) using 1
  ring

theorem truncatedTaylor_sub_self_mem_sq (D : Derivation ℚ A A) (I : Ideal A)
    (u : A) (hDu : D u = 0) {n : ℕ} (hun : u ^ n = 0) (hn : 2 ≤ n)
    (hu : u ∈ I) (hDI : ∀ a ∈ I, D a ∈ I) {a : A} (ha : a ∈ I) :
    truncatedTaylor D u hDu hun a - a ∈ I ^ 2 := by
  have h := truncatedTaylor_sub_first_order_mem D I u hDu hun hn hu a
  have hc : u * D a ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hu (hDI a ha)
  convert (I ^ 2).add_mem h hc using 1
  ring

omit [Algebra ℚ A] in

theorem ringHom_comp3_sub_first_order_mem (I : Ideal A) (f₁ f₂ f₃ : A →+* A)
    (hf₁ : ∀ x ∈ I, f₁ x - x ∈ I ^ 2)
    (hf₂ : ∀ x ∈ I, f₂ x - x ∈ I ^ 2)
    (hg₂ : ∀ x, f₂ x - x ∈ I)
    {a e₁ e₂ e₃ : A} (hg₃ : f₃ a - a ∈ I)
    (h₁ : f₁ a - (a + e₁) ∈ I ^ 2)
    (h₂ : f₂ a - (a + e₂) ∈ I ^ 2)
    (h₃ : f₃ a - (a + e₃) ∈ I ^ 2) :
    f₁ (f₂ (f₃ a)) - (a + e₁ + e₂ + e₃) ∈ I ^ 2 := by
  have h23 : f₂ (f₃ a) - a ∈ I := by
    convert I.add_mem (hg₂ (f₃ a)) hg₃ using 1
    ring
  have hc₁ := ringHom_comp_sub_first_order_mem I f₁ (f₂.comp f₃) hf₁ h23
  have hc₂ := ringHom_comp_sub_first_order_mem I f₂ f₃ hf₂ hg₃
  have h := (I ^ 2).add_mem ((I ^ 2).add_mem ((I ^ 2).add_mem
    ((I ^ 2).add_mem hc₁ hc₂) h₁) h₂) h₃
  convert h using 1
  simp only [RingHom.comp_apply]
  ring

theorem rectangularCoefficientDerivation_mem_vars (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) {p : MvPolynomial σ A ⧸ rectangularIdeal k}
    (hp : p ∈ (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) :
    rectangularCoefficientDerivation σ k D p ∈
      (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  have he : (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k)) =
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (rectangularIdeal k)
        (MvPolynomial.X i : MvPolynomial σ A)) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [he] at hp ⊢
  apply derivation_mem_span_of_vanishes _ _ _ hp
  rintro _ ⟨i, rfl⟩
  exact rectangularCoefficientDerivation_X σ k D i

theorem rectangularTaylorAlong_sub_first_order_mem (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (hk : 2 ≤ k i)
    (p : MvPolynomial σ A ⧸ rectangularIdeal k) :
    rectangularTaylorAlong σ k D i p -
      (p + Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) *
        rectangularCoefficientDerivation σ k D p) ∈
      ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  apply truncatedTaylor_sub_first_order_mem _ _ _ _ _ hk
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

theorem rectangularTaylorAlong_sub_self_mem (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (hk : 2 ≤ k i)
    (p : MvPolynomial σ A ⧸ rectangularIdeal k) :
    rectangularTaylorAlong σ k D i p - p ∈
      (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  apply truncatedTaylor_sub_self_mem _ _ _ _ _ hk
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

theorem rectangularTaylorAlong_sub_self_mem_sq (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (hk : 2 ≤ k i)
    {p : MvPolynomial σ A ⧸ rectangularIdeal k}
    (hp : p ∈ (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) :
    rectangularTaylorAlong σ k D i p - p ∈
      ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  apply truncatedTaylor_sub_self_mem_sq _ _ _ _ _ hk _ _ hp
  · exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
  · exact fun _ => rectangularCoefficientDerivation_mem_vars σ k D

theorem rectangularTaylorComp3_sub_first_order_mem (σ : Type*) (k : σ → ℕ)
    (D₁ D₂ D₃ : Derivation ℚ A A) (i₁ i₂ i₃ : σ)
    (hk₁ : 2 ≤ k i₁) (hk₂ : 2 ≤ k i₂) (hk₃ : 2 ≤ k i₃)
    (p : MvPolynomial σ A ⧸ rectangularIdeal k) :
    rectangularTaylorAlong σ k D₁ i₁
      (rectangularTaylorAlong σ k D₂ i₂ (rectangularTaylorAlong σ k D₃ i₃ p)) -
      (p + Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₁) *
        rectangularCoefficientDerivation σ k D₁ p +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₂) *
        rectangularCoefficientDerivation σ k D₂ p +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₃) *
        rectangularCoefficientDerivation σ k D₃ p) ∈
      ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  apply ringHom_comp3_sub_first_order_mem _
    (rectangularTaylorAlong σ k D₁ i₁).toRingHom
    (rectangularTaylorAlong σ k D₂ i₂).toRingHom
    (rectangularTaylorAlong σ k D₃ i₃).toRingHom
  · exact fun _ => rectangularTaylorAlong_sub_self_mem_sq σ k D₁ i₁ hk₁
  · exact fun _ => rectangularTaylorAlong_sub_self_mem_sq σ k D₂ i₂ hk₂
  · exact rectangularTaylorAlong_sub_self_mem σ k D₂ i₂ hk₂
  · exact rectangularTaylorAlong_sub_self_mem σ k D₃ i₃ hk₃ p
  · exact rectangularTaylorAlong_sub_first_order_mem σ k D₁ i₁ hk₁ p
  · exact rectangularTaylorAlong_sub_first_order_mem σ k D₂ i₂ hk₂ p
  · exact rectangularTaylorAlong_sub_first_order_mem σ k D₃ i₃ hk₃ p

omit [Algebra ℚ A] in

theorem rectangularMap_vars_le {B : Type*} [CommRing B] (σ : Type*) (k : σ → ℕ)
    (f : A →+* B) :
    ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))).map
      (rectangularMap k f) ≤
        (MvPolynomial.idealOfVars σ B).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  rw [Ideal.map_map, MvPolynomial.idealOfVars, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨p, ⟨i, rfl⟩, rfl⟩
  change rectangularMap k f (Ideal.Quotient.mk _ (MvPolynomial.X i)) ∈ _
  rw [rectangularMap_mk, MvPolynomial.map_X]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

theorem rectangularTaylorThree_sub_first_order_mem {B : Type*} [CommRing B]
    (σ : Type*) (k : σ → ℕ) (D₁ D₂ D₃ : Derivation ℚ A A)
    (i₁ i₂ i₃ : σ) (hk₁ : 2 ≤ k i₁) (hk₂ : 2 ≤ k i₂) (hk₃ : 2 ≤ k i₃)
    (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a -
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f a)) +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₁) *
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f (D₁ a))) +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₂) *
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f (D₂ a))) +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₃) *
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f (D₃ a)))) ∈
      ((MvPolynomial.idealOfVars σ B).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  have h := rectangularTaylorComp3_sub_first_order_mem σ k D₁ D₂ D₃ i₁ i₂ i₃
    hk₁ hk₂ hk₃ (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C a))
  have hm := Ideal.mem_map_of_mem (rectangularMap k f) h
  rw [Ideal.map_pow] at hm
  have ht := pow_le_pow_left' (rectangularMap_vars_le σ k f) 2 hm
  simpa only [map_sub, map_add, map_mul, rectangularCoefficientDerivation_mk,
    coefficientDerivation_C, rectangularMap_mk, MvPolynomial.map_C,
    MvPolynomial.map_X, rectangularTaylorThree, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using ht

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {R B σ : Type*} [CommRing R] [Algebra ℚ R] [CommRing B] [Fintype σ]

omit [Fintype σ] in
theorem quotient_X_mul_C (J : Ideal (MvPolynomial σ B)) (i : σ) (a : B) :
    Ideal.Quotient.mk J (MvPolynomial.X i) * Ideal.Quotient.mk J (MvPolynomial.C a) =
      a • Ideal.Quotient.mk J (MvPolynomial.X i) := by
  rw [← map_mul, mul_comm, MvPolynomial.C_mul']
  exact (Ideal.Quotient.mkₐ B J).toLinearMap.map_smul a (MvPolynomial.X i)

omit [Fintype σ] in
theorem rectangular_augmentation_ker_eq (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    (RingHom.ker (rectangularAugmentation (K := B) k hk).toRingHom :
      Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) =
      (MvPolynomial.idealOfVars σ B).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  exact ker_quotientAugmentation (rectangularIdeal k) (rectangularIdeal_le_ker_constantCoeff k hk)

theorem rectangularTaylorThree_one_first_order (k : σ → ℕ) (hk : ∀ j, 2 ≤ k j)
    (D : σ → Derivation ℚ R R) (i : σ) (hi : ∀ j, j = i)
    (f : R →+* B) (a : R) (ha : f a = 0) :
    rectangularTaylorThree σ k (D i) 0 0 i i i f a -
      ∑ j, f (D j a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X j) ∈
      (RingHom.ker (rectangularAugmentation (K := B) k
        (fun j => by have := hk j; omega)).toRingHom :
          Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) ^ 2 := by
  classical
  have h := rectangularTaylorThree_sub_first_order_mem σ k (D i) 0 0 i i i
    (hk i) (hk i) (hk i) f a
  have hs : (∑ j, f (D j a) • Ideal.Quotient.mk (rectangularIdeal k)
      (MvPolynomial.X j : MvPolynomial σ B)) =
      f (D i a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact False.elim (hji (hi j))
    · simp
  rw [hs]
  rw [rectangular_augmentation_ker_eq]
  simpa [ha, quotient_X_mul_C] using h

theorem rectangularTaylorThree_two_first_order (k : σ → ℕ) (hk : ∀ l, 2 ≤ k l)
    (D : σ → Derivation ℚ R R) (i j : σ) (hij : i ≠ j)
    (hijcover : ∀ l, l = i ∨ l = j) (f : R →+* B) (a : R) (ha : f a = 0) :
    rectangularTaylorThree σ k (D i) (D j) 0 i j j f a -
      ∑ l, f (D l a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X l) ∈
      (RingHom.ker (rectangularAugmentation (K := B) k
        (fun l => by have := hk l; omega)).toRingHom :
          Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) ^ 2 := by
  classical
  have h := rectangularTaylorThree_sub_first_order_mem σ k (D i) (D j) 0 i j j
    (hk i) (hk j) (hk j) f a
  have hu : (Finset.univ : Finset σ) = {i, j} := by
    ext l
    simpa using hijcover l
  rw [hu, Finset.sum_pair hij]
  rw [rectangular_augmentation_ker_eq]
  simpa [ha, quotient_X_mul_C] using h

theorem rectangularTaylorThree_three_first_order (k : σ → ℕ) (hk : ∀ l, 2 ≤ k l)
    (D : σ → Derivation ℚ R R) (i j l : σ) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hcover : ∀ u, u = i ∨ u = j ∨ u = l) (f : R →+* B) (a : R) (ha : f a = 0) :
    rectangularTaylorThree σ k (D i) (D j) (D l) i j l f a -
      ∑ u, f (D u a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X u) ∈
      (RingHom.ker (rectangularAugmentation (K := B) k
        (fun u => by have := hk u; omega)).toRingHom :
          Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) ^ 2 := by
  classical
  have h := rectangularTaylorThree_sub_first_order_mem σ k (D i) (D j) (D l) i j l
    (hk i) (hk j) (hk l) f a
  have hu : (Finset.univ : Finset σ) = {i, j, l} := by
    ext u
    simpa using hcover u
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, hij, hil, hjl,
    or_self, not_false_eq_true, Finset.sum_singleton]
  rw [rectangular_augmentation_ker_eq]
  simpa [ha, quotient_X_mul_C, add_assoc] using h

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
