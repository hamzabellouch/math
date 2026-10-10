import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialLinearCoefficients
import OAI.NumberTheory.SiegelZeros.Structure.InvariantJetMonomial

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets.Geometry

theorem finrank_polynomialBox (K : Type*) [Field K] (N : ℕ) :
    Module.finrank K (polynomialBox K N) = N ^ 4 := by
  let f : (Fin 4 → Fin N) → (Fin 4 →₀ ℕ) :=
    fun n => Finsupp.equivFunOnFinite.symm fun i => (n i : ℕ)
  have hf : Function.Injective f := by
    intro n m h
    funext i
    apply Fin.ext
    exact congrArg (fun g : Fin 4 →₀ ℕ => g i) h
  have h := (MvPolynomial.basisMonomials (Fin 4) K).linearIndependent.comp f hf
  convert! finrank_span_eq_card h using 1
  simp

theorem invariantJet_mem_polynomialBox {K : Type*} [Field K] {N : ℕ}
    (c : Fin 3 → Fin 4 → K) (a : Fin 3 → ℕ)
    {F : MvPolynomial (Fin 4) K} (hF : F ∈ polynomialBox K N) :
    invariantJet c a F ∈ polynomialBox K N := by
  let L : Module.End K (MvPolynomial (Fin 4) K) :=
    (invariantDerivation (c 0)).toLinearMap ^ a 0 *
      (invariantDerivation (c 1)).toLinearMap ^ a 1 *
      (invariantDerivation (c 2)).toLinearMap ^ a 2
  have hL (g : MvPolynomial (Fin 4) K) : L g = invariantJet c a g := by
    simp only [L, Module.End.mul_apply, Module.End.pow_apply, Derivation.coeFn_coe,
      invariantJet]
  rw [← hL]
  induction hF using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, rfl⟩ := hg
    rw [hL, invariantJet_monomial]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  | zero => simpa only [map_zero] using (polynomialBox K N).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul r f _ hf => simpa only [map_smul] using Submodule.smul_mem _ r hf

theorem invariantDerivation_mem_polynomialBox {K : Type*} [Field K] {N : ℕ}
    (c : Fin 4 → K) {F : MvPolynomial (Fin 4) K} (hF : F ∈ polynomialBox K N) :
    invariantDerivation c F ∈ polynomialBox K N := by
  simpa [invariantJet] using invariantJet_mem_polynomialBox ![c, 0, 0] ![1, 0, 0] hF



theorem surjective_of_rectangular_first_order
    {R σ : Type*} [CommRing R] [Algebra ℚ R] [Fintype σ]
    (m : Ideal R) [m.IsMaximal] (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i)
    (D : σ → Derivation ℚ R R)
    (hD : LinearIndependent (R ⧸ m) (fun i => derivationCotangentResidue (D i) m))
    (φ : R →+* (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k))
    (hres : ∀ a, rectangularAugmentation k (fun i => by have := hk i; omega) (φ a) =
      Ideal.Quotient.mk m a)
    (hfirst : ∀ x : m, φ x -
        ∑ i, Ideal.Quotient.mk m (D i x) •
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
      (RingHom.ker (rectangularAugmentation (K := R ⧸ m) k
        (fun i => by have := hk i; omega)).toRingHom) ^ 2) :
    Function.Surjective φ := by
  classical
  let := Ideal.Quotient.field m
  let ε : (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k) →ₐ[R ⧸ m] R ⧸ m :=
    rectangularAugmentation (K := R ⧸ m) k (fun i => by have := hk i; omega)
  let N := RingHom.ker ε.toRingHom
  have hres' (a : R) : ε (φ a) = Ideal.Quotient.mk m a := hres a
  have hφ : Function.Surjective φ := by
    apply surjective_of_nilpotent_ideal_lifts φ N
      (isNilpotent_ker_rectangularAugmentation k (fun i => by have := hk i; omega))
    · intro z
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ε z)
      refine ⟨a, ?_⟩
      change ε (z - φ a) = 0
      rw [map_sub, hres', ha, sub_self]
    · intro z hz
      let zN : N := ⟨z, hz⟩
      let c : σ → R ⧸ m := rectangularAugmentationCotangentEquiv k hk (N.toCotangent zN)
      obtain ⟨x, hx⟩ := exists_ideal_element_with_derivatives m D hD c
      refine ⟨x, ?_, ?_⟩
      · change ε (φ x) = 0
        rw [hres']
        exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property
      · have hlinear := rectangularAugmentation_linear_representative k hk zN
        have hfirstx := hfirst x
        simp_rw [hx] at hfirstx
        change z - ∑ i, c i • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
          N ^ 2 at hlinear
        change φ x - ∑ i, c i • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
          N ^ 2 at hfirstx
        convert (N ^ 2).sub_mem hlinear hfirstx using 1 <;> abel
  exact hφ



abbrev idealPowLayer {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :=
  ↥(I ^ n) ⧸ (I • ⊤ : Submodule A ↥(I ^ n))

theorem idealPowLayer_kernel {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :
    (LinearMap.ker (Submodule.mkQ (I • ⊤ : Submodule A ↥(I ^ n)))).map
      (I ^ n).subtype = I ^ (n + 1) := by
  rw [Submodule.ker_mkQ, Submodule.map_smul'', Submodule.map_subtype_top,
    Ideal.smul_eq_mul, pow_succ']


def mapIdealPowLayer {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (I : Ideal A) (J : Ideal B) (hf : I ≤ J.comap f) (n : ℕ) :
    idealPowLayer I n →ₗ[R] idealPowLayer J n := by
  have hpow : I ^ n ≤ (J ^ n).comap f :=
    (pow_le_pow_left' hf n).trans (Ideal.le_comap_pow f n)
  refine Submodule.mapQ ((I • ⊤ : Submodule A ↥(I ^ n)).restrictScalars R)
    ((J • ⊤ : Submodule B ↥(J ^ n)).restrictScalars R) ?_ ?_
  · exact f.toLinearMap.restrict (p := (I ^ n).restrictScalars R)
      (q := (J ^ n).restrictScalars R) hpow
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx ?_ (fun _ _ ↦ add_mem)
    rintro a ha ⟨b, hb⟩ _
    change (⟨f (a * b), hpow ((I ^ n).mul_mem_left a hb)⟩ : ↥(J ^ n)) ∈
      J • (⊤ : Submodule B ↥(J ^ n))
    convert!
      (Submodule.smul_mem_smul (M := ↥(J ^ n)) (r := f a) (n := ⟨f b, hpow hb⟩)
        (hf ha) Submodule.mem_top) using 1
    ext
    exact map_mul f a b

def mapIdealPowLayerSemilinear {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B) (hf : I ≤ J.comap f) (n : ℕ) :
    idealPowLayer I n →ₛₗ[Ideal.quotientMap J f hf] idealPowLayer J n := by
  let : Algebra A B := f.toAlgebra
  let g := mapIdealPowLayer (Algebra.ofId A B) I J hf n
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        change g (a • x) = f a • g x
        exact g.map_smul a x }



theorem length_idealPow_step {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :
    Module.length A ↥(I ^ n) =
      Module.length A ↥(I ^ (n + 1)) + Module.length A (idealPowLayer I n) := by
  let P := (I • ⊤ : Submodule A ↥(I ^ n))
  have hP : P.map (I ^ n).subtype = I ^ (n + 1) := by
    simpa only [Submodule.ker_mkQ] using idealPowLayer_kernel I n
  have hlen : Module.length A P = Module.length A ↥(I ^ (n + 1)) := by
    exact (((I ^ n).equivSubtypeMap P).trans (LinearEquiv.ofEq _ _ hP)).length_eq
  rw [Module.length_eq_add_of_exact P.subtype P.mkQ (Submodule.subtype_injective P)
    (Submodule.mkQ_surjective P) (LinearMap.exact_subtype_mkQ P), hlen]

theorem length_eq_sum_idealPowLayer {A : Type*} [CommRing A]
    (I : Ideal A) (N : ℕ) (hN : I ^ N = ⊥) :
    Module.length A A = ∑ n ∈ Finset.range N, Module.length A (idealPowLayer I n) := by
  have hsum : ∀ j : ℕ, Module.length A A =
      Module.length A ↥(I ^ j) + ∑ n ∈ Finset.range j, Module.length A (idealPowLayer I n) := by
    intro j
    induction j with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        have htop : I ^ 0 = ⊤ := by simp
        exact (Module.length_top (R := A) (M := A)).symm.trans
          (LinearEquiv.ofEq _ _ htop).length_eq.symm
    | succ j ih =>
        rw [Finset.sum_range_succ]
        calc
          Module.length A A = Module.length A ↥(I ^ j) +
            ∑ n ∈ Finset.range j, Module.length A (idealPowLayer I n) := ih
          _ = Module.length A ↥(I ^ (j + 1)) + Module.length A (idealPowLayer I j) +
            ∑ n ∈ Finset.range j, Module.length A (idealPowLayer I n) := by
              rw [length_idealPow_step I j]
          _ = _ := by ac_rfl
  have hzero : Module.length A ↥(I ^ N) = 0 :=
    (LinearEquiv.ofEq _ _ hN).length_eq.trans (Module.length_bot (R := A) (M := A))
  simpa only [hzero, zero_add] using hsum N

theorem length_idealPowLayer_eq_finrank {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [I.IsMaximal] (n : ℕ) :
    Module.length A (idealPowLayer I n) =
      (Module.finrank (A ⧸ I) (idealPowLayer I n) : ℕ∞) := by
  let := Ideal.Quotient.field I
  let : Module.Finite (A ⧸ I) (idealPowLayer I n) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ I) (idealPowLayer I n)
  rw [Module.length_eq_of_surjective (R := A ⧸ I) (S := A)
    (Ideal.Quotient.mk_surjective)]
  exact Module.length_eq_finrank (A ⧸ I) (idealPowLayer I n)

theorem length_eq_sum_finrank_idealPowLayer {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [I.IsMaximal] (N : ℕ) (hN : I ^ N = ⊥) :
    Module.length A A =
      ∑ n ∈ Finset.range N, (Module.finrank (A ⧸ I) (idealPowLayer I n) : ℕ∞) := by
  rw [length_eq_sum_idealPowLayer I N hN]
  apply Finset.sum_congr rfl
  intro n hn
  exact length_idealPowLayer_eq_finrank I n



theorem quotient_length_eq_sum_finrank_idealPowLayer
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m)
    (N : ℕ) (hN : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥) :
    Module.length R (R ⧸ J) =
      ∑ n ∈ Finset.range N,
        let := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n)
          (DoubleQuot.quotQuotEquivQuotOfLE hJm).symm.toRingHom
        (Module.finrank (R ⧸ m) (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) : ℕ∞) := by
  let I := m.map (Ideal.Quotient.mk J)
  let : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : I.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hJm)
  calc
    Module.length R (R ⧸ J) = Module.length (R ⧸ J) (R ⧸ J) :=
      Module.length_eq_of_surjective (R := R ⧸ J) (M := R ⧸ J) (S := R)
        Ideal.Quotient.mk_surjective
    _ = ∑ n ∈ Finset.range N,
        (Module.finrank ((R ⧸ J) ⧸ I) (idealPowLayer I n) : ℕ∞) :=
      length_eq_sum_finrank_idealPowLayer I N hN
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
      let := Module.compHom (idealPowLayer I n) e.symm.toRingHom
      have hdim : Module.finrank (R ⧸ m) (idealPowLayer I n) =
          Module.finrank ((R ⧸ J) ⧸ I) (idealPowLayer I n) :=
        congrArg Cardinal.toNat (rank_eq_of_equiv_equiv e.symm
          (AddEquiv.refl (idealPowLayer I n)) e.symm.bijective (fun _ _ => rfl))
      exact congrArg (fun z : ℕ => (z : ℕ∞)) hdim.symm




theorem augmentation_length_eq_sum_finrank_idealPowLayer
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (q : A →ₐ[K] K) (N : ℕ) (hN : (RingHom.ker q) ^ N = ⊥) :
    Module.length A A =
      ∑ n ∈ Finset.range N, (Module.finrank K (idealPowLayer (RingHom.ker q) n) : ℕ∞) := by
  have hnil : IsNilpotent (RingHom.ker q) := ⟨N, by simpa only [Ideal.zero_eq_bot] using hN⟩
  let := isLocalRing_of_nilpotent_augmentation q hnil
  rw [length_eq_sum_idealPowLayer (RingHom.ker q) N hN]
  apply Finset.sum_congr rfl
  intro n hn
  exact local_module_length_eq_finrank (residue_surjective_of_nilpotent_augmentation q hnil)



noncomputable def mapIdealPowLayerQuotientAugmentation {R B : Type*}
    [CommRing R] [CommRing B] (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (n : ℕ) :
    let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
    letI := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) e.symm.toRingHom
    idealPowLayer (m.map (Ideal.Quotient.mk J)) n →ₗ[R ⧸ m]
      idealPowLayer (RingHom.ker q) n := by
  let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
  letI := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) e.symm.toRingHom
  have hf : m.map (Ideal.Quotient.mk J) ≤ (RingHom.ker q).comap f := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).mp ha
    change q (f (Ideal.Quotient.mk J r)) = 0
    exact (RingHom.congr_fun hcomp r).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hq : Function.Surjective q := fun c => ⟨algebraMap (R ⧸ m) B c, q.commutes c⟩
  have hscalar (c : R ⧸ m) :
      Ideal.quotientMap (RingHom.ker q) f hf (e.symm c) =
        algebraMap (R ⧸ m) (B ⧸ RingHom.ker q) c := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    change Ideal.quotientMap (RingHom.ker q) f hf
      ((DoubleQuot.quotQuotEquivQuotOfLE hJm).symm (Ideal.Quotient.mk m r)) = _
    rw [DoubleQuot.quotQuotEquivQuotOfLE_symm_mk]
    apply (q.toRingHom.quotientKerEquivOfSurjective hq).injective
    change q (f (Ideal.Quotient.mk J r)) =
      q (algebraMap (R ⧸ m) B (Ideal.Quotient.mk m r))
    rw [q.commutes]
    exact RingHom.congr_fun hcomp r
  let g := mapIdealPowLayerSemilinear f (m.map (Ideal.Quotient.mk J)) (RingHom.ker q) hf n
  refine { toFun := g, map_add' := g.map_add, map_smul' := ?_ }
  intro c x
  change g (e.symm c • x) = c • g x
  rw [g.map_smulₛₗ, hscalar, algebraMap_smul]

theorem quotientAugmentation_comap_ker_eq {R B : Type*} [CommRing R] [CommRing B]
    (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m) :
    (RingHom.ker q).comap f = m.map (Ideal.Quotient.mk J) := by
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJm]
  change RingHom.ker ((q.toRingHom.comp f).comp (Ideal.Quotient.mk J)) = m
  rw [hcomp, Ideal.mk_ker]

@[simp]
theorem mapIdealPowLayerQuotientAugmentation_mk {R B : Type*}
    [CommRing R] [CommRing B] (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (n : ℕ) (x : ↥((m.map (Ideal.Quotient.mk J)) ^ n)) :
    mapIdealPowLayerQuotientAugmentation J m hJm f q hcomp n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f x, (Ideal.le_comap_pow f n)
          ((pow_le_pow_left' (quotientAugmentation_comap_ker_eq J m hJm f q hcomp).ge n)
            x.property)⟩ : ↥((RingHom.ker q) ^ n)) := rfl

theorem mapIdealPowLayerQuotientAugmentation_surjective {R B : Type*}
    [CommRing R] [CommRing B] (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (mapIdealPowLayerQuotientAugmentation J m hJm f q hcomp n) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmap : ((m.map (Ideal.Quotient.mk J)) ^ n).map f = (RingHom.ker q) ^ n := by
    rw [Ideal.map_pow, ← quotientAugmentation_comap_ker_eq J m hJm f q hcomp,
      Ideal.map_comap_of_surjective f hf]
  have hy : (y : B) ∈ ((m.map (Ideal.Quotient.mk J)) ^ n).map f := by
    rw [hmap]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hy
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
  rw [mapIdealPowLayerQuotientAugmentation_mk]
  congr 1
  exact Subtype.ext hxy


theorem finite_quotientIdealPowLayer_over_residue
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m) (n : ℕ) :
    let := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n)
      (DoubleQuot.quotQuotEquivQuotOfLE hJm).symm.toRingHom
    Module.Finite (R ⧸ m) (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) := by
  let I := m.map (Ideal.Quotient.mk J)
  let : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : I.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hJm)
  let := Ideal.Quotient.field m
  let := Ideal.Quotient.field I
  let : Module.Finite ((R ⧸ J) ⧸ I) (idealPowLayer I n) :=
    Module.Finite.of_restrictScalars_finite (R ⧸ J) ((R ⧸ J) ⧸ I) (idealPowLayer I n)
  let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
  let := Module.compHom (idealPowLayer I n) e.symm.toRingHom
  apply Module.rank_lt_aleph0_iff.mp
  rw [rank_eq_of_equiv_equiv e.symm (AddEquiv.refl (idealPowLayer I n))
    e.symm.bijective (fun _ _ => rfl)]
  exact Module.rank_lt_aleph0 _ _

theorem augmentation_length_le_quotient_length
    {R B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m)
    [Algebra (R ⧸ m) B] [Module.Finite (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (hf : Function.Surjective f)
    (N : ℕ) (hN : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥) :
    Module.length B B ≤ Module.length R (R ⧸ J) := by
  let := Ideal.Quotient.field m
  have htarget : (RingHom.ker q) ^ N = ⊥ := by
    rw [← Ideal.map_comap_of_surjective f hf (RingHom.ker q),
      quotientAugmentation_comap_ker_eq J m hJm f q hcomp, ← Ideal.map_pow, hN, Ideal.map_bot]
  rw [augmentation_length_eq_sum_finrank_idealPowLayer q N htarget,
    quotient_length_eq_sum_finrank_idealPowLayer J m hJm N hN]
  apply Finset.sum_le_sum
  intro n hn
  let := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n)
    (DoubleQuot.quotQuotEquivQuotOfLE hJm).symm.toRingHom
  let := finite_quotientIdealPowLayer_over_residue J m hJm n
  change (Module.finrank (R ⧸ m) (idealPowLayer (RingHom.ker q) n) : ℕ∞) ≤
    (Module.finrank (R ⧸ m) (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) : ℕ∞)
  exact_mod_cast LinearMap.finrank_le_finrank_of_surjective
    (mapIdealPowLayerQuotientAugmentation_surjective J m hJm f q hcomp hf n)

theorem augmentation_finrank_le_quotient_length
    {R B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m)
    [Algebra (R ⧸ m) B] [Module.Finite (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (hf : Function.Surjective f)
    (N : ℕ) (hN : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥) :
    (Module.finrank (R ⧸ m) B : ℕ∞) ≤ Module.length R (R ⧸ J) := by
  let := Ideal.Quotient.field m
  have htarget : (RingHom.ker q) ^ N = ⊥ := by
    rw [← Ideal.map_comap_of_surjective f hf (RingHom.ker q),
      quotientAugmentation_comap_ker_eq J m hJm f q hcomp, ← Ideal.map_pow, hN, Ideal.map_bot]
  have hnil : IsNilpotent (RingHom.ker q) := ⟨N, by simpa only [Ideal.zero_eq_bot] using htarget⟩
  rw [← length_eq_finrank_of_nilpotent_augmentation q hnil]
  exact augmentation_length_le_quotient_length J m hJm f q hcomp hf N hN


theorem local_graded_length_lower_of_rectangular_first_order
    {R σ : Type*} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] [Fintype σ]
    (m J : Ideal R) [m.IsMaximal] (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i)
    (D : σ → Derivation ℚ R R)
    (hD : LinearIndependent (R ⧸ m) (fun i => derivationCotangentResidue (D i) m))
    (φ : R →+* (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k))
    (hJ : J ≤ RingHom.ker φ)
    (hres : ∀ a, rectangularAugmentation k (fun i => by have := hk i; omega) (φ a) =
      Ideal.Quotient.mk m a)
    (hfirst : ∀ x : m, φ x -
        ∑ i, Ideal.Quotient.mk m (D i x) •
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
      (RingHom.ker (rectangularAugmentation (K := R ⧸ m) k
        (fun i => by have := hk i; omega)).toRingHom) ^ 2)
    (hprimary : J.radical = m) :
    (∏ i, k i : ℕ) ≤ Module.length R (R ⧸ J) := by
  classical
  let := Ideal.Quotient.field m
  let ε : (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k) →ₐ[R ⧸ m] R ⧸ m :=
    rectangularAugmentation (K := R ⧸ m) k (fun i => by have := hk i; omega)
  have hφ := surjective_of_rectangular_first_order m k hk D hD φ hres hfirst
  let ψ := Ideal.Quotient.lift J φ (fun _ hx => hJ hx)
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨a, rfl⟩ := hφ z
    exact ⟨Ideal.Quotient.mk J a, rfl⟩
  have hJm : J ≤ m := J.le_radical.trans_eq hprimary
  have hcomp : (ε.toRingHom.comp ψ).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m := by
    ext a
    exact hres a
  obtain ⟨N, hN⟩ := J.exists_radical_pow_le_of_fg (Ideal.fg_of_isNoetherianRing _)
  rw [hprimary] at hN
  have hpow : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hN
  have h := augmentation_finrank_le_quotient_length J m hJm ψ ε hcomp hψ N hpow
  simpa only [finrank_rectangularQuotient] using h

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]

theorem derivativeStageIdeal_graded_length_lower_one (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (i : I) (hi : ∀ j : I, j = i)
    (t : Fin 3 → ℕ) (ht : ∀ j : I, 2 ≤ t j + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun j : I => derivationCotangentResidue (D j) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ j : I, (t j + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  have hvanish := (derivativeStageIdeal_le_ker_iff D t (b + 1) F (Ideal.Quotient.mk m)).mp
    (by simpa only [Ideal.mk_ker] using hnext)
  refine local_graded_length_lower_of_rectangular_first_order m (derivativeStageIdeal D t b F)
    (fun j : I => t j + 1) ht (fun j : I => D j) hD
    (rectangularTaylorThree I (fun j => t j + 1) (D i) 0 0 i i i (Ideal.Quotient.mk m))
    (derivativeStageIdeal_le_ker_taylor_one D h01 h02 h12 I i t b F _ hvanish) ?_ ?_ hprimary
  · intro a
    exact rectangularTaylorThree_augmentation _ _ _ _ _ _ _ _ _ a
  · intro x
    exact rectangularTaylorThree_one_first_order _ ht (fun j : I => D j) i hi
      (Ideal.Quotient.mk m) x (Ideal.Quotient.eq_zero_iff_mem.mpr x.property)

theorem derivativeStageIdeal_graded_length_lower_two (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (i j : I) (hij : i ≠ j)
    (hcover : ∀ l : I, l = i ∨ l = j)
    (t : Fin 3 → ℕ) (ht : ∀ l : I, 2 ≤ t l + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun l : I => derivationCotangentResidue (D l) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ l : I, (t l + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  have hvanish := (derivativeStageIdeal_le_ker_iff D t (b + 1) F (Ideal.Quotient.mk m)).mp
    (by simpa only [Ideal.mk_ker] using hnext)
  refine local_graded_length_lower_of_rectangular_first_order m (derivativeStageIdeal D t b F)
    (fun l : I => t l + 1) ht (fun l : I => D l) hD
    (rectangularTaylorThree I (fun l => t l + 1) (D i) (D j) 0 i j j (Ideal.Quotient.mk m))
    (derivativeStageIdeal_le_ker_taylor_two D h01 h02 h12 I i j hij t b F _ hvanish) ?_ ?_ hprimary
  · intro a
    exact rectangularTaylorThree_augmentation _ _ _ _ _ _ _ _ _ a
  · intro x
    exact rectangularTaylorThree_two_first_order _ ht (fun l : I => D l) i j hij hcover
      (Ideal.Quotient.mk m) x (Ideal.Quotient.eq_zero_iff_mem.mpr x.property)

theorem derivativeStageIdeal_graded_length_lower_three (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (i j l : I)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hcover : ∀ u : I, u = i ∨ u = j ∨ u = l)
    (t : Fin 3 → ℕ) (ht : ∀ u : I, 2 ≤ t u + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun u : I => derivationCotangentResidue (D u) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ u : I, (t u + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  have hvanish := (derivativeStageIdeal_le_ker_iff D t (b + 1) F (Ideal.Quotient.mk m)).mp
    (by simpa only [Ideal.mk_ker] using hnext)
  refine local_graded_length_lower_of_rectangular_first_order m (derivativeStageIdeal D t b F)
    (fun u : I => t u + 1) ht (fun u : I => D u) hD
    (rectangularTaylorThree I (fun u => t u + 1) (D i) (D j) (D l) i j l (Ideal.Quotient.mk m))
    (derivativeStageIdeal_le_ker_taylor_three D h01 h02 h12 I i j l hij hil hjl t b F _ hvanish) ?_ ?_ hprimary
  · intro a
    exact rectangularTaylorThree_augmentation _ _ _ _ _ _ _ _ _ a
  · intro x
    exact rectangularTaylorThree_three_first_order _ ht (fun u : I => D u) i j l hij hil hjl hcover
      (Ideal.Quotient.mk m) x (Ideal.Quotient.eq_zero_iff_mem.mpr x.property)

theorem derivativeStageIdeal_graded_length_lower (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (hI : I.Nonempty)
    (t : Fin 3 → ℕ) (ht : ∀ i : I, 2 ≤ t i + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun i : I => derivationCotangentResidue (D i) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ i : I, (t i + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  classical
  have hpos := Finset.card_pos.mpr hI
  have hmax : I.card ≤ 3 := by simpa using Finset.card_le_univ I
  have hcard : I.card = 1 ∨ I.card = 2 ∨ I.card = 3 := by omega
  rcases hcard with hcard | hcard | hcard
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    exact derivativeStageIdeal_graded_length_lower_one D h01 h02 h12 m {i} ⟨i, by simp⟩
      (fun j => Subtype.ext (Finset.mem_singleton.mp j.property)) t ht b F hnext hD hprimary
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
    let ii : ↥({i, j} : Finset (Fin 3)) := ⟨i, by simp⟩
    let jj : ↥({i, j} : Finset (Fin 3)) := ⟨j, by simp⟩
    refine derivativeStageIdeal_graded_length_lower_two D h01 h02 h12 m {i, j} ii jj
      (fun h => hij (congrArg Subtype.val h)) ?_ t ht b F hnext hD hprimary
    intro u
    rcases Finset.mem_insert.mp u.property with hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hu))
  · obtain ⟨i, j, l, hij, hil, hjl, rfl⟩ := Finset.card_eq_three.mp hcard
    let ii : ↥({i, j, l} : Finset (Fin 3)) := ⟨i, by simp⟩
    let jj : ↥({i, j, l} : Finset (Fin 3)) := ⟨j, by simp⟩
    let ll : ↥({i, j, l} : Finset (Fin 3)) := ⟨l, by simp⟩
    refine derivativeStageIdeal_graded_length_lower_three D h01 h02 h12 m {i, j, l} ii jj ll
      (fun h => hij (congrArg Subtype.val h))
      (fun h => hil (congrArg Subtype.val h))
      (fun h => hjl (congrArg Subtype.val h)) ?_ t ht b F hnext hD hprimary
    intro u
    have hu : u.val = i ∨ u.val = j ∨ u.val = l := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using u.property
    rcases hu with hu | hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr (Or.inl (Subtype.ext hu))
    · exact Or.inr (Or.inr (Subtype.ext hu))

end WeightedTorusJets.Geometry


end SiegelZeros

end OAI
