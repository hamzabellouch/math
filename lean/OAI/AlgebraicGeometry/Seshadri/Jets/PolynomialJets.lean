import Mathlib

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

abbrev JetIndex (σ : Type*) (n : ℕ) := {d : σ →₀ ℕ // d.degree < n}

instance jetIndexFinite [Finite σ] (n : ℕ) : Finite (JetIndex σ n) :=
  (Finsupp.finite_of_degree_lt n).to_subtype

def polynomialJetCoeffs (n : ℕ) : MvPolynomial σ R →ₗ[R] (JetIndex σ n → R) where
  toFun polynomial index := polynomial.coeff index.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma polynomialJetCoeffs_ker (n : ℕ) :
    (polynomialJetCoeffs (σ := σ) (R := R) n).ker =
      ((idealOfVars σ R) ^ n).restrictScalars R := by
  ext p
  rw [LinearMap.mem_ker, funext_iff]
  change (∀ index : JetIndex σ n, p.coeff index.val = 0) ↔ _
  rw [Submodule.restrictScalars_mem, mem_pow_idealOfVars_iff']
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d.val d.property⟩

lemma polynomialJetCoeffs_surjective [Finite σ] (n : ℕ) :
    Function.Surjective (polynomialJetCoeffs (σ := σ) (R := R) n) := by
  classical
  let : Fintype (JetIndex σ n) := Fintype.ofFinite _
  intro a
  refine ⟨∑ d : JetIndex σ n, monomial d.val (a d), ?_⟩
  ext e
  change (∑ index : JetIndex σ n, monomial index.val (a index)).coeff e.val = a e
  simp only [coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d _ hde
    rw [ite_eq_right (fun equality => hde (Subtype.ext equality))]
  · simp

def polynomialJetEquiv [Finite σ] (n : ℕ) :
    (MvPolynomial σ R ⧸ (idealOfVars σ R) ^ n) ≃ₗ[R] (JetIndex σ n → R) := by
  let e := LinearMap.quotKerEquivOfSurjective
    (polynomialJetCoeffs (σ := σ) (R := R) n) (polynomialJetCoeffs_surjective n)
  exact (Submodule.quotEquivOfEq _ _ (polynomialJetCoeffs_ker n).symm).trans e

def polynomialTranslate (x : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i + C (x i)))
    (aeval (fun i => X i - C (x i)))
    (by ext i; simp)
    (by ext i; simp)

lemma polynomialTranslate_constantCoeff (x : σ → R) (p : MvPolynomial σ R) :
    constantCoeff (polynomialTranslate x p) = eval x p := by
  have h : (constantCoeff : MvPolynomial σ R →+* R).comp
      (polynomialTranslate x).toRingHom = eval x := by
    apply ringHom_ext
    · intro c; simp [polynomialTranslate]
    · intro i; simp [polynomialTranslate]
  exact RingHom.congr_fun h p

lemma idealOfVars_eq_ker_constantCoeff :
    idealOfVars σ R = RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) := by
  ext p
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff']
  change (∀ index, index.degree < 1 → p.coeff index = 0) ↔ p.coeff 0 = 0
  constructor
  · exact fun h => h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    simpa [hd0] using h

theorem mem_rationalPoint_pow_iff (x : σ → R) (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ (RingHom.ker (eval x)) ^ n ↔
      ∀ index : σ →₀ ℕ, index.degree < n → (polynomialTranslate x p).coeff index = 0 := by
  have heq : RingHom.ker (eval x) =
      (idealOfVars σ R).map (polynomialTranslate x).symm.toRingHom := by
    simp only [RingEquiv.toRingHom_eq_coe]
    rw [Ideal.map_comap_of_equiv ((polynomialTranslate x).symm.toRingEquiv)]
    ext f
    change eval x f = 0 ↔ polynomialTranslate x f ∈ idealOfVars σ R
    rw [idealOfVars_eq_ker_constantCoeff]
    change eval x f = 0 ↔ constantCoeff (polynomialTranslate x f) = 0
    rw [polynomialTranslate_constantCoeff]
  rw [heq, ← Ideal.map_pow]
  simp only [RingEquiv.toRingHom_eq_coe]
  rw [Ideal.map_comap_of_equiv ((polynomialTranslate x).symm.toRingEquiv)]
  change polynomialTranslate x p ∈ (idealOfVars σ R) ^ n ↔ _
  exact mem_pow_idealOfVars_iff' n _

end

noncomputable section
open MvPolynomial
variable {σ R : Type*} [CommRing R]

def polynomialJetCoeffsAt (x : σ → R) (n : ℕ) :
    MvPolynomial σ R →ₗ[R] (JetIndex σ n → R) :=
  (polynomialJetCoeffs n).comp (polynomialTranslate x).toLinearMap

lemma polynomialJetCoeffsAt_ker (x : σ → R) (n : ℕ) :
    (polynomialJetCoeffsAt x n).ker =
      ((RingHom.ker (eval x)) ^ n).restrictScalars R := by
  ext p
  rw [LinearMap.mem_ker, funext_iff]
  change (∀ index : JetIndex σ n, (polynomialTranslate x p).coeff index.val = 0) ↔ _
  rw [Submodule.restrictScalars_mem, mem_rationalPoint_pow_iff]
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d.val d.property⟩

lemma polynomialJetCoeffsAt_surjective [Finite σ] (x : σ → R) (n : ℕ) :
    Function.Surjective (polynomialJetCoeffsAt x n) :=
  (polynomialJetCoeffs_surjective n).comp (polynomialTranslate x).surjective

def polynomialJetEquivAt [Finite σ] (x : σ → R) (n : ℕ) :
    (MvPolynomial σ R ⧸ (RingHom.ker (eval x)) ^ n) ≃ₗ[R] (JetIndex σ n → R) := by
  let e := LinearMap.quotKerEquivOfSurjective
    (polynomialJetCoeffsAt x n) (polynomialJetCoeffsAt_surjective x n)
  exact (Submodule.quotEquivOfEq _ _ (polynomialJetCoeffsAt_ker x n).symm).trans e

@[simp] lemma polynomialJetEquivAt_mk [Finite σ] (x : σ → R) (n : ℕ)
    (p : MvPolynomial σ R) (d : JetIndex σ n) :
    polynomialJetEquivAt x n (Ideal.Quotient.mk _ p) d =
      (polynomialTranslate x p).coeff d.val := rfl

@[simp] lemma polynomialJetEquiv_mk [Finite σ] (n : ℕ)
    (p : MvPolynomial σ R) (d : JetIndex σ n) :
    polynomialJetEquiv (σ := σ) (R := R) n (Ideal.Quotient.mk _ p) d =
      p.coeff d.val := rfl

end

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

abbrev JetAlgebra (σ R : Type*) [CommRing R] (n : ℕ) :=
  MvPolynomial σ R ⧸ (idealOfVars σ R) ^ n

def jetAugment (n : ℕ) (hn : 0 < n) : JetAlgebra σ R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval (fun _ : σ => (0 : R))) (by
    intro p hp
    have hc := (mem_pow_idealOfVars_iff' n p).mp hp 0 (by simpa using hn)
    simpa [aeval_def, eval_zero, constantCoeff_eq] using hc)

@[simp] lemma jetAugment_mk (n : ℕ) (hn : 0 < n) (p : MvPolynomial σ R) :
    jetAugment n hn (Ideal.Quotient.mk _ p) = constantCoeff p := by
  change (aeval (fun _ : σ => (0 : R))) p = _
  simp [aeval_def]

lemma jetAugment_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (jetAugment (σ := σ) (R := R) n hn) :=
  fun c => ⟨algebraMap R _ c, by simp⟩

lemma jetAugment_ker (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := R) n hn) =
      (idealOfVars σ R).map (Ideal.Quotient.mk ((idealOfVars σ R) ^ n)) := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.mem_ker, jetAugment_mk,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro h
    exact ⟨p, by rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker], rfl⟩
  · rintro ⟨f, hf, hfp⟩
    have hd : f - p ∈ (idealOfVars σ R) ^ n := Ideal.Quotient.eq.mp hfp
    have hd' := (mem_pow_idealOfVars_iff' n (f - p)).mp hd 0 (by simpa using hn)
    have hf' : constantCoeff f = 0 := by
      rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker] at hf
    change constantCoeff (f - p) = 0 at hd'
    simpa [map_sub, hf'] using hd'

lemma jetAugment_ker_nilpotent (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker (jetAugment (σ := σ) (R := R) n hn)) := by
  refine ⟨n, ?_⟩
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end

noncomputable section
open MvPolynomial

variable {σ F S B : Type*} [CommRing F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma exists_lift_with_coordinates [CommRing B] [Algebra F B]
    [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (β : MvPolynomial σ F →ₐ[F] B) (α : B →ₐ[F] S)
    (hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
    (hα : Function.Surjective α) (hnil : IsNilpotent (RingHom.ker α)) :
    ∃ τ : S →ₐ[F] B, α.comp τ = AlgHom.id F S ∧
      τ.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) = β := by
  let : Algebra (MvPolynomial σ F) B := β.toRingHom.toAlgebra
  let : IsScalarTower F (MvPolynomial σ F) B :=
    IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  let ap : B →ₐ[MvPolynomial σ F] S :=
    { α.toRingHom with
      commutes' := fun p => AlgHom.congr_fun hαβ p }
  let τ := Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  have hτ := Algebra.FormallySmooth.comp_liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  refine ⟨τ.restrictScalars F, ?_, ?_⟩
  · ext s
    exact AlgHom.congr_fun hτ s
  · ext i
    exact τ.commutes (X i)

theorem exists_regular_taylor [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) :
    ∃ τ : S →ₐ[F] JetAlgebra σ S n,
      (∀ s, jetAugment n hn (τ s) = s) ∧
      (∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
        algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
          Ideal.Quotient.mk _ (X i)) := by
  let T := JetAlgebra σ S n
  let x : σ → S := fun i => algebraMap (MvPolynomial σ F) S (X i)
  let β : MvPolynomial σ F →ₐ[F] T :=
    aeval (fun i => algebraMap S T (x i) + Ideal.Quotient.mk _ (X i))
  let α := (jetAugment (σ := σ) (R := S) n hn).restrictScalars F
  have hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S := by
    ext i
    change jetAugment n hn (β (X i)) = x i
    simp only [β, aeval_X, map_add, jetAugment_mk, constantCoeff_X, add_zero]
    exact (jetAugment (σ := σ) (R := S) n hn).commutes (x i)
  obtain ⟨τ, hτ, hcoord⟩ := exists_lift_with_coordinates β α hαβ
    (jetAugment_surjective n hn) (jetAugment_ker_nilpotent n hn)
  refine ⟨τ, fun s => AlgHom.congr_fun hτ s, ?_⟩
  intro i
  have hi := AlgHom.congr_fun hcoord (X i)
  exact hi.trans (aeval_X _ _)

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

lemma map_idealOfVars (φ : R →ₐ[F] S) :
    (idealOfVars σ R).map (MvPolynomial.map φ.toRingHom) = idealOfVars σ S := by
  rw [idealOfVars, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.map_X φ.toRingHom i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, MvPolynomial.map_X φ.toRingHom i⟩

def mapJetAlgebra (φ : R →ₐ[F] S) (n : ℕ) :
    JetAlgebra σ R n →ₐ[F] JetAlgebra σ S n :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom φ) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    change ((idealOfVars σ R).map (MvPolynomial.map φ.toRingHom)) ^ n ≤ _
    rw [map_idealOfVars])

@[simp] lemma mapJetAlgebra_mk (φ : R →ₐ[F] S) (n : ℕ) (p : MvPolynomial σ R) :
    mapJetAlgebra (σ := σ) φ n (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map φ.toRingHom p) := rfl

lemma jetAugment_map (φ : R →ₐ[F] S) (n : ℕ) (hn : 0 < n)
    (z : JetAlgebra σ R n) :
    jetAugment n hn (mapJetAlgebra φ n z) = φ (jetAugment n hn z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp [MvPolynomial.constantCoeff_map]

lemma jetAugment_ker_pow (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := S) n hn) ^ n = 0 := by
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
