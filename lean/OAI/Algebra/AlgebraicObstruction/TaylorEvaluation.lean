import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.TaylorCoefficients

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace ResidueSection
variable (K R : Type*) [Field K] [PerfectField K] [CommRing R] [IsLocalRing R]
  [Algebra K R] [Algebra.EssFiniteType K R]

abbrev Trunc (q : ℕ) := R ⧸ (IsLocalRing.maximalIdeal R)^q

def reduction (q : ℕ) (hq : 1 ≤ q) : Trunc R q →ₐ[K] IsLocalRing.ResidueField R :=
  Ideal.Quotient.factorₐ K (Ideal.pow_le_self (by omega : q ≠ 0))

omit [PerfectField K] [Algebra.EssFiniteType K R] in
lemma reduction_surjective (q : ℕ) (hq : 1 ≤ q) :
    Function.Surjective (reduction K R q hq) :=
  Ideal.Quotient.factor_surjective (Ideal.pow_le_self (by omega : q ≠ 0))

omit [PerfectField K] [Algebra.EssFiniteType K R] in
lemma reduction_ker_pow (q : ℕ) (hq : 1 ≤ q) :
    RingHom.ker (reduction K R q hq : Trunc R q →+* IsLocalRing.ResidueField R) ^ q = ⊥ := by
  change RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self (by omega : q ≠ 0))) ^ q = ⊥
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

noncomputable def sectionMap (q : ℕ) (hq : 1 ≤ q) :
    IsLocalRing.ResidueField R →ₐ[K] Trunc R q :=
  by
  letI : Algebra.EssFiniteType K (IsLocalRing.ResidueField R) :=
    Algebra.EssFiniteType.comp K R (IsLocalRing.ResidueField R)
  exact Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K _)
    (reduction K R q hq) (reduction_surjective K R q hq)
    ⟨q,reduction_ker_pow K R q hq⟩

@[simp] lemma reduction_sectionMap (q : ℕ) (hq : 1 ≤ q) (a : IsLocalRing.ResidueField R) :
    reduction K R q hq (sectionMap K R q hq a) = a :=
  by
  let : Algebra.EssFiniteType K (IsLocalRing.ResidueField R) :=
    Algebra.EssFiniteType.comp K R (IsLocalRing.ResidueField R)
  exact Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ a

omit [PerfectField K] [Algebra.EssFiniteType K R] in
@[simp] lemma reduction_mk (q : ℕ) (hq : 1 ≤ q) (a : R) :
    reduction K R q hq (Ideal.Quotient.mk _ a) = IsLocalRing.residue R a := rfl

end ResidueSection
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace TaylorEvaluate
variable {K A α D F : Type*} [CommRing K] [CommRing A] [CommRing D] [CommRing F]
  [Algebra K A] [Algebra (MvPolynomial α K) A] [IsScalarTower K (MvPolynomial α K) A]

noncomputable def poly (I : Ideal A) (f : A →+* D) (c : A ⧸ I →+* D) :
    MvPolynomial α (A ⧸ I) →+* D :=
  MvPolynomial.eval₂Hom c (fun i ↦ f (algebraMap (MvPolynomial α K) A (MvPolynomial.X i)) -
    c (Ideal.Quotient.mk I (algebraMap (MvPolynomial α K) A (MvPolynomial.X i))))

omit [Algebra K A] [IsScalarTower K (MvPolynomial α K) A] in
lemma variables_map_le (I : Ideal A) (f : A →+* D) (c : A ⧸ I →+* D)
    (g : D →+* F) (hc : ∀ a : A, g (c (Ideal.Quotient.mk I a)) = g (f a)) :
    (TaylorTarget.variablesIdeal (A ⧸ I) α).map (poly (K := K) (α := α) I f c) ≤ RingHom.ker g := by
  rw [Ideal.map_le_iff_le_comap,Ideal.span_le]
  rintro _ ⟨i,rfl⟩
  change g (poly (K := K) (α := α) I f c (MvPolynomial.X i)) = 0
  simp only [poly,MvPolynomial.eval₂Hom_X',map_sub,hc,sub_self]

noncomputable def evaluate (I : Ideal A) (f : A →+* D) (c : A ⧸ I →+* D)
    (g : D →+* F) (hc : ∀ a : A, g (c (Ideal.Quotient.mk I a)) = g (f a))
    (q : ℕ) (hg : RingHom.ker g ^ q = ⊥) : TaylorShift.Target (α := α) I q →+* D :=
  Ideal.Quotient.lift _ (poly (K := K) (α := α) I f c) (by
    change TaylorTarget.variablesIdeal (A ⧸ I) α ^ q ≤ RingHom.ker (poly (K := K) (α := α) I f c)
    rw [RingHom.ker_eq_comap_bot,← Ideal.map_le_iff_le_comap,Ideal.map_pow]
    exact (pow_le_pow_left' (variables_map_le I f c g hc) q).trans (le_of_eq hg))

omit [Algebra K A] [IsScalarTower K (MvPolynomial α K) A] in
@[simp] lemma evaluate_mk (I : Ideal A) (f : A →+* D) (c : A ⧸ I →+* D)
    (g : D →+* F) (hc : ∀ a : A, g (c (Ideal.Quotient.mk I a)) = g (f a))
    (q : ℕ) (hg : RingHom.ker g ^ q = ⊥) (p : MvPolynomial α (A ⧸ I)) :
    evaluate (K := K) I f c g hc q hg (TaylorTarget.mk (A ⧸ I) α q p) =
      poly (K := K) (α := α) I f c p := rfl

lemma evaluate_shift (I : Ideal A) (f : A →+* D) (c : A ⧸ I →+* D)
    (g : D →+* F) (hc : ∀ a : A, g (c (Ideal.Quotient.mk I a)) = g (f a))
    (q : ℕ) (hg : RingHom.ker g ^ q = ⊥)
    (hcK : ∀ k : K, c (Ideal.Quotient.mk I (algebraMap K A k)) = f (algebraMap K A k))
    (p : MvPolynomial α K) :
    evaluate (K := K) I f c g hc q hg (TaylorShift.shift I q p) =
      f (algebraMap (MvPolynomial α K) A p) := by
  have h : (evaluate (K := K) I f c g hc q hg).comp (TaylorShift.shift I q) =
      f.comp (algebraMap (MvPolynomial α K) A) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [RingHom.comp_apply,TaylorShift.shift,MvPolynomial.eval₂Hom_C]
      rw [evaluate_mk]
      simp only [poly,MvPolynomial.eval₂Hom_C]
      rw [hcK]
      exact congrArg f (IsScalarTower.algebraMap_apply K (MvPolynomial α K) A k)
    · intro i
      simp [TaylorShift.shift,poly]
  exact RingHom.congr_fun h p

omit [Algebra K A] [IsScalarTower K (MvPolynomial α K) A] in
lemma reduction_evaluate (I : Ideal A) (f : A →+* D) (c : A ⧸ I →+* D)
    (g : D →+* F) (hc : ∀ a : A, g (c (Ideal.Quotient.mk I a)) = g (f a))
    (q : ℕ) (hq : 1 ≤ q) (hg : RingHom.ker g ^ q = ⊥)
    (x : TaylorShift.Target (α := α) I q) :
    g (evaluate (K := K) I f c g hc q hg x) =
      g (c (TaylorTarget.reduction (A ⧸ I) α q hq x)) := by
  have hh : g.comp (poly (K := K) (α := α) I f c) =
      (g.comp c).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [poly]
    · intro i
      simp only [RingHom.comp_apply,poly,MvPolynomial.eval₂Hom_X',map_sub,hc,
        sub_self,MvPolynomial.constantCoeff_X,map_zero]
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun hh p

theorem evaluate_taylor [Algebra.FormallyEtale (MvPolynomial α K) A]
    (I : Ideal A) (f : A →+* D) (c : A ⧸ I →+* D)
    (g : D →+* F) (hc : ∀ a : A, g (c (Ideal.Quotient.mk I a)) = g (f a))
    (q : ℕ) (hq : 1 ≤ q) (hg : RingHom.ker g ^ q = ⊥)
    (hcK : ∀ k : K, c (Ideal.Quotient.mk I (algebraMap K A k)) = f (algebraMap K A k))
    (a : A) :
    evaluate (K := K) I f c g hc q hg (TaylorShift.taylor (K := K) (α := α) I q hq a) = f a := by
  let : Algebra (MvPolynomial α K) D := (f.comp (algebraMap (MvPolynomial α K) A)).toAlgebra
  let u : A →ₐ[MvPolynomial α K] D :=
    { (evaluate (K := K) I f c g hc q hg).comp (TaylorShift.taylor (K := K) (α := α) I q hq) with
      commutes' := by
        intro p
        change evaluate (K := K) I f c g hc q hg
          (TaylorShift.taylor (K := K) (α := α) I q hq (algebraMap (MvPolynomial α K) A p)) = _
        rw [TaylorShift.taylor_coordinates]
        exact evaluate_shift I f c g hc q hg hcK p }
  let v : A →ₐ[MvPolynomial α K] D := ⟨f, fun _ ↦ rfl⟩
  have huv : u = v := Algebra.FormallyUnramified.ext' g ⟨q,hg⟩ u v (by
    intro b
    change g (evaluate (K := K) I f c g hc q hg
      (TaylorShift.taylor (K := K) (α := α) I q hq b)) = g (f b)
    rw [reduction_evaluate I f c g hc q hq hg,TaylorShift.reduction_taylor]
    exact hc b)
  exact AlgHom.congr_fun huv a

end TaylorEvaluate
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace SymbolicTaylor
variable {K A α : Type*} [Field K] [PerfectField K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A] [IsScalarTower K (MvPolynomial α K) A]
  [Algebra.EssFiniteType K A] [Algebra.FormallyEtale (MvPolynomial α K) A]

theorem kernel_le_symbolic (I p : Ideal A) [p.IsPrime] (hIp : I ≤ p)
    (q : ℕ) (hq : 1 ≤ q) (a : A)
    (ha : TaylorShift.taylor (K := K) (α := α) I q hq a = 0) :
    ∃ s : A, s ∉ p ∧ s*a ∈ p^q := by
  let R := Localization.AtPrime p
  let : Algebra.EssFiniteType A R :=
    Algebra.EssFiniteType.of_isLocalization R p.primeCompl
  let : Algebra.EssFiniteType K R := Algebra.EssFiniteType.comp K A R
  let m := IsLocalRing.maximalIdeal R
  let D := R ⧸ m^q
  let F := IsLocalRing.ResidueField R
  let f : A →ₐ[K] D := (Ideal.Quotient.mkₐ K (m^q)).comp (IsScalarTower.toAlgHom K A R)
  let rho : A →ₐ[K] F :=
    (IsScalarTower.toAlgHom K R F).comp (IsScalarTower.toAlgHom K A R)
  have hI : I ≤ RingHom.ker (rho : A →+* F) := by
    intro b hb
    change IsLocalRing.residue R (algebraMap A R b) = 0
    rw [IsLocalRing.residue_eq_zero_iff,← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hIp hb)
  let rhoQ : A ⧸ I →ₐ[K] F := Ideal.Quotient.liftₐ I rho hI
  let c : A ⧸ I →ₐ[K] D := (ResidueSection.sectionMap K R q hq).comp rhoQ
  let g : D →ₐ[K] F := ResidueSection.reduction K R q hq
  have hc : ∀ b : A, g (c (Ideal.Quotient.mk I b)) = g (f b) := by
    intro b
    dsimp [c,g,f,rhoQ]
    rw [ResidueSection.reduction_sectionMap]
    rfl
  have hcK : ∀ k : K, c (Ideal.Quotient.mk I (algebraMap K A k)) = f (algebraMap K A k) := by
    intro k
    change c (algebraMap K (A ⧸ I) k) = f (algebraMap K A k)
    rw [c.commutes,f.commutes]
  have hg : RingHom.ker (g : D →+* F) ^ q = ⊥ := ResidueSection.reduction_ker_pow K R q hq
  have hf : f a = 0 := by
    have he := TaylorEvaluate.evaluate_taylor (α := α) I f.toRingHom c.toRingHom
      g.toRingHom hc q hq hg hcK a
    rw [ha,map_zero] at he
    exact he.symm
  have ham : algebraMap A R a ∈ m^q := (Ideal.Quotient.eq_zero_iff_mem).mp hf
  have hmp : m = p.map (algebraMap A R) := Localization.AtPrime.map_eq_maximalIdeal.symm
  rw [hmp,← Ideal.map_pow,IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl] at ham
  exact ham

end SymbolicTaylor
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
