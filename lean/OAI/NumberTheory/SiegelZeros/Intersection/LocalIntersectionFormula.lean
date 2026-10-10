import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalizedFiltrationLength
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ParameterKilledFiniteLength
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.TriangularLocalParametersTransport
import OAI.NumberTheory.SiegelZeros.Structure.EndomorphismEulerAdditivity

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W28.LocalIntersection

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem finite_length_kernel_eq_cokernel
    (u : M →ₗ[A] M) (hfin : IsFiniteLength A M) :
    Module.length A (LinearMap.ker u) =
      Module.length A (M ⧸ LinearMap.range u) := by
  have hk := Module.length_eq_add_of_exact (LinearMap.ker u).subtype
    (LinearMap.ker u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [u.quotKerEquivRange.length_eq] at hk
  have hr := Module.length_eq_add_of_exact (LinearMap.range u).subtype
    (LinearMap.range u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hfiniteRange : Module.length A (LinearMap.range u) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (hfin.of_injective (Submodule.subtype_injective (LinearMap.range u)))
  apply ENat.add_left_injective_of_ne_top hfiniteRange
  calc
    Module.length A (LinearMap.ker u) + Module.length A (LinearMap.range u) =
        Module.length A M := hk.symm
    _ = Module.length A (M ⧸ LinearMap.range u) +
        Module.length A (LinearMap.range u) := hr.trans (add_comm _ _)

def quotientMul (I : Ideal A) (x : A) : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
  x • LinearMap.id

@[simp] theorem quotientMul_apply (I : Ideal A) (x : A) (y : A ⧸ I) :
    quotientMul I x y = x • y := rfl

@[simp] theorem quotientMul_mk (I : Ideal A) (x a : A) :
    quotientMul I x (I.mkQ a) = I.mkQ (a * x) := by
  change x • I.mkQ a = I.mkQ (a * x)
  calc
    x • I.mkQ a = I.mkQ (x • a) := (I.mkQ.map_smul x a).symm
    _ = I.mkQ (a * x) := by rw [smul_eq_mul, mul_comm]

theorem quotientMul_kernel (I : Ideal A) (x : A) :
    LinearMap.ker (quotientMul I x) = Submodule.map I.mkQ (I.colon {x}) := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := I.mkQ_surjective y
    have ha : a * x ∈ I := by
      have hz : quotientMul I x (I.mkQ a) = 0 := hy
      rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      exact hz
    refine ⟨a, ?_, rfl⟩
    change a ∈ I.colon {x}
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha
  · rintro ⟨a, ha, rfl⟩
    change a ∈ I.colon {x} at ha
    change quotientMul I x (I.mkQ a) = 0
    rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha

noncomputable def colonQuotientEquivKernel (I : Ideal A) (x : A) :
    ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≃ₗ[A]
      LinearMap.ker (quotientMul I x) :=
  (W22.subquotientEquivImage I (I.colon {x})).trans
    (LinearEquiv.ofEq _ _ (quotientMul_kernel I x).symm)

theorem quotientMul_range (I : Ideal A) (x : A) :
    LinearMap.range (quotientMul I x) = Submodule.map I.mkQ (Ideal.span {x}) := by
  have hcomp : (quotientMul I x).comp I.mkQ =
      I.mkQ.comp (LinearMap.toSpanSingleton A A x) := by
    apply LinearMap.ext
    intro a
    change quotientMul I x (I.mkQ a) = I.mkQ (a * x)
    exact quotientMul_mk I x a
  have hr := congrArg LinearMap.range hcomp
  simpa only [LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top,
    LinearMap.range_toSpanSingleton] using hr

noncomputable def cokernelEquivCut (I : Ideal A) (x : A) :
    ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) ≃ₗ[A]
      A ⧸ (I ⊔ Ideal.span {x}) :=
  (Submodule.quotEquivOfEq _ _ (quotientMul_range I x)).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span {x}))

theorem kernel_length_eq_colon (I : Ideal A) (x : A) :
    Module.length A (LinearMap.ker (quotientMul I x)) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) :=
  (colonQuotientEquivKernel I x).length_eq.symm

theorem cokernel_length_eq_cut (I : Ideal A) (x : A) :
    Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {x})) :=
  (cokernelEquivCut I x).length_eq

theorem finite_length_cut_eq_colon (I : Ideal A) (x : A)
    (hfin : IsFiniteLength A (A ⧸ I)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) := by
  rw [← cokernel_length_eq_cut, ← kernel_length_eq_colon]
  exact (finite_length_kernel_eq_cokernel (quotientMul I x) hfin).symm

theorem regular_colon_length_zero (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) = 0 := by
  rw [← kernel_length_eq_colon, LinearMap.ker_eq_bot.mpr hregular]
  exact Module.length_bot

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem prime_quotientMul_injective (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) : Function.Injective (quotientMul P x) := by
  have hx0 : Ideal.Quotient.mk P x ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hx
  intro y z hyz
  change x • y = x • z at hyz
  simp only [Algebra.smul_def] at hyz
  exact mul_left_cancel₀ hx0 hyz

theorem prime_colon_length_zero (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) :
    Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) = 0 :=
  regular_colon_length_zero P x (prime_quotientMul_injective P x hx)

theorem quotientMul_eq_zero_of_mem (P : Ideal A) (x : A) (hx : x ∈ P) :
    quotientMul P x = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := P.mkQ_surjective y
  change quotientMul P x (P.mkQ a) = 0
  rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact P.mul_mem_left a hx

noncomputable def minimalPrimeCutSum [IsNoetherianRing A]
    (I : Ideal A) (x : A) : ℕ∞ := by
  classical
  letI : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  exact ∑ P : I.minimalPrimes,
    letI : P.val.IsPrime := P.property.1.1
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸
        I.map (algebraMap A (Localization.AtPrime P.val))) *
      Module.length A (A ⧸ (P.val ⊔ Ideal.span {x}))

def LocalOneCutLengthStatement (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] : Prop :=
  ∀ (I : Ideal A) (x : A),
    ringKrullDim (A ⧸ I) = 1 →
    Function.Injective (quotientMul I x) →
    (I ⊔ Ideal.span {x}).IsPrimary →
    (I ⊔ Ideal.span {x}).radical = IsLocalRing.maximalIdeal A →
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) = minimalPrimeCutSum I x

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem map_scalar_kernel (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change x • e z = 0
    change x • z = 0 at hz
    rw [← map_smul, hz, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change x • e.symm y = 0
    change x • y = 0 at hy
    rw [← map_smul, hy, map_zero]

theorem map_scalar_range (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.range (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨e w, ?_⟩
    change x • e w = e (x • w)
    exact (map_smul e x w).symm
  · rintro ⟨z, rfl⟩
    refine ⟨x • e.symm z, ⟨e.symm z, rfl⟩, ?_⟩
    change e (x • e.symm z) = x • z
    rw [map_smul, e.apply_symm_apply]

noncomputable def scalarKernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M)) ≃ₗ[A]
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) :=
  e.ofSubmodules _ _ (map_scalar_kernel e x)

noncomputable def scalarCokernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
      (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  Submodule.Quotient.equiv _ _ e (map_scalar_range e x)

theorem scalar_kernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarKernelEquiv e x).length_eq

theorem scalar_cokernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarCokernelEquiv e x).length_eq

theorem cyclic_factor_kernel_length (I : Ideal A) (f x : A) :
    Module.length A (LinearMap.ker (x • (LinearMap.id :
      (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) →ₗ[A]
      (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f}))))) =
    Module.length A (((I.colon {f}).colon {x}) ⧸
      (I.colon {f}).submoduleOf ((I.colon {f}).colon {x})) := by
  rw [scalar_kernel_length_eq (W22.cyclicFactorEquiv I f).symm x]
  exact kernel_length_eq_colon (I.colon {f}) x

theorem cyclic_factor_cokernel_length (I : Ideal A) (f x : A) :
    Module.length A
      ((↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) ⧸
        LinearMap.range (x • (LinearMap.id :
          (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) →ₗ[A]
          (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f}))))) =
      Module.length A (A ⧸ ((I.colon {f}) ⊔ Ideal.span {x})) := by
  rw [scalar_cokernel_length_eq (W22.cyclicFactorEquiv I f).symm x]
  exact cokernel_length_eq_cut (I.colon {f}) x

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
theorem quotient_annihilator_eq_colon (J : Ideal A) (f : A) :
    (⊥ : Submodule A (A ⧸ J)).colon {J.mkQ f} = J.colon {f} := by
  ext a
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change a • J.mkQ f = 0 ↔ a * f ∈ J
  rw [← J.mkQ.map_smul, smul_eq_mul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

theorem exists_cyclic_prime_filtration_nat :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      ∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i} := by
  classical
  obtain ⟨s, hshead, hslast⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A A
  have hsmono : Monotone s := Fin.monotone_iff_le_succ.mpr fun i => (s.step i).1
  let J : ℕ → Ideal A := fun i =>
    s ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hd : ∀ i : Fin s.length, ∃ f : A,
      ((s i.castSucc).colon {f}).IsPrime ∧
        s i.succ = s i.castSucc ⊔ Ideal.span {f} := by
    intro i
    obtain ⟨f, hp, hf⟩ :=
      Submodule.isQuotientEquivQuotientPrime_iff.mp (s.step i)
    exact ⟨f, by simpa only [quotient_annihilator_eq_colon] using hp, hf⟩
  let generators : Fin s.length → A := fun i => (hd i).choose
  let f : ℕ → A := fun i => if hi : i < s.length then generators ⟨i, hi⟩ else 0
  refine ⟨s.length, J, f, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hsmono
    exact min_le_min_right s.length (Nat.le_succ i)
  · calc
      J 0 = s.head := by
        apply congrArg s
        apply Fin.ext
        simp
      _ = ⊥ := hshead
  · calc
      J s.length = s.last := by
        apply congrArg s
        apply Fin.ext
        exact min_self s.length
      _ = ⊤ := hslast
  · intro i hi
    have hleft : J i = s (Fin.castSucc ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hi)
    have hright : J (i + 1) = s (Fin.succ ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hi)
    simpa only [f, dite_eq_left hi, generators, hleft, hright] using (hd ⟨i, hi⟩).choose_spec

theorem exists_cyclic_filtration_all_local_counts :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      (∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  obtain ⟨n, J, f, hmono, hstart, hend, hstep⟩ :=
    exists_cyclic_prime_filtration_nat (A := A)
  refine ⟨n, J, f, hmono, hstart, hend, hstep, ?_⟩
  intro P hP hp
  exact W22.localized_cyclic_filtration_length ⊥ P hp J hmono hstart n hend f
    (fun i hi => (hstep i hi).2) (fun i hi => (hstep i hi).1)

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem maximal_factor_cut_eq_colon (P : Ideal A) [P.IsMaximal] (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) := by
  let quotientSimple : IsSimpleModule A (A ⧸ P) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  apply finite_length_cut_eq_colon P x
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_one A (A ⧸ P)]
  exact ENat.one_ne_top

theorem regular_not_mem_minimalPrime (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) (hP : P ∈ minimalPrimes A) : x ∉ P := by
  exact fun hxP => Set.disjoint_left.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hxP hx

theorem dimension_one_prime_factor_dichotomy
    [Ring.KrullDimLE 1 A] [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) [P.IsPrime] :
    (P ∈ minimalPrimes A ∧ Function.Injective (quotientMul P x)) ∨
    (P = IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x}))) := by
  rcases (Ring.krullDimLE_one_iff.mp inferInstance) P inferInstance with hP | hP
  · exact Or.inl ⟨hP,
      prime_quotientMul_injective P x (regular_not_mem_minimalPrime x hx P hP)⟩
  · let primeMaximal : P.IsMaximal := hP
    exact Or.inr ⟨IsLocalRing.eq_maximalIdeal hP, maximal_factor_cut_eq_colon P x⟩

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

theorem scalar_euler_cross_add (x : A)
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hExact : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Module.length A (M₂ ⧸ LinearMap.range (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₃ →ₗ[A] M₃))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (M₁ ⧸ LinearMap.range (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (M₃ ⧸ LinearMap.range (x • (LinearMap.id : M₃ →ₗ[A] M₃))) := by
  apply EndomorphismEuler.endomorphism_euler_cross_add
    (x • LinearMap.id) (x • LinearMap.id) (x • LinearMap.id) f g hExact
  · ext m
    exact map_smul f x m
  · ext m
    exact map_smul g x m
  · exact hf
  · exact hg

theorem cyclic_ideal_step_cross_add (I : Ideal A) (f x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) +
        Module.length A (((I.colon {f}).colon {x}) ⧸
          (I.colon {f}).submoduleOf ((I.colon {f}).colon {x})) +
        Module.length A (((I ⊔ Ideal.span {f}).colon {x}) ⧸
          (I ⊔ Ideal.span {f}).submoduleOf ((I ⊔ Ideal.span {f}).colon {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) +
        Module.length A (A ⧸ ((I.colon {f}) ⊔ Ideal.span {x})) +
        Module.length A (A ⧸ ((I ⊔ Ideal.span {f}) ⊔ Ideal.span {x})) := by
  let J : Ideal A := I ⊔ Ideal.span {f}
  let T : Submodule A (A ⧸ I) := Submodule.map I.mkQ J
  let eT : (A ⧸ I.colon {f}) ≃ₗ[A] T :=
    (W22.cyclicFactorEquiv I f).trans (W22.subquotientEquivImage I J)
  let eQ : ((A ⧸ I) ⧸ T) ≃ₗ[A] (A ⧸ J) :=
    Submodule.quotientQuotientEquivQuotient I J le_sup_left
  have h := scalar_euler_cross_add x T.subtype T.mkQ
    (LinearMap.exact_subtype_mkQ T) (Submodule.subtype_injective T)
    (Submodule.mkQ_surjective T)
  rw [scalar_kernel_length_eq eT.symm x, scalar_kernel_length_eq eQ x,
    scalar_cokernel_length_eq eT.symm x, scalar_cokernel_length_eq eQ x] at h
  change Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) +
      Module.length A (LinearMap.ker (quotientMul (I.colon {f}) x)) +
      Module.length A (LinearMap.ker (quotientMul J x)) =
    Module.length A (LinearMap.ker (quotientMul I x)) +
      Module.length A ((A ⧸ I.colon {f}) ⧸ LinearMap.range (quotientMul (I.colon {f}) x)) +
      Module.length A ((A ⧸ J) ⧸ LinearMap.range (quotientMul J x)) at h
  simpa only [cokernel_length_eq_cut, kernel_length_eq_colon, J] using h

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A]

noncomputable def cutEuler (I : Ideal A) (x : A) : ℤ :=
  ((Module.length A (A ⧸ (I ⊔ Ideal.span {x}))).toNat : ℤ) -
    (Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x}))).toNat

private theorem finite_cross_add_to_integer
    (a b c d e f : ℕ∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) (he : e ≠ ⊤) (hf : f ≠ ⊤)
    (h : a + b + c = d + e + f) :
    (a.toNat : ℤ) - d.toNat =
      ((e.toNat : ℤ) - b.toNat) + ((f.toNat : ℤ) - c.toNat) := by
  lift a to ℕ using ha
  lift b to ℕ using hb
  lift c to ℕ using hc
  lift d to ℕ using hd
  lift e to ℕ using he
  lift f to ℕ using hf
  have hn : a + b + c = d + e + f := by exact_mod_cast h
  simp only [ENat.toNat_natCast]
  omega

theorem cutEuler_cyclic_step (I : Ideal A) (f x : A)
    (hcut : ∀ J : Ideal A, Module.length A (A ⧸ (J ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ J : Ideal A,
      Module.length A ((J.colon {x}) ⧸ J.submoduleOf (J.colon {x})) ≠ ⊤) :
    cutEuler I x = cutEuler (I.colon {f}) x + cutEuler (I ⊔ Ideal.span {f}) x := by
  exact finite_cross_add_to_integer _ _ _ _ _ _
    (hcut I) (hker (I.colon {f})) (hker (I ⊔ Ideal.span {f}))
    (hker I) (hcut (I.colon {f})) (hcut (I ⊔ Ideal.span {f}))
    (cyclic_ideal_step_cross_add I f x)

@[simp] theorem cutEuler_top (x : A) : cutEuler (⊤ : Ideal A) x = 0 := by
  simp [cutEuler, Module.length_eq_zero]

theorem cutEuler_filtration (J : ℕ → Ideal A) (f : ℕ → A) (x : A) (n : ℕ)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hcut : ∀ I : Ideal A, Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ I : Ideal A,
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤) :
    cutEuler (J 0) x = (∑ i ∈ Finset.range n, cutEuler ((J i).colon {f i}) x) +
      cutEuler (J n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)),
      cutEuler_cyclic_step (J n) (f n) x hcut hker,
      ← hstep n (Nat.lt_succ_self n), Finset.sum_range_succ, add_assoc]

theorem exists_prime_factor_euler_sum [IsNoetherianRing A] (x : A)
    (hcut : ∀ I : Ideal A, Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ I : Ideal A,
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤) :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      (∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      cutEuler (⊥ : Ideal A) x = ∑ i ∈ Finset.range n, cutEuler ((J i).colon {f i}) x := by
  obtain ⟨n, J, f, hm, h0, hn, hs⟩ := exists_cyclic_prime_filtration_nat (A := A)
  refine ⟨n, J, f, hm, h0, hn, hs, ?_⟩
  simpa only [h0, hn, cutEuler_top, add_zero] using
    cutEuler_filtration J f x n (fun i hi => (hs i hi).2) hcut hker

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem regular_cut_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤ := by
  rw [← cokernel_length_eq_cut]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_coker_parameter_mul (M := A ⧸ I) hx)

theorem regular_colon_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤ := by
  rw [← kernel_length_eq_colon]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_ker_parameter_mul (M := A ⧸ I) hx)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem regular_colon_bot (x : A) (hx : x ∈ nonZeroDivisors A) :
    (⊥ : Ideal A).colon {x} = ⊥ := by
  ext a
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  exact mul_right_mem_nonZeroDivisors_eq_zero_iff hx

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem cutEuler_bot_regular (x : A) (hx : x ∈ nonZeroDivisors A) :
    cutEuler (⊥ : Ideal A) x =
      ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) := by
  have hz : Module.length A
      (((⊥ : Ideal A).colon {x}) ⧸ (⊥ : Ideal A).submoduleOf ((⊥ : Ideal A).colon {x})) = 0 := by
    rw [regular_colon_bot x hx]
    exact Module.length_eq_zero
  have hlen : Module.length A (A ⧸ ((⊥ : Ideal A) ⊔ Ideal.span {x})) =
      Module.length A (A ⧸ Ideal.span {x}) :=
    (Submodule.quotEquivOfEq _ _ (bot_sup_eq (Ideal.span {x}))).length_eq
  simp only [cutEuler, hz, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hlen

omit [IsNoetherianRing A] in
theorem cutEuler_prime_regular [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (P : Ideal A) [P.IsPrime] :
    cutEuler P x = if P ∈ minimalPrimes A then
      ((Module.length A (A ⧸ (P ⊔ Ideal.span {x}))).toNat : ℤ) else 0 := by
  classical
  by_cases hp : P ∈ minimalPrimes A
  · have hz := prime_colon_length_zero P x (regular_not_mem_minimalPrime x hx P hp)
    simp [cutEuler, hp, hz]
  · rcases dimension_one_prime_factor_dichotomy x hx P with hmin | hmax
    · exact False.elim (hp hmin.1)
    · simp only [hp, ↓reduceIte, cutEuler, hmax.2, sub_self]

theorem exists_regular_onecut_sum_and_local_counts [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i < n, ((J i).colon {f i}).IsPrime) ∧
      (((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} ∈ minimalPrimes A then
          ((Module.length A (A ⧸ ((J i).colon {f i} ⊔ Ideal.span {x}))).toNat : ℤ) else 0) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  classical
  obtain ⟨n, J, f, hm, h0, hn, hs, hcounts⟩ :=
    exists_cyclic_filtration_all_local_counts (A := A)
  refine ⟨n, J, f, (fun i hi => (hs i hi).1), ?_, hcounts⟩
  have he := cutEuler_filtration J f x n (fun i hi => (hs i hi).2)
    (regular_cut_length_ne_top x hx) (regular_colon_length_ne_top x hx)
  rw [h0, hn, cutEuler_top, add_zero, cutEuler_bot_regular x hx] at he
  refine he.trans (Finset.sum_congr rfl ?_)
  intro i hi
  let colonPrime : ((J i).colon {f i}).IsPrime := (hs i (Finset.mem_range.mp hi)).1
  exact cutEuler_prime_regular x hx ((J i).colon {f i})

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] in
private theorem subtype_indicator_sum
    (S : Set (Ideal A)) [Fintype S] (P : Ideal A) (w : Ideal A → ℕ∞) :
    (∑ Q : S, if P = Q.val then w Q.val else 0) =
      if P ∈ S then w P else 0 := by
  classical
  by_cases hp : P ∈ S
  · rw [ite_eq_left hp]
    calc
      (∑ Q : S, if P = Q.val then w Q.val else 0) =
          (if P = P then w P else 0) := by
        apply Finset.sum_eq_single (⟨P, hp⟩ : S)
        · intro Q hQ hne
          have hne' : P ≠ Q.val := by
            intro h
            apply hne
            exact Subtype.ext h.symm
          simp only [hne', ↓reduceIte]
        · simp
      _ = w P := ite_eq_left rfl
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro Q hQ
    have hne : P ≠ Q.val := fun h => hp (h.symm ▸ Q.property)
    simp only [hne, ↓reduceIte]

theorem regular_ring_onecut_length (x : A) (hx : x ∈ nonZeroDivisors A) :
    Module.length A (A ⧸ Ideal.span {x}) =
      minimalPrimeCutSum (⊥ : Ideal A) x := by
  classical
  obtain ⟨n, J, f, hp, he, hcounts⟩ := exists_regular_onecut_sum_and_local_counts x hx
  let ps : ℕ → Ideal A := fun i => (J i).colon {f i}
  let w : Ideal A → ℕ∞ := fun P => Module.length A (A ⧸ (P ⊔ Ideal.span {x}))
  have hsumNat : (Module.length A (A ⧸ Ideal.span {x})).toNat =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then (w (ps i)).toNat else 0 := by
    exact_mod_cast he
  have hsumENat : ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℕ∞) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then ((w (ps i)).toNat : ℕ∞) else 0 := by
    exact_mod_cast hsumNat
  have hzeroCut : Module.length A (A ⧸ Ideal.span {x}) ≠ ⊤ := by
    exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton A hx)
  rw [ENat.natCast_toNat hzeroCut] at hsumENat
  have hsum : Module.length A (A ⧸ Ideal.span {x}) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := by
    refine hsumENat.trans (Finset.sum_congr rfl ?_)
    intro i hi
    split_ifs with hmin
    · exact ENat.natCast_toNat (regular_cut_length_ne_top x hx (ps i))
    · rfl
  let minimalPrimesFintype : Fintype ((⊥ : Ideal A).minimalPrimes) :=
    ((⊥ : Ideal A).finite_minimalPrimes_of_isNoetherianRing A).fintype
  have hterm (P : (⊥ : Ideal A).minimalPrimes) :
      (letI : P.val.IsPrime := P.property.1.1
       Module.length (Localization.AtPrime P.val)
          (Localization.AtPrime P.val ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P.val))) * w P.val) =
        ∑ i ∈ Finset.range n, if ps i = P.val then w P.val else 0 := by
    let minimalPrime : P.val.IsPrime := P.property.1.1
    rw [hcounts P.val P.property, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ps i = P.val
    · simp only [ps] at h
      simp only [h, ↓reduceIte, one_mul, ps]
    · simp only [ps] at h
      simp only [h, ↓reduceIte, zero_mul, ps]
  calc
    Module.length A (A ⧸ Ideal.span {x}) =
        ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := hsum
    _ = ∑ i ∈ Finset.range n, ∑ P : (⊥ : Ideal A).minimalPrimes,
        if ps i = P.val then w P.val else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (subtype_indicator_sum ((⊥ : Ideal A).minimalPrimes) (ps i) w).symm
    _ = ∑ P : (⊥ : Ideal A).minimalPrimes, ∑ i ∈ Finset.range n,
        if ps i = P.val then w P.val else 0 := Finset.sum_comm
    _ = minimalPrimeCutSum (⊥ : Ideal A) x := by
      unfold minimalPrimeCutSum
      apply Finset.sum_congr rfl
      intro P hP
      exact (hterm P).symm

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem quotient_cut_length (I J : Ideal A) :
    Module.length A (A ⧸ (I ⊔ J)) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) := by
  calc
    Module.length A (A ⧸ (I ⊔ J)) =
        Module.length (A ⧸ (I ⊔ J)) (A ⧸ (I ⊔ J)) :=
      SiegelZeros.W23.quotient_module_length_eq_intrinsic _
    _ = Module.length ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
        ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (SiegelZeros.W23.intrinsic_length_eq_of_ringEquiv
        (DoubleQuot.quotQuotEquivQuotSup I J)).symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (SiegelZeros.W23.quotient_module_length_eq_intrinsic _).symm

theorem quotient_principal_cut_length (I : Ideal A) (x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) := by
  have hmap : (Ideal.span {x}).map (Ideal.Quotient.mk I) =
      Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_span, Set.image_singleton]
  exact (quotient_cut_length I (Ideal.span {x})).trans
    (Submodule.quotEquivOfEq _ _ hmap).length_eq

theorem quotient_prime_cut_length (I P : Ideal A) (hIP : I ≤ P) (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) := by
  have hleft : I ⊔ (P ⊔ Ideal.span {x}) = P ⊔ Ideal.span {x} :=
    sup_eq_right.mpr (hIP.trans le_sup_left)
  have hright : (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I) =
      P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  calc
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A (A ⧸ (I ⊔ (P ⊔ Ideal.span {x}))) :=
      (Submodule.quotEquivOfEq _ _ hleft).length_eq.symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I)) :=
      quotient_cut_length I (P ⊔ Ideal.span {x})
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) :=
      (Submodule.quotEquivOfEq _ _ hright).length_eq

noncomputable def quotientMinimalPrimesEquiv (I : Ideal A) :
    minimalPrimes (A ⧸ I) ≃ I.minimalPrimes := by
  classical
  let f : minimalPrimes (A ⧸ I) → I.minimalPrimes := fun Q =>
    ⟨Q.val.comap (Ideal.Quotient.mk I), by
      rw [I.minimalPrimes_eq_comap]
      exact ⟨Q.val, Q.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro Q R h
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    exact congrArg Subtype.val h
  · intro P
    have hmem : P.val ∈ Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (A ⧸ I) :=
      Eq.mp (congrArg (fun S : Set (Ideal A) => P.val ∈ S) I.minimalPrimes_eq_comap) P.property
    obtain ⟨Q, hQ, hQP⟩ := hmem
    exact ⟨⟨Q, hQ⟩, Subtype.ext hQP⟩

@[simp] theorem quotientMinimalPrimesEquiv_apply (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (quotientMinimalPrimesEquiv I Q).val = Q.val.comap (Ideal.Quotient.mk I) := rfl

theorem quotient_minimal_local_length (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (letI : (quotientMinimalPrimesEquiv I Q).val.IsPrime :=
       (quotientMinimalPrimesEquiv I Q).property.1.1
     Module.length (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)
       (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val ⧸
        I.map (algebraMap A (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)))) =
    (letI : Q.val.IsPrime := Q.property.1.1
     Module.length (Localization.AtPrime Q.val)
       (Localization.AtPrime Q.val ⧸ (⊥ : Ideal (A ⧸ I)).map
        (algebraMap (A ⧸ I) (Localization.AtPrime Q.val)))) := by
  let P := (quotientMinimalPrimesEquiv I Q).val
  let correspondingPrime : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let quotientPrime : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : SiegelZeros.W23.quotientParameterPrime I P hIP = Q.val := by
    exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hlocal := SiegelZeros.W23.quotient_localized_length_eq_explicit I P hIP
  have hprime :
      (⟨SiegelZeros.W23.quotientParameterPrime I P hIP,
        SiegelZeros.W23.quotientParameterPrime_isPrime I P hIP⟩ : PrimeSpectrum (A ⧸ I)) =
      ⟨Q.val, Q.property.1.1⟩ := PrimeSpectrum.ext hmap
  have hlength := congrArg (fun p : PrimeSpectrum (A ⧸ I) =>
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) hprime
  refine (hlocal.trans hlength).trans ?_
  rw [Ideal.map_bot]
  exact ((⊥ : Submodule (Localization.AtPrime Q.val) (Localization.AtPrime Q.val)).quotEquivOfEqBot
    rfl).length_eq.symm

end WeightedTorusJets.W28.LocalIntersection



namespace WeightedTorusJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem minimalPrimeCutSum_quotient (I : Ideal A) (x : A) :
    minimalPrimeCutSum I x =
      minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) := by
  classical
  let minimalPrimesFintype : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  let quotientMinimalPrimesFintype : Fintype (minimalPrimes (A ⧸ I)) :=
    ((⊥ : Ideal (A ⧸ I)).finite_minimalPrimes_of_isNoetherianRing (A ⧸ I)).fintype
  symm
  unfold minimalPrimeCutSum
  apply Fintype.sum_equiv (quotientMinimalPrimesEquiv I)
  intro Q
  let P := (quotientMinimalPrimesEquiv I Q).val
  let correspondingPrime : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let quotientPrime : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : P.map (Ideal.Quotient.mk I) = Q.val :=
    Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hc := quotient_prime_cut_length I P hIP x
  rw [hmap] at hc
  exact congrArg₂ HMul.hMul (quotient_minimal_local_length I Q).symm hc.symm

omit [IsNoetherianRing A] in
theorem quotient_parameter_mem_nonZeroDivisors (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Ideal.Quotient.mk I x ∈ nonZeroDivisors (A ⧸ I) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro y hy
  apply hregular
  change x • y = x • (0 : A ⧸ I)
  rw [smul_zero, Algebra.smul_def]
  exact hy

theorem local_onecut_length [IsLocalRing A]
    (I : Ideal A) (x : A) (hdim : ringKrullDim (A ⧸ I) = 1)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) = minimalPrimeCutSum I x := by
  have hnot : ¬ Subsingleton (A ⧸ I) := by
    intro hsub
    let quotientSubsingleton := hsub
    have hbot : ringKrullDim (A ⧸ I) = ⊥ := ringKrullDim_eq_bot_of_subsingleton
    rw [hdim] at hbot
    exact WithBot.one_ne_bot hbot
  let quotientNontrivial : Nontrivial (A ⧸ I) := not_subsingleton_iff_nontrivial.mp hnot
  let quotientLocal : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let quotientDimension : Ring.KrullDimLE 1 (A ⧸ I) := Ring.krullDimLE_iff.mpr hdim.le
  calc
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
        Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) :=
      quotient_principal_cut_length I x
    _ = minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) :=
      regular_ring_onecut_length _ (quotient_parameter_mem_nonZeroDivisors I x hregular)
    _ = minimalPrimeCutSum I x := (minimalPrimeCutSum_quotient I x).symm

theorem localOneCutLengthStatement_proved [IsLocalRing A] :
    LocalOneCutLengthStatement A := by
  intro I x hdim hregular _hprimary _hradical
  exact local_onecut_length I x hdim hregular

end WeightedTorusJets.W28.LocalIntersection


end SiegelZeros

end OAI
