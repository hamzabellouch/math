import Mathlib

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LaurentTails
open LaurentPolynomial
open scoped LaurentPolynomial
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module K[T;T⁻¹] M] [IsScalarTower K K[T;T⁻¹] M]

omit [IsScalarTower K K[T;T⁻¹] M] in
lemma positive_tail (A : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A) {x : M} (hx : x ∈ A) :
    ∀ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, T_add, mul_smul]
      using hA _ ih

omit [IsScalarTower K K[T;T⁻¹] M] in
lemma negative_tail (B : Submodule K M)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B) {x : M} (hx : x ∈ B) :
    ∀ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have he : -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) := by omega
    simpa only [he, T_add, mul_smul] using hB _ ih

theorem quotient_finite [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B)
    (locA : ∀ x : M, ∃ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B) :
    Module.Finite K (M ⧸ (A ⊔ B)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[T;T⁻¹]) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  let q := (A ⊔ B).mkQ
  let J := (i : Fin n) × ↥(Finset.Icc (-(b i : ℤ)) (a i : ℤ))
  let g : J → M ⧸ (A ⊔ B) := fun v => q ((T v.2.val : K[T;T⁻¹]) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ) : q ((T z : K[T;T⁻¹]) • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z
    · have he : z = ((z - a i).toNat : ℤ) + a i := by omega
      have hm : (T z : K[T;T⁻¹]) • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact positive_tail A hA (ha i) _
      have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
        (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show A ≤ A ⊔ B from le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : z ≤ -(b i : ℤ)
      · have he : z = -((-(b i : ℤ) - z).toNat : ℤ) + -(b i : ℤ) := by omega
        have hm : (T z : K[T;T⁻¹]) • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact negative_tail B hB (hb i) _
        have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
          (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show B ≤ A ⊔ B from le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · exact Submodule.subset_span ⟨⟨i,⟨z,Finset.mem_Icc.mpr (by omega)⟩⟩,rfl⟩
  have scalar_monomial (i : Fin n) (p : K[T;T⁻¹]) : q (p • s i) ∈ W := by
    induction p using LaurentPolynomial.induction_on' with
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | C_mul_T z c =>
      rw [mul_smul, C_eq_algebraMap, algebraMap_smul, map_smul]
      exact W.smul_mem c (monomial i z)
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m,rfl⟩ := (A ⊔ B).mkQ_surjective x
    have hm : m ∈ Submodule.span K[T;T⁻¹] (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : K[T;T⁻¹], q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro p; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end PiExponentSeshadri.LaurentTails

namespace PiExponentSeshadri.LaurentCech
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

omit [IsScalarTower K K[X] P] in
theorem cokernel_finite [Module.Finite K[X] N]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y)
    (opposite_denominators : ∀ x : Q, ∃ n : ℕ, ∃ y : P,
      ((Polynomial.X : K[X])^n) • g y = x) :
    Module.Finite K (Q ⧸ ((f.restrictScalars K).range ⊔ g.range)) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentTails.quotient_finite (A := (f.restrictScalars K).range) (B := g.range)
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    change f ((Polynomial.X : K[X]) • y) = (T 1 : K[T;T⁻¹]) • f y
    rw [map_smul, pos1]
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
  · intro x
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away (Polynomial.X : K[X]) f).surj _ _ x
    refine ⟨n, y, ?_⟩
    change f y = (T (n : ℤ) : K[T;T⁻¹]) • x
    rw [pos]
    exact hy.symm
  · intro x
    obtain ⟨n,y,hy⟩ := opposite_denominators x
    refine ⟨n,y,?_⟩
    rw [← hy, ← pos n, cancel n]
end PiExponentSeshadri.LaurentCech

namespace PiExponentSeshadri.LaurentLattices

section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance : IsPrincipalIdealRing K[T;T⁻¹] where
  principal I := by
    obtain ⟨a,ha⟩ := (IsPrincipalIdealRing.principal (I.under K[X])).principal
    refine ⟨⟨algebraMap K[X] K[T;T⁻¹] a, ?_⟩⟩
    rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : K[X]))
      K[T;T⁻¹] I, ha, Ideal.map_span, Set.image_singleton]

def boundedBelow {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (l : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Ici l)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

def boundedAbove {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (u : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Iic u)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

variable {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

lemma mem_boundedBelow (b : Basis ι K[T;T⁻¹] M) (l : ℤ) (x : M) :
    x ∈ boundedBelow b l ↔ ∀ i z, z < l → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedBelow, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Ici, not_le]

lemma mem_boundedAbove (b : Basis ι K[T;T⁻¹] M) (u : ℤ) (x : M) :
    x ∈ boundedAbove b u ↔ ∀ i z, u < z → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedAbove, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Iic, not_le]

lemma coeff_T_mul (p : K[T;T⁻¹]) (n z : ℤ) :
    (T n * p).coeff z = p.coeff (z-n) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  omega

lemma below_shift (b : Basis ι K[T;T⁻¹] M) (l : ℤ) {x : M}
    (hx : x ∈ boundedBelow b l) (n : ℕ) :
    (T (n : ℤ) : K[T;T⁻¹]) • x ∈ boundedBelow b l := by
  rw [mem_boundedBelow] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

lemma above_shift (b : Basis ι K[T;T⁻¹] M) (u : ℤ) {x : M}
    (hx : x ∈ boundedAbove b u) (n : ℕ) :
    (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ boundedAbove b u := by
  rw [mem_boundedAbove] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

theorem band_finite [Fintype ι] (b : Basis ι K[T;T⁻¹] M) (l u : ℤ) :
    Module.Finite K ↥(boundedBelow b l ⊓ boundedAbove b u) := by
  classical
  let W := boundedBelow b l ⊓ boundedAbove b u
  let J := ι × ↥(Finset.Icc l u)
  let φ : W →ₗ[K] (J → K) := LinearMap.pi (fun j =>
    (Finsupp.lapply j.2.val).comp ((AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap.comp
      ((((Finsupp.lapply j.1).comp b.repr.toLinearMap).restrictScalars K).comp W.subtype)))
  apply Module.Finite.of_injective φ
  intro x y hxy
  apply Subtype.ext
  apply b.repr.injective
  ext i z
  by_cases hzL : z < l
  · rw [(mem_boundedBelow b l x.val).mp x.property.1 i z hzL,
      (mem_boundedBelow b l y.val).mp y.property.1 i z hzL]
  · by_cases hzU : u < z
    · rw [(mem_boundedAbove b u x.val).mp x.property.2 i z hzU,
        (mem_boundedAbove b u y.val).mp y.property.2 i z hzU]
    · exact congrFun hxy (i,⟨z,Finset.mem_Icc.mpr (by omega)⟩)

lemma finite_generators_bounded [Fintype ι] {κ : Type*} [Fintype κ]
    (b : Basis ι K[T;T⁻¹] M) (s : κ → M) :
    ∃ l u : ℤ, ∀ j, s j ∈ boundedBelow b l ∧ s j ∈ boundedAbove b u := by
  classical
  let S : Set ℤ := ⋃ i, ⋃ j, (↑((b.repr (s j)) i).coeff.support : Set ℤ)
  have hS : S.Finite := Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    Finset.finite_toSet _
  obtain ⟨l,hl⟩ := hS.bddBelow
  obtain ⟨u,hu⟩ := hS.bddAbove
  refine ⟨l,u,fun j => ⟨?_,?_⟩⟩
  · rw [mem_boundedBelow]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hl hm)
  · rw [mem_boundedAbove]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hu hm)

theorem intersection_finite [Module.Finite K[T;T⁻¹] M]
    [Module.IsTorsionFree K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let b := Module.Free.chooseBasis K[T;T⁻¹] M
  obtain ⟨l,_,hs⟩ := finite_generators_bounded b s
  obtain ⟨_,u,ht⟩ := finite_generators_bounded b t
  have hbelow : A ≤ boundedBelow b l := hA.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact below_shift b l (hs j).1 n))
  have habove : B ≤ boundedAbove b u := hB.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact above_shift b u (ht j).2 n))
  let := band_finite b l u
  exact Module.Finite.of_injective (Submodule.inclusion (inf_le_inf hbelow habove))
    (Submodule.inclusion_injective _)

end

section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance laurent_finiteType : Algebra.FiniteType K K[T;T⁻¹] := by
  let : IsScalarTower K K[X] K[T;T⁻¹] := IsScalarTower.of_algebraMap_eq (fun c => by
    simp only [Polynomial.algebraMap_eq, algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
      ← LaurentPolynomial.C_eq_algebraMap])
  let : Algebra.FinitePresentation K[X] K[T;T⁻¹] :=
    IsLocalization.Away.finitePresentation (Polynomial.X : K[X])
  let : Algebra.FiniteType K[X] K[T;T⁻¹] := inferInstance
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K K[X]) inferInstance

lemma quotient_finite (a : K[T;T⁻¹]) (ha : a ≠ 0) :
    Module.Finite K (K[T;T⁻¹] ⧸ Ideal.span {a}) := by
  have hlen := isFiniteLength_quotient_span_singleton K[T;T⁻¹]
    (mem_nonZeroDivisors_of_ne_zero ha)
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  let : IsArtinianRing (K[T;T⁻¹] ⧸ Ideal.span {a}) :=
    isArtinian_of_tower K[T;T⁻¹] inferInstance
  exact Module.finite_of_isArtinianRing K _

theorem torsion_finite {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M] [Module.Finite K[T;T⁻¹] M]
    (hM : Module.IsTorsion K[T;T⁻¹] M) : Module.Finite K M := by
  obtain ⟨a,ha,hn⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hkill : Module.IsTorsionBy K[T;T⁻¹] M a := fun x =>
    Submodule.mem_annihilator.mp ha x trivial
  let hset : Module.IsTorsionBySet K[T;T⁻¹] M (Ideal.span {a}) :=
    (Module.isTorsionBySet_span_singleton_iff a).mpr hkill
  let := hset.module
  let : IsScalarTower K[T;T⁻¹] (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : IsScalarTower K (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : Module.Finite (K[T;T⁻¹] ⧸ Ideal.span {a}) M :=
    Module.Finite.of_restrictScalars_finite K[T;T⁻¹] _ M
  let := quotient_finite a (nonZeroDivisors.ne_zero hn)
  exact Module.Finite.trans (K[T;T⁻¹] ⧸ Ideal.span {a}) M
end

section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

theorem intersection_finite_general [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let D := Submodule.torsion K[T;T⁻¹] M
  let q := D.mkQ.restrictScalars K
  let : Module.Finite K D := torsion_finite Submodule.torsion_isTorsion
  have ha : A.map q ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • q (s j.1))) := by
    apply (Submodule.map_mono hA).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  have hb : B.map q ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • q (t j.1))) := by
    apply (Submodule.map_mono hB).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  let := intersection_finite (A.map q) (B.map q) (fun i => q (s i))
    (fun i => q (t i)) ha hb
  let f : ↥(A ⊓ B) →ₗ[K] ↥(A.map q ⊓ B.map q) :=
    (q.comp (A ⊓ B).subtype).codRestrict _ (fun x =>
      ⟨Submodule.mem_map.mpr ⟨x.val,x.property.1,rfl⟩,
        Submodule.mem_map.mpr ⟨x.val,x.property.2,rfl⟩⟩)
  let g : f.ker →ₗ[K] D :=
    (((A ⊓ B).subtype.comp f.ker.subtype).codRestrict (D.restrictScalars K)
      (fun x => by
        have h : q x.val.val = 0 := congrArg Subtype.val x.property
        exact (Submodule.Quotient.mk_eq_zero D).mp h))
  let : Module.Finite K f.ker := Module.Finite.of_injective g (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : D => (z : M)) h)
  let : Module.Finite K (↥(A ⊓ B) ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient f.ker
end

open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K N Q : Type*} [Field K] [AddCommGroup N] [AddCommGroup Q]
  [Module K N] [Module K Q] [Module K[X] N] [IsScalarTower K K[X] N]
  [Module K[T;T⁻¹] Q] [IsScalarTower K K[T;T⁻¹] Q]

omit [IsScalarTower K K[T;T⁻¹] Q] in
lemma range_le_lattice {ι : Type*} [Fintype ι] (s : ι → N)
    (hs : Submodule.span K[X] (Set.range s) = ⊤) (g : N →ₗ[K] Q) (d : ℤ)
    (hpow : ∀ (n : ℕ) (x : N), g ((Polynomial.X : K[X])^n • x) =
      (T (d*n) : K[T;T⁻¹]) • g x) :
    g.range ≤ Submodule.span K (Set.range (fun j : ι × ℕ =>
      (T (d*j.2) : K[T;T⁻¹]) • g (s j.1))) := by
  classical
  rintro _ ⟨x,rfl⟩
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    (show x ∈ Submodule.span K[X] (Set.range s) from hs ▸ trivial)
  rw [← hf, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [← Polynomial.sum_C_mul_X_pow_eq (f i), Polynomial.sum, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul, map_smul, hpow]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,n),rfl⟩)

theorem range_intersection_finite [Module.Finite K[X] N]
    {P : Type*} [AddCommGroup P] [Module K P] [Module K[X] P]
    [IsScalarTower K K[X] P] [Module.Finite K[X] P]
    [Module.Finite K[T;T⁻¹] Q]
    (f : N →ₗ[K] Q) (g : P →ₗ[K] Q)
    (hf : ∀ x, f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x)
    (hg : ∀ x, g ((Polynomial.X : K[X]) • x) = (T (-1) : K[T;T⁻¹]) • g x) :
    Module.Finite K ↥(f.range ⊓ g.range) := by
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[X]) (M := N)
  obtain ⟨m,t,ht⟩ := Module.Finite.exists_fin (R := K[X]) (M := P)
  have hp (j : ℕ) (x : N) : f ((Polynomial.X : K[X])^j • x) =
      (T (1*(j : ℤ)) : K[T;T⁻¹]) • f x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hf, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  have hn (j : ℕ) (x : P) : g ((Polynomial.X : K[X])^j • x) =
      (T ((-1)*(j : ℤ)) : K[T;T⁻¹]) • g x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hg, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  apply intersection_finite_general f.range g.range (fun i => f (s i)) (fun i => g (t i))
  · simpa only [one_mul] using range_le_lattice s hs f 1 hp
  · simpa only [neg_one_mul] using range_le_lattice t ht g (-1) hn
end PiExponentSeshadri.LaurentLattices

namespace PiExponentSeshadri.LaurentCech
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

theorem intersection_finite [Module.Finite K[X] N] [Module.Finite K[X] P]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y) :
    Module.Finite K ↥((f.restrictScalars K).range ⊓ g.range) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentLattices.range_intersection_finite (f.restrictScalars K) g
  · intro x
    change f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x
    rw [map_smul, pos1]
  · intro y
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
end PiExponentSeshadri.LaurentCech

end

end OAI
