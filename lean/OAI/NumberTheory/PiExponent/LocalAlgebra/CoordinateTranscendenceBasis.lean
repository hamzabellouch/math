import Mathlib.Algebra.MvPolynomial.Degrees
import OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity
import OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential

namespace OAI

noncomputable section
namespace PiExponent
open MvPolynomial
open NormalBasisRigidity

section Linear
variable {K ι : Type*} [Field K] [Fintype ι]

theorem normalBasis_complement_surjective (T : Submodule K (ι → K))
    (A : Finset ι)
    (hA : IsNormalBasis (K := K) (fun i => T.mkQ (Pi.basisFun K ι i)) A) :
    Function.Surjective (fun t : T => fun i : {i // i ∉ A} => t.val i.val) := by
  classical
  have hli : LinearIndependent K (fun i : A => T.mkQ (Pi.basisFun K ι i)) := hA.1
  let b : Module.Basis A K ((ι → K) ⧸ T) := Module.Basis.mk hli (by
    have hr : Set.range (fun i : A => T.mkQ (Pi.basisFun K ι i)) =
        (fun i => T.mkQ (Pi.basisFun K ι i)) '' (A : Set ι) := by ext; simp
    change ⊤ ≤ Submodule.span K (Set.range (fun i : A => T.mkQ (Pi.basisFun K ι i)))
    rw [hr, hA.2])
  intro g
  let u : ι → K := fun i => if hi : i ∈ A then 0 else g ⟨i, hi⟩
  let w : ι → K := ∑ i : A, b.repr (T.mkQ u) i • Pi.basisFun K ι i.val
  have hw : T.mkQ w = T.mkQ u := by
    change T.mkQ (∑ i : A, _) = _
    simp only [map_sum, map_smul]
    simpa only [b, Module.Basis.mk_apply] using b.sum_repr (T.mkQ u)
  have ht : u - w ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change T.mkQ (u - w) = 0
    rw [map_sub, hw, sub_self]
  refine ⟨⟨u - w, ht⟩, ?_⟩
  funext i
  have hw0 : w i.val = 0 := by
    dsimp [w]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro a _
    have hn : a.val ≠ i.val := fun he => i.property (he ▸ a.property)
    simp [Pi.basisFun_apply, Ne.symm hn]
  change u i.val - w i.val = g i
  simp [u, i.property, hw0]

theorem normalBasis_complement_injective (T : Submodule K (ι → K))
    (A : Finset ι)
    (hA : IsNormalBasis (K := K) (fun i => T.mkQ (Pi.basisFun K ι i)) A) :
    Function.Injective (fun t : T => fun i : {i // i ∉ A} => t.val i.val) := by
  classical
  suffices hz : ∀ t : T, (∀ i, i ∉ A → t.val i = 0) → t = 0 by
    intro t u h
    have hd : t - u = 0 := hz (t - u) (by
      intro i hi
      exact sub_eq_zero.mpr (congrFun h ⟨i,hi⟩))
    exact sub_eq_zero.mp hd
  intro t ht
  have he : (∑ a : A, t.val a.val • Pi.basisFun K ι a.val) = t.val := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply]
    by_cases hi : i ∈ A
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : A)]
      · simp
      · intro a _ hn
        have hn' : a.val ≠ i := fun h => hn (Subtype.ext h)
        simp [Ne.symm hn']
      · simp
    · simp [ht i hi, show ∀ a : A, a.val ≠ i from fun a h => hi (h ▸ a.property)]
  have hs : (∑ a : A, t.val a.val • T.mkQ (Pi.basisFun K ι a.val)) = 0 := by
    calc
      _ = T.mkQ (∑ a : A, t.val a.val • Pi.basisFun K ι a.val) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [he]; exact (Submodule.Quotient.mk_eq_zero T).mpr t.property
  have hall := (Fintype.linearIndependent_iff.mp hA.1) _ hs
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ A
  · exact hall ⟨i,hi⟩
  · exact ht i hi

end Linear

section PolynomialChain
variable {C E ι κ : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι] [Fintype κ]

theorem polynomialGradient_mul (φ : MvPolynomial ι C →ₐ[C] E) (t : ι → E)
    (p q : MvPolynomial ι C) :
    (∑ i, φ (pderiv i (p*q)) * t i) =
      φ p * (∑ i, φ (pderiv i q) * t i) +
      φ q * (∑ i, φ (pderiv i p) * t i) := by
  simp only [pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem polynomialGradient_rename (φ : MvPolynomial ι C →ₐ[C] E) (t : ι → E)
    (f : κ → ι) (p : MvPolynomial κ C) :
    (∑ i, φ (pderiv i (rename f p)) * t i) =
      ∑ j, φ (rename f (pderiv j p)) * t (f j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, polynomialGradient_mul, hp]
    have hgrad : (∑ i, φ (pderiv i (rename f (X j))) * t i) = t (f j) := by
      simp [Pi.single_apply]
    rw [hgrad]
    let ψ : MvPolynomial κ C →ₐ[C] E := φ.comp (rename f)
    have hR := polynomialGradient_mul ψ (t ∘ f) p (X j)
    change _ = ∑ i, ψ (pderiv i (p * X j)) * (t ∘ f) i
    rw [hR]
    simp [ψ, Pi.single_apply]

end PolynomialChain

section KernelCriterion
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

omit [CharZero C] in
theorem pderiv_totalDegree_lt_of_pos (p : MvPolynomial ι C) (hp : 0 < p.totalDegree)
    (i : ι) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  apply lt_of_le_of_lt (show (pderiv i p).totalDegree ≤ p.totalDegree - 1 from ?_)
    (Nat.sub_lt hp (by omega))
  apply Finset.sup_le
  intro m hm
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have hh := (mem_support_iff.mp hm)
    rw [coeff_pderiv] at hh
    exact (mul_ne_zero_iff.mp hh).1
  have hb := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) =
      m.sum (fun _ e => e) + 1 := by
    simp [Finsupp.sum_fintype, Finset.sum_add_distrib]
  rw [hsum] at hb
  omega

theorem eq_C_of_pderiv_eq_zero (p : MvPolynomial ι C)
    (hp : ∀ i, pderiv i p = 0) : p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m; simp
  · rw [coeff_C, ite_eq_right (Ne.symm hm)]
    have hex : ∃ i, m i ≠ 0 := by
      by_contra! h
      apply hm
      ext i
      exact h i
    obtain ⟨i, hi'⟩ := hex
    have hc := congrArg (fun p : MvPolynomial ι C => p.coeff (m - Finsupp.single i 1)) (hp i)
    rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi'] at hc
    have hpos : 0 < ((m - Finsupp.single i 1 : ι →₀ ℕ) i) + 1 := by omega
    have hn : ((((m - Finsupp.single i 1 : ι →₀ ℕ) i) : C) + 1) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    exact (mul_eq_zero.mp hc).resolve_right hn

theorem algebraicIndependent_of_pderiv_kernel (x : ι → E)
    (hker : ∀ p : MvPolynomial ι C, aeval x p = 0 →
      ∀ i, aeval x (pderiv i p) = 0) : AlgebraicIndependent C x := by
  apply algebraicIndependent_iff.mpr
  intro p
  induction hp : p.totalDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hz
    by_cases hn : n = 0
    · have he := totalDegree_eq_zero_iff_eq_C.mp (hp.trans hn)
      rw [he, aeval_C] at hz
      have hconstant : p.coeff 0 = 0 := (algebraMap C E).injective (by simpa using hz)
      rw [he, hconstant, map_zero]
    · have hpartials : ∀ i, pderiv i p = 0 := by
        intro i
        exact ih _ (hp ▸ pderiv_totalDegree_lt_of_pos p (by omega) i)
          _ rfl (hker p hz i)
      have he := eq_C_of_pderiv_eq_zero p hpartials
      rw [he, aeval_C] at hz
      have hconstant : p.coeff 0 = 0 := (algebraMap C E).injective (by simpa using hz)
      rw [he, hconstant, map_zero]


theorem normalBasis_complement_algebraicIndependent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 → p ∈ Q)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)) A) :
    AlgebraicIndependent C (fun i : {i // i ∉ A} => φ (X i.val)) := by
  classical
  let x : {i // i ∉ A} → E := fun i => φ (X i.val)
  have hφ (p : MvPolynomial {i // i ∉ A} C) : φ (rename Subtype.val p) = aeval x p := by
    have he : φ.comp (rename Subtype.val) = aeval x := by ext i; simp [x]
    exact AlgHom.congr_fun he p
  apply algebraicIndependent_of_pderiv_kernel
  intro p hp j
  obtain ⟨t,ht⟩ := normalBasis_complement_surjective (polynomialTangent φ Q) A hA
    (Pi.single j 1)
  have hmem : rename Subtype.val p ∈ Q := hker _ ((hφ p).trans hp)
  have heq : (∑ i, φ (pderiv i (rename Subtype.val p)) * t.val i) = 0 := by
    exact congrFun t.property ⟨rename Subtype.val p,hmem⟩
  rw [polynomialGradient_rename] at heq
  have hv : ∀ i : {i // i ∉ A}, t.val i.val = (Pi.single j (1 : E) : {i // i ∉ A} → E) i := by
    intro i
    exact congrFun ht i
  simpa [hv, hφ, Pi.single_apply, x] using heq

end KernelCriterion

section Algebraicity
open KaehlerDifferential
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

omit [CharZero C] [Fintype ι] in
theorem derivation_eq_zero_of_field_generators
    (x : ι → E) (hgen : IntermediateField.adjoin C (Set.range x) = ⊤)
    (d : Derivation C E E) (hd : ∀ i, d (x i) = 0) : d = 0 := by
  have hp : ∀ a ∈ Algebra.adjoin C (Set.range x), d a = 0 := by
    exact Derivation.eqOn_adjoin (D1 := d) (D2 := 0) (by rintro _ ⟨i,rfl⟩; exact hd i)
  apply Derivation.ext
  intro z
  have hz : z ∈ IntermediateField.adjoin C (Set.range x) := by rw [hgen]; trivial
  obtain ⟨a,ha,b,hb,rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  change d (a / b) = 0
  rw [d.leibniz_div, hp a ha, hp b hb, smul_zero, smul_zero, sub_self, smul_zero]

theorem normalBasis_complement_isAlgebraic
    [Algebra.EssFiniteType C E]
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0)
    (hgen : IntermediateField.adjoin C (Set.range (fun i => φ (X i))) = ⊤)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent (φ) Q).mkQ
        (Pi.basisFun (E) ι i)) A) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin C
        (Set.range (fun i : {i // i ∉ A} => φ (X i.val))))
      (E) := by
  classical
  let K := IntermediateField.adjoin C
    (Set.range (fun i : {i // i ∉ A} => φ (X i.val)))
  have hdzero (d : Derivation K E E) : d = 0 := by
    let dC := d.restrictScalars C
    let t : polynomialTangent (φ) Q :=
      ⟨(fun i => dC (φ (X i))),
        derivation_mem_polynomialTangent _ _ hQ dC⟩
    have ht : t = 0 := normalBasis_complement_injective _ A hA (by
      funext i
      change d (φ (X i.val)) = 0
      let k : K := ⟨φ (X i.val),
        IntermediateField.subset_adjoin C _ (Set.mem_range_self i)⟩
      exact d.map_algebraMap k)
    have hc : ∀ i, dC (φ (X i)) = 0 := by
      intro i
      exact congrFun (congrArg Subtype.val ht) i
    have hh := derivation_eq_zero_of_field_generators (fun i => φ (X i)) hgen dC hc
    ext z
    exact DFunLike.congr_fun hh z
  let : Algebra.EssFiniteType K E := Algebra.EssFiniteType.of_comp C K E
  constructor
  intro z
  have hz : D K E z = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff E _).mp
    intro l
    let d : Derivation K E E := l.compDer (D K E)
    exact DFunLike.congr_fun (hdzero d) z
  exact isAlgebraic_of_logarithmic_differential (C := K) (0 : E) z (by rw [map_zero, hz, smul_zero])

end Algebraicity

section TranscendenceBasis
open scoped IntermediateField.algebraAdjoinAdjoin
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem normalBasis_complement_isTranscendenceBasis
    [Algebra.EssFiniteType C E]
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p, φ p = 0 ↔ p ∈ Q)
    (hgen : IntermediateField.adjoin C (Set.range (fun i => φ (X i))) = ⊤)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)) A) :
    IsTranscendenceBasis C (fun i : {i // i ∉ A} => φ (X i.val)) := by
  have hind := normalBasis_complement_algebraicIndependent φ Q
    (fun p => (hQ p).mp) A hA
  apply hind.isTranscendenceBasis_iff_isAlgebraic.mpr
  let K := IntermediateField.adjoin C
    (Set.range (fun i : {i // i ∉ A} => φ (X i.val)))
  let : Algebra.IsAlgebraic K E := normalBasis_complement_isAlgebraic φ Q
    (fun p => (hQ p).mpr) hgen A hA
  exact Algebra.IsAlgebraic.trans _ K E

end TranscendenceBasis

variable {C ι : Type*} [Field C] [Fintype ι]

omit [Fintype ι] in

theorem polynomialResidueMap_field_generation
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    IntermediateField.adjoin C (Set.range (fun i => polynomialResidueMap Q (X i))) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a,b,hb,hz⟩ := IsFractionRing.div_surjective (MvPolynomial ι C ⧸ Q) z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : aeval (fun i => polynomialResidueMap Q (X i)) = polynomialResidueMap Q := by
    ext i
    simp
  apply (IntermediateField.mem_adjoin_range_iff C _ z).mpr
  refine ⟨a,b,?_⟩
  rw [he]
  exact hz.symm

theorem primeNormalBasis_complement_isTranscendenceBasis
    [CharZero C] (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (A : Finset ι)
    (hA : IsNormalBasis (K := PolynomialResidueField Q)
      (fun i => (polynomialTangent (polynomialResidueMap Q) Q).mkQ
        (Pi.basisFun (PolynomialResidueField Q) ι i)) A) :
    IsTranscendenceBasis C
      (fun i : {i // i ∉ A} => polynomialResidueMap Q (X i.val)) :=
  normalBasis_complement_isTranscendenceBasis (polynomialResidueMap Q) Q
    (polynomialResidueMap_eq_zero_iff Q) (polynomialResidueMap_field_generation Q) A hA


omit [Fintype ι] in

theorem idealResidueMap_field_generation
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    IntermediateField.adjoin C
      (Set.range (fun i => algebraMap (MvPolynomial ι C) Q.ResidueField (X i))) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a,b,hb,hz⟩ := IsFractionRing.div_surjective (MvPolynomial ι C ⧸ Q) z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : aeval (fun i => algebraMap (MvPolynomial ι C) Q.ResidueField (X i)) =
      IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField := by
    ext i
    simp
  apply (IntermediateField.mem_adjoin_range_iff C _ z).mpr
  refine ⟨a,b,?_⟩
  rw [he]
  simpa only [IsScalarTower.coe_toAlgHom', Ideal.algebraMap_quotient_residueField_mk] using hz.symm

theorem idealResidueNormalBasis_complement_isTranscendenceBasis
    [CharZero C] (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (A : Finset ι)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField) Q).mkQ
          (Pi.basisFun Q.ResidueField ι i)) A) :
    IsTranscendenceBasis C
      (fun i : {i // i ∉ A} => algebraMap (MvPolynomial ι C) Q.ResidueField (X i.val)) := by
  let : Algebra.EssFiniteType C Q.ResidueField :=
    .comp C (MvPolynomial ι C) Q.ResidueField
  exact normalBasis_complement_isTranscendenceBasis
    (IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField) Q
    (fun _ => Ideal.algebraMap_residueField_eq_zero)
    (idealResidueMap_field_generation Q) A hA

end PiExponent

end

end OAI
