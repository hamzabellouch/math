import OAI.Combinatorics.EuclideanRamsey.StencilConvolution

namespace OAI

universe uRing uGroup uSemigroup uModule uModuleTarget uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

open scoped TensorProduct
namespace EuclideanRamsey

section NilpotentLog
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
open Finset

lemma nil_exp_quadratic {a : R} (ha : IsNilpotent a) :
    ∃ b : R, IsNilpotent b ∧ IsNilpotent.exp a = 1 + a * (1 + b) := by
  obtain ⟨n, hn⟩ := ha
  let c : R := ∑ i ∈ range n, ((i + 2).factorial : ℚ)⁻¹ • a ^ i
  refine ⟨a * c, ?_, ?_⟩
  · exact ⟨n, by rw [mul_pow, hn, zero_mul]⟩
  · rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn)]
    rw [show n + 2 = 2 + n by omega, sum_range_add]
    have h2 : (∑ i ∈ range 2, (i.factorial : ℚ)⁻¹ • a ^ i) = 1 + a := by
      simp [sum_range_succ]
    rw [h2]
    have ht : (∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ (2 + i)) = a ^ 2 * c := by
      simp only [c, mul_sum, pow_add, mul_smul_comm, add_comm 2, mul_comm]
    rw [ht]
    ring

lemma nil_exp_eq_one_iff {a : R} (ha : IsNilpotent a) :
    IsNilpotent.exp a = 1 ↔ a = 0 := by
  obtain ⟨b, hb, he⟩ := nil_exp_quadratic ha
  rw [he]
  constructor
  · intro h
    have hmul : a * (1 + b) = 0 := by linear_combination h
    exact hb.isUnit_one_add.mul_right_cancel (by simpa using hmul)
  · intro h
    simp [h]

lemma nil_exp_sub_one_sub_mem {J : Ideal R} {a : R} (ha : IsNilpotent a) (hJ : a ∈ J) :
    IsNilpotent.exp a - 1 - a ∈ J ^ 2 := by
  obtain ⟨n, hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn)]
  rw [show n + 2 = 2 + n by omega, sum_range_add]
  have h2 : (∑ i ∈ range 2, (i.factorial : ℚ)⁻¹ • a ^ i) = 1 + a := by
    simp [sum_range_succ]
  rw [h2]
  have he : 1 + a + (∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ (2 + i)) - 1 - a =
      ∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ (2 + i) := by ring
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_left
  rw [pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hJ 2)

lemma nil_exp_sub_one_mem {J : Ideal R} {a : R} (ha : IsNilpotent a) (hJ : a ∈ J) :
    IsNilpotent.exp a - 1 ∈ J := by
  have h2 := nil_exp_sub_one_sub_mem ha hJ
  have hle : J ^ 2 ≤ J := Ideal.pow_le_self (by omega)
  have := J.add_mem (hle h2) hJ
  simpa only [sub_add_cancel] using this

omit [Algebra ℚ R] in
lemma nilpotent_of_mem_nil_ideal {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)
    {x : R} (hx : x ∈ I) : IsNilpotent x := by
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hx n
  simpa only [hI, Ideal.mem_bot] using this

lemma nil_ideal_exp_surjective {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)
    {z : R} (hz : z ∈ I) : ∃ x ∈ I, IsNilpotent.exp x = 1 + z := by
  have happrox : ∀ k : ℕ, ∃ x ∈ I, IsNilpotent.exp x - (1 + z) ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, I.zero_mem, ?_⟩
      simpa using I.neg_mem hz
    | succ k ih =>
      obtain ⟨x, hx, he⟩ := ih
      let e := (1 + z) - IsNilpotent.exp x
      have he' : e ∈ I ^ (k + 1) := by simpa only [e, neg_sub] using (I ^ (k + 1)).neg_mem he
      have hp : I ^ (k + 1) ≤ I := Ideal.pow_le_self (by omega)
      have hei : e ∈ I := hp he'
      have hnx := nilpotent_of_mem_nil_ideal hI hx
      have hne := nilpotent_of_mem_nil_ideal hI hei
      refine ⟨x + e, I.add_mem hx hei, ?_⟩
      rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hne]
      let r := IsNilpotent.exp e - 1 - e
      have hr : r ∈ (I ^ (k + 1)) ^ 2 := nil_exp_sub_one_sub_mem hne he'
      have hle : (I ^ (k + 1)) ^ 2 ≤ I ^ (k + 2) := by
        rw [← pow_mul]
        exact Ideal.pow_le_pow_right (by omega)
      have hterm1 : (IsNilpotent.exp x - 1) * e ∈ I ^ (k + 2) := by
        have hh := Ideal.mul_mem_mul (nil_exp_sub_one_mem hnx hx) he'
        simpa only [← pow_succ', Nat.add_assoc] using hh
      have hterm2 : IsNilpotent.exp x * r ∈ I ^ (k + 2) :=
        Ideal.mul_mem_left _ _ (hle hr)
      have hh := (I ^ (k + 2)).add_mem hterm1 hterm2
      convert hh using 1 ; dsimp [r, e] ; ring
  obtain ⟨x, hx, he⟩ := happrox n
  have hp : I ^ (n + 1) = ⊥ := by simp [pow_succ, hI]
  rw [hp, Ideal.mem_bot, sub_eq_zero] at he
  exact ⟨x, hx, he⟩

end NilpotentLog

section LogCharacter
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
  {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)

include hI in
lemma nil_exp_injective {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (he : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hna := nilpotent_of_mem_nil_ideal hI ha
  have hnb := nilpotent_of_mem_nil_ideal hI hb
  have hnd := nilpotent_of_mem_nil_ideal hI (I.sub_mem ha hb)
  apply sub_eq_zero.mp
  apply (nil_exp_eq_one_iff hnd).mp
  rw [sub_eq_add_neg, IsNilpotent.exp_add_of_commute (Commute.all _ _) hna hnb.neg,
    he, hnb.exp_mul_exp_neg_self]

variable {G : Type uGroup} [AddCommGroup G] (χ : Multiplicative G →* R)
  (hχ : ∀ γ : G, χ (Multiplicative.ofAdd γ) - 1 ∈ I)

noncomputable def characterLog (γ : G) : R :=
  Classical.choose (nil_ideal_exp_surjective hI (hχ γ))

lemma characterLog_mem (γ : G) : characterLog hI χ hχ γ ∈ I :=
  (Classical.choose_spec (nil_ideal_exp_surjective hI (hχ γ))).1

lemma characterLog_exp (γ : G) :
    IsNilpotent.exp (characterLog hI χ hχ γ) = χ (Multiplicative.ofAdd γ) := by
  have := (Classical.choose_spec (nil_ideal_exp_surjective hI (hχ γ))).2
  simpa only [characterLog, add_sub_cancel] using this

noncomputable def characterLogHom : G →+ R where
  toFun := characterLog hI χ hχ
  map_zero' := by
    apply nil_exp_injective hI (characterLog_mem ..) I.zero_mem
    rw [characterLog_exp, IsNilpotent.exp_zero]
    exact χ.map_one
  map_add' a b := by
    apply nil_exp_injective hI (characterLog_mem ..)
      (I.add_mem (characterLog_mem ..) (characterLog_mem ..))
    rw [characterLog_exp, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      (nilpotent_of_mem_nil_ideal hI (characterLog_mem ..))
      (nilpotent_of_mem_nil_ideal hI (characterLog_mem ..)), characterLog_exp, characterLog_exp]
    exact χ.map_mul _ _

lemma characterLog_map_zero {S : Type uSemigroup} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (γ : G) (h : f (χ (Multiplicative.ofAdd γ)) = 1) :
    f (characterLogHom hI χ hχ γ) = 0 := by
  have hn := nilpotent_of_mem_nil_ideal hI (characterLog_mem hI χ hχ γ)
  apply (nil_exp_eq_one_iff (hn.map f)).mp
  rw [← hn.map_exp f, characterLog_exp, h]

end LogCharacter

section LatticeLog
variable {k : ℕ} {R : Type uRing} [CommRing R] [Algebra ℚ R]

def rationalExtension (f : (Fin k → ℤ) →+ R) : (Fin k → ℚ) →ₗ[ℚ] R where
  toFun v := ∑ j, v j • f (Pi.single j 1)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [mul_smul, Finset.smul_sum]

lemma rationalExtension_lattice (f : (Fin k → ℤ) →+ R) (γ : Fin k → ℤ) :
    rationalExtension f (fun j => (γ j : ℚ)) = f γ := by
  dsimp [rationalExtension]
  simp_rw [Int.cast_smul_eq_zsmul, ← map_zsmul]
  rw [← map_sum]
  congr 1
  convert Finset.univ_sum_single γ using 1
  congr 1
  ext j
  rw [← Pi.single_smul]
  simp

lemma rationalExtension_mem {I : Ideal R} (f : (Fin k → ℤ) →+ R)
    (hf : ∀ γ, f γ ∈ I) (v : Fin k → ℚ) : rationalExtension f v ∈ I := by
  change (∑ j, v j • f (Pi.single j 1)) ∈ I
  apply I.sum_mem
  intro j hj
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ (hf _)

end LatticeLog

section AdicLifting
variable {R : Type uRing} {M : Type uModule} {N : Type uModuleTarget} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R N]

lemma adic_kernel_lifting (I : Ideal R) (f : M →ₗ[R] N) (q : ℕ) :
    ∃ n : ℕ, ∀ x : M, f x ∈ I ^ n • (⊤ : Submodule R N) →
      ∃ y : M, f y = 0 ∧ x - y ∈ I ^ q • (⊤ : Submodule R M) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k + q, ?_⟩
  intro x hx
  have hfx : f x ∈ I ^ (k + q) • (⊤ : Submodule R N) ⊓ LinearMap.range f :=
    ⟨hx, ⟨x, rfl⟩⟩
  rw [hk (k + q) (by omega), Nat.add_sub_cancel_left] at hfx
  have hle : I ^ q • (I ^ k • (⊤ : Submodule R N) ⊓ LinearMap.range f) ≤
      I ^ q • LinearMap.range f := smul_mono_right _ inf_le_right
  have hf' : f x ∈ I ^ q • LinearMap.range f := hle hfx
  have hm : I ^ q • LinearMap.range f = Submodule.map f (I ^ q • (⊤ : Submodule R M)) := by
    rw [Submodule.map_smul'']
    simp
  rw [hm] at hf'
  obtain ⟨z, hz, he⟩ := hf'
  refine ⟨x - z, ?_, ?_⟩
  · rw [map_sub, he, sub_self]
  · simpa using hz

end AdicLifting

section IntersectionLifting
variable {R : Type uRing} [CommRing R] [IsNoetherianRing R]
  {ι : Type uIndex} [Fintype ι] (I : Ideal R) (J : ι → Ideal R)

lemma adic_intersection_lifting (q : ℕ) :
    ∃ n : ℕ, ∀ x : R, (∀ i, x ∈ J i ⊔ I ^ n) →
      ∃ y : R, (∀ i, y ∈ J i) ∧ x - y ∈ I ^ q := by
  classical
  let f : R →ₗ[R] (∀ i, R ⧸ J i) := LinearMap.pi (fun i => Algebra.linearMap R (R ⧸ J i))
  obtain ⟨n, hn⟩ := adic_kernel_lifting I f q
  refine ⟨n, fun x hx => ?_⟩
  have hm : f x ∈ I ^ n • (⊤ : Submodule R (∀ i, R ⧸ J i)) := by
    have hz : ∀ i, ∃ z ∈ I ^ n, (Ideal.Quotient.mk (J i)) z = (Ideal.Quotient.mk (J i)) x := by
      intro i
      obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hx i)
      refine ⟨z, hz, ?_⟩
      rw [← he, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hy, zero_add]
    choose z hz he using hz
    have he' : f x = ∑ i, z i • Pi.single i (1 : R ⧸ J i) := by
      simp_rw [← Pi.single_smul, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, he]
      exact (Finset.univ_sum_single _).symm
    rw [he']
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hz i) Submodule.mem_top)
  obtain ⟨y, hy, hxy⟩ := hn x hm
  refine ⟨y, ?_, ?_⟩
  · intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrFun hy i
  · simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hxy

end IntersectionLifting

section Construction
variable {k : ℕ}

@[simp] lemma rationalExtension_single {R : Type uRing} [CommRing R] [Algebra ℚ R]
    (f : Lattice k →+ R) (a : Fin k) :
    rationalExtension f (Pi.single a 1) = f (Pi.single a 1) := by
  classical
  simp [rationalExtension, Pi.single_apply]

lemma tensor_quotient_quadratic {S : Type uSemigroup} [CommRing S] [Algebra ℚ S]
    (V : Submodule ℚ (RationalSpace k)) (C : Matrix (Fin k) (Fin k) ℚ)
    (f : RationalSpace k →ₗ[ℚ] S) (hf : V ≤ LinearMap.ker f)
    (hC : TensorProduct.map V.mkQ V.mkQ (matrixTensor C) = 0) :
    (∑ a, ∑ b, C a b • (f (Pi.single a 1) * f (Pi.single b 1))) = 0 := by
  let u := V.liftQ f hf
  let φ := (Algebra.TensorProduct.lmul' ℚ : S ⊗[ℚ] S →ₐ[ℚ] S).toLinearMap.comp
    (TensorProduct.map u u)
  have hh := congrArg φ hC
  simpa [φ, u, matrixTensor, LinearMap.comp_apply] using hh

def cosetMap (Λ : AddSubgroup (Lattice k)) :
    LatticeRing k →ₐ[ℚ] AddMonoidAlgebra ℚ (Lattice k ⧸ Λ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (QuotientAddGroup.mk' Λ)

def cosetIdeal (Λ : AddSubgroup (Lattice k)) : Ideal (LatticeRing k) :=
  RingHom.ker (cosetMap Λ)

lemma mem_cosetIdeal_iff (Λ : AddSubgroup (Lattice k)) (x : LatticeRing k) :
    x ∈ cosetIdeal Λ ↔ cosetPushforward Λ x = 0 := by
  change cosetMap Λ x = 0 ↔ _
  rw [← AddMonoidAlgebra.coeff_injective.eq_iff, AddMonoidAlgebra.coeff_zero]
  rfl

lemma monomial_sub_one_mem_cosetIdeal (Λ : AddSubgroup (Lattice k)) {γ : Lattice k}
    (hγ : γ ∈ Λ) : AddMonoidAlgebra.single γ 1 - 1 ∈ cosetIdeal Λ := by
  change cosetMap Λ (AddMonoidAlgebra.single γ 1 - 1) = 0
  rw [map_sub, map_one]
  simp only [cosetMap, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  have hh : QuotientAddGroup.mk' Λ γ = 0 := (QuotientAddGroup.eq_zero_iff γ).mpr hγ
  rw [hh]
  exact sub_self _

lemma quotient_nil_augmentation (N : ℕ) :
    (Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (augmentationIdeal : Ideal (LatticeRing k))) ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

lemma finite_order_logs (N : ℕ) :
    ∃ f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N),
      (∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal) ∧
      (∀ γ, IsNilpotent.exp (f γ) =
        (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1)) := by
  let q := Ideal.Quotient.mkₐ ℚ ((augmentationIdeal : Ideal (LatticeRing k)) ^ N)
  let χ : Multiplicative (Lattice k) →* (LatticeRing k ⧸ augmentationIdeal ^ N) :=
    q.toMonoidHom.comp (AddMonoidAlgebra.of ℚ (Lattice k))
  have hχ : ∀ γ : Lattice k, χ (Multiplicative.ofAdd γ) - 1 ∈
      Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal := by
    intro γ
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (monomial_sub_one_mem γ)
    simpa [χ, q, AddMonoidAlgebra.of_apply, map_sub] using h
  refine ⟨characterLogHom (quotient_nil_augmentation N) χ hχ, ?_, ?_⟩
  · intro γ
    exact characterLog_mem (quotient_nil_augmentation N) χ hχ γ
  · intro γ
    simpa [χ, q, AddMonoidAlgebra.of_apply, characterLogHom] using
      characterLog_exp (quotient_nil_augmentation N) χ hχ γ

lemma log_quadratic_mod_coset (N : ℕ) (f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N))
    (hf : ∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal)
    (hfexp : ∀ γ, IsNilpotent.exp (f γ) =
      (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1))
    (Λ : AddSubgroup (Lattice k)) (C : Matrix (Fin k) (Fin k) ℚ)
    (hC : quotientTensor Λ (matrixTensor C) = 0)
    (l : Fin k → LatticeRing k)
    (hl : ∀ a, (Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a) = f (Pi.single a 1)) :
    quadraticStencil C l ∈ cosetIdeal Λ ⊔ augmentationIdeal ^ N := by
  let J := cosetIdeal Λ ⊔ (augmentationIdeal : Ideal (LatticeRing k)) ^ N
  let ψ := Ideal.Quotient.factorₐ ℚ (show augmentationIdeal ^ N ≤ J from le_sup_right)
  let g := ψ.toLinearMap.comp (rationalExtension f)
  have hgγ : ∀ γ ∈ Λ, g (rationalize γ) = 0 := by
    intro γ hγ
    have hn := nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf γ)
    change ψ (rationalExtension f (rationalize γ)) = 0
    rw [show rationalize γ = (fun j => (γ j : ℚ)) from rfl, rationalExtension_lattice]
    apply (nil_exp_eq_one_iff (hn.map ψ)).mp
    rw [← hn.map_exp ψ, hfexp]
    change (Ideal.Quotient.mk J) (AddMonoidAlgebra.single γ 1) = 1
    have hm : AddMonoidAlgebra.single γ (1 : ℚ) - 1 ∈ J :=
      Ideal.mem_sup_left (monomial_sub_one_mem_cosetIdeal Λ hγ)
    have hz : (Ideal.Quotient.mk J) (AddMonoidAlgebra.single γ 1 - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  have hg : latticeSpan Λ ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    exact hgγ γ hγ
  have hquad := tensor_quotient_quadratic (latticeSpan Λ) C g hg hC
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mkₐ ℚ J) (quadraticStencil C l) = 0
  have hlj : ∀ a, (Ideal.Quotient.mkₐ ℚ J) (l a) = g (Pi.single a 1) := by
    intro a
    change ψ ((Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a)) =
      ψ (rationalExtension f (Pi.single a 1))
    rw [hl, rationalExtension_single]
  simp only [quadraticStencil, map_smul, map_sum, map_mul, hlj, hquad, smul_zero]

lemma finite_order_log_lifts (N : ℕ) (hN : 2 ≤ N)
    (f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N))
    (hf : ∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal)
    (hfexp : ∀ γ, IsNilpotent.exp (f γ) =
      (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1)) :
    ∃ l : Fin k → LatticeRing k,
      (∀ a, (Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a) = f (Pi.single a 1)) ∧
      (∀ a, mass (l a) = 0) ∧
      (∀ a b, firstMoment (l a) b = if a = b then 1 else 0) := by
  classical
  let I : Ideal (LatticeRing k) := augmentationIdeal
  let q := Ideal.Quotient.mk (I ^ N)
  let M := Ideal.map q I
  have hex : ∀ a : Fin k, ∃ x ∈ I, q x = f (Pi.single a 1) := by
    intro a
    exact (Ideal.mem_map_iff_of_surjective q (Ideal.Quotient.mk_surjective)).mp (hf _)
  choose l hlI hl using hex
  refine ⟨l, hl, fun a => (mem_augmentationIdeal _).mp (hlI a), ?_⟩
  have hker : RingHom.ker q = I ^ N := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  have hpre : Ideal.comap q (Ideal.map q (I ^ 2)) = I ^ 2 := by
    rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, hker]
    exact sup_eq_left.mpr (Ideal.pow_le_pow_right hN)
  intro a b
  let z : LatticeRing k := AddMonoidAlgebra.single (Pi.single a 1) 1 - 1
  have hdiff : l a - z ∈ I ^ 2 := by
    rw [← hpre]
    change q (l a - z) ∈ Ideal.map q (I ^ 2)
    rw [Ideal.map_pow]
    have hn := nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf (Pi.single a 1))
    have hr : IsNilpotent.exp (f (Pi.single a 1)) - 1 - f (Pi.single a 1) ∈ M ^ 2 :=
      nil_exp_sub_one_sub_mem hn (hf _)
    have hre : q (l a - z) = -(IsNilpotent.exp (f (Pi.single a 1)) - 1 - f (Pi.single a 1)) := by
      rw [hfexp, map_sub, hl]
      dsimp [z, q]
      rw [map_sub, map_one]
      ring
    rw [hre]
    exact (M ^ 2).neg_mem hr
  have hj := augmentation_sq_le_jetOne hdiff
  have hjb := hj.2 b
  simp only [firstMoment_sub, sub_eq_zero] at hjb
  rw [hjb]
  simp [z, Pi.single_apply, eq_comm]

theorem finite_lattice_identity : FiniteLatticeIdentity := by
  intro k s hk hs Λ C hCs hC
  let I : Ideal (LatticeRing k) := augmentationIdeal
  obtain ⟨n, hn⟩ := adic_intersection_lifting I (fun i => cosetIdeal (Λ i)) 3
  let N := n + 3
  obtain ⟨f, hf, hfexp⟩ := finite_order_logs (k := k) N
  obtain ⟨l, hl, hm, hfirst⟩ := finite_order_log_lifts N (by omega) f hf hfexp
  have hx : ∀ i, quadraticStencil C l ∈ cosetIdeal (Λ i) ⊔ I ^ n := by
    intro i
    apply (sup_le_sup_left (α := Ideal (LatticeRing k))
      (Ideal.pow_le_pow_right (show n ≤ N by omega)) (cosetIdeal (Λ i)))
    exact log_quadratic_mod_coset N f hf hfexp (Λ i) C (hC i) l hl
  obtain ⟨y, hy, hxy⟩ := hn (quadraticStencil C l) hx
  have he := moments_eq_of_sub_mem_cube hxy
  have hM := quadraticStencil_moments C hCs l hm hfirst
  refine ⟨y, fun i => (mem_cosetIdeal_iff _ _).mp (hy i), ?_, ?_, ?_⟩
  · exact he.1.symm.trans hM.1
  · intro a
    exact (he.2.1 a).symm.trans (hM.2.1 a)
  · intro a b
    exact (he.2.2 a b).symm.trans (hM.2.2 a b)

end Construction

end EuclideanRamsey

end

end OAI
