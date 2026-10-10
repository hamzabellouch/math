import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Hilbert.HomogeneousDeformation

namespace OAI

namespace SiegelZeros



open MvPolynomial

noncomputable section

namespace WeightedTorusJets.Geometry.GradedQuotient

variable {K σ : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

def degreeMap {I J : Ideal (MvPolynomial σ K)} (hIJ : I ≤ J) (n : ℕ) :
    degreePiece I n →ₗ[K] degreePiece J n where
  toFun x := ⟨Ideal.Quotient.factorₐ K hIJ x, by
    rcases x.property with ⟨p, hp, hpx⟩
    exact ⟨p, hp, by rw [← hpx]; rfl⟩⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (map_smul _ _ _)

theorem degreeMap_surjective {I J : Ideal (MvPolynomial σ K)} (hIJ : I ≤ J) (n : ℕ) :
    Function.Surjective (degreeMap hIJ n) := by
  rintro ⟨x, p, hp, rfl⟩
  exact ⟨⟨Ideal.Quotient.mk I p, p, hp, rfl⟩, rfl⟩

def degreeMul (I : Ideal (MvPolynomial σ K)) {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (n : ℕ) : degreePiece I n →ₗ[K] degreePiece I (d + n) where
  toFun x := ⟨Ideal.Quotient.mk I f * x, by
    rcases x.property with ⟨p, hp, hpx⟩
    refine ⟨f * p, hf.mul hp, ?_⟩
    change Ideal.Quotient.mk I (f * p) = _
    change Ideal.Quotient.mk I p = _ at hpx
    rw [map_mul, hpx]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (mul_smul_comm _ _ _)

theorem degreeMul_injective (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hreg : IsSMulRegular (MvPolynomial σ K ⧸ I) (Ideal.Quotient.mk I f)) (n : ℕ) :
    Function.Injective (degreeMul I hf n) := by
  intro x y hxy
  apply Subtype.ext
  exact hreg (congrArg Subtype.val hxy)

theorem homogeneous_mem_sup_span_iff
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f p : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d)
    (hp : p.IsHomogeneous n) (hdn : d ≤ n) :
    p ∈ I ⊔ Ideal.span {f} ↔
      ∃ g : MvPolynomial σ K, g.IsHomogeneous (n - d) ∧ p - f * g ∈ I := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp (by
      simpa only [sup_comm] using h)
    rw [mul_comm a f] at hab
    refine ⟨homogeneousComponent (n - d) a, homogeneousComponent_isHomogeneous _ _, ?_⟩
    have heq : p - f * homogeneousComponent (n - d) a = homogeneousComponent n b := by
      conv_lhs => lhs; rw [← homogeneousComponent_eq_self hp, ← hab]
      rw [map_add, homogeneousComponent_mul_of_le hf hdn]
      simp
    rw [heq]
    exact homogeneousComponent_mem_of_mem hI hb n
  · rintro ⟨g, _, hpg⟩
    rw [← sub_add_cancel p (f * g)]
    exact Ideal.add_mem _ ((le_sup_left : I ≤ I ⊔ Ideal.span {f}) hpg)
      ((le_sup_right : Ideal.span {f} ≤ I ⊔ Ideal.span {f})
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton f))))

theorem homogeneous_mem_sup_span_iff_of_lt
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f p : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d)
    (hp : p.IsHomogeneous n) (hnd : n < d) :
    p ∈ I ⊔ Ideal.span {f} ↔ p ∈ I := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp (by
      simpa only [sup_comm] using h)
    rw [mul_comm a f] at hab
    have heq : p = homogeneousComponent n b := by
      rw [← homogeneousComponent_eq_self hp, ← hab, map_add,
        homogeneousComponent_mul_of_lt hf hnd, zero_add]
    rw [heq]
    exact homogeneousComponent_mem_of_mem hI hb n
  · exact fun hpI => (le_sup_left : I ≤ I ⊔ Ideal.span {f}) hpI

theorem ker_degreeMap_eq_range_degreeMul
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (degreeMap (le_sup_left : I ≤ I ⊔ Ideal.span {f}) (d + n)) =
      LinearMap.range (degreeMul I hf n) := by
  ext x
  rcases x with ⟨x, p, hp, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    have hpJ : p ∈ I ⊔ Ideal.span {f} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h)
    obtain ⟨g, hg, hpg⟩ := (homogeneous_mem_sup_span_iff hI hf hp (Nat.le_add_right d n)).mp hpJ
    have hgn : g.IsHomogeneous n := by simpa using hg
    refine ⟨⟨Ideal.Quotient.mk I g, g, hgn, rfl⟩, Subtype.ext ?_⟩
    change Ideal.Quotient.mk I f * Ideal.Quotient.mk I g = Ideal.Quotient.mk I p
    rw [← map_mul]
    exact (Ideal.Quotient.eq.mpr hpg).symm
  · rintro ⟨y, hy⟩
    rw [← hy]
    apply Subtype.ext
    change Ideal.Quotient.factorₐ K _ (Ideal.Quotient.mk I f * (y : MvPolynomial σ K ⧸ I)) = 0
    rw [map_mul]
    have hfJ : Ideal.Quotient.mk (I ⊔ Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((le_sup_right : Ideal.span {f} ≤ I ⊔ Ideal.span {f}) (Ideal.subset_span (Set.mem_singleton f)))
    change Ideal.Quotient.mk (I ⊔ Ideal.span {f}) f * _ = 0
    rw [hfJ, zero_mul]

def degreeCokernelEquiv
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    (degreePiece I (d + n) ⧸ LinearMap.range (degreeMul I hf n)) ≃ₗ[K]
      degreePiece (I ⊔ Ideal.span {f}) (d + n) :=
  (Submodule.quotEquivOfEq _ _ (ker_degreeMap_eq_range_degreeMul hI hf n).symm).trans
    ((degreeMap (le_sup_left : I ≤ I ⊔ Ideal.span {f}) (d + n)).quotKerEquivOfSurjective
      (degreeMap_surjective _ _))

theorem degreeCokernelEquiv_mk
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ)
    (x : degreePiece I (d + n)) :
    degreeCokernelEquiv hI hf n (Submodule.Quotient.mk x) = degreeMap le_sup_left (d + n) x := by
  simp [degreeCokernelEquiv, Submodule.quotEquivOfEq_mk]

instance degreePiece_finite [Finite σ] (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.Finite K (degreePiece I n) :=
  Module.Finite.of_fg ((homogeneousSubmodule_fg σ K n).map _)

theorem finrank_degreePiece_sup_span_add [Finite σ]
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hreg : IsSMulRegular (MvPolynomial σ K ⧸ I) (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank K (degreePiece (I ⊔ Ideal.span {f}) (d + n)) =
      Module.finrank K (degreePiece I (d + n)) - Module.finrank K (degreePiece I n) := by
  have h := (degreeCokernelEquiv hI hf n).finrank_eq
  rw [Submodule.finrank_quotient,
    LinearMap.finrank_range_of_inj (degreeMul_injective I hf hreg n)] at h
  exact h.symm

theorem degreeMap_injective_of_lt
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d) (hnd : n < d) :
    Function.Injective (degreeMap (le_sup_left : I ≤ I ⊔ Ideal.span {f}) n) := by
  apply LinearMap.ker_eq_bot.mp
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hx
    rcases x with ⟨x, p, hp, rfl⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I p = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (homogeneous_mem_sup_span_iff_of_lt hI hf hp hnd).mp
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hx)
  · rintro rfl
    exact map_zero _

def degreeEquivOfLt
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d n : ℕ} (hf : f.IsHomogeneous d) (hnd : n < d) :
    degreePiece I n ≃ₗ[K] degreePiece (I ⊔ Ideal.span {f}) n :=
  LinearEquiv.ofBijective (degreeMap le_sup_left n)
    ⟨degreeMap_injective_of_lt hI hf hnd, degreeMap_surjective _ _⟩

theorem finrank_degreePiece_sup_span [Finite σ]
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hreg : IsSMulRegular (MvPolynomial σ K ⧸ I) (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank K (degreePiece (I ⊔ Ideal.span {f}) n) =
      Module.finrank K (degreePiece I n) -
        if d ≤ n then Module.finrank K (degreePiece I (n - d)) else 0 := by
  split_ifs with hdn
  · have h := finrank_degreePiece_sup_span_add hI hf hreg (n - d)
    have hindex : d + (n - d) = n := by omega
    rw [hindex] at h
    exact h
  · simpa using (degreeEquivOfLt hI hf (Nat.lt_of_not_ge hdn)).finrank_eq.symm

theorem finrank_degreePiece_sup_span_add_finrank [Finite σ]
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hreg : IsSMulRegular (MvPolynomial σ K ⧸ I) (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank K (degreePiece (I ⊔ Ideal.span {f}) n) +
        (if d ≤ n then Module.finrank K (degreePiece I (n - d)) else 0) =
      Module.finrank K (degreePiece I n) := by
  split_ifs with hdn
  · have h := (LinearMap.range (degreeMul I hf (n - d))).finrank_quotient_add_finrank
    rw [(degreeCokernelEquiv hI hf (n - d)).finrank_eq,
      LinearMap.finrank_range_of_inj (degreeMul_injective I hf hreg (n - d))] at h
    have hindex : d + (n - d) = n := by omega
    rw [hindex] at h
    exact h
  · simpa using (degreeEquivOfLt hI hf (Nat.lt_of_not_ge hdn)).finrank_eq.symm

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def quotientMulColon (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    (MvPolynomial σ K ⧸ I.colon {f}) →ₗ[K] (MvPolynomial σ K ⧸ I) :=
  ((I.colon {f}).restrictScalars K).mapQ (I.restrictScalars K)
    (LinearMap.mul K (MvPolynomial σ K) f) (by
      intro p hp
      change f * p ∈ I
      change p ∈ I.colon {f} at hp
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hp)

theorem quotientMulColon_mk (I : Ideal (MvPolynomial σ K)) (f p : MvPolynomial σ K) :
    quotientMulColon I f (Ideal.Quotient.mk (I.colon {f}) p) =
      Ideal.Quotient.mk I (f * p) := rfl

theorem quotientMulColon_injective (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    Function.Injective (quotientMulColon I f) := by
  apply LinearMap.ker_eq_bot.mp
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotientMulColon_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hx
  · rintro rfl
    exact map_zero _

noncomputable def degreeMulColon (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    degreePiece (I.colon {f}) n →ₗ[K] degreePiece I (d + n) where
  toFun x := ⟨quotientMulColon I f x, by
    rcases x.property with ⟨p, hp, hpx⟩
    refine ⟨f * p, hf.mul hp, ?_⟩
    rw [← hpx]
    rfl⟩
  map_add' x y := Subtype.ext (map_add (quotientMulColon I f)
    (x : MvPolynomial σ K ⧸ I.colon {f}) (y : MvPolynomial σ K ⧸ I.colon {f}))
  map_smul' a x := Subtype.ext (map_smul (quotientMulColon I f) a
    (x : MvPolynomial σ K ⧸ I.colon {f}))

theorem degreeMulColon_injective (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    Function.Injective (degreeMulColon I hf n) := by
  intro x y hxy
  apply Subtype.ext
  exact quotientMulColon_injective I f (congrArg Subtype.val hxy)

theorem degreeMulColon_comp_degreeMap (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    (degreeMulColon I hf n).comp (degreeMap (Ideal.le_colon : I ≤ I.colon {f}) n) =
      degreeMul I hf n := by
  ext x
  rcases x with ⟨x, p, hp, rfl⟩
  exact map_mul (Ideal.Quotient.mk I) f p

theorem range_degreeMulColon (I : Ideal (MvPolynomial σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.range (degreeMulColon I hf n) = LinearMap.range (degreeMul I hf n) := by
  rw [← degreeMulColon_comp_degreeMap I hf n, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (degreeMap_surjective _ _), Submodule.map_top]

theorem colon_isHomogeneous {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (I.colon {f}).IsHomogeneous (homogeneousSubmodule σ K) := by
  intro n p hp
  change (decomposition.decompose' p n : MvPolynomial σ K) ∈ I.colon {f}
  rw [decomposition.decompose'_apply, Submodule.mem_colon_singleton]
  change homogeneousComponent n p * f ∈ I
  have hfp : f * p ∈ I := by
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hp
  have h := homogeneousComponent_mem_of_mem hI hfp (d + n)
  rw [homogeneousComponent_mul_of_le hf (Nat.le_add_right d n), Nat.add_sub_cancel_left] at h
  simpa only [mul_comm] using h

theorem finrank_degreePiece_sup_span_add_colon [Finite σ]
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank K (degreePiece (I ⊔ Ideal.span {f}) n) +
        (if d ≤ n then Module.finrank K (degreePiece (I.colon {f}) (n - d)) else 0) =
      Module.finrank K (degreePiece I n) := by
  split_ifs with hdn
  · have h := (LinearMap.range (degreeMul I hf (n - d))).finrank_quotient_add_finrank
    rw [(degreeCokernelEquiv hI hf (n - d)).finrank_eq,
      ← range_degreeMulColon I hf (n - d),
      LinearMap.finrank_range_of_inj (degreeMulColon_injective I hf (n - d))] at h
    have hindex : d + (n - d) = n := by omega
    rw [hindex] at h
    exact h
  · simpa using (degreeEquivOfLt hI hf (Nat.lt_of_not_ge hdn)).finrank_eq.symm

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

theorem degreePiece_eq_bot_of_variables_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ i : σ, X i ∈ I)
    {n : ℕ} (hn : 0 < n) : degreePiece I n = ⊥ := by
  have hvars : idealOfVars σ K ≤ I := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hI i)
  apply le_antisymm _ bot_le
  rintro x ⟨p, hp, rfl⟩
  change Ideal.Quotient.mk I p = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hvars
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff']
  intro a ha
  exact hp.coeff_eq_zero (by omega)

theorem finrank_degreePiece_eq_zero_of_variables_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ i : σ, X i ∈ I)
    {n : ℕ} (hn : 0 < n) : Module.finrank K (degreePiece I n) = 0 := by
  rw [degreePiece_eq_bot_of_variables_mem I hI hn, finrank_bot]

end WeightedTorusJets.Geometry.GradedQuotient

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R]

local notation "HR" => fun S : PowerSeries R ↦
  ∃ d : ℕ, ∃ p : Polynomial R,
    ((1 : PowerSeries R) - PowerSeries.X) ^ d * S = (p : PowerSeries R)

theorem HilbertRational.polynomial (p : Polynomial R) :
    HR (p : PowerSeries R) := ⟨0, p, by simp⟩

theorem HilbertRational.add {S T : PowerSeries R}
    (hS : HR S) (hT : HR T) : HR (S + T) := by
  obtain ⟨d, p, hp⟩ := hS
  obtain ⟨e, q, hq⟩ := hT
  refine ⟨d + e, (1 - Polynomial.X) ^ e * p + (1 - Polynomial.X) ^ d * q, ?_⟩
  push_cast
  rw [pow_add, mul_add]
  calc
    _ = (1 - PowerSeries.X) ^ e * ((1 - PowerSeries.X) ^ d * S) +
        (1 - PowerSeries.X) ^ d * ((1 - PowerSeries.X) ^ e * T) := by ring
    _ = _ := by rw [hp, hq]

theorem HilbertRational.X_mul {S : PowerSeries R} (hS : HR S) :
    HR (PowerSeries.X * S) := by
  obtain ⟨d, p, hp⟩ := hS
  refine ⟨d, Polynomial.X * p, ?_⟩
  push_cast
  calc
    _ = PowerSeries.X * ((1 - PowerSeries.X) ^ d * S) := by ring
    _ = _ := by rw [hp]

theorem HilbertRational.of_eq_add_X_mul_self {S T : PowerSeries R}
    (hT : HR T) (hST : S = T + PowerSeries.X * S) : HR S := by
  obtain ⟨d, p, hp⟩ := hT
  have hclear : (1 - PowerSeries.X) * S = T := by
    rw [sub_mul, one_mul]
    exact sub_eq_iff_eq_add.mpr hST
  refine ⟨d + 1, p, ?_⟩
  rw [pow_succ, mul_assoc, hclear, hp]

theorem HilbertRational.exists_mul_invOneSubPow {S : PowerSeries R}
    (hS : HR S) :
    ∃ p : Polynomial R, ∃ d : ℕ, S = p * PowerSeries.invOneSubPow R d := by
  obtain ⟨d, p, hp⟩ := hS
  refine ⟨p, d, ?_⟩
  calc
    S = ((PowerSeries.invOneSubPow R d).val * (1 - PowerSeries.X) ^ d) * S := by
      rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.val_inv, one_mul]
    _ = (PowerSeries.invOneSubPow R d).val * p := by rw [mul_assoc, hp]
    _ = _ := mul_comm _ _

theorem hilbertRational_of_noetherian_recurrence
    {A : Type*} [PartialOrder A] [WellFoundedGT A]
    (H : A → PowerSeries R) (P : A → Prop)
    (hstep : ∀ I, P I → HR (H I) ∨
      ∃ J K, I < J ∧ I ≤ K ∧ P J ∧ P K ∧
        H I = H J + PowerSeries.X * H K) :
    ∀ I, P I → HR (H I) := by
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    intro hI
    rcases hstep I hI with h | ⟨J, K, hIJ, hIK, hJ, hK, hrec⟩
    · exact h
    have hJrat := ih J hIJ hJ
    rcases hIK.eq_or_lt with hKeq | hKlt
    · subst K
      exact HilbertRational.of_eq_add_X_mul_self hJrat hrec
    · rw [hrec]
      exact HilbertRational.add hJrat (HilbertRational.X_mul (ih K hKlt hK))

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace Polynomial

open _root_.Polynomial

variable {F : Type*} [Field F] [CharZero F]

theorem coeff_hilbertPoly_succ_top (p : F[X]) (d : ℕ) :
    (hilbertPoly p (d + 1)).coeff d = p.eval 1 / (d.factorial : F) := by
  rw [hilbertPoly_succ]
  simp only [finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul, coeff_preHilbertPoly_self,
    ← Finset.sum_mul, div_eq_mul_inv]
  congr 1
  simp only [eval_eq_sum, one_pow, mul_one, Polynomial.sum_def]

theorem natDegree_hilbertPoly_succ_le (p : F[X]) (d : ℕ) :
    (hilbertPoly p (d + 1)).natDegree ≤ d := by
  rw [hilbertPoly_succ]
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_smul_le _ _).trans (natDegree_preHilbertPoly F d i).le

theorem natDegree_hilbertPoly_succ_of_eval_one_ne_zero {p : F[X]} {d : ℕ}
    (hp : p.eval 1 ≠ 0) : (hilbertPoly p (d + 1)).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_hilbertPoly_succ_le p d)
  rw [coeff_hilbertPoly_succ_top]
  exact div_ne_zero hp (by exact_mod_cast Nat.factorial_ne_zero d)

theorem leadingCoeff_hilbertPoly_succ_of_eval_one_ne_zero {p : F[X]} {d : ℕ}
    (hp : p.eval 1 ≠ 0) :
    (hilbertPoly p (d + 1)).leadingCoeff = p.eval 1 / (d.factorial : F) := by
  rw [leadingCoeff, natDegree_hilbertPoly_succ_of_eval_one_ne_zero hp,
    coeff_hilbertPoly_succ_top]

theorem factorial_mul_leadingCoeff_hilbertPoly_succ {p : F[X]} {d : ℕ}
    (hp : p.eval 1 ≠ 0) :
    (d.factorial : F) * (hilbertPoly p (d + 1)).leadingCoeff = p.eval 1 := by
  rw [leadingCoeff_hilbertPoly_succ_of_eval_one_ne_zero hp]
  have hd : (d.factorial : F) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  field_simp

theorem hilbertPoly_mul_one_sub_X_pow (p : F[X]) (d e : ℕ) :
    hilbertPoly (p * (1 - Polynomial.X ^ e)) (d + 1) =
      hilbertPoly (p * ∑ j ∈ Finset.range e, Polynomial.X ^ j) d := by
  have hfactor : p * (1 - Polynomial.X ^ e) =
      (p * ∑ j ∈ Finset.range e, Polynomial.X ^ j) * (1 - Polynomial.X) := by
    rw [← mul_neg_geom_sum (Polynomial.X : F[X]) e]
    ring
  rw [hfactor, hilbertPoly_mul_one_sub_succ]

theorem factorial_mul_leadingCoeff_hilbertPoly_hypersurface
    {p : F[X]} (d : ℕ) {e : ℕ} (he : 0 < e) (hp : p.eval 1 ≠ 0) :
    (d.factorial : F) * (hilbertPoly (p * (1 - Polynomial.X ^ e)) (d + 2)).leadingCoeff =
      (e : F) * p.eval 1 := by
  rw [show d + 2 = (d + 1) + 1 by omega, hilbertPoly_mul_one_sub_X_pow]
  have heval : (p * ∑ j ∈ Finset.range e, (Polynomial.X : F[X]) ^ j).eval 1 =
      p.eval 1 * (e : F) := by simp
  rw [factorial_mul_leadingCoeff_hilbertPoly_succ (by
    rw [heval]
    exact mul_ne_zero hp (by exact_mod_cast he.ne')),
    heval, mul_comm]

end Polynomial

end

end SiegelZeros

end OAI
