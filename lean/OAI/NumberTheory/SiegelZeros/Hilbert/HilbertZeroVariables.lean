import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.CoordinateQuotientGrading

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem homogeneous_mem_step_decomposition
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous (n + d))
    (hmem : p ∈ Ideal.span {f} ⊔ I) :
    ∃ a : MvPolynomial σ k, a.IsHomogeneous n ∧ p - a * f ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  let aₙ := DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) a n
  refine ⟨aₙ.1, aₙ.2, ?_⟩
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) (n + d)) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_add_of_right_mem
      (MvPolynomial.homogeneousSubmodule σ k) hf,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  have hb' := (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb (n + d)
  have heq : p - aₙ.1 * f =
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) b (n + d) :
        MvPolynomial σ k) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [aₙ, add_comm] using hproj.symm
  rw [heq]
  exact hb'

omit [Finite σ] in
theorem homogeneous_mem_step_of_degree_lt
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous n) (hnd : n < d)
    (hmem : p ∈ Ideal.span {f} ⊔ I) : p ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) n) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_of_not_le
      (MvPolynomial.homogeneousSubmodule σ k) hf (Nat.not_le_of_lt hnd),
    zero_add,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  rw [← hproj]
  exact (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb n

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientSectionFactor (I J : Ideal (MvPolynomial σ k))
    (hIJ : I ≤ J) (n : ℕ) : quotientSection I n →ₗ[k] quotientSection J n where
  toFun x := ⟨Ideal.Quotient.factorₐ k hIJ x.1, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    apply Submodule.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    exact congrArg (Ideal.Quotient.factorₐ k hIJ) hpx⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _

omit [Finite σ] in
theorem quotientSectionFactor_surjective (I J : Ideal (MvPolynomial σ k))
    (hIJ : I ≤ J) (n : ℕ) :
    Function.Surjective (quotientSectionFactor I J hIJ n) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := Submodule.mem_map.mp y.2
  refine ⟨⟨Ideal.Quotient.mk I p, Submodule.mem_map.mpr ⟨p, hp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hpy

omit [Finite σ] in
theorem quotientSectionFactor_ker_eq (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)) =
      LinearMap.range (quotientSectionMultiply I f hf n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ k le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ k le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨a, ha, hpa⟩ := homogeneous_mem_step_decomposition I hI f p hf hp hmem
    apply LinearMap.mem_range.mpr
    refine ⟨⟨Ideal.Quotient.mk I a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I f = x.1
    rw [← map_mul]
    have he : Ideal.Quotient.mk I (p - a * f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hpa
    rw [map_sub, sub_eq_zero] at he
    exact he.symm.trans hpx
  · intro hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change (Ideal.Quotient.factorₐ k le_sup_right)
      (y.1 * Ideal.Quotient.mk I f) = 0
    rw [map_mul]
    change (Ideal.Quotient.factorₐ k le_sup_right) y.1 *
      Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0
    have hf0 : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hinc : Ideal.span {f} ≤ Ideal.span {f} ⊔ I := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    rw [hf0, mul_zero]

theorem regular_hilbert_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := quotientSectionCokernel_finrank_add I f hf hreg n
  rw [← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
      (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

omit [Finite σ] in
theorem hilbert_step_of_degree_lt (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (hnd : n < d) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) =
      Module.finrank k (quotientSection I n) := by
  let φ := quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right n
  have hinj : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ k le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ k le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    have hpI := homogeneous_mem_step_of_degree_lt I hI f p hf hp hnd
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    apply Subtype.ext
    change x.1 = 0
    rw [← hpx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  exact (LinearEquiv.ofBijective φ
    ⟨hinj, quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right n⟩).finrank_eq.symm

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (Module.finrank k (quotientSection I n) : ℤ))

omit [Finite σ] in
@[simp] theorem coeff_sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (sectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℤ) :=
  PowerSeries.coeff_mk _ _

theorem sectionHilbertSeries_regular_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) :
    sectionHilbertSeries (Ideal.span {f} ⊔ I) =
      (1 - PowerSeries.X ^ d) * sectionHilbertSeries I := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := regular_hilbert_step I hI f hf hreg (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    apply eq_sub_of_add_eq
    exact_mod_cast h
  · rw [ite_eq_right hdn, sub_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn))

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem ideal_le_colon_singleton (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) : I ≤ I.colon {f} := by
  intro p hp
  apply Submodule.mem_colon_singleton.mpr
  simpa only [smul_eq_mul] using I.mul_mem_right f hp

omit [Finite σ] in
theorem quotientSectionFactor_colon_ker (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n) =
      LinearMap.ker (quotientSectionMultiply I f hf n) := by
  ext x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
  change Ideal.Quotient.mk I p = x.1 at hpx
  simp only [LinearMap.mem_ker, Subtype.ext_iff]
  change (Ideal.Quotient.factorₐ k (ideal_le_colon_singleton I f)) x.1 = 0 ↔
    x.1 * Ideal.Quotient.mk I f = 0
  rw [← hpx]
  change Ideal.Quotient.mk (I.colon {f}) p = 0 ↔
    Ideal.Quotient.mk I (p * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    Submodule.mem_colon_singleton, smul_eq_mul]

theorem quotientSectionMultiply_range_finrank_colon
    (I : Ideal (MvPolynomial σ k)) {d : ℕ}
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (LinearMap.range (quotientSectionMultiply I f hf n)) =
      Module.finrank k (quotientSection (I.colon {f}) n) := by
  let φ := quotientSectionFactor I (I.colon {f}) (ideal_le_colon_singleton I f) n
  have hd := (LinearMap.ker φ).finrank_quotient_add_finrank
  let e := φ.quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (I.colon {f}) (ideal_le_colon_singleton I f) n)
  rw [e.finrank_eq] at hd
  change Module.finrank k (quotientSection (I.colon {f}) n) +
    Module.finrank k (LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n)) = _ at hd
  rw [quotientSectionFactor_colon_ker I f hf n] at hd
  have hm := (quotientSectionMultiply I f hf n).finrank_range_add_finrank_ker
  omega

theorem colon_hilbert_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection (I.colon {f}) n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank
  rw [quotientSectionMultiply_range_finrank_colon I f hf n,
    ← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

theorem sectionHilbertSeries_colon_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) :
    sectionHilbertSeries I = sectionHilbertSeries (Ideal.span {f} ⊔ I) +
      PowerSeries.X ^ d * sectionHilbertSeries (I.colon {f}) := by
  ext n
  rw [map_add, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := colon_hilbert_step I hI f hf (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right hdn, add_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn)).symm

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

variable {σ : Type*}

noncomputable def exponentDegreeEquivSym (n : ℕ) :
    {d : σ →₀ ℕ | d.degree = n} ≃ Sym σ n := by
  classical
  exact
    { toFun := fun d => ⟨d.1.toMultiset, by
        rw [Finsupp.card_toMultiset]
        exact d.2⟩
      invFun := fun m => ⟨Multiset.toFinsupp m.1, by
        have hc := Finsupp.card_toMultiset (Multiset.toFinsupp m.1)
        rw [Multiset.toFinsupp_toMultiset] at hc
        change (Multiset.toFinsupp m.1).degree = n
        exact hc.symm.trans m.2⟩
      left_inv := fun d => Subtype.ext (Multiset.toFinsupp.apply_symm_apply d.1)
      right_inv := fun m => Subtype.ext (Multiset.toFinsupp.symm_apply_apply m.1) }

theorem card_exponents_degree [Fintype σ] (n : ℕ) :
    Nat.card {d : σ →₀ ℕ | d.degree = n} = (Fintype.card σ).multichoose n := by
  classical
  rw [Nat.card_congr (exponentDegreeEquivSym n), Nat.card_eq_fintype_card]
  exact Sym.card_sym_eq_multichoose σ n

variable {k : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem quotientSection_bot_finrank (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) := by
  let e := LinearEquiv.ofBijective
    (Ideal.Quotient.mkₐ k (⊥ : Ideal (MvPolynomial σ k))).toLinearMap
    ((Ideal.Quotient.mk_bijective_iff_eq_bot (⊥ : Ideal (MvPolynomial σ k))).mpr rfl)
  exact e.finrank_map_eq (MvPolynomial.homogeneousSubmodule σ k n)

theorem quotientSection_bot_finrank_multichoose [Fintype σ] (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      (Fintype.card σ).multichoose n := by
  rw [quotientSection_bot_finrank, homogeneousSection_finrank, card_exponents_degree]

theorem sectionHilbertSeries_bot [Fintype σ] (hσ : 0 < Fintype.card σ) :
    sectionHilbertSeries (⊥ : Ideal (MvPolynomial σ k)) =
      (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ (Fintype.card σ) hσ]
  ext n
  rw [coeff_sectionHilbertSeries, PowerSeries.coeff_mk,
    quotientSection_bot_finrank_multichoose, Nat.multichoose_eq]
  congr 1
  have hs : Fintype.card σ + n - 1 = (Fintype.card σ - 1) + n := by omega
  rw [hs]
  exact Nat.choose_symm_add.symm

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem quotientSection_finrank_zero_of_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (quotientSection I (n+1)) = 0 := by
  have h := Submodule.finrank_map_le (Ideal.Quotient.mkₐ k I).toLinearMap
    (MvPolynomial.homogeneousSubmodule σ k (n+1))
  rw [homogeneousSection_finrank, card_exponents_degree, hσ,
    Nat.multichoose_zero_succ] at h
  exact Nat.eq_zero_of_le_zero h

theorem sectionHilbertSeries_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I = PowerSeries.C (Module.finrank k (quotientSection I 0) : ℤ) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_sectionHilbertSeries, quotientSection_finrank_zero_of_no_variables hσ I n]
    simp only [PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, Nat.cast_zero]

theorem exists_hilbert_numerator_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  refine ⟨Polynomial.C (Module.finrank k (quotientSection I 0) : ℤ), ?_⟩
  simpa only [hσ, PowerSeries.invOneSubPow_zero, Units.val_one, mul_one,
    Polynomial.coe_C] using sectionHilbertSeries_no_variables hσ I

end WeightedTorusJets.W64

end

end SiegelZeros

end OAI
