import Mathlib.LinearAlgebra.Isomorphisms
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousIdealStep

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

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

theorem quotientSectionFactor_surjective (I J : Ideal (MvPolynomial σ k))
    (hIJ : I ≤ J) (n : ℕ) :
    Function.Surjective (quotientSectionFactor I J hIJ n) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := Submodule.mem_map.mp y.2
  refine ⟨⟨Ideal.Quotient.mk I p, Submodule.mem_map.mpr ⟨p, hp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hpy

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

theorem regular_hilbert_step [Finite σ] (I : Ideal (MvPolynomial σ k))
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

end PiExponentJets.W64

end OAI
