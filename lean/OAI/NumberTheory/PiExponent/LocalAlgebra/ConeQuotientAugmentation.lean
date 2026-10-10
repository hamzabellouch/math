import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution

namespace OAI

namespace PiExponentSiegelAux.W30
open scoped Pointwise
variable {R Y Z Q : Type*} [CommRing R] [AddCommGroup Y] [AddCommGroup Z]
  [AddCommGroup Q] [Module R Y] [Module R Z] [Module R Q]

def coneQuotientAugmentation (π : Z →ₗ[R] Q) (r : R) : Z →ₗ[R] QuotSMulTop r Q :=
  (r • (⊤ : Submodule R Q)).mkQ.comp π

theorem coneQuotientAugmentation_exact (g : Y →ₗ[R] Z) (π : Z →ₗ[R] Q) (r : R)
    (hπ : Function.Surjective π) (hg : LinearMap.range g = LinearMap.ker π) :
    LinearMap.range (coneBottom g r) = LinearMap.ker (coneQuotientAugmentation π r) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨y, w⟩, rfl⟩
    have hz : π (g y) = 0 := LinearMap.congr_fun (comp_zero_of_range_eq_ker g π hg) y
    change (Submodule.Quotient.mk (π (g y + r • w)) : QuotSMulTop r Q) = 0
    apply (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R Q))).mpr
    simp only [map_add, map_smul, hz, zero_add]
    exact Submodule.smul_mem_pointwise_smul (π w) r ⊤ (Submodule.mem_top)
  · intro hz
    have hmem : π z ∈ r • (⊤ : Submodule R Q) :=
      (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R Q))).mp hz
    obtain ⟨q, _, hq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
    obtain ⟨w, hw⟩ := hπ q
    have hcycle : π (z - r • w) = 0 := by
      simp only [map_sub, map_smul, hw, hq, sub_self]
    have hrange : z - r • w ∈ LinearMap.range g := by
      rw [hg]
      exact hcycle
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hrange
    refine ⟨(y, w), ?_⟩
    change g y + r • w = z
    rw [hy]
    abel

theorem coneQuotientAugmentation_surjective (π : Z →ₗ[R] Q) (r : R)
    (hπ : Function.Surjective π) : Function.Surjective (coneQuotientAugmentation π r) :=
  (Submodule.mkQ_surjective _).comp hπ

end PiExponentSiegelAux.W30

end OAI
