import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDecomposition
import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientTrace

namespace OAI

/-! # Unimodularity on the Cartan ideal

The quotient of the ambient algebra by its nonzero-root ideal is generated
by the nilpotent Cartan subalgebra. Its induced adjoint operators are
nilpotent. Consequently restriction to the ideal preserves the trace.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include T

theorem cartan_quotient_ad_nilpotent (h : H) :
    let N := (cartanRootIdeal H).toSubmodule
    _root_.IsNilpotent (N.mapQ N (ad ℝ L h)
      (fun _ hx => (cartanRootIdeal H).lie_mem hx)) := by
  let N := (cartanRootIdeal H).toSubmodule
  let A := N.mapQ N (ad ℝ L h) (fun _ hx => (cartanRootIdeal H).lie_mem hx)
  let φ : H →ₗ[ℝ] (L ⧸ N) := N.mkQ.comp H.subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    have hx : x ∈ N ⊔ H.toSubmodule := by
      rw [triangular_cartan_spanning T H]
      trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨v, hv⟩, ?_⟩
    change N.mkQ v = N.mkQ (u + v)
    have hu' : N.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hu
    rw [map_add, hu', zero_add]
  have hinter (x : H) : A (φ x) = φ (ad ℝ H h x) := rfl
  have hpow (k : ℕ) (x : H) : (A ^ k) (φ x) = φ ((ad ℝ H h ^ k) x) := by
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply, hk, hinter, pow_succ', Module.End.mul_apply]
  obtain ⟨k, hk⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra (R := ℝ) (L := H)
  refine ⟨k, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := hφ q
  rw [hpow, hk h]
  rfl

/-- The trace-zero action required by the support data follows from ambient
unimodularity, even when the Cartan subgroup overlaps the root ideal. -/
theorem trace_cartanRootIdeal_eq_zero
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.trace ℝ (cartanRootIdeal H) (toEnd ℝ H (cartanRootIdeal H) h) = 0 := by
  let N := (cartanRootIdeal H).toSubmodule
  have hf : ∀ x ∈ N, ad ℝ L h x ∈ N :=
    fun _ hx => (cartanRootIdeal H).lie_mem hx
  have ht := trace_eq_restrict_of_nilpotent_quotient N (ad ℝ L h) hf
    (cartan_quotient_ad_nilpotent T H h)
  have heq : (ad ℝ L h).restrict hf = toEnd ℝ H (cartanRootIdeal H) h := by
    ext x
    rfl
  rw [heq] at ht
  exact ht.symm.trans (hunimod h)

end PolycyclicRecognition

end

end OAI
