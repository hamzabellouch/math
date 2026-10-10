import OAI.Analysis.BoundedHochschild.FiniteProjectionAbsoluteContinuity

namespace OAI

/-!
# Uniform normal-state decay along unitary orbits

Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.2,
for positive normal functionals. This is the specialization needed for the
normal-state orbit used in constructing a trace.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A normal positive functional vanishes along projections subequivalent to
an orthogonal sequence in a finite algebra. -/
theorem normal_positive_subequivalent_tendsto_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    Tendsto (fun n => ψ (p n)) atTop (𝓝 0) := by
  obtain ⟨R, _, _, hle, ht⟩ := finite_subequivalent_orthogonal_tails e hfinite p q
    hp hq horth hembed
  have hRt : Tendsto (fun n => ‖ψ (R n)‖) atTop (𝓝 0) := by
    simpa only [map_zero, norm_zero] using (trace_predual_tendsto e ψ hψ ht).norm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hRt
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (ψ.monotone (hle n))
    (ψ.map_nonneg (hp n).nonneg)

/-- Choosing a different unitary at each index still gives normal-state decay. -/
theorem normal_positive_unitary_orbit_tendsto_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (u : ℕ → unitary M) :
    Tendsto (fun n => ψ ((u n : M) * q n * star (u n : M))) atTop (𝓝 0) := by
  let w (n : ℕ) : PartialIso M := ⟨(u n : M) * q n, by
    have hu := (Unitary.mem_iff.mp (u n).property).1
    simp only [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      ((u n : M) * q n) * (q n * star (u n : M)) * ((u n : M) * q n) =
          (u n : M) * (q n * q n) * (star (u n : M) * (u n : M)) * q n := by
        simp only [mul_assoc]
      _ = (u n : M) * q n := by
        rw [(hq n).isIdempotentElem.eq, hu, mul_one, mul_assoc,
          (hq n).isIdempotentElem.eq]⟩
  have hwi (n : ℕ) : (w n).initial = q n := by
    change star ((u n : M) * q n) * ((u n : M) * q n) = q n
    rw [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      _ = q n * (star (u n : M) * (u n : M)) * q n := by simp only [mul_assoc]
      _ = q n := by rw [(Unitary.mem_iff.mp (u n).property).1, mul_one,
        (hq n).isIdempotentElem.eq]
  have hwf (n : ℕ) : (w n).final = (u n : M) * q n * star (u n : M) := by
    change ((u n : M) * q n) * star ((u n : M) * q n) = _
    rw [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      _ = (u n : M) * (q n * q n) * star (u n : M) := by simp only [mul_assoc]
      _ = _ := by rw [(hq n).isIdempotentElem.eq]
  have ht := normal_positive_subequivalent_tendsto_zero e hfinite ψ hψ
    (fun n => (w n).final) q (fun n => (w n).final_proj) hq horth
    (fun n => ⟨adjointPartialIso (w n), by simp, by simp [hwi]⟩)
  simpa only [hwf] using ht

/-- Normal positive functionals are uniformly small on every unitary conjugate
of the terms of an orthogonal projection sequence in a finite algebra. -/
theorem normal_positive_uniform_unitary_orbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u : unitary M, ‖ψ ((u : M) * q n * star (u : M))‖ < ε := by
  classical
  let u (n : ℕ) : unitary M := if h : ∃ v : unitary M,
      ε ≤ ‖ψ ((v : M) * q n * star (v : M))‖ then h.choose else 1
  have ht := normal_positive_unitary_orbit_tendsto_zero e hfinite ψ hψ q hq horth u
  have hlt : ∀ᶠ n in atTop, ‖ψ ((u n : M) * q n * star (u n : M))‖ < ε :=
    (tendsto_order.1 (by simpa only [norm_zero] using ht.norm)).2 ε hε
  filter_upwards [hlt] with n hn v
  by_contra hv
  have hex : ∃ v : unitary M, ε ≤ ‖ψ ((v : M) * q n * star (v : M))‖ :=
    ⟨v, le_of_not_gt hv⟩
  have hu : ε ≤ ‖ψ ((u n : M) * q n * star (u n : M))‖ := by
    simpa only [u, dite_eq_left hex] using hex.choose_spec
  exact (not_le_of_gt hn) hu

end KadisonRingrose
end BoundedHochschild

end

end OAI
