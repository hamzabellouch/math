import OAI.NumberTheory.Ostmann.QuadraticSievePoisson

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform

theorem schwartz_summable_translate (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun n : ℤ => f (x + n)) := by
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ
    ((Function.HasTemperateGrowth.const x).add Function.HasTemperateGrowth.id')
    (isometry_add_left x).antilipschitzWith f
  exact schwartz_summable_int g

theorem residue_lattice_summable (q : ℕ) (c : Fin q → ℂ) (f : 𝓢(ℝ, ℂ)) :
    Summable (fun p : Fin q × ℤ => c p.1 * f ((p.1.val : ℝ) / q + p.2)) := by
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro a
  exact ((schwartz_summable_translate f ((a.val : ℝ) / q)).mul_left (c a)).norm

theorem integer_lattice_eq_residue_sum (q : ℕ) [NeZero q] (c : Fin q → ℂ)
    (f : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, c ((Int.divModEquiv q m).2) * f ((m : ℝ) / q)) =
      ∑ a : Fin q, c a * ∑' n : ℤ, f ((a.val : ℝ) / q + n) := by
  let e : ℤ ≃ Fin q × ℤ := (Int.divModEquiv q).trans (Equiv.prodComm _ _)
  let F : Fin q × ℤ → ℂ := fun p => c p.1 * f ((p.1.val : ℝ) / q + p.2)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hF : ∀ m : ℤ,
      c ((Int.divModEquiv q m).2) * f ((m : ℝ) / q) = F (e m) := by
    intro m
    have hr : (((Int.divModEquiv q m).1 : ℤ) : ℝ) * (q : ℝ) +
        (((Int.divModEquiv q m).2.val : ℕ) : ℝ) = (m : ℝ) := by
      exact_mod_cast (Int.divModEquiv q).symm_apply_apply m
    congr 1
    apply congrArg f
    change (m : ℝ) / q = (((Int.divModEquiv q m).2.val : ℕ) : ℝ) / q +
      (((Int.divModEquiv q m).1 : ℤ) : ℝ)
    apply (div_eq_iff hq).mpr
    field_simp
    nlinarith
  calc
    _ = ∑' m : ℤ, F (e m) := tsum_congr hF
    _ = ∑' p : Fin q × ℤ, F p := e.tsum_eq F
    _ = ∑' a : Fin q, ∑' n : ℤ, F (a, n) := (residue_lattice_summable q c f).tsum_prod
    _ = _ := by simp only [tsum_fintype, F, tsum_mul_left]

theorem periodic_weighted_poisson (q : ℕ) [NeZero q] (c : Fin q → ℂ) (f : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, c ((Int.divModEquiv q m).2) * f ((m : ℝ) / q)) =
      ∑' h : ℤ, (∑ a : Fin q,
        c a * fourier h (((a.val : ℝ) / q : ℝ) : UnitAddCircle)) * 𝓕 f (h : ℝ) := by
  rw [integer_lattice_eq_residue_sum]
  exact finite_weighted_poisson Finset.univ c (fun a => (a.val : ℝ) / q) f

end Ostmann.QuadraticSieve

end OAI
