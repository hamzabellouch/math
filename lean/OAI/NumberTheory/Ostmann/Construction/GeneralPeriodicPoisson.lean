import OAI.NumberTheory.Ostmann.Construction.FourierScale
import OAI.NumberTheory.Ostmann.Construction.PeriodicPoisson
import OAI.NumberTheory.Ostmann.QuadraticSievePoisson

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Construction

theorem periodic_poisson (Q : ℕ) [NeZero Q] (f : SchwartzMap ℝ ℂ) (F : Fin Q → ℂ) :
    (∑' n : ℤ, periodicResidueTest Q F n*f ((n:ℝ)/Q)) =
      ∑' s : ℤ, (∑ r : Fin Q, F r*fourier s (((r:ℝ)/Q:ℝ):UnitAddCircle))*𝓕 f (s:ℝ) := by
  let e : (Fin Q × ℤ) ≃ ℤ := (Equiv.prodComm (Fin Q) ℤ).trans (Int.divModEquiv Q).symm
  let g : Fin Q × ℤ → ℂ := fun z => F z.1 * f ((z.1 : ℝ)/Q + z.2)
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne Q)
  have hcomp (z : Fin Q × ℤ) :
      periodicResidueTest Q F (e z) * f ((e z : ℤ) / (Q : ℝ)) = g z := by
    rcases z with ⟨r,k⟩
    have hr : (Int.divModEquiv Q (e (r,k))).2 = r := by
      exact congrArg Prod.snd ((Int.divModEquiv Q).apply_symm_apply (k,r))
    rw [periodicResidueTest, hr]
    congr 1
    change f (((k * (Q : ℤ) + r : ℤ) : ℝ) / Q) = f ((r : ℝ)/Q+k)
    congr 1
    push_cast
    field_simp
    ring
  have hfib (r : Fin Q) : Summable (fun k : ℤ => ‖g (r,k)‖) := by
    simpa only [g, norm_mul] using (schwartz_shift_norm_summable f ((r : ℝ)/Q)).mul_left ‖F r‖
  have hnorm : Summable (fun z : Fin Q × ℤ => ‖g z‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨hfib, (hasSum_fintype _).summable⟩
  have hg : Summable g := hnorm.of_norm
  calc
    (∑' n : ℤ, periodicResidueTest Q F n * f ((n : ℝ)/Q)) =
        ∑' z : Fin Q × ℤ, g z := by
      rw [← e.tsum_eq (fun n : ℤ => periodicResidueTest Q F n * f ((n : ℝ)/Q))]
      exact tsum_congr hcomp
    _ = ∑' r : Fin Q, ∑' k : ℤ, F r * f ((r : ℝ)/Q+k) := hg.tsum_prod
    _ = ∑ r : Fin Q, F r*(∑' k : ℤ, f ((r:ℝ)/Q+k)) := by
      rw [tsum_fintype]
      simp only [tsum_mul_left]
    _ = _ := Ostmann.QuadraticSieve.finite_weighted_poisson Finset.univ F
      (fun r => (r:ℝ)/Q) f

theorem scaled_periodic_poisson_full (Q : ℕ) [NeZero Q]
    (ψ : SchwartzMap ℝ ℂ) (F : Fin Q → ℂ) {X : ℝ} (hX : 0<X) :
    (∑' n : ℤ, periodicResidueTest Q F n*ψ ((n:ℝ)/X)) =
      (X/(Q:ℝ):ℂ)*(∑' s : ℤ,
        (∑ r : Fin Q, F r*fourier s (((r:ℝ)/Q:ℝ):UnitAddCircle))*
          𝓕 ψ ((s:ℝ)*X/Q)) := by
  have hQ : (0:ℝ)<Q := by exact_mod_cast NeZero.pos Q
  let a : ℝ := Q/X
  have ha : 0<a := div_pos hQ hX
  let f := schwartzScale ψ a ha.ne'
  have hterm (n : ℤ) : f ((n:ℝ)/Q)=ψ ((n:ℝ)/X) := by
    change ψ (((n:ℝ)/Q)*(Q/X))=_
    congr 1
    field_simp
  have hf (s : ℤ) : 𝓕 f (s:ℝ)=(X/(Q:ℝ):ℂ)*𝓕 ψ ((s:ℝ)*X/Q) := by
    rw [schwartzScale_fourier, abs_of_pos (inv_pos.mpr ha)]
    have hainv : a⁻¹=X/(Q:ℝ) := by simp only [a,inv_div]
    have harg : (s:ℝ)/a=(s:ℝ)*X/Q := by dsimp [a]; field_simp
    rw [hainv,harg,Complex.real_smul,Complex.ofReal_div]
  have h := periodic_poisson Q f F
  simp_rw [hterm,hf] at h
  rw [h]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro s
  ring

end Ostmann.Construction

end

end OAI
