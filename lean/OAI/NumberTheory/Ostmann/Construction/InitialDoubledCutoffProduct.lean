import OAI.NumberTheory.Ostmann.Construction.InitialCutoffProduct

namespace OAI

/-! # Product windows on both actual copies of the weighted initial list -/
namespace Ostmann
open scoped Classical BigOperators

theorem initial_doubled_cutoff_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P)
    (hprior : productPrior (Fin.append
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0)
    (hw : doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0) :
    |Real.log (∏ i, (x i : ℝ)) - 2 * (G + cb + cd + ∑ i, center i)| ≤ 2 * (r + 3) := by
  let n := (b + (d + r)) + 1
  let xl : Fin n → P := fun i => x (i.castAdd n)
  let xr : Fin n → P := fun i => x (i.natAdd n)
  let ν : Fin n → P → ℝ := Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))
  have hp : productPrior ν xl ≠ 0 ∧ productPrior ν xr ≠ 0 := by
    unfold productPrior at hprior ⊢
    rw [Fin.prod_univ_add] at hprior
    simpa only [Fin.append_left, Fin.append_right, ne_eq, mul_eq_zero, not_or] using hprior
  have hw' : (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail xl) : ℂ) ≠ 0 ∧
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail xr) : ℂ) ≠ 0 :=
    mul_ne_zero_iff.mp hw
  have hl := initial_half_cutoff_log_product P hP b d r μ₀ μb μd μc G cb cd center hG hc
    xl hp.1 (by exact_mod_cast hw'.1)
  have hr := initial_half_cutoff_log_product P hP b d r μ₀ μb μd μc G cb cd center hG hc
    xr hp.2 (by exact_mod_cast hw'.2)
  have hlog (y : Fin n → P) : Real.log (∏ i, (y i : ℝ)) = ∑ i, Real.log (y i : ℝ) :=
    Real.log_prod (fun i _ => by exact_mod_cast (hP _ (y i).property).ne_zero)
  rw [hlog xl] at hl
  rw [hlog xr] at hr
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (x i).property).ne_zero), Fin.sum_univ_add]
  obtain ⟨hllo, hlhi⟩ := abs_le.mp hl
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hr
  dsimp only [xl, xr] at hllo hlhi hrlo hrhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ostmann

end OAI
