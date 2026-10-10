import OAI.MeasureTheory.Falconer.Estimates.EndpointCountBudget

namespace OAI

/-! # Profile cancellation in the weak radial tube-counting budget -/

namespace Falconer
open Real Filter
open scoped Topology

private theorem real_rpow_nat_power {x : ℝ} (hx : 0 < x) (a : ℝ) (j : ℕ) :
    (x^a)^j = x^(a*(j:ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]

theorem weak_radial_profile_cancel {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (n : ℕ) (K e τ : ℝ) :
    (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*(δ^(-τ)/D)^n =
      K^(n+1)*δ^((n+1)*e-n*τ) := by
  have hd : (n:ℝ)+1 ≠ 0 := by positivity
  have hroot : (D^((n:ℝ)/(n+1)))^(n+1) = D^n := by
    rw [real_rpow_nat_power hD, Nat.cast_add, Nat.cast_one]
    rw [div_mul_cancel₀ _ hd,Real.rpow_natCast]
  rw [div_div_eq_mul_div,div_pow,mul_pow,div_pow,hroot,
    real_rpow_nat_power hδ,real_rpow_nat_power hδ]
  calc
    _ = K^(n+1)*(δ^(-τ*(n:ℝ))/δ^(-e*((n+1:ℕ):ℝ))) := by
      field_simp [pow_ne_zero n hD.ne']
    _ = _ := by
      rw [← Real.rpow_sub hδ]
      congr 2
      push_cast
      ring

theorem weak_radial_local_count_power {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (n : ℕ) (K G e τ η : ℝ) :
    (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*
      (G/(δ^η)^(n+1))^(n*(n+1))*(δ^(-τ)/D)^n =
    (K^(n+1)*G^(n*(n+1)))*
      δ^((n+1)*e-n*τ-η*n*(n+1)^2) := by
  calc
    _ = ((K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*(δ^(-τ)/D)^n)*
        (G/(δ^η)^(n+1))^(n*(n+1)) := by ring
    _ = (K^(n+1)*δ^((n+1)*e-n*τ))*
        (G^(n*(n+1))/δ^(η*(((n+1)*(n*(n+1)):ℕ):ℝ))) := by
      rw [weak_radial_profile_cancel hδ hD,div_pow,← pow_mul,real_rpow_nat_power hδ]
    _ = (K^(n+1)*G^(n*(n+1)))*
        (δ^((n+1)*e-n*τ)/δ^(η*(((n+1)*(n*(n+1)):ℕ):ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hδ]
      congr 2
      push_cast
      ring

theorem eventually_weak_radial_local_budget (n : ℕ) (K G e τ η u : ℝ)
    (hgap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ ∀ D > 0,
      (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*
        (G/(δ^η)^(n+1))^(n*(n+1))*(δ^(-τ)/D)^n < (δ^u)^n := by
  let A : ℝ := K^(n+1)*G^(n*(n+1))
  let gap : ℝ := (n+1)*e-n*τ-η*n*(n+1)^2-n*u
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show -gap < 0 by dsimp [gap]; linarith)).eventually
    (eventually_gt_atTop A)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,fun D hD => ?_⟩
  rw [weak_radial_local_count_power hδ.1 hD]
  calc
    _ < δ^(-gap)*δ^((n+1)*e-n*τ-η*n*(n+1)^2) :=
      mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = (δ^u)^n := by
      rw [← Real.rpow_add hδ.1,real_rpow_nat_power hδ.1]
      congr 1
      dsimp [gap]
      ring

end Falconer

end OAI
