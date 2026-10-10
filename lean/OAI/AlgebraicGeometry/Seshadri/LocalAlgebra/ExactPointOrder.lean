import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.EtaleJetCharts

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.AnalyticCoordinates

lemma formalTrunc_zero_iff_order (f : MvPowerSeries (Fin 2) ℂ) (n : ℕ) :
    formalTrunc n f = 0 ↔ (n : ℕ∞) ≤ f.order := by
  change Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h
    apply MvPowerSeries.nat_le_order
    intro d hd
    simpa only [MvPowerSeries.coeff_truncTotal f hd] using h d hd
  · intro h d hd
    rw [MvPowerSeries.coeff_truncTotal f hd]
    apply MvPowerSeries.coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hd) h

lemma taylor_mem_power_iff_order {R : Type} [CommRing R] [Algebra ℂ R]
    (ρ : R →ₐ[ℂ] ℂ) (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hτ : ∀ n : ℕ, 0 < n → RingHom.ker ((formalTrunc n).comp τ) = (RingHom.ker ρ)^n)
    (a : R) (n : ℕ) : a ∈ (RingHom.ker ρ)^n ↔ (n : ℕ∞) ≤ (τ a).order := by
  by_cases hn : n = 0
  · subst n; simp
  · rw [← hτ n (Nat.pos_of_ne_zero hn)]
    change formalTrunc n (τ a) = 0 ↔ _
    exact formalTrunc_zero_iff_order _ _

lemma taylor_cancel_power {R : Type} [CommRing R] [Algebra ℂ R]
    (ρ : R →ₐ[ℂ] ℂ) (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hτ : ∀ n : ℕ, 0 < n → RingHom.ker ((formalTrunc n).comp τ) = (RingHom.ker ρ)^n)
    (a b : R) (n m : ℕ) (ha : a ∉ (RingHom.ker ρ)^(m+1))
    (hab : a*b ∈ (RingHom.ker ρ)^n) : b ∈ (RingHom.ker ρ)^(n-m) := by
  by_contra hb
  rw [taylor_mem_power_iff_order ρ τ hτ] at ha hb hab
  have ha' := lt_of_not_ge ha
  have hb' := lt_of_not_ge hb
  have hat : (τ a).order ≠ ⊤ := ne_top_of_lt ha'
  have hbt : (τ b).order ≠ ⊤ := ne_top_of_lt hb'
  rw [← ENat.natCast_toNat hat] at ha'
  rw [← ENat.natCast_toNat hbt] at hb'
  have haN : (τ a).order.toNat < m+1 := by exact_mod_cast ha'
  have hbN : (τ b).order.toNat < n-m := by exact_mod_cast hb'
  rw [map_mul,MvPowerSeries.order_mul,← ENat.natCast_toNat hat,
    ← ENat.natCast_toNat hbt,← Nat.cast_add] at hab
  have habN : n ≤ (τ a).order.toNat+(τ b).order.toNat := by exact_mod_cast hab
  omega

theorem standard_smooth_cancel_power {R : Type} [CommRing R] [IsDomain R] [Algebra ℂ R]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ R]
    (ρ : R →ₐ[ℂ] ℂ) (a b : R) (n m : ℕ)
    (ha : a ∉ (RingHom.ker ρ)^(m+1)) (hab : a*b ∈ (RingHom.ker ρ)^n) :
    b ∈ (RingHom.ker ρ)^(n-m) := by
  classical
  obtain ⟨ι,σ,hσ,hι,P,hP⟩ := Algebra.IsStandardSmoothOfRelativeDimension.out (n := 2) (R := ℂ) (S := R)
  let := hσ
  let := hι
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite ι
  let e : ((Set.range P.map)ᶜ : Set ι) ≃ Fin 2 := Fintype.equivFinOfCardEq (by
    rw [← hP]
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
      Fintype.card_compl_set, Set.card_range_of_injective P.map_inj])
  obtain ⟨q,hq,-,-,hjets,-⟩ := presentation_analytic_realization P e ρ
  exact taylor_cancel_power ρ (analyticTaylor q hq) hjets a b n m ha hab

end
end MaximalSeshadri.Geometry

end


end OAI
