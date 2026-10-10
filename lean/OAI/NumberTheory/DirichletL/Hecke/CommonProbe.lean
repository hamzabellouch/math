import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
import OAI.NumberTheory.DirichletL.Hecke.Dirichlet

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Classical
namespace SevenEighths.HeckeCommonProbe
open HeckeFamily HeckeZeroSupremum

def PrimitiveContract (ω σ : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re} ∧
      (∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x^(3/16+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H (-11/16) x) =O[atTop]
        (fun x : ℝ => x^(beta-11/16-σ))

def UniformCommonProbe : Prop :=
  7/8 < beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < beta-7/8 ∧ 0 < σ ∧ PrimitiveContract ω σ

theorem beta_le_seven_eighths (h : UniformCommonProbe) : beta ≤ 7/8 := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := Supremum.continuationMargin_pos hω hσ
  have hboundary := Supremum.continuation_boundary_gt (β := beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask (by linarith) hχpole,
      hz, zero_mul]
  apply (HeckeSignal.nonzero_of_probe_bounds χ H J beta ω σ (-11/16)
    beta_le_one hω0 hω hσ hH hb ?_ ?_ hnear hχpole) hzχ
  · convert hJ using 1; ring_nf
  · convert herr using 1; ring_nf

theorem hecke_ne_zero_of_common_probe (h : UniformCommonProbe)
    (χ : Character) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  exact LFunction_ne_zero_of_beta_lt χ ((beta_le_seven_eighths h).trans_lt hs) hpole

theorem dirichlet_of_common_probe (h : UniformCommonProbe) (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  exact HeckeDirichlet.dirichlet_seven_eighths_of_hecke
    (hecke_ne_zero_of_common_probe h) χ s hs hexc

theorem zeta_of_common_probe (h : UniformCommonProbe) (s : ℂ)
    (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  HeckeDirichlet.zeta_seven_eighths_of_hecke (hecke_ne_zero_of_common_probe h) s hs

end SevenEighths.HeckeCommonProbe

end

end OAI
