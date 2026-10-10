import OAI.NumberTheory.Ostmann.ZeroDensity.ResidueRieszFinite
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszNearby

namespace OAI

/-! # Sharp residue-class Mangoldt sums for the small-modulus range -/

namespace Ostmann

open Filter

theorem residuePsi_small_modulus_bound : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X) / 2) →
      ∀ a : ℕ, a.Coprime q →
        |residuePsi q a X - thetaMainTerm q.totient
          (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
            35 * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, hdecay⟩ := canonical_riesz_residue_decay
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hdecay
  refine ⟨d / 4, by positivity, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (max 4 (2 * X0)),
    ht.eventually (eventually_ge_atTop ((4 / d) * Real.log 2))] with X hXL hscale
  intro q hq hqX a ha
  let : NeZero q := ⟨by omega⟩
  have hX : 4 ≤ X := (le_max_left _ _).trans hXL
  have hXX0 : 2 * X0 ≤ X := (le_max_right _ _).trans hXL
  have hXp : 0 < X := by linarith
  dsimp only [Function.comp_apply] at hscale
  let y := Real.sqrt (Real.log X)
  let h := X * Real.exp (-(d / 4) * y)
  let E := 16 * X ^ 2 * Real.exp (-(d / 2) * y)
  let N := ⌈2 * X⌉₊
  let w := residueMangoldtWeight q a
  let F := integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
    (pageBeta (actualLocalZero q))
  let m := thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
    (pageBeta (actualLocalZero q)) X
  have hN : 2 * X ≤ (N : ℝ) := Nat.le_ceil _
  have hh : 0 < h := by dsimp [h]; positivity
  have hlog : Real.log 2 ≤ (d / 4) * y := by
    have hm := mul_le_mul_of_nonneg_left hscale (show 0 ≤ d / 4 by positivity)
    have he : (d / 4) * ((4 / d) * Real.log 2) = Real.log 2 := by field_simp
    rw [he] at hm
    exact hm
  have hexphalf : Real.exp (-(d / 4) * y) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hhalf : h ≤ X / 2 := by
    have hm := mul_le_mul_of_nonneg_left hexphalf hXp.le
    dsimp [h]
    linarith
  have herr (Y : ℝ) (hlo : X / 2 ≤ Y) (hhi : Y ≤ 2 * X) :
      |finiteRieszSum (Finset.range (N + 1)) w Y - F Y| ≤ E := by
    have hYp : 0 < Y := by linarith
    have hroot := sqrt_log_nearby_lower X Y hX hlo
    have hqY : (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log Y)) :=
      hqX.trans (Real.exp_le_exp.mpr hroot)
    have hraw := hX0 Y (by linarith) q hq hqY a ha
    have he : Real.exp (-d * Real.sqrt (Real.log Y)) ≤
        Real.exp (-(d / 2) * y) := Real.exp_le_exp.mpr (by dsimp [y]; nlinarith)
    change |finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) Y -
      integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
        (pageBeta (actualLocalZero q)) Y| ≤ E
    rw [residueRieszMean_finite_error q a N Y hYp (hhi.trans hN)]
    calc
      _ ≤ Y * (4 * Y * Real.exp (-d * Real.sqrt (Real.log Y))) :=
        mul_le_mul_of_nonneg_left hraw hYp.le
      _ = 4 * Y ^ 2 * Real.exp (-d * Real.sqrt (Real.log Y)) := by ring
      _ ≤ 16 * X ^ 2 * Real.exp (-(d / 2) * y) := by
        apply mul_le_mul _ he (Real.exp_nonneg _) (by positivity)
        nlinarith
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hmain := integratedThetaMain_remainder_pair (q.totient : ℝ)
    (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X h
    hφ (pageCoefficient_abs_le_one _ _) (pageBeta_pos _) (pageBeta_le_one _) hh (by linarith)
  have hrec := finiteRieszSum_smooth_recovery (Finset.range (N + 1)) w F X h m E hh
    (fun n _ => residueMangoldtWeight_nonneg q a n)
    (herr X (by linarith) (by linarith))
    (herr (X + h) (by linarith) (by linarith))
    (herr (X - h) (by linarith) (by linarith)) hmain.1 hmain.2
  change |(∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => (n : ℝ) ≤ X),
    residueMangoldtWeight q a n) - m| ≤ _ at hrec
  rw [residue_finite_count q a N X hXp.le (by linarith)] at hrec
  have hexp2 : Real.exp (-(d / 2) * y) = (Real.exp (-(d / 4) * y)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hE : E = 16 * h ^ 2 := by
    dsimp [E, h]
    rw [hexp2]
    ring
  have hratio : 2 * E / h = 32 * h := by
    rw [hE]
    field_simp
    ring
  have hfinal : |residuePsi q a X - m| ≤ 35 * h := by
    rw [hratio] at hrec
    linarith
  simpa only [m, h, y, mul_assoc] using hfinal

end Ostmann

end OAI
