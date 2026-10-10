import OAI.MeasureTheory.Falconer.Estimates.FarRegionSplit

namespace OAI

/-! # Uniform shell regimes throughout the actual far region -/

namespace Falconer
open Set MeasureTheory

 theorem shell_regime_of_lower_distance {Ψ : ℝ → ℝ}
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (v D base κ ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : ℓ ≤ d)
    (hfreq : 1 ≤ ((2:ℝ)^v/4)*ℓ)
    (hscale : D^2/(((2:ℝ)^v/4)*ℓ) ≤ base^(-κ)) :
    ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 → 1 ≤ r*d ∧ D^2/(r*d) ≤ base^(-κ) := by
  intro r hr
  have h2 : 0 < (2:ℝ)^v := by positivity
  have hr0 : (2:ℝ)^v/4 < r := by
    have hh := (lt_div_iff₀ h2).mp (hs _ hr).1
    linarith
  have hmin : 0 < ((2:ℝ)^v/4)*ℓ := mul_pos (by positivity) hℓ
  have hlower : ((2:ℝ)^v/4)*ℓ ≤ r*d :=
    mul_le_mul hr0.le hd hℓ.le (by linarith)
  exact ⟨hfreq.trans hlower,
    (div_le_div_of_nonneg_left (sq_nonneg D) hmin hlower).trans hscale⟩

 theorem comparableFarRegion_lower {d a h : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableFarRegion d a h) :
    4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.1.1 z.1.2 ∧
      4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.2.1 z.2.2 := by
  constructor <;> linarith [hz.2.1,hz.2.2.1,hz.2.2.2]

 theorem leftNoncomparableFar_lower {d a h : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ leftNoncomparableFar d a h) :
    4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.1.1 z.1.2 := by
  have hsep : 2*dist z.2.1 z.2.2 < dist z.1.1 z.1.2 := hz.2
  have hnonneg : 0 ≤ dist z.2.1 z.2.2 := dist_nonneg
  have he : max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) = dist z.1.1 z.1.2 :=
    max_eq_left (by linarith)
  have hh := hz.1.2
  rw [he] at hh
  have hp : 0 ≤ ((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) := by positivity
  linarith

 theorem rightNoncomparableFar_lower {d a h : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ rightNoncomparableFar d a h) :
    4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.2.1 z.2.2 := by
  have hsep : 2*dist z.1.1 z.1.2 < dist z.2.1 z.2.2 := hz.2
  have hnonneg : 0 ≤ dist z.1.1 z.1.2 := dist_nonneg
  have he : max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) = dist z.2.1 z.2.2 :=
    max_eq_right (by linarith)
  have hh := hz.1.2
  rw [he] at hh
  have hp : 0 ≤ ((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) := by positivity
  linarith

 theorem far_band_frequency_mono {b h t : ℕ} (hb : b ≤ h+6) {D : ℝ}
    (hD : D^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ))) :
    D^2 ≤ (2:ℝ)^((t:ℝ)-b) := by
  apply hD.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hcast : (b:ℝ) ≤ (h+6:ℕ) := by exact_mod_cast hb
  linarith

end Falconer

end OAI
