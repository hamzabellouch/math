import OAI.NumberTheory.TotientAsymptotic.FordCollisionCutoffs

namespace OAI

/-! Polynomially small normalized alignment mesh at each actual collision cut. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma cube_root_le_div_pow {h k : ℕ} {b : ℝ} (hh : 1 ≤ h)
    (hb : (h : ℝ)^(3*k) ≤ b) : b^(1/3 : ℝ) ≤ b/(h : ℝ)^(2*k) := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := zero_lt_one.trans_le h1
  have hb0 : 0 < b := (pow_pos h0 _).trans_le hb
  have hp : (h : ℝ)^(6*k) ≤ b^2 := by
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (h : ℝ)^(3*k)) hb 2
    convert hs using 1
    ring_nf
  have hc : b ≤ (b/(h : ℝ)^(2*k))^3 := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((h : ℝ)^(2*k))^3)).mpr
    have hs := mul_le_mul_of_nonneg_left hp hb0.le
    convert hs using 1 <;> ring_nf
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hb0.le _) (by positivity) (by norm_num : 3 ≠ 0)).mp
  have he : (b^(1/3 : ℝ))^3=b := by
    rw [← Real.rpow_mul_natCast hb0.le]
    norm_num
  rwa [he]

def collisionMesh (x y : ℝ) (i : ℕ) : ℝ :=
  Real.sqrt (B (normalityScale x i)*B y)/B y

lemma collisionMesh_pos {x y : ℝ} {i : ℕ} (hb : 0 < fordBandScale x i) (hy : 0 < B y) :
    0 < collisionMesh x y i := by
  have hs : B (normalityScale x i)=(fordBandScale x i)^(1/3 : ℝ) := by
    simp only [B,normalityScale,Real.log_exp]
  unfold collisionMesh
  rw [hs]
  exact div_pos (Real.sqrt_pos.mpr (mul_pos (Real.rpow_pos_of_pos hb _) hy)) hy

/-- The actual normalized alignment error is smaller than an arbitrary fixed
polynomial mesh; exponent 32 suffices for the retained collision grid. -/
theorem collisionMesh_bound : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 0 < B y → fordBandScale x i/2 ≤ B y →
    collisionMesh x y i ≤ 2/((m x-i : ℕ) : ℝ)^32 := by
  filter_upwards [ford_band_polynomial_lower 96,eventually_ge_atTop 1] with H hpoly hH
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hBy hlo
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hh : 1 ≤ m x-i := hH.trans hHi
  have h0 : (0 : ℝ) < (m x-i : ℕ) := by exact_mod_cast hh
  have hb := hx i him hHi
  have hb0 : 0 < fordBandScale x i := (pow_pos h0 96).trans_le hb
  have hs : B (normalityScale x i) ≤ fordBandScale x i/((m x-i : ℕ) : ℝ)^64 := by
    simpa only [B,normalityScale,Real.log_exp] using cube_root_le_div_pow (k := 32) hh hb
  have hsq : B (normalityScale x i)*B y ≤
      (2/((m x-i : ℕ) : ℝ)^32*B y)^2 := by
    have hbY : fordBandScale x i ≤ 2*B y := by linarith
    have ht : B (normalityScale x i) ≤ (2*B y)/((m x-i : ℕ) : ℝ)^64 :=
      hs.trans (div_le_div_of_nonneg_right hbY (pow_pos h0 _).le)
    have hp := mul_le_mul_of_nonneg_right ht hBy.le
    have he : (2/((m x-i : ℕ) : ℝ)^32*B y)^2 =
        4*(B y)^2/((m x-i : ℕ) : ℝ)^64 := by ring
    rw [he]
    calc
      _ ≤ (2*B y)/((m x-i : ℕ) : ℝ)^64*B y := hp
      _ = 2*((B y)^2/((m x-i : ℕ) : ℝ)^64) := by ring
      _ ≤ 4*((B y)^2/((m x-i : ℕ) : ℝ)^64) := by
        have hn : 0 ≤ (B y)^2/((m x-i : ℕ) : ℝ)^64 := by positivity
        linarith
      _ = _ := by ring
  apply (div_le_iff₀ hBy).mpr
  exact (Real.sqrt_le_iff).mpr ⟨by positivity,hsq⟩

end TotientAsymptotic

end

end OAI
