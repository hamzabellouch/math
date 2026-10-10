import OAI.Geometry.RCD.Harmonic.EventualQuadraticError

namespace OAI

/-! # Radius-preserving balance of the quadratic Young parameter -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem eventual_balanced_error {Y : Type*} (f : ℕ → Y → ℝ)
    {C V M B : ℝ} (hV : 0<V) (hM : 0<M) (hB : 0≤B)
    (h : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ y (a : ℝ), 0<a →
      4*a*|f k y|≤C*(4*a^2*V+M*(B+δ))) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ k in atTop, ∀ y, |f k y|≤(C*Real.sqrt V*Real.sqrt M)*Real.sqrt (B+δ) := by
  let v := Real.sqrt V
  let m := Real.sqrt M
  let b := Real.sqrt (B+δ)
  have hv : 0<v := Real.sqrt_pos.mpr hV
  have hm : 0<m := Real.sqrt_pos.mpr hM
  have hb : 0<b := Real.sqrt_pos.mpr (by linarith)
  have hv2 : v^2=V := Real.sq_sqrt hV.le
  have hm2 : m^2=M := Real.sq_sqrt hM.le
  have hb2 : b^2=B+δ := Real.sq_sqrt (by linarith)
  let a := m*b/(2*v)
  have ha : 0<a := div_pos (mul_pos hm hb) (by positivity)
  have he : C*(4*a^2*V+M*(B+δ))=(4*a)*((C*v*m)*b) := by
    calc
      _ = C*(4*(m*b/(2*v))^2*v^2+m^2*b^2) := by rw [hv2,hm2,hb2]
      _ = _ := by
        dsimp only [a]
        field_simp [hv.ne']
        ring
  filter_upwards [h δ hδ] with k hk y
  have hh := hk y a ha
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ (show 0<4*a by positivity)).mp hh

theorem eventual_balanced_error_add {Y : Type*} (f : ℕ → Y → ℝ)
    {C V M B : ℝ} (hV : 0<V) (hM : 0<M) (hB : 0≤B)
    (h : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ y (a : ℝ), 0<a →
      4*a*|f k y|≤C*(4*a^2*V+M*(B+δ))) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ y,
      |f k y|≤(C*Real.sqrt V*Real.sqrt M)*Real.sqrt B+ε := by
  let δ (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hδ j : 0<δ j := by dsimp only [δ]; positivity
  have hz : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hs := ((tendsto_const_nhds (x := B)).add hz).sqrt.const_mul
    (C*Real.sqrt V*Real.sqrt M)
  simp only [add_zero] at hs
  obtain ⟨j,hj⟩ := (hs.eventually (gt_mem_nhds (show
    (C*Real.sqrt V*Real.sqrt M)*Real.sqrt B<
      (C*Real.sqrt V*Real.sqrt M)*Real.sqrt B+ε by linarith))).exists
  filter_upwards [eventual_balanced_error f hV hM hB h (hδ j)] with k hk y
  exact (hk y).trans hj.le

end RegularPointCoordinates

end

end OAI
