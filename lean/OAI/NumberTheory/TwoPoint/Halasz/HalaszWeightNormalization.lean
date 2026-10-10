import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleSpecialization

namespace OAI

/-! Normalized coordinate weights when both short variables have the same
length. The three terms exhibit the triangular saving in the degree. -/
namespace TwoPointCorrelations

noncomputable def halaszNormalizedWeight {k : ℕ} (r M : ℕ)
    (γ : Fin k → ℝ) (j : Fin k) : ℝ :=
  min (2*(r:ℝ)+1) ((5/2:ℝ)/(M:ℝ)^(j.val+1)+2*r*|γ j|+
    1/(2*r*((M:ℝ)^(j.val+1))^2*|γ j|))

lemma halasz_weight_normalized {k r M : ℕ} (hr : 1≤r) (hM : 1≤M)
    (γ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) (j : Fin k) :
    halaszDoubleWeight r r M M γ j≤
      (M:ℝ)^(j.val+1)*halaszNormalizedWeight r M γ j := by
  let m : ℝ := (M:ℝ)^(j.val+1)
  let g := |γ j|
  have hrR : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hMR : 1≤(M:ℝ) := by exact_mod_cast hM
  have hm : 1≤m := one_le_pow₀ hMR
  have hm0 : 0<m := by linarith
  have hg : 0<g := abs_pos.mpr (hγ j)
  have htriv : 2*(r:ℝ)*m+1≤m*(2*r+1) := by nlinarith
  have he : 8*(r:ℝ)*m*(1/(16*r*m))+2*r*m*g+8*(1/(16*r*m))/g+2=
      m*((5/2:ℝ)/m+2*r*g+1/(2*r*m^2*g)) := by
    field_simp
    ring
  unfold halaszDoubleWeight halaszDoubleWindow halaszNormalizedWeight
  push_cast
  change min (2*((r:ℝ)*m)+1)
      (8*((r:ℝ)*m)*(1/(16*r*m))+2*((r:ℝ)*m)*g+8*(1/(16*r*m))/g+2)≤
    m*min (2*(r:ℝ)+1) ((5/2:ℝ)/m+2*r*g+1/(2*r*m^2*g))
  rw [show 8*((r:ℝ)*m)*(1/(16*r*m))+2*((r:ℝ)*m)*g+8*(1/(16*r*m))/g+2=
      8*(r:ℝ)*m*(1/(16*r*m))+2*r*m*g+8*(1/(16*r*m))/g+2 by ring,he,
    mul_min_of_nonneg _ _ hm0.le]
  apply min_le_min _ le_rfl
  simpa only [mul_assoc] using htriv

end TwoPointCorrelations

end OAI
