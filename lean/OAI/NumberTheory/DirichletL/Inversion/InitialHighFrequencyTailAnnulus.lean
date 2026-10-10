import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailGeometry

namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem actual_annulus_radial_lower
    (Z D m B θ H b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 0<Z) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D) :
    Z^(radialCenter m H θ D B)/(64*b^2) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hc : 0<C := (show 0<Z^B/4 by positivity).trans_le hC
  have hh : 0≤hnorm := (show 0≤Z^H/4 by positivity).trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ (b*Z^D)
    (by positivity) hc hd hv hn₁ hn₂ (by positivity) h₁ h₂
  have he : Z^m*(Z^B)^2*Z^H/(Z^θ*(Z^D)^2)=Z^(radialCenter m H θ D B) := by
    simp only [pow_two]
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
      ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
    congr 1
    unfold radialCenter
    ring
  calc
    _ = Z^m*(Z^B/4)^2*(Z^H/4)/(Z^θ*(b*Z^D)^2) := by
      rw [←he]
      ring
    _ ≤ Z^m*C^2*hnorm/(d*(b*Z^D)^2) := by gcongr
    _ = (Z^m*C^2/(d*(b*Z^D)^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem actual_annulus_high_gate
    (Z D m B θ H η τ b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D)
    (hfixed : 64*b^2≤Z^η) (hhigh : 4*η+τ≤radialCenter m H θ D B) :
    Z^τ≤(Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply le_trans _ (actual_annulus_radial_lower Z D m B θ H b C d v n₁ n₂ hnorm
    hz hb hd hv hn₁ hn₂ hC hdiv hfreq h₁ h₂)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    Z^τ*(64*b^2)≤Z^τ*Z^η := mul_le_mul_of_nonneg_left hfixed (by positivity)
    _ = Z^(τ+η) := (Real.rpow_add hz τ η).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
