import OAI.NumberTheory.DirichletL.Hecke.DetectorSaturation

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_power_allowance (C p dmin α : ℝ) (hα : 0≤α) (hgap : p<dmin*α) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → C*Z^p≤(Z^d)^α := by
  have hh := constant_absorbed_eventually C (dmin*α-p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd
  have hZp : 0<Z := by linarith
  calc
    _ ≤ Z^(dmin*α-p)*Z^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*α) := by rw [←Real.rpow_add hZp]; congr 1; ring
    _ ≤ Z^(d*α) := Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hα)
    _ = _ := Real.rpow_mul hZp.le _ _

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

lemma uniform_zero_height (dmin τ : ℝ) (I : ℕ) (hgap : τ<dmin/2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3*i : ℕ)*Z^τ≤(Z^d)^(1/2 : ℝ) := by
  have hh := uniform_power_allowance (3*I : ℕ) τ dmin (1/2) (by norm_num) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hn : (3*i : ℕ)≤3*I := by omega
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.rpow_nonneg (by linarith) _)).trans (hZ d hd)

lemma uniform_height_budget (dmin τ η : ℝ) (I : ℕ) (hτ : 0≤τ)
    (hη : 0≤η) (hgap : 4*τ<dmin*η) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η := by
  have hh := uniform_power_allowance ((3*(I : ℝ)+5)^4*16) (4*τ) dmin η hη hgap
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hT : 1≤Z^τ := Real.one_le_rpow hZ1 hτ
  have hp : (1+Z^τ)^4≤16*Z^(4*τ) := by
    calc
      _ ≤ (2*Z^τ)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        have he : (Z^τ)^4=Z^(4*τ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤Z)]
          congr 1
          norm_num
          ring
        rw [mul_pow,he]
        norm_num
  calc
    _ ≤ (3*(I : ℝ)+5)^4*(1+Z^τ)^4 := indexed_height_bound i I hi (Z^τ) (by linarith)
    _ ≤ (3*(I : ℝ)+5)^4*(16*Z^(4*τ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((3*(I : ℝ)+5)^4*16)*Z^(4*τ) := by ring
    _ ≤ _ := hZ d hd

lemma uniform_fourier_allowance (dmax τ : ℝ) (hdmax : 0<dmax) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, 0≤d → d≤dmax →
      2*Real.pi*(Z^d)^(τ/(2*dmax))≤Z^τ/2 := by
  have hh := constant_absorbed_eventually (4*Real.pi) (τ/2) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd hd'
  have hZp : 0<Z := by linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^(τ/2) := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hm := mul_le_mul_of_nonneg_right hd' (show 0≤τ/(2*dmax) by positivity)
    have he : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rwa [he] at hm
  have he : Z^(τ/2)*Z^(τ/2)=Z^τ := by rw [←Real.rpow_add hZp]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le (τ/2))
  rw [he] at hh
  have hpi := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.pi by positivity)
  nlinarith

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
