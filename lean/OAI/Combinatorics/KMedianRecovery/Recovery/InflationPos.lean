import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RealVector

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inflation_pos (n : ℕ) (hn : 1≤n) : 0<1-1/(8*(n:ℝ)^2) := by
  have hp : (1:ℝ)≤n := by exact_mod_cast hn
  have hb : 1/(8*(n:ℝ)^2)<1 := (div_lt_one (by positivity)).mpr (by nlinarith)
  linarith

lemma robust_scalar_growth (n : ℕ) (hn : 1≤n) :
    1+1/(2*(n:ℝ))≤(1-1/(8*(n:ℝ)^2))^(2*n)*(1+1/(n:ℝ)) := by
  have hp : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (n:ℝ)≠0 := by positivity
  have hq : 1/(8*(n:ℝ)^2)≤1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hb := one_add_mul_le_pow (show (-2:ℝ)≤ -(1/(8*(n:ℝ)^2)) by linarith) (2*n)
  have he : 1+(2*n:ℕ)*( -(1/(8*(n:ℝ)^2)))=1-1/(4*(n:ℝ)) := by
    push_cast
    field_simp
    ring
  have hl : 1-1/(4*(n:ℝ))≤(1-1/(8*(n:ℝ)^2))^(2*n) := by
    simpa only [he,sub_eq_add_neg] using hb
  calc
    _ ≤ (1-1/(4*(n:ℝ)))*(1+1/(n:ℝ)) := by
      have h : 0≤(n:ℝ)-1 := by linarith
      have heq : (1-1/(4*(n:ℝ)))*(1+1/(n:ℝ))-(1+1/(2*(n:ℝ)))=
          ((n:ℝ)-1)/(4*(n:ℝ)^2) := by field_simp; ring
      have hh : 0≤((n:ℝ)-1)/(4*(n:ℝ)^2) := div_nonneg h (by positivity)
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hl (by positivity)

lemma robust_cut_det (M R : Matrix V V ℝ) (hM : M.PosDef) (u : V → ℝ)
    (hu : quad M u=1) (hn : 2≤Fintype.card V)
    (hR : (R-(1-1/(8*(Fintype.card V:ℝ)^2)) •
      ((1-1/(8*(Fintype.card V:ℝ)^2)) • cutMatrix (Fintype.card V) M u)).PosSemidef) :
    (1+1/(2*(Fintype.card V:ℝ)))*M.det≤R.det := by
  let lam : ℝ := 1-1/(8*(Fintype.card V:ℝ)^2)
  have hlam : 0<lam := inflation_pos _ (by omega)
  have hcut : (cutMatrix (Fintype.card V) M u).PosDef :=
    cutMatrix_pos _ (by exact_mod_cast (show 1<Fintype.card V by omega)) M hM u
  have hd := det_mono_posDef (lam • (lam • cutMatrix (Fintype.card V) M u)) R
    ((hcut.smul hlam).smul hlam) hR
  simp only [Matrix.det_smul] at hd
  have hg := cutMatrix_grows M hM u hu hn
  have hlg := mul_le_mul_of_nonneg_left hg (pow_nonneg hlam.le (2*Fintype.card V))
  have hs := mul_le_mul_of_nonneg_right
    (robust_scalar_growth (Fintype.card V) (by omega)) hM.det_pos.le
  have he : lam^(2*Fintype.card V)=lam^(Fintype.card V)*lam^(Fintype.card V) := by
    rw [two_mul,pow_add]
  dsimp [lam] at he ⊢
  dsimp [lam] at hlg hd
  rw [he] at hlg hs
  nlinarith

lemma robust_block_growth (n : ℕ) (hn : 1≤n) : (2:ℝ)≤(1+1/(2*(n:ℝ)))^(2*n) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hq : (0:ℝ)≤1/(2*(n:ℝ)) := by positivity
  have hh := one_add_mul_le_pow (le_trans (show (-2:ℝ)≤0 by norm_num) hq) (2*n)
  have he : (2*n:ℕ)*(1/(2*(n:ℝ)))=1 := by push_cast; field_simp
  simpa only [he,one_add_one_eq_two] using hh

omit [DecidableEq V] in
lemma quad_le_of_sub (A B : Matrix V V ℝ) (h : (B-A).PosSemidef) (x : V → ℝ) :
    quad A x≤quad B x := by
  have hh := quad_nonneg _ h x
  rw [quad_sub_matrix] at hh
  linarith

omit [DecidableEq V] in
lemma quad_cauchy_unit (M : Matrix V V ℝ) (hM : M.PosSemidef) (u x : V → ℝ)
    (hu : quad M u=1) : (x ⬝ᵥ (M *ᵥ u))^2≤quad M x := by
  let b := x ⬝ᵥ (M *ᵥ u)
  have hh := quad_nonneg M hM (x+(-b) • u)
  rw [quad_add_scaled M hM.isHermitian,hu,bilinear_symm M hM.isHermitian u x] at hh
  change 0≤quad M x+2*(-b)*b+(-b)^2*1 at hh
  change b^2≤quad M x
  nlinarith

omit [DecidableEq V] in
lemma cutMatrix_spectral (d : ℝ) (hd : 2≤d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) (hu : quad M u=1) :
    (cutMatrix d M u-(3/4:ℝ) • M).PosSemidef ∧
    ((3:ℝ) • M-cutMatrix d M u).PosSemidef := by
  have hd0 : 0<d := by linarith
  have hc := (cutMatrix_pos d (by linarith) M hM u).isHermitian
  have hhi : (3/4:ℝ)≤(d^2-1)/d^2 := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hlo : (d^2-1)/d^2+2*(d+1)/d^2≤3 := by
    rw [←add_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb : 0≤2*(d+1)/d^2 := by positivity
  constructor
  · apply posSemidef_of_quad _ (hc.sub (hM.isHermitian.smul (IsSelfAdjoint.all _)))
    intro x
    have hq := quad_nonneg M hM.posSemidef x
    have hh := mul_le_mul_of_nonneg_right hhi hq
    have hp := mul_nonneg hb (sq_nonneg (x ⬝ᵥ (M *ᵥ u)))
    rw [quad_sub_matrix,quad_smul_matrix,quad_cutMatrix]
    nlinarith
  · apply posSemidef_of_quad _ ((hM.isHermitian.smul (IsSelfAdjoint.all _)).sub hc)
    intro x
    have hq := quad_nonneg M hM.posSemidef x
    have hh := mul_le_mul_of_nonneg_right hlo hq
    have hp := mul_le_mul_of_nonneg_left (quad_cauchy_unit M hM.posSemidef u x hu) hb
    rw [quad_sub_matrix,quad_smul_matrix,quad_cutMatrix]
    nlinarith

lemma inflation_bounds (d : ℝ) (hd : 1≤d) :
    (7/8:ℝ)≤1-1/(8*d^2) ∧ 1-1/(8*d^2)≤1 := by
  have he : 1/(8*d^2)≤1/8 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  constructor <;> linarith [show 0≤1/(8*d^2) by positivity]

omit [DecidableEq V] in

lemma robust_spectral (d : ℝ) (hd : 2≤d) (M R : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) (hu : quad M u=1)
    (hRlo : (R-(1-1/(8*d^2)) • ((1-1/(8*d^2)) • cutMatrix d M u)).PosSemidef)
    (hRhi : ((1-1/(8*d^2)) • cutMatrix d M u-R).PosSemidef) :
    (R-(1/2:ℝ) • M).PosSemidef ∧ ((3:ℝ) • M-R).PosSemidef := by
  let lam : ℝ := 1-1/(8*d^2)
  have hlb := inflation_bounds d (by linarith)
  have hl0 : 0≤lam := by dsimp [lam]; linarith
  have hl1 : lam≤1 := hlb.2
  have hll : (7/8:ℝ)≤lam := hlb.1
  have hcpos := cutMatrix_pos d (by linarith) M hM u
  have hRherm : R.IsHermitian := by
    have hh := hRlo.isHermitian.add ((hcpos.isHermitian.smul (IsSelfAdjoint.all (1-1/(8*d^2)))).smul (IsSelfAdjoint.all (1-1/(8*d^2))))
    simpa only [sub_add_cancel] using hh
  obtain ⟨hc1,hc2⟩ := cutMatrix_spectral d hd M hM u hu
  constructor
  · apply posSemidef_of_quad _ (hRherm.sub (hM.isHermitian.smul (IsSelfAdjoint.all _)))
    intro x
    have hh := quad_le_of_sub _ _ hRlo x
    have hcut := quad_le_of_sub _ _ hc1 x
    have hqm := quad_nonneg M hM.posSemidef x
    simp only [quad_smul_matrix] at hh hcut
    have hl2 : (1/2:ℝ)≤lam^2*(3/4) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hcut (sq_nonneg lam)
    have h2 := mul_le_mul_of_nonneg_right hl2 hqm
    rw [quad_sub_matrix,quad_smul_matrix]
    change lam* (lam*quad (cutMatrix d M u) x) ≤quad R x at hh
    nlinarith
  · apply posSemidef_of_quad _ ((hM.isHermitian.smul (IsSelfAdjoint.all _)).sub hRherm)
    intro x
    have hh := quad_le_of_sub _ _ hRhi x
    have hcut := quad_le_of_sub _ _ hc2 x
    have hqc := quad_nonneg _ hcpos.posSemidef x
    simp only [quad_smul_matrix] at hh hcut
    have h1 := mul_le_mul_of_nonneg_right hl1 hqc
    rw [quad_sub_matrix,quad_smul_matrix]
    change quad R x≤lam*quad (cutMatrix d M u) x at hh
    linarith

end MetricKMedianRecovery.Ellipsoid

end OAI
