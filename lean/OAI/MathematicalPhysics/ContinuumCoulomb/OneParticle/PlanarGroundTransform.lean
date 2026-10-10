import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPoisson

namespace OAI

/-! The planar manufactured well's ground-state transform. Integration by
parts establishes positivity on actual compact C¹ test functions. Existence,
decay and the excitation gap of the specific resolvent-generated mode remain
separate analytic steps. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

abbrev PlanarPosition := EuclideanSpace ℝ (Fin 2)

def planarPartial (f : PlanarPosition → ℝ) (e : PlanarPosition) (x : PlanarPosition) : ℝ :=
  fderiv ℝ f x e

def planarAxis (a : Fin 2) : PlanarPosition := EuclideanSpace.single a 1

def planarLaplacian (f : PlanarPosition → ℝ) (x : PlanarPosition) : ℝ :=
  ∑ a : Fin 2, planarPartial (planarPartial f (planarAxis a)) (planarAxis a) x

theorem planarPartial_C1 {phi : PlanarPosition → ℝ} (hphi : ContDiff ℝ 2 phi)
    (e : PlanarPosition) : ContDiff ℝ 1 (planarPartial phi e) :=
  (hphi.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem planarPartial_continuous {v : PlanarPosition → ℝ} (hv : ContDiff ℝ 1 v)
    (e : PlanarPosition) : Continuous (planarPartial v e) :=
  ((hv.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
    contDiff_const).continuous

theorem planarPartial_mul (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 1 phi) (hv : ContDiff ℝ 1 v) (e x : PlanarPosition) :
    planarPartial (fun y => phi y * v y) e x =
      phi x * planarPartial v e x + v x * planarPartial phi e x := by
  dsimp [planarPartial]
  rw [fderiv_fun_mul (hphi.differentiable (by norm_num) x) (hv.differentiable (by norm_num) x)]
  rfl

theorem planarPartial_mul_square (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 1 phi) (hv : ContDiff ℝ 1 v) (e x : PlanarPosition) :
    planarPartial (fun y => phi y * v y ^ 2) e x =
      planarPartial phi e x * v x ^ 2 + 2 * phi x * v x * planarPartial v e x := by
  rw [planarPartial_mul phi (fun y => v y ^ 2) hphi (hv.pow 2)]
  have hp : planarPartial (fun y => v y ^ 2) e x = 2 * v x * planarPartial v e x := by
    dsimp [planarPartial]
    rw [fderiv_fun_pow 2 (hv.differentiable (by norm_num) x)]
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  rw [hp]
  ring

theorem planar_transform_integrable (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (e : PlanarPosition) :
    Integrable (fun x => planarPartial (fun y => phi y * v y ^ 2) e x * planarPartial phi e x) ∧
    Integrable (fun x => (phi x * v x ^ 2) * planarPartial (planarPartial phi e) e x) ∧
    Integrable (fun x => (phi x * v x ^ 2) * planarPartial phi e x) ∧
    Integrable (fun x => phi x ^ 2 * planarPartial v e x ^ 2) := by
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by norm_num)
  have hp := planarPartial_C1 hphi e
  have hvc : HasCompactSupport (planarPartial v e) := hc.fderiv_apply ℝ e
  have hv2c : HasCompactSupport (fun x => v x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hf : ContDiff ℝ 1 (fun x => phi x * v x ^ 2) := hphi1.mul (hv.pow 2)
  have hfc : HasCompactSupport (fun x => phi x * v x ^ 2) := hv2c.mul_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((planarPartial_continuous hf e).mul hp.continuous).integrable_of_hasCompactSupport
      (hfc.fderiv_apply ℝ e).mul_right
  · exact (hf.continuous.mul (planarPartial_continuous hp e)).integrable_of_hasCompactSupport
      hfc.mul_right
  · exact (hf.continuous.mul hp.continuous).integrable_of_hasCompactSupport hfc.mul_right
  · have hsq : HasCompactSupport (fun x => planarPartial v e x ^ 2) :=
      hvc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    have hcompact : HasCompactSupport (fun x => phi x ^ 2 * planarPartial v e x ^ 2) :=
      hsq.mul_left
    exact ((hphi.continuous.pow 2).mul ((planarPartial_continuous hv e).pow 2)).integrable_of_hasCompactSupport hcompact

theorem planar_transform_ibp (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (e : PlanarPosition) :
    (∫ x, (phi x * v x ^ 2) * planarPartial (planarPartial phi e) e x) =
      -(∫ x, planarPartial (fun y => phi y * v y ^ 2) e x * planarPartial phi e x) := by
  obtain ⟨hA, hB, hfg, hR⟩ := planar_transform_integrable phi v hphi hv hc e
  have hf : ContDiff ℝ 1 (fun x => phi x * v x ^ 2) :=
    (hphi.of_le (by norm_num)).mul (hv.pow 2)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hfg
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => (planarPartial_C1 hphi e).differentiable (by norm_num) x)

theorem planar_ground_transform_direction (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (e : PlanarPosition) :
    (∫ x, planarPartial (fun y => phi y * v y) e x ^ 2 +
      phi x * planarPartial (planarPartial phi e) e x * v x ^ 2) =
      ∫ x, phi x ^ 2 * planarPartial v e x ^ 2 := by
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by norm_num)
  obtain ⟨hA, hB, hfg, hR⟩ := planar_transform_integrable phi v hphi hv hc e
  have heq : (fun x => planarPartial (fun y => phi y * v y) e x ^ 2 +
      phi x * planarPartial (planarPartial phi e) e x * v x ^ 2) =
      (fun x => (phi x ^ 2 * planarPartial v e x ^ 2 +
        planarPartial (fun y => phi y * v y ^ 2) e x * planarPartial phi e x) +
        (phi x * v x ^ 2) * planarPartial (planarPartial phi e) e x) := by
    funext x
    rw [planarPartial_mul phi v hphi1 hv, planarPartial_mul_square phi v hphi1 hv]
    ring
  rw [heq]
  change (∫ x, ((fun y => phi y ^ 2 * planarPartial v e y ^ 2) +
    (fun y => planarPartial (fun z => phi z * v z ^ 2) e y * planarPartial phi e y)) x +
    (fun y => phi y * v y ^ 2 * planarPartial (planarPartial phi e) e y) x) = _
  rw [integral_add (hR.add hA) hB, integral_add' hR hA,
    planar_transform_ibp phi v hphi hv hc e]
  ring

/-- Nonnegativity of the shifted manufactured-well form on compact C¹
tests follows from the actual directional integration-by-parts identities. -/
theorem planar_ground_transform_nonnegative (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    0 ≤ ∑ a : Fin 2, ∫ x,
      planarPartial (fun y => phi y * v y) (planarAxis a) x ^ 2 +
        phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2 := by
  apply Finset.sum_nonneg
  intro a _
  rw [planar_ground_transform_direction phi v hphi hv hc]
  exact integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

def planarTestForm (W u : PlanarPosition → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ a : Fin 2, ∫ x, planarPartial u (planarAxis a) x ^ 2) +
    ∫ x, W x * u x ^ 2

theorem planar_partial_square_integrable (u : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (e : PlanarPosition) :
    Integrable (fun x => planarPartial u e x ^ 2) := by
  have hpc : HasCompactSupport (planarPartial u e) := hc.fderiv_apply ℝ e
  have hsq : HasCompactSupport (fun x => planarPartial u e x ^ 2) :=
    hpc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact ((planarPartial_continuous hu e).pow 2).integrable_of_hasCompactSupport hsq

theorem planar_transform_energy_split (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    (∑ a : Fin 2, ∫ x,
      planarPartial (fun y => phi y * v y) (planarAxis a) x ^ 2 +
        phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2) =
    (∑ a : Fin 2, ∫ x, planarPartial (fun y => phi y * v y) (planarAxis a) x ^ 2) +
      ∫ x, phi x * planarLaplacian phi x * v x ^ 2 := by
  have hu : ContDiff ℝ 1 (fun x => phi x * v x) := (hphi.of_le (by norm_num)).mul hv
  have huc : HasCompactSupport (fun x => phi x * v x) := hc.mul_left
  have hvc : HasCompactSupport (fun x => v x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hb (a : Fin 2) : Integrable (fun x =>
      phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2) := by
    have hs : HasCompactSupport (fun x =>
        phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2) := hvc.mul_left
    exact ((hphi.continuous.mul (planarPartial_continuous (planarPartial_C1 hphi _) _)).mul
      (hv.continuous.pow 2)).integrable_of_hasCompactSupport hs
  have hd (a : Fin 2) := planar_partial_square_integrable _ hu huc (planarAxis a)
  simp_rw [integral_add (hd _) (hb _)]
  rw [Finset.sum_add_distrib, ← integral_finsetSum _ (fun a _ => hb a)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [planarLaplacian, Finset.mul_sum, Finset.sum_mul]

/-- A positive classical mode at energy `-1/2` gives the lower bound on
every compact C¹ test, without assuming the well's spectral conclusion. -/
theorem planar_positive_mode_form_lower (phi W u : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hpos : ∀ x, 0 < phi x) (hW : Continuous W)
    (heigen : ∀ x, planarLaplacian phi x = (2 * W x + 1) * phi x)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    -(1 / 2 : ℝ) * (∫ x, u x ^ 2) ≤ planarTestForm W u := by
  let v : PlanarPosition → ℝ := fun x => u x / phi x
  have hv : ContDiff ℝ 1 v := hu.div (hphi.of_le (by norm_num)) (fun x => (hpos x).ne')
  have hvc : HasCompactSupport v := by
    change HasCompactSupport (fun x => u x / phi x)
    simp only [div_eq_mul_inv]
    exact hc.mul_right
  have hv2c : HasCompactSupport (fun x => v x ^ 2) :=
    hvc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hu2c : HasCompactSupport (fun x => u x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hfactor (x : PlanarPosition) : phi x * v x = u x := by
    dsimp [v]
    field_simp [(hpos x).ne']
  have hfactor_fun : (fun x => phi x * v x) = u := funext hfactor
  have hB (x : PlanarPosition) :
      phi x * planarLaplacian phi x * v x ^ 2 = (2 * W x + 1) * u x ^ 2 := by
    rw [heigen]
    calc
      _ = (2 * W x + 1) * (phi x * v x) ^ 2 := by ring
      _ = _ := by rw [hfactor]
  have hnonneg := planar_ground_transform_nonnegative phi v hphi hv hvc
  rw [planar_transform_energy_split phi v hphi hv hvc, hfactor_fun] at hnonneg
  simp_rw [hB] at hnonneg
  have hpot : Integrable (fun x => W x * u x ^ 2) :=
    (hW.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport hu2c.mul_left
  have hmass : Integrable (fun x => u x ^ 2) :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport hu2c
  have heq : (∫ x, (2 * W x + 1) * u x ^ 2) =
      2 * (∫ x, W x * u x ^ 2) + ∫ x, u x ^ 2 := by
    rw [show (fun x => (2 * W x + 1) * u x ^ 2) =
      (fun x => 2 * (W x * u x ^ 2) + u x ^ 2) from by funext x; ring]
    rw [integral_add (hpot.const_mul 2) hmass, integral_const_mul]
  rw [heq] at hnonneg
  dsimp [planarTestForm]
  linarith

end ContinuumCoulomb

end

end OAI
