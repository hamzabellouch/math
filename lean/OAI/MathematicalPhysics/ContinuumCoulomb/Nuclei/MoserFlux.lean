import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.DensitySynthesis

namespace OAI

/-! The explicit density homotopy and continuity equation used to transport
uniform slab density in the unit-charge construction. The identities describe
the explicit field and its density homotopy. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

def homotopyDensity (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) : ℝ :=
  rho + t * manufacturedCharge V x

def moserVelocity (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) : Position :=
  WithLp.toLp 2 (fun a => -(dirPartial V (axis a) x) /
    (4 * Real.pi * homotopyDensity rho V t x))

theorem homotopyDensity_bounds {rho : ℝ} (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    rho / 2 ≤ homotopyDensity rho V t x ∧
      homotopyDensity rho V t x ≤ 3 * rho / 2 := by
  have hrho : 0 ≤ rho := by linarith [abs_nonneg (manufacturedCharge V x), hbound x]
  have hb := abs_le.mp (hbound x)
  have hlow := mul_le_mul_of_nonneg_left hb.1 ht0
  have hupp := mul_le_mul_of_nonneg_left hb.2 ht0
  have hscale := mul_le_mul_of_nonneg_right ht1 (by linarith : 0 ≤ rho / 2)
  dsimp [homotopyDensity]
  constructor <;> nlinarith

theorem homotopyDensity_pos {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    0 < homotopyDensity rho V t x :=
  (by positivity : (0 : ℝ) < rho / 2).trans_le
    (homotopyDensity_bounds V hbound ht0 ht1 x).1

theorem homotopyDensity_endpoints (rho : ℝ) (V : Position → ℝ) (x : Position) :
    homotopyDensity rho V 0 x = rho ∧
      homotopyDensity rho V 1 x = rho + manufacturedCharge V x := by
  simp only [homotopyDensity, zero_mul, one_mul, add_zero, and_self]

theorem homotopyDensity_time_deriv (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) :
    deriv (fun s => homotopyDensity rho V s x) t = manufacturedCharge V x := by
  simpa only [homotopyDensity, one_mul, id_eq] using
    ((hasDerivAt_id t).mul_const (manufacturedCharge V x)).const_add rho |>.deriv

theorem moserVelocity_zero {rho t : ℝ} {V : Position → ℝ} {x : Position}
    (hx : x ∉ tsupport V) : moserVelocity rho V t x = 0 := by
  ext a
  have hp : x ∉ tsupport (dirPartial V (axis a)) :=
    fun hp => hx (NeutralAtom.tsupport_dirPartial_subset V (axis a) hp)
  change -(dirPartial V (axis a) x) / (4 * Real.pi * homotopyDensity rho V t x) = 0
  rw [image_eq_zero_of_notMem_tsupport hp, neg_zero, zero_div]

theorem moser_flux (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position)
    (hpos : homotopyDensity rho V t x ≠ 0) (a : Fin 3) :
    homotopyDensity rho V t x * moserVelocity rho V t x a =
      -(dirPartial V (axis a) x) / (4 * Real.pi) := by
  change homotopyDensity rho V t x *
    (-(dirPartial V (axis a) x) / (4 * Real.pi * homotopyDensity rho V t x)) = _
  field_simp [hpos]

/-- The continuity equation holds as an exact identity before any use of
flow transport or a numerical approximation to the flow. -/
theorem moser_continuity_equation {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 2 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    deriv (fun s => homotopyDensity rho V s x) t +
      (∑ a : Fin 3, dirPartial
        (fun y => homotopyDensity rho V t y * moserVelocity rho V t y a) (axis a) x) = 0 := by
  have hflux (a : Fin 3) :
      (fun y => homotopyDensity rho V t y * moserVelocity rho V t y a) =
      (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) := by
    funext y
    rw [moser_flux rho V t y (homotopyDensity_pos hrho V hbound ht0 ht1 y).ne' a]
    ring
  have hp (a : Fin 3) : Differentiable ℝ (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num)
  rw [homotopyDensity_time_deriv]
  simp_rw [hflux]
  have hpartial (a : Fin 3) :
      dirPartial (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) (axis a) x =
      -(4 * Real.pi)⁻¹ * dirPartial (dirPartial V (axis a)) (axis a) x := by
    change (fderiv ℝ (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) x) (axis a) = _
    rw [fderiv_const_mul (hp a x)]
    rfl
  simp_rw [hpartial]
  rw [← Finset.mul_sum, ← NeutralAtom.coordinateLaplacian_eq_partials hV.contDiffAt]
  dsimp [manufacturedCharge]
  ring

end ContinuumCoulomb

end

end OAI
