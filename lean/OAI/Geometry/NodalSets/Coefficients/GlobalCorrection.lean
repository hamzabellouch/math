import Mathlib.Analysis.Calculus.ContDiff.Comp
import OAI.Geometry.NodalSets.Coefficients.CoordinateCorrection
import OAI.Geometry.NodalSets.Elliptic.SmoothQuotient

namespace OAI

namespace Yau
noncomputable section
open Function Set
open scoped ContDiff
variable {n : ℕ}

theorem pairing_smooth {u : Coord n → ℝ} {V : Coord n → Coord n}
    (hu : ContDiff ℝ ∞ u) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (pairing u V) := by
  apply ContDiff.sum
  intro i _
  exact ((hu.fderiv_right (by simp)).clm_apply contDiff_const).mul (hV i)

def correctionDenominator (u : Coord n → ℝ) (V : Coord n → Coord n)
    (lam : ℝ) (x : Coord n) : ℝ := pairing u V x + lam * u x ^ 2

theorem correctionDenominator_smooth {u : Coord n → ℝ} {V : Coord n → Coord n}
    (hu : ContDiff ℝ ∞ u) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (lam : ℝ) :
    ContDiff ℝ ∞ (correctionDenominator u V lam) :=
  (pairing_smooth hu hV).add (contDiff_const.mul (hu.pow 2))

theorem global_exact_correction {gamma u R : Coord n → ℝ} {V : Coord n → Coord n}
    {lam : ℝ} (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hR : ContDiff ℝ ∞ R) (hcompact : HasCompactSupport R)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (hlam : lam ≠ 0)
    (hden : ∀ x ∈ tsupport R, correctionDenominator u V lam x ≠ 0) :
    ∃ f : Coord n → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ tsupport R ∧
      (∀ x, f x = R x / correctionDenominator u V lam x) ∧
      ∀ x, weightedDiv gamma (fun y i ↦ u y * (f y * V y i)) x +
        lam * (f x * u x - lam⁻¹ *
          weightedDiv gamma (fun y i ↦ f y * V y i) x) * u x = R x := by
  let D := correctionDenominator u V lam
  let f := fun x ↦ R x / D x
  have hf : ContDiff ℝ ∞ f :=
    smooth_quotient_on_residual_support hR (correctionDenominator_smooth hu hV lam) hden
  refine ⟨f, hf, quotient_compact_support hcompact,
    quotient_tsupport_subset R D, fun _ ↦ rfl, ?_⟩
  intro x
  by_cases hx : D x ≠ 0
  · exact weighted_exact_correction (hg.differentiable (by simp)).differentiableAt (hgn x)
      (hu.differentiable (by simp)).differentiableAt (hf.differentiable (by simp)).differentiableAt
      (fun i ↦ ((hV i).differentiable (by simp)).differentiableAt) hlam hx rfl
  · have hRx : R x = 0 := by
      by_contra hr
      exact hx (hden x (subset_closure hr))
    have hfx : f x = 0 := by simp [f, hRx]
    rw [weightedDiv_mul (V := fun y i ↦ f y * V y i)
      (hg.differentiable (by simp)).differentiableAt (hgn x) (hu.differentiable (by simp)).differentiableAt
      (fun i ↦ (hf.differentiable (by simp)).differentiableAt.mul
        ((hV i).differentiable (by simp)).differentiableAt)]
    have hp : pairing u (fun y i ↦ f y * V y i) x = 0 := by simp [pairing, hfx]
    rw [hp, hfx, hRx]
    field_simp [hlam]
    ring

theorem weightedDiv_smooth {gamma : Coord n → ℝ} {V : Coord n → Coord n}
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (weightedDiv gamma V) := by
  apply (hg.inv hgn).mul
  apply ContDiff.sum
  intro i _
  exact (((hg.mul (hV i)).fderiv_right (by simp)).clm_apply contDiff_const)

def densityCorrection (gamma u f : Coord n → ℝ) (V : Coord n → Coord n)
    (lam : ℝ) (x : Coord n) : ℝ :=
  f x * u x - lam⁻¹ * weightedDiv gamma (fun y i ↦ f y * V y i) x

theorem densityCorrection_smooth {gamma u f : Coord n → ℝ} {V : Coord n → Coord n}
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (lam : ℝ) :
    ContDiff ℝ ∞ (densityCorrection gamma u f V lam) :=
  (hf.mul hu).sub (contDiff_const.mul
    (weightedDiv_smooth hg hgn (fun i ↦ hf.mul (hV i))))

theorem weightedDiv_zero_off_support (gamma f : Coord n → ℝ)
    (V : Coord n → Coord n) {x : Coord n} (hx : x ∉ tsupport f) :
    weightedDiv gamma (fun y i ↦ f y * V y i) x = 0 := by
  have he : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hd (i : Fin n) :
      fderiv ℝ (fun y ↦ gamma y * (f y * V y i)) x = 0 := by
    have heq : (fun y ↦ gamma y * (f y * V y i)) =ᶠ[nhds x] (fun _ ↦ 0) := by
      filter_upwards [he] with y hy
      simp [hy]
    rw [heq.fderiv_eq]
    simp
  simp [weightedDiv, coordDiv, coordPartial, hd]

theorem densityCorrection_tsupport_subset (gamma u f : Coord n → ℝ)
    (V : Coord n → Coord n) (lam : ℝ) :
    tsupport (densityCorrection gamma u f V lam) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra h
  have hf0 := image_eq_zero_of_notMem_tsupport h
  have hd0 := weightedDiv_zero_off_support gamma f V h
  exact hx (by simp [densityCorrection, hf0, hd0])

theorem densityCorrection_compact_support (gamma u f : Coord n → ℝ)
    (V : Coord n → Coord n) (lam : ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (densityCorrection gamma u f V lam) :=
  hf.of_isClosed_subset (isClosed_tsupport _)
    (densityCorrection_tsupport_subset gamma u f V lam)

end
end Yau

end OAI
