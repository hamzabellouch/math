import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTransformDecay
import OAI.NumberTheory.CubicMoment.Estimates.HeckeSmoothDual

namespace OAI

/-! The norm twist in the original Voronoi formula is exactly the
translated Mellin variable in the shifted transform. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma phaseWeight_compact {W : ℝ → ℂ} (hW : HasCompactSupport W) (t : ℝ) :
    HasCompactSupport (fun x => W x*mellinPhase t x) := hW.mul_right

lemma phaseWeight_positive {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0) (t : ℝ) :
    tsupport (fun x => W x*mellinPhase t x) ⊆ Ioi 0 :=
  tsupport_mul_subset_left.trans hpos

lemma phaseWeight_smooth {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => W x*mellinPhase t x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (0:ℝ) ∉ tsupport W := fun h => (lt_irrefl (0:ℝ)) (hpos h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change W y = 0 at hy
    simp only [hy,zero_mul]
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => t*Real.log y) x :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hx)
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => ((t*Real.log y:ℝ):ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
    exact hsm.contDiffAt.mul (hc.mul contDiffAt_const).cexp

lemma mellin_mul_phase (W : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    mellin (fun x => W x*mellinPhase t x) s = mellin W (s+(t:ℂ)*Complex.I) := by
  calc
    _ = mellin (fun x => (x:ℂ)^((t:ℂ)*Complex.I) • W x) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [mellinPhase_eq_cpow hx t]
      simp only [smul_eq_mul]
      ring
    _ = _ := mellin_cpow_smul W s ((t:ℂ)*Complex.I)

/-- Exact scalar identity. Its outside phase has modulus one. -/
theorem metaplecticTransform_twisted (ℓ : ℤ) (W : ℝ → ℂ)
    (σ : ℝ) {v : ℝ} (hv : 0 < v) (t : ℝ) :
    metaplecticTransform ℓ (fun x => W x*mellinPhase t x) σ v =
      mellinPhase (-t) v*metaplecticShiftTransform ℓ W (-σ) v t := by
  let F : ℝ → ℂ := fun τ =>
    (v:ℂ)^(((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      mellin W (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)
  have he (τ : ℝ) :
      (v:ℂ)^(((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        mellin (fun x => W x*mellinPhase t x) (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I) = F (τ+t) := by
    rw [mellin_mul_phase]
    dsimp [F]
    have h1 : ((τ+t-t:ℝ):ℂ) = (τ:ℂ) := by push_cast; ring
    have h2 : ((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I+(t:ℂ)*Complex.I =
        ((-σ:ℝ):ℂ)+((τ+t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [h1,h2]
  have hphase (τ : ℝ) : F τ = mellinPhase (-t) v*
      ((v:ℂ)^(((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
        mellin W (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)) := by
    rw [mellinPhase_eq_cpow hv]
    dsimp [F]
    have hs : (((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
        (((-t:ℝ):ℂ)*Complex.I)+(((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I) := by push_cast; ring
    rw [hs,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    ring
  unfold metaplecticTransform metaplecticShiftTransform
  simp_rw [he]
  rw [integral_add_right_eq_self F t]
  simp_rw [hphase]
  rw [integral_const_mul]
  ring

/-- The original twisted transform has the sharp far-left bound. -/
theorem metaplecticTransform_twisted_far_left (ℓ : ℤ) (m : ℕ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 < v → ∀ t : ℝ,
      ‖metaplecticTransform ℓ (fun x => W x*mellinPhase t x) ((m:ℝ)-1/2) v‖ ≤
        C*v^(1/2-(m:ℝ))*(1+|t|)^(4*m) := by
  obtain ⟨C,hC,hbound⟩ := metaplecticShiftTransform_far_left ℓ m W hW hpos hsm
  refine ⟨C,hC,?_⟩
  intro v hv t
  rw [metaplecticTransform_twisted ℓ W _ hv t,norm_mul,mellinPhase_norm,one_mul]
  simpa only [show -((m:ℝ)-1/2) = 1/2-(m:ℝ) by ring] using hbound v hv t

end CubicFirstMoment

end

end OAI
