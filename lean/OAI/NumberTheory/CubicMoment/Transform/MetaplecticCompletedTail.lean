import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedContinuity

namespace OAI

/-! Add the actual discarded dual tail to the finite retained estimate.
Both sides are legitimate interval integrals of the original completed
sum; continuity is derived from the finite primal and critical dual forms. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_completed_tail_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X σ A J T E : ℝ} (hX : 0 < X) (hσ : 0 < σ) (hσs : σ < 1/10000)
    (hA : σ ≤ A) (hT : 0 < T)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (htail : ∀ t : ℝ, |t| ≤ 2*T →
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W x*mellinPhase t x) A X J nd‖ ≤ E) :
    (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X t-
      mellinPhase t X*metaplecticMain r ℓ (fun x => W x*mellinPhase t x) X‖)/T ≤
        (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
          ∑ nd ∈ metaplecticDualBall J,
            metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd‖)/T+
          ‖metaplecticPrefactor r ℓ‖*E := by
  let F := fun t : ℝ => metaplecticHeightCompleted r ℓ W X t-
    mellinPhase t X*metaplecticMain r ℓ (fun x => W x*mellinPhase t x) X
  let P := fun t : ℝ => metaplecticPrefactor r ℓ*
    ∑ nd ∈ metaplecticDualBall J,
      metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd
  have hF : Continuous F := (continuous_metaplectic_height_completed r ℓ W hW hX).sub
    (continuous_metaplectic_height_main r ℓ W hW hpos hsm X)
  have hP : Continuous P := continuous_const.mul
    (continuous_metaplectic_retained a hr ℓ W hW hpos hsm (hσ.le.trans hA) hX J hm hp)
  have hb (t : ℝ) (ht : t ∈ Icc T (2*T)) : ‖F t‖ ≤ ‖P t‖+‖metaplecticPrefactor r ℓ‖*E := by
    have habs : |t| ≤ 2*T := by rw [abs_of_nonneg (hT.le.trans ht.1)]; exact ht.2
    obtain ⟨hs,he⟩ := metaplectic_height_voronoi_far_line hV hr hsr ℓ W hW hpos hsm
      hX hσ hσs hA hm hp t
    rw [metaplecticDualTerm_split a r ℓ (fun x => W x*mellinPhase t x) A X J hs] at he
    have hfe : F t = mellinPhase t X*(P t+metaplecticPrefactor r ℓ*
        ∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W x*mellinPhase t x) A X J nd) := by
      dsimp [F,P]
      rw [he]
      ring
    rw [hfe,norm_mul,mellinPhase_norm,one_mul]
    calc
      _ ≤ ‖P t‖+‖metaplecticPrefactor r ℓ*
          ∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W x*mellinPhase t x) A X J nd‖ :=
        norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul]
        have hh := mul_le_mul_of_nonneg_left (htail t habs) (_root_.norm_nonneg (metaplecticPrefactor r ℓ))
        linarith only [hh]
  have hFi : IntervalIntegrable (fun t => ‖F t‖) volume T (2*T) :=
    hF.norm.intervalIntegrable T (2*T)
  have hPi : IntervalIntegrable (fun t => ‖P t‖) volume T (2*T) :=
    hP.norm.intervalIntegrable T (2*T)
  have hCi : IntervalIntegrable (fun _ : ℝ => ‖metaplecticPrefactor r ℓ‖*E) volume T (2*T) :=
    continuous_const.intervalIntegrable T (2*T)
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (show T ≤ 2*T by linarith) hFi (hPi.add hCi) hb
  have hh : (∫ t in T..2*T, ‖F t‖)/T ≤
      (∫ t in T..2*T, ‖P t‖)/T+‖metaplecticPrefactor r ℓ‖*E := by
    apply (div_le_iff₀ hT).mpr
    apply hi.trans_eq
    rw [intervalIntegral.integral_add hPi hCi,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [hT.ne']
    ring
  exact hh

end CubicFirstMoment

end

end OAI
