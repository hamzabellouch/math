import OAI.NumberTheory.CubicMoment.Transform.MetaplecticMellinMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPoleContour
import OAI.NumberTheory.CubicMoment.Estimates.MellinHeckeContour

namespace OAI

/-! Applying the one-pole contour calculation to the Gauss series.
Polynomial strip growth follows from Heath-Brown (19), the finite-divisor
identity and partial summation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace CubicFirstMoment

def MetaplecticStripPolynomial (F : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ σ ∈ Icc a b, ∀ v : ℝ, 1 ≤ |v| →
    ‖F ((σ:ℂ)+(v:ℂ)*Complex.I)‖ ≤ C*(1+|v|)^N

lemma continuous_integrable_of_large_height_bound (f : ℝ → ℂ) (hf : Continuous f)
    (H : ℝ → ℝ) (hH : Integrable H) (hH0 : ∀ t, 0 ≤ H t)
    (hb : ∀ t : ℝ, 1 ≤ |t| → ‖f t‖ ≤ H t) : Integrable f := by
  have hin : Integrable ((Icc (-1:ℝ) 1).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hf.integrableOn_Icc
  have hout : Integrable (((Icc (-1:ℝ) 1)ᶜ).indicator f) := by
    apply hH.mono' (hf.aestronglyMeasurable.indicator measurableSet_Icc.compl)
    filter_upwards with t
    by_cases ht : t ∈ (Icc (-1:ℝ) 1)ᶜ
    · rw [indicator_of_mem ht]
      apply hb
      have hnot : t ∉ Icc (-1:ℝ) 1 := ht
      by_contra hn
      have ha := abs_lt.mp (lt_of_not_ge hn)
      exact hnot ⟨ha.1.le,ha.2.le⟩
    · rw [indicator_of_notMem ht,norm_zero]
      exact hH0 t
  convert hin.add hout using 1
  ext t
  by_cases ht : t ∈ Icc (-1:ℝ) 1 <;> simp [ht]

lemma metaplectic_mellin_large_majorant (F : ℂ → ℂ) {a b : ℝ}
    (hF : MetaplecticStripPolynomial F a b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {U : ℝ} (hU : 1 ≤ U) (t : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc a b, ∀ v : ℝ, 1 ≤ |v| →
      ‖mellin W ((σ:ℂ)+((v+t):ℂ)*Complex.I)*
        (U:ℂ)^((σ:ℂ)+((v+t):ℂ)*Complex.I)*F ((σ:ℂ)+(v:ℂ)*Complex.I)‖ ≤
        mellinEdgeMajorant K (v+t) := by
  obtain ⟨C,hC,N,hbound⟩ := hF
  let L : ℂ → ℂ := fun s => if 1 ≤ |s.im| then F s else 0
  have hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L ((σ:ℂ)+((τ-t):ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N := by
    intro σ hσ τ
    have hi : (((σ:ℂ)+((τ-t):ℂ)*Complex.I):ℂ).im = τ-t := by simp
    dsimp only [L]
    rw [hi]
    split_ifs with hτ
    · simpa only [Complex.ofReal_sub] using hbound σ hσ (τ-t) hτ
    · simp only [norm_zero]
      positivity
  obtain ⟨K,hK,hKbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hU t L hC N
    (by simpa only [Complex.ofReal_sub] using hL)
  refine ⟨K,hK,?_⟩
  intro σ hσ v hv
  have h := hKbound σ hσ (v+t)
  simpa [L,Complex.ofReal_add,Complex.ofReal_sub,hv] using h

/-- Under polynomial strip growth, the original sum equals its shifted
integral plus the explicit residue. -/
theorem metaplectic_smooth_shift_of_polynomial {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    {a : ℝ} (ha : 1/2 < a) (hac : a < 5/6)
    (hpoly : MetaplecticStripPolynomial (F r) a 2)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {U : ℝ} (hU : 1 ≤ U) (t : ℝ) :
    metaplecticSmoothSum r W U t = ((1/(2*Real.pi):ℝ):ℂ)*
      (∫ v : ℝ, mellin W ((a:ℂ)+(v:ℂ)*Complex.I)*
        (U:ℂ)^((a:ℂ)+(v:ℂ)*Complex.I)*F r ((a:ℂ)+((v-t):ℂ)*Complex.I))+
      metaplecticResidue r*(U:ℂ)^((5/6:ℝ)+(t:ℂ)*Complex.I)*
        mellin W ((5/6:ℝ)+(t:ℂ)*Complex.I) := by
  obtain ⟨_,g,hg,heq⟩ := hF r hr hs
  obtain ⟨K,hK,hbound⟩ := metaplectic_mellin_large_majorant (F r) hpoly W hW hpos hsm hU t
  let M : ℂ → ℂ := fun s => mellin W (s+(t:ℂ)*Complex.I)*(U:ℂ)^(s+(t:ℂ)*Complex.I)
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have : NeZero (U:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hUp.ne'⟩
  have hM : Differentiable ℂ M :=
    ((smooth_mellin_entire W hW hpos hsm.continuous).comp
      (differentiable_id.add_const _)).mul
      ((differentiable_const_cpow_of_neZero _).comp (differentiable_id.add_const _))
  have hg' : DifferentiableOn ℂ g (closedVerticalStrip a 2) := hg.mono (by
    intro s h
    exact ha.trans_le h.1)
  have he (σ v : ℝ) : M ((σ:ℂ)+(v:ℂ)*Complex.I)*F r ((σ:ℂ)+(v:ℂ)*Complex.I) =
      mellin W ((σ:ℂ)+((v+t):ℂ)*Complex.I)*(U:ℂ)^((σ:ℂ)+((v+t):ℂ)*Complex.I)*
        F r ((σ:ℂ)+(v:ℂ)*Complex.I) := by
    have hh : (σ:ℂ)+(v:ℂ)*Complex.I+(t:ℂ)*Complex.I =
        (σ:ℂ)+((v+t):ℂ)*Complex.I := by ring
    simp only [M,hh]
  have hHInt : Integrable (fun v : ℝ => mellinEdgeMajorant K (v+t)) :=
    (measurePreserving_add_right volume t).integrable_comp_of_integrable
      (mellinEdgeMajorant_integrable K)
  have hInt (σ : ℝ) (hσ : σ ∈ Icc a 2) (hσp : σ ≠ 5/6) :
      Integrable (fun v : ℝ => M ((σ:ℂ)+(v:ℂ)*Complex.I)*F r ((σ:ℂ)+(v:ℂ)*Complex.I)) := by
    apply continuous_integrable_of_large_height_bound _
      ((hM.continuous.comp (by fun_prop)).mul (hF.continuous_line hr hs
        (ha.trans_le hσ.1) hσp)) _ hHInt
    · intro v
      dsimp [mellinEdgeMajorant]
      positivity
    · intro v hv
      dsimp only [Function.comp_apply, Pi.mul_apply]
      rw [he]
      exact hbound σ hσ v hv
  have hLine (σ : ℝ) (hσ : σ ∈ Icc a 2) (hσp : σ ≠ 5/6) (v : ℝ) :
      F r ((σ:ℂ)+(v:ℂ)*Complex.I) =
        g ((σ:ℂ)+(v:ℂ)*Complex.I)+metaplecticResidue r/((σ:ℂ)+(v:ℂ)*Complex.I-((5/6:ℝ):ℂ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    apply heq
    · simpa using ha.trans_le hσ.1
    · intro h
      exact hσp (by simpa using congrArg Complex.re h)
  have ha2 : a ≤ 2 := by linarith
  have hLeft := hInt a ⟨le_rfl,ha2⟩ hac.ne
  have hRight := hInt 2 ⟨ha2,le_rfl⟩ (by norm_num)
  have hshift := mellin_single_pole_shift_of_majorant M g (metaplecticResidue r) hac
    (by norm_num : (5/6:ℝ) < 2) hM hg'
    (by simpa only [hLine a ⟨le_rfl,ha2⟩ hac.ne] using hLeft)
    (by simpa only [hLine 2 ⟨ha2,le_rfl⟩ (by norm_num)] using hRight)
    (fun v => mellinEdgeMajorant K (v+t))
    ((mellinEdgeMajorant_tendsto K).1.comp (tendsto_atTop_add_const_right _ _ tendsto_id))
    ((mellinEdgeMajorant_tendsto K).2.comp (tendsto_atBot_add_const_right _ _ tendsto_id))
    (by
      intro σ hσ v hv
      have hn : (σ:ℂ)+(v:ℂ)*Complex.I ≠ (5/6:ℂ) := by
        intro hh
        have hz : v = 0 := by simpa using congrArg Complex.im hh
        simp only [hz, abs_zero] at hv
        linarith
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [← heq _ (by simpa using ha.trans_le hσ.1) hn]
      rw [he]
      exact hbound σ hσ v hv)
  simp_rw [← hLine a ⟨le_rfl,ha2⟩ hac.ne,
    ← hLine 2 ⟨ha2,le_rfl⟩ (by norm_num)] at hshift
  have htranslate (σ : ℝ) :
      (∫ v : ℝ, M ((σ:ℂ)+(v:ℂ)*Complex.I)*F r ((σ:ℂ)+(v:ℂ)*Complex.I)) =
      ∫ v : ℝ, mellin W ((σ:ℂ)+(v:ℂ)*Complex.I)*(U:ℂ)^((σ:ℂ)+(v:ℂ)*Complex.I)*
        F r ((σ:ℂ)+((v-t):ℂ)*Complex.I) := by
    let Q : ℝ → ℂ := fun v => mellin W ((σ:ℂ)+(v:ℂ)*Complex.I)*
      (U:ℂ)^((σ:ℂ)+(v:ℂ)*Complex.I)*F r ((σ:ℂ)+((v-t):ℂ)*Complex.I)
    calc
      _ = ∫ v : ℝ, Q (v+t) := by
        apply integral_congr_ae
        filter_upwards with v
        rw [he]
        simp [Q]
      _ = ∫ v : ℝ, Q v := integral_add_right_eq_self Q t
  rw [metaplectic_smooth_mellin hF hr hs W hW hpos hsm hUp t,
    ← htranslate 2,hshift,htranslate a]
  have hc : ((1/(2*Real.pi):ℝ):ℂ)*((2*Real.pi:ℝ):ℂ) = 1 := by
    push_cast
    field_simp
  rw [mul_add,← mul_assoc _ ((2*Real.pi:ℝ):ℂ),hc,one_mul]
  dsimp only [M]
  ring

end CubicFirstMoment

end

end OAI
