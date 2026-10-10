import OAI.NumberTheory.CubicMoment.Estimates.MellinSeries
import OAI.NumberTheory.CubicMoment.Estimates.NormSeries
import OAI.NumberTheory.CubicGram.Reciprocity

namespace OAI

/-! The zero-angular metaplectic inputs, stated for the literal Gauss series.

Sources: Heath-Brown, *Kummer's conjecture for cubic Gauss sums* (2000),
§3 Lemma 3 (author manuscript p.9), with angular index zero; Dunn–Radziwiłł,
*Bias in cubic Gauss sums* (2024), arXiv:2109.07463v3, Proposition 5.2,
pp.29–30. No Type-I estimate or Mellin contour identity is an input here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev PrimaryArgument := {u : Eisenstein // primary u}

def metaplecticGaussSeries (r : Eisenstein) (s : ℂ) : ℂ :=
  normDirichletSeries (fun u : PrimaryArgument => gauss (r*u))
    (fun u : PrimaryArgument => norm u) s

def metaplecticTotient (r : Eisenstein) : ℝ := (Nat.card (Residues r)ˣ : ℝ)

def metaplecticEulerAtTwo (r : Eisenstein) : ℝ :=
  ∑' d : PrimaryArgument, if IsCoprime r (d:Eisenstein) then norm d^(-2:ℝ) else 0

def metaplecticA0 : ℝ :=
  (2*Real.pi)^(5/3:ℝ)/(3^(7/2:ℝ)*Real.Gamma (2/3:ℝ))

def metaplecticResidue (r : Eisenstein) : ℂ :=
  (metaplecticA0*metaplecticTotient r*norm r^(-7/6:ℝ)/metaplecticEulerAtTwo r : ℝ)

lemma primary_norm_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun u : PrimaryArgument => norm u^(-s)) :=
  (summable_eisenstein_norm_rpow hs).subtype _

lemma gauss_series_absolutely_summable {r : Eisenstein} (hr : primary r)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun u : PrimaryArgument => ‖gauss (r*u)‖*norm u^(-σ)) := by
  apply (primary_norm_rpow_summable hσ).of_nonneg_of_le
  · intro u
    exact mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  · intro u
    have hnorm : ‖gauss (r*u)‖ ≤ 1 := by
      rw [norm_gauss (primary_mul hr u.property)]
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _) hnorm

lemma metaplecticTotient_le_norm {r : Eisenstein} (hr : primary r) :
    metaplecticTotient r ≤ norm r := by
  let := finite_residues (primary_ne_zero hr)
  have h := Nat.card_le_card_of_injective (Units.val : (Residues r)ˣ → Residues r)
    Units.val_injective
  rw [residues_card (primary_ne_zero hr)] at h
  exact (Nat.cast_le (α := ℝ).mpr h).trans_eq (normNat_cast r)

lemma metaplecticEulerAtTwo_summable (r : Eisenstein) :
    Summable (fun d : PrimaryArgument => if IsCoprime r (d:Eisenstein)
      then norm d^(-2:ℝ) else 0) :=
  (primary_norm_rpow_summable (show (1:ℝ) < 2 by norm_num)).indicator _

lemma metaplecticEulerAtTwo_ge_one (r : Eisenstein) : 1 ≤ metaplecticEulerAtTwo r := by
  let oneArg : PrimaryArgument := ⟨1,by simp [primary]⟩
  have h := (metaplecticEulerAtTwo_summable r).le_tsum oneArg
    (fun d _ => by
      split_ifs
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · exact le_rfl)
  simpa [oneArg,metaplecticEulerAtTwo,norm,isCoprime_one_right] using h

lemma norm_metaplecticResidue_le {r : Eisenstein} (hr : primary r) :
    ‖metaplecticResidue r‖ ≤ |metaplecticA0| *norm r^(-1/6:ℝ) := by
  have hN : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hφ : 0 ≤ metaplecticTotient r := Nat.cast_nonneg _
  have hE : 1 ≤ metaplecticEulerAtTwo r := metaplecticEulerAtTwo_ge_one r
  have hp : 0 ≤ norm r^(-7/6:ℝ) := Real.rpow_nonneg hN.le _
  rw [metaplecticResidue,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,abs_mul,
    abs_of_nonneg hφ,abs_of_nonneg hp,abs_of_pos (zero_lt_one.trans_le hE)]
  calc
    _ ≤ |metaplecticA0| *metaplecticTotient r*norm r^(-7/6:ℝ) :=
      div_le_self (by positivity) hE
    _ ≤ |metaplecticA0| *norm r*norm r^(-7/6:ℝ) := by
      gcongr
      exact metaplecticTotient_le_norm hr
    _ = _ := by
      have hpw : norm r*norm r^(-7/6:ℝ) = norm r^(-1/6:ℝ) := by
        calc
          _ = norm r^(1:ℝ)*norm r^(-7/6:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hN]; norm_num
      rw [mul_assoc,hpw]

/-- The needed continuation/residue consequence of DR2024 Proposition 5.2,
after the nonvanishing Euler factor in `Re s>1/2` is removed. -/
def MetaplecticContinuation (F : Eisenstein → ℂ → ℂ) : Prop :=
  ∀ r : Eisenstein, primary r → Squarefree r →
    (∀ s : ℂ, 1 < s.re → F r s = metaplecticGaussSeries r s) ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s | (1/2:ℝ) < s.re} ∧
      ∀ s : ℂ, (1/2:ℝ) < s.re → s ≠ (5/6:ℂ) →
        F r s = g s + metaplecticResidue r/(s-(5/6:ℂ))

/-- HB2000 §3 Lemma 3, angular index zero, with only its actual vertical
mean-square bound as the published hypothesis. -/
def MetaplecticMeanSquare (F : Eisenstein → ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1/12 → ∃ C : ℝ, 0 < C ∧
    ∀ r : Eisenstein, primary r → Squarefree r → ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖F r ((1/2+ε:ℝ)+(t:ℂ)*Complex.I)‖^2) ≤
        C*(norm r)^(1/2+4*ε)*T^2

lemma MetaplecticContinuation.continuous_line {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    {σ : ℝ} (hσ : (1/2:ℝ) < σ) (hσp : σ ≠ 5/6) :
    Continuous (fun t : ℝ => F r ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
  obtain ⟨_,g,hg,heq⟩ := hF r hr hs
  have hline : Continuous (fun t : ℝ => (σ:ℂ)+(t:ℂ)*Complex.I) := by fun_prop
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*Complex.I ≠ (5/6:ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hre
    norm_num at hre
    exact hσp hre
  have hc : Continuous (fun t : ℝ => g ((σ:ℂ)+(t:ℂ)*Complex.I) +
      metaplecticResidue r/((σ:ℂ)+(t:ℂ)*Complex.I-(5/6:ℂ))) := (hg.continuousOn.comp_continuous hline (by intro t; simpa using hσ)).add
    (continuous_const.div (hline.sub continuous_const) (fun t => sub_ne_zero.mpr (hne t)))
  exact hc.congr (fun t => (heq _ (by simpa using hσ) (hne t)).symm)

def metaplecticSmoothSum (r : Eisenstein) (W : ℝ → ℂ) (U t : ℝ) : ℂ :=
  ∑' u : PrimaryArgument, (gauss (r*u)*(norm u:ℂ)^((t:ℂ)*Complex.I))*W (norm u/U)

/-- The original smoothed, norm-twisted Gauss series on its line of
absolute convergence. The subsequent pole-crossing shift is separate. -/
theorem metaplectic_smooth_mellin {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {U : ℝ} (hU : 0 < U) (t : ℝ) :
    metaplecticSmoothSum r W U t = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ v : ℝ, mellin W ((2:ℝ)+(v:ℂ)*Complex.I)*
        (U:ℂ)^((2:ℝ)+(v:ℂ)*Complex.I)*
        F r ((2:ℝ)+((v-t):ℂ)*Complex.I) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hn (u : PrimaryArgument) : 0 < norm u :=
    norm_pos_of_ne_zero (primary_ne_zero u.property)
  have habs : Summable (fun u : PrimaryArgument =>
      ‖gauss (r*u)*(norm u:ℂ)^((t:ℂ)*Complex.I)‖*norm u^(-(2:ℝ))) := by
    simpa only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hn _),Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
      zero_mul,sub_self,Real.rpow_zero,mul_one] using
      gauss_series_absolutely_summable hr (show (1:ℝ) < 2 by norm_num)
  rw [metaplecticSmoothSum,smooth_mellin_series _ _ hn W hW hpos hsm 2 habs hU]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  congr 1
  rw [(hF r hr hs).1 _ (by norm_num)]
  unfold metaplecticGaussSeries normDirichletSeries
  apply tsum_congr
  intro u
  rw [mul_assoc,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hn u).ne')]
  congr 2
  push_cast
  ring

end CubicFirstMoment

end

end OAI
