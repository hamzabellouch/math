import OAI.NumberTheory.DirichletL.Moments.FirstScale
import OAI.NumberTheory.DirichletL.Moments.SectorLocalization
import OAI.NumberTheory.DirichletL.Moments.FirstExtractedLedger

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstPhysicalLedger
open CenteredMomentFirstScale CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstExtractedLedger CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

theorem nominal_log (I J E : Ideal O) (hE : E≠0)
    (Z H X : ℝ) (hH : 0<H) (hX : 0<X) :
    Real.logb Z (firstNominalScale I J E H X)=
      2*Real.logb Z X-Real.logb Z ((commonPart I J).absNorm:ℝ)-
        Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)+
        Real.logb Z (E.absNorm:ℝ)-Real.logb Z H := by
  have hc:=norm_pos _ (commonPart_ne_zero I J)
  have hd:=norm_pos _ (commonPart_ne_zero J I)
  have he:=norm_pos E hE
  have hr:=active_norm_pos I J
  unfold firstNominalScale
  rw [Real.logb_div (mul_pos (mul_pos he hr) (sq_pos_of_pos hX)).ne'
      (mul_pos (mul_pos hH hc) hd).ne',
    Real.logb_mul (mul_pos he hr).ne' (sq_pos_of_pos hX).ne',
    Real.logb_mul he.ne' hr.ne',Real.logb_pow,
    Real.logb_mul (mul_pos hH hc).ne' hd.ne',Real.logb_mul hH.ne' hc.ne']
  push_cast
  ring

theorem retained_nominal_frequency (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1<Z) (hH : 0<H) (hX : 0<X)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n)≤
      Real.logb Z (firstNominalScale I J E H X)+frequencyLoss Z Csec ξ := by
  apply retained_first_dyad_enclosure Tsec Z Csec _ ξ hZ hC _ n hn
  simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (firstNominalScale_pos I J E hE H X hH hX)] using hsec

theorem retained_deficit (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1<Z) (hH : 0<H) (hX : 0<X)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec ξ≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n) := by
  linarith [retained_nominal_frequency I J E hE Z H X Tsec Csec ξ hZ hH hX hC hsec n hn]

theorem frequency_loss_eventually (Csec ξ : ℝ) (hC : 0<Csec) (hξ : 0<ξ) :
    ∃Z₀ : ℝ,1<Z₀ ∧ ∀Z : ℝ,Z₀≤Z → 1<Z ∧ frequencyLoss Z Csec ξ<ξ := by
  have hg := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ξ/4 by linarith))) (4*Csec)
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (hg.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max Z₀ 2,by linarith [le_max_right Z₀ (2:ℝ)],?_⟩
  intro Z hZ
  obtain ⟨hb,hZ1⟩:=hZ₀ Z ((le_max_left Z₀ 2).trans hZ)
  have hl:=Real.logb_le_logb_of_le hZ1 (show 0<4*Csec by positivity) hb
  rw [Real.logb_rpow (zero_lt_one.trans hZ1) hZ1.ne'] at hl
  exact ⟨hZ1,by unfold frequencyLoss;linarith⟩

theorem actual_first_saving (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hE : E≠0) (Z H X Tsec Csec ξ q w wo ell σ branch : ℝ)
    (hZ : 1<Z) (hH : 0<H) (hX : 0<X) (hC : 1≤Csec)
    (hξ : 0≤ξ) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n)
    (hq : 0≤q) (hw : 0≤w) (hwo : 0≤wo) (hell : 0≤ell) (hσ : 0≤σ)
    (hbranch : branch≤2) (hwσ : w≤7*σ/3) :
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let e:=Real.logb Z (E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n)
    2*(c+w)/3-3*σ-5*(frequencyLoss Z Csec ξ)/6≤
      firstSaving c D₀ w (q+R+e) wo (c+d-2*p-R)
        (max (D₀-c-2*w+wo) 0+branch*σ) ell := by
  dsimp only
  have hRn : (1:ℝ)≤((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hEn : (1:ℝ)≤(E.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hR:=Real.logb_nonneg hZ hRn
  have he:=Real.logb_nonneg hZ hEn
  apply actual_extracted_first_saving I J hI hJ Z hZ _ _ _ _ _ _ _ _ hw
    (by linarith) hwo hσ (frequencyLoss_nonneg Z Csec ξ hZ hC hξ)
    (by linarith) (retained_deficit I J E hE Z H X Tsec Csec ξ hZ hH hX
      (by linarith) hsec n hn) _ hell hwσ
  nlinarith

end SevenEighths.CenteredMomentFirstPhysicalLedger

end

end OAI
