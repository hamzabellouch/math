import OAI.Analysis.ModularRecovery.FourierLocalization

namespace OAI

/-! Uniformly bounded recovery on exact factor-four spectral bands. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma RealSpectralCalculus.HasSpectralSupport.real_smul {D : RealSpectralCalculus H}
    {I : Set ℝ} {h : H} (hh : D.HasSpectralSupport I h) (r : ℝ) :
    D.HasSpectralSupport I (r • h) := by
  rw [← algebraMap_smul ℂ r h]
  exact hh.smul _

lemma RealSpectralCalculus.HasSpectralSupport.sum {D : RealSpectralCalculus H}
    {I : Set ℝ} {ι : Type uι} [Fintype ι] {h : ι → H}
    (hh : ∀ i, D.HasSpectralSupport I (h i)) : D.HasSpectralSupport I (∑ i, h i) := by
  intro f hf
  simp only [map_sum, hh _ f hf, Finset.sum_const_zero]

lemma phaseSum_mem (M : VonNeumannAlgebra H) {n : ℕ} (a : Fin n → H →L[ℂ] H)
    (ha : ∀ i, a i ∈ M) (e : Fin n → Fin 4) : phaseSum a e ∈ M :=
  sum_mem (fun i _ => M.toStarSubalgebra.smul_mem (ha i) _)

lemma phaseSum_vector_support (D : RealSpectralCalculus H) (xi : H) {I : Set ℝ} {n : ℕ}
    (a : Fin n → H →L[ℂ] H) (ha : ∀ i, D.HasSpectralSupport I (a i xi))
    (e : Fin n → Fin 4) : D.HasSpectralSupport I (phaseSum a e xi) := by
  simp only [phaseSum, sum_apply, smul_apply]
  exact RealSpectralCalculus.HasSpectralSupport.sum (fun i => (ha i).smul _)

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
lemma norm_sq_le_twice_sum (x y : H) :
    ‖x‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * ‖x-y‖ ^ 2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg x) (norm_le_norm_sub_add x y) 2
  nlinarith [sq_nonneg (‖y‖-‖x-y‖)]

namespace StandardModularData

lemma bounded_recovery_finite_step (S : StandardModularData H) (T : H →L[ℂ] H)
    {s d gamma Q K : ℝ} (hd : 0 < d) (hg : 0 < gamma) (hK : 0 < K)
    (hcut : ‖T‖ ^ 2 * (K ^ 2)⁻¹ * Q ≤ gamma / 4)
    {y : H →L[ℂ] H} (hy : y ∈ S.M)
    (hband : S.D.HasSpectralSupport (Icc (s-d) (s+d)) (y S.xi))
    (n : ℕ) (p t : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hdef : gamma ≤ ∑ i, p i * ‖T (S.sigma (t i) y S.xi)‖ ^ 2)
    (hmom : (S.state ((S.modularAverage p t (star y * y)) ^ 2)).re +
      (∑ i, p i * (S.state (star (S.sigma (t i) y) *
        S.modularAverage p t (y * star y) * S.sigma (t i) y)).re) ≤ Q) :
    ∃ v : H →L[ℂ] H, v ∈ S.M ∧ ‖v‖ ≤ filterL1 * K ∧
      Real.sqrt gamma / 2 ≤ ‖T (v S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s-2*d) (s+2*d)) (v S.xi) := by
  let a (i : Fin n) := Real.sqrt (p i) • S.sigma (t i) y
  let z (e : Fin n → Fin 4) := phaseSum a e
  let v (e : Fin n → Fin 4) := S.bandFilter s d hd (polarCutoff (z e) K)
  have hzm (e) : z e ∈ S.M := phaseSum_mem S.M a
    (fun i => S.real_smul_mem (S.sigma_mem (t i) hy) _) e
  have hzb (e) : S.D.HasSpectralSupport (Icc (s-d) (s+d)) (z e S.xi) := by
    apply phaseSum_vector_support
    intro i
    simp only [a, smul_apply, S.sigma_apply_xi]
    exact (hband.unitary (t i)).real_smul _
  have hvnorm (e) : ‖v e‖ ≤ filterL1 * K :=
    (S.norm_bandFilter_le s d hd _).trans
      (mul_le_mul_of_nonneg_left (norm_polarCutoff_le _ hK) filterL1_nonneg)
  have hfourth : phaseMean n (fun e => (S.state ((star (z e) * z e)^2)).re) ≤ Q := by
    have hh := S.phaseMean_fourth_le n p hp (fun i => S.sigma (t i) y)
    rw [S.averageSquare_eq, S.averageReverseSquare_eq] at hh
    exact hh.trans hmom
  have hzd : gamma ≤ phaseMean n (fun e => ‖T (z e S.xi)‖^2) := by
    rw [S.phaseMean_defect T n p hp]
    exact hdef
  have herr (e) : ‖z e S.xi - v e S.xi‖ ^ 2 ≤
      (K ^ 2)⁻¹ * (S.state ((star (z e) * z e)^2)).re := by
    have hf := S.bandFilter_vector_error_le hd (polarCutoff (z e) K) (hzb e)
    have he : ‖z e S.xi - v e S.xi‖ ≤ ‖(z e - polarCutoff (z e) K) S.xi‖ := by
      simpa only [v, sub_apply, norm_sub_rev] using hf
    exact (pow_le_pow_left₀ (norm_nonneg _) he 2).trans (polarCutoff_vector_error_sq S.xi (z e) hK)
  have hdet (e) : ‖T (z e S.xi)‖ ^ 2 ≤ 2 * ‖T (v e S.xi)‖ ^ 2 +
      (2 * ‖T‖ ^ 2 * (K ^ 2)⁻¹) * (S.state ((star (z e) * z e)^2)).re := by
    have hh := norm_sq_le_twice_sum (T (z e S.xi)) (T (v e S.xi))
    have ht : ‖T (z e S.xi) - T (v e S.xi)‖ ^ 2 ≤
        ‖T‖ ^ 2 * ‖z e S.xi - v e S.xi‖ ^ 2 := by
      rw [← map_sub]
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
    have hn := mul_le_mul_of_nonneg_left (herr e) (sq_nonneg ‖T‖)
    nlinarith
  have hmean := phaseMean_mono n hdet
  rw [phaseMean_add, phaseMean_mul, phaseMean_mul] at hmean
  have hfourth' := mul_le_mul_of_nonneg_left hfourth
    (show 0 ≤ 2 * ‖T‖^2 * (K^2)⁻¹ by positivity)
  have hvd : gamma / 4 ≤ phaseMean n (fun e => ‖T (v e S.xi)‖ ^ 2) := by
    nlinarith
  obtain ⟨e,he⟩ := exists_phaseMean_le n (fun e => ‖T (v e S.xi)‖ ^ 2)
  refine ⟨v e, S.bandFilter_mem s d hd (polarCutoff_mem S.M (hzm e) K), hvnorm e, ?_,
    S.bandFilter_support s d hd _⟩
  have hs := Real.sq_sqrt hg.le
  have hn := Real.sqrt_nonneg gamma
  have hnorm := norm_nonneg (T (v e S.xi))
  nlinarith

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def recoveryMomentBound (s : ℝ) : ℝ := 26 + 16 * Real.exp (s+1)

lemma recoveryMomentBound_pos (s : ℝ) : 0 < recoveryMomentBound s := by
  unfold recoveryMomentBound
  positivity

omit [CompleteSpace H] in
lemma exists_recovery_cutoff (T : H →L[ℂ] H) {gamma : ℝ} (hg : 0 < gamma) (s : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ‖T‖^2 * (K^2)⁻¹ * recoveryMomentBound s ≤ gamma/4 := by
  let A := 4 * ‖T‖^2 * recoveryMomentBound s / gamma
  let K := A+1
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by have := (recoveryMomentBound_pos s).le; positivity) hg.le
  have hK : 0 < K := by dsimp [K]; linarith
  have hKsq : A ≤ K^2 := by dsimp [K]; nlinarith [sq_nonneg A]
  have hh : 4 * ‖T‖^2 * recoveryMomentBound s ≤ K^2 * gamma := (div_le_iff₀ hg).mp hKsq
  refine ⟨K,hK,?_⟩
  have he : ‖T‖^2 * (K^2)⁻¹ * recoveryMomentBound s =
      (‖T‖^2 * recoveryMomentBound s) / K^2 := by ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hK)).mpr
  nlinarith

namespace StandardModularData

lemma moment_bound_of_narrow_band (S : StandardModularData H) {s rho : ℝ}
    (hwidth : 2*rho ≤ 1) {y : H →L[ℂ] H} (hy : y ∈ S.M) (hn : ‖y S.xi‖ ≤ 2)
    (hband : S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho)) (y S.xi)) :
    (‖y S.xi‖^2+1)^2 + ‖y S.xi‖^2 * ‖star y S.xi‖^2 + 1 ≤ recoveryMomentBound s := by
  have hstar := S.norm_star_apply_xi_le hy hband
    (b := s+1) (fun u hu => le_trans hu.2 (by linarith))
  have hexp : (Real.exp ((s+1)/2))^2 = Real.exp (s+1) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquare : ‖star y S.xi‖^2 ≤ Real.exp (s+1) * ‖y S.xi‖^2 := by
    simpa only [mul_pow, hexp] using pow_le_pow_left₀ (norm_nonneg _) hstar 2
  let q := ‖y S.xi‖^2
  let b := ‖star y S.xi‖^2
  have hq : q ≤ 4 := by
    simpa only [show (2:ℝ)^2 = 4 by norm_num] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hb0 : 0 ≤ b := sq_nonneg _
  have hb : b ≤ 4 * Real.exp (s+1) := by
    calc
      b ≤ Real.exp (s+1) * q := hsquare
      _ ≤ Real.exp (s+1) * 4 := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  have hprod : q*b ≤ 16 * Real.exp (s+1) := by
    calc
      _ ≤ 4*b := mul_le_mul_of_nonneg_right hq hb0
      _ ≤ 4*(4*Real.exp (s+1)) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  change (q+1)^2 + q*b + 1 ≤ recoveryMomentBound s
  unfold recoveryMomentBound
  nlinarith

lemma exists_band_representative_with_defect (S : StandardModularData H)
    (omega : Ultrafilter ℕ) (T : H →L[ℂ] H) {s rho gamma : ℝ}
    (hrho : 0 < rho) (hg : 0 < gamma) {h : H} (hn : ‖h‖ = 1)
    (hband : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h)
    (hdef : 4*gamma ≤ fixedMean omega (S.D.orbitDefect T h)) :
    ∃ y : H →L[ℂ] H, y ∈ S.M ∧ ‖y S.xi‖ ≤ 2 ∧
      S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho)) (y S.xi) ∧
      gamma < fixedMean omega (S.D.orbitDefect T (y S.xi)) := by
  let eps := gamma / (3 * (‖T‖^2+1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨y,hy,hyn,hyclose,hyband⟩ := S.exists_band_representative hrho hband hn heps
  refine ⟨y,hy,hyn,hyband,?_⟩
  have hdiff := S.D.abs_mean_orbitDefect_sub_le omega T (y S.xi) h
  have hbound : ‖T‖^2 * (‖y S.xi‖+‖h‖) * ‖y S.xi-h‖ < gamma := by
    calc
      _ ≤ 3 * (‖T‖^2+1) * ‖y S.xi-h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [hn]
        have := sq_nonneg ‖T‖
        nlinarith
      _ < 3 * (‖T‖^2+1) * eps := mul_lt_mul_of_pos_left hyclose (by positivity)
      _ = gamma := by dsimp [eps]; field_simp
  have habs := hdiff.trans_lt hbound
  have hlo := (abs_lt.mp habs).1
  linarith

lemma bounded_recovery_single (S : StandardModularData H) (hscalar : S.ScalarCentralizer)
    (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop) (T : H →L[ℂ] H)
    {s rho gamma K : ℝ} (hrho : 0 < rho) (hwidth : 2*rho ≤ 1)
    (hg : 0 < gamma) (hK : 0 < K)
    (hcut : ‖T‖^2 * (K^2)⁻¹ * recoveryMomentBound s ≤ gamma/4)
    {h : H} (hn : ‖h‖ = 1) (hband : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h)
    (hdef : 4*gamma ≤ fixedMean omega (S.D.orbitDefect T h)) :
    ∃ v : H →L[ℂ] H, v ∈ S.M ∧ ‖v‖ ≤ filterL1*K ∧ Real.sqrt gamma/2 ≤ ‖T (v S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s-4*rho) (s+4*rho)) (v S.xi) := by
  obtain ⟨y,hy,hyn,hyband,hydef⟩ := S.exists_band_representative_with_defect omega T hrho hg hn hband hdef
  obtain ⟨n,p,t,hp,_hsum,hpd,hpm⟩ := S.exists_finite_defect_moment_average hscalar omega hω T hy hydef
  have hbound := hpm.trans (S.moment_bound_of_narrow_band hwidth hy hyn hyband)
  have he := S.bounded_recovery_finite_step T (mul_pos (by norm_num : (0:ℝ)<2) hrho) hg hK
    hcut hy hyband n p t hp hpd hbound
  simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 from by norm_num] using he

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bounded_recovery (S : StandardModularData H) (hscalar : S.ScalarCentralizer)
    (omega : Ultrafilter ℕ) (hfree : (omega : Filter ℕ) ≤ Filter.atTop)
    (T : H →L[ℂ] H) (s : ℝ) (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta0 : Tendsto delta atTop (𝓝 0)) (h : ℕ → H) (hunit : ∀ n, ‖h n‖ = 1)
    (hband : ∀ n, S.D.HasSpectralSupport (Icc (s - delta n) (s + delta n)) (h n))
    (hpositive : 0 < Filter.limsup
      (fun n => fixedMean omega (fun t => ‖T (S.D.unitary t (h n))‖ ^ 2)) atTop) :
    RecoveryConclusion S T s delta := by
  let a : ℕ → ℝ := fun n => fixedMean omega (S.D.orbitDefect T (h n))
  let gamma : ℝ := Filter.limsup a atTop / 8
  have hpos : 0 < Filter.limsup a atTop := hpositive
  have hg : 0 < gamma := by dsimp [gamma]; positivity
  have hlt : 4 * gamma < Filter.limsup a atTop := by dsimp [gamma]; linarith
  have hco := Filter.isCoboundedUnder_le_of_le atTop
    (fun n => S.D.mean_orbitDefect_nonneg omega T (h n))
  have hfreq : ∃ᶠ n in atTop, 4 * gamma < a n :=
    Filter.frequently_lt_of_lt_limsup hco hlt
  have hw : ∀ᶠ n in atTop, 2 * delta n ≤ 1 := by
    filter_upwards [hdelta0.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with n hn
    linarith
  obtain ⟨nj,hnj,hs⟩ := Filter.extraction_of_frequently_atTop (hfreq.and_eventually hw)
  obtain ⟨K,hK,hcut⟩ := exists_recovery_cutoff T hg s
  have hex : ∀ j, ∃ v : H →L[ℂ] H, v ∈ S.M ∧ ‖v‖ ≤ filterL1*K ∧
      Real.sqrt gamma/2 ≤ ‖T (v S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s-4*delta (nj j)) (s+4*delta (nj j))) (v S.xi) := by
    intro j
    exact S.bounded_recovery_single hscalar omega hfree T (hdelta _) (hs j).2 hg hK
      hcut (hunit _) (hband _) (hs j).1.le
  choose v hv using hex
  refine ⟨nj,hnj,v,filterL1*K,Real.sqrt gamma/2,?_,hv⟩
  exact div_pos (Real.sqrt_pos.mpr hg) (by norm_num)

end BoundedRecovery

end
end
end

end OAI
