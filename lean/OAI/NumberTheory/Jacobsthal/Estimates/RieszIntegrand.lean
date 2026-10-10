import OAI.NumberTheory.Jacobsthal.Analysis.RieszIntegralRepresentation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped BigOperators

noncomputable def rieszSum (f : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), f n*(rieszWeight ((n:ℝ)/X):ℂ)

lemma tsum_riesz_eq_finite (f : ℕ → ℂ) {X : ℝ} (hX : 0 < X) :
    (∑' n:ℕ, f n*(rieszWeight ((n:ℝ)/X):ℂ)) = rieszSum f X := by
  unfold rieszSum
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌊X⌋₊ < n := by simp only [Finset.mem_range] at hn; omega
  have hXn : X < (n:ℝ) := (Nat.floor_lt hX.le).mp hn'
  have hw : rieszWeight ((n:ℝ)/X) = 0 := rieszWeight_eq_zero
    ((le_div_iff₀ hX).mpr (by linarith))
  rw [hw,Complex.ofReal_zero,mul_zero]

theorem finite_character_riesz_mellin {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X : ℝ} (hs : 1 < sigma) (hX : 0 < X) :
    rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X =
      mellinFactor * ∫ t:ℝ,
        (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  rw [← tsum_riesz_eq_finite _ hX]
  exact character_riesz_mellin chi hs hX

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Filter
open scoped Topology

noncomputable def characterRieszIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X : ℝ) (s : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction chi) s * rieszKernel s * (X:ℂ)^s

lemma finite_riesz_eq_integrand {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X : ℝ} (hs : 1 < sigma) (hX : 0 < X) :
    rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X =
      mellinFactor * ∫ t:ℝ, characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  simpa only [characterRieszIntegrand,logDeriv_apply,neg_div] using finite_character_riesz_mellin chi hs hX

lemma norm_characterRieszIntegrand {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ‖characterRieszIntegrand chi X s‖ =
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ * ‖rieszKernel s‖ * X^s.re := by
  unfold characterRieszIntegrand
  rw [norm_mul,norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hX]

lemma differentiableAt_rieszKernel {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ rieszKernel s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he
    linarith
  unfold rieszKernel
  have hc : DifferentiableAt ℂ (fun _ : ℂ => (1:ℂ)) s := by fun_prop
  exact hc.div (by fun_prop) (mul_ne_zero h0 h1)

lemma differentiableAt_characterRieszIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {X : ℝ} (hX : 0 < X)
    {s : ℂ} (hs : 0 < s.re) (hne : DirichletCharacter.LFunction chi s ≠ 0) :
    DifferentiableAt ℂ (characterRieszIntegrand chi X) s := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hder : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction chi)) s :=
    (hL.analyticAt s).deriv.differentiableAt
  have hlog : DifferentiableAt ℂ (fun z => -logDeriv (DirichletCharacter.LFunction chi) z) s := by
    change DifferentiableAt ℂ (fun z => -(deriv (DirichletCharacter.LFunction chi) z /
      DirichletCharacter.LFunction chi z)) s
    exact (hder.div hL.differentiableAt hne).neg
  have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpow : DifferentiableAt ℂ (fun z:ℂ => (X:ℂ)^z) s := by
    fun_prop (disch := exact Or.inl hXC)
  exact (hlog.mul (differentiableAt_rieszKernel hs)).mul hpow

lemma continuous_characterRiesz_right {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {sigma X : ℝ}
    (hs : 1 < sigma) (hX : 0 < X) :
    Continuous (fun t:ℝ => characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  exact (differentiableAt_characterRieszIntegrand chi hchi hX (by rw [hre]; linarith)
    (LFunction_ne_zero_right chi (by simpa only [hre] using hs))).continuousAt.comp (by fun_prop)

lemma integrable_characterRiesz_right {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {sigma X : ℝ}
    (hs : 1 < sigma) (hX : 0 < X) :
    Integrable (fun t:ℝ => characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_log_derivative_right
  have hg := (integrable_rieszKernel_line (show 1/2 ≤ sigma by linarith)).norm.const_mul
    (((sigma-1)⁻¹+C)*X^sigma)
  apply hg.mono' (continuous_characterRiesz_right chi hchi hs hX).aestronglyMeasurable
  filter_upwards [] with t
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  have hb := hbound q chi ((sigma:ℂ)+(t:ℂ)*Complex.I) (by simpa only [hre] using hs)
  rw [norm_characterRieszIntegrand chi hX,hre]
  change ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ * _ * _ ≤ _
  have hb' : ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (sigma-1)⁻¹+C := by simpa only [logDeriv_apply,hre] using hb
  calc
    _ ≤ ((sigma-1)⁻¹+C)*‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖*X^sigma := by gcongr
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
