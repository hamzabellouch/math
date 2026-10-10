import Mathlib
import OAI.Probability.SKRatio.FiniteChain.RatioProbabilityUniformBounds
import OAI.Probability.SKRatio.Dynamics.ClockLower
import OAI.Probability.SKRatio.Dynamics.ClockTransfer

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus

lemma uniform_holding_of_norm
    (G : ∀ n : ℕ, Set (Disorder n)) {K : ℝ} (hK : 0 < K)
    (hnorm : ∀ n, ∀ g ∈ G n,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ ≤ K) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ n, 0 < n → ∀ g ∈ G n, ∀ x, 1-q ≤ transition g x x := by
  let a : ℝ := 1/(2*(1+Real.exp (2*(Real.sqrt 2*K))))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith [Real.exp_pos (2*(Real.sqrt 2*K))]
  refine ⟨1-a,by linarith,by linarith,?_⟩
  intro n hn g hg x
  have h := attempted_holding_lower hn (coupling g) hK (hnorm n g hg) x
  rw [attemptKernel_eq_transition] at h
  simpa only [sub_sub_cancel] using h

theorem uniform_discrete_cutoff_of_positive_lag
    (G : ∀ n : ℕ, Set (Disorder n)) {c C K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hnorm : ∀ n, ∀ g ∈ G n,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ ≤ K)
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      c*Real.log n ≤ medianTime g ∧ medianTime g ≤ C*Real.log n)
    (hlag : ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ)
    {b δ : ℝ} (hb : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < discreteDistance g ⌊(1-b)*(n:ℝ)*medianTime g⌋₊ ∧
        discreteDistance g ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ ≤ δ := by
  have hdiv := median_attempts_diverge_of_log_lower G hc
    (hscale.mono (fun _ hn g hg => (hn g hg).1))
  have hb2 : 0 < b/2 := by positivity
  have hb21 : b/2 < 1 := by linarith
  have hcont (e : ℝ) (he : 0 < e) :=
    uniform_continuous_cutoff_of_positive_lag G hc hscale hlag hb2 hb21 he
  obtain ⟨q,hq,hq1,hhold⟩ := uniform_holding_of_norm G hK hnorm
  have hup := uniform_discrete_upper_of_holding G hb hq hq1 hdiv hhold
    (fun e he => (hcont e he).mono (fun _ hn g hg => (hn g hg).2)) δ hδ
  have hlo := uniform_discrete_lower_from_continuous G hb hb1 hdiv
    (fun e he => (hcont e he).mono (fun _ hn g hg => (hn g hg).1)) δ hδ
  filter_upwards [hlo,hup] with n hnlo hnup
  intro g hg
  exact ⟨hnlo g hg,hnup g hg⟩

theorem ratio_cutoff_of_positive_lag (β ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n)) {c C K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hnorm : ∀ n, ∀ g ∈ G n,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ ≤ K)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      c*Real.log n ≤ medianTime g ∧ medianTime g ≤ C*Real.log n)
    (hlag : ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  refine ⟨?_,denominator_eventually_positive ε hε hε1⟩
  let b : ℝ := η/(2*(2+η))
  have hden : 0 < 2*(2+η) := by positivity
  have hb : 0 < b := div_pos hη hden
  have hb1 : b < 1 := (div_lt_one hden).mpr (by linarith)
  have hbid : b*(2+η) = η/2 := by dsimp only [b]; field_simp
  have hbase : (1+b)/(1-b) < 1+η := by
    apply (div_lt_iff₀ (sub_pos.mpr hb1)).mpr
    nlinarith only [hbid,hη]
  have hdiv := median_attempts_diverge_of_log_lower G hc
    (hscale.mono (fun _ hn g hg => (hn g hg).1))
  have hd := uniform_discrete_cutoff_of_positive_lag G hc hK hnorm hscale hlag hb hb1 hε
  apply ratio_probability_zero_of_uniform_bounds (disorderLaw β) G
    (fun n g => (n:ℝ)*medianTime g) hε hε1 hb hb1 hbase hG hdiv
  · filter_upwards [hd] with n hn
    intro g hg
    simpa only [mul_assoc] using (hn g hg).1
  · filter_upwards [hd] with n hn
    intro g hg
    simpa only [mul_assoc] using (hn g hg).2

end SKRatio.Calculus

end
end

end OAI
