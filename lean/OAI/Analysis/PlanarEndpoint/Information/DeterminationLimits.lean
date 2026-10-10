import OAI.Analysis.PlanarEndpoint.Extension
import OAI.Analysis.PlanarEndpoint.Information.ChainRule
import OAI.Analysis.PlanarEndpoint.Information.Determination
import OAI.Analysis.PlanarEndpoint.Information.FiniteLaws
import OAI.Analysis.PlanarEndpoint.Information.Sampling
import OAI.Analysis.PlanarEndpoint.Information.WeakLimits

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
  {S V Y : ℕ → Type*} [∀ n, Fintype (S n)]
  [∀ n, Fintype (V n)] [∀ n, Fintype (Y n)]
  (L : ℕ → ℝ) (a : (n : ℕ) → S n → ℝ)
  (ha : ∀ n s, 0 ≤ a n s) (ha1 : ∀ n, ∑ s, a n s = 1)
  (v : (n : ℕ) → S n → V n) (y : (n : ℕ) → S n → Y n)
  (X : (n : ℕ) → S n → Ω)

lemma ae_determination_in_limit {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto (fun n => finiteInformationLaw (a n) (ha n) (ha1 n) (X n))
      atTop (𝓝 μ)) (hL : ∀ n, 1 < L n) (hLlim : Tendsto L atTop atTop)
    (E : (n : ℕ) → S n → Prop) (A : (n : ℕ) → V n → Finset (Y n))
    (hA : ∀ n s, E n s → y n s ∈ A n (v n s))
    {c : ℕ → ℝ} {γ : ℝ} (hc : Tendsto c atTop (𝓝 γ))
    (hcard : ∀ n z, ((A n z).card : ℝ) ≤ (L n) ^ (c n))
    {d b : Ω → ℝ} (hd : Continuous d) (hb : Continuous b)
    (hrep : ∀ n s, d (X n s) = sampledInformation (L n) (a n) (v n) (y n) s ∧
      b (X n s) = if E n s then 1 else 0) :
    ∀ᵐ x ∂(μ : Measure Ω), b x = 1 → d x ≤ γ := by
  have hbound : ∀ᵐ x ∂(μ : Measure Ω), x ∈ {x | 1/2 < b x} → d x ≤ γ := by
    apply ae_le_on_open_of_weak_limit_tails hμ (isOpen_lt continuous_const hb) hd γ
    intro η hη
    have henv : Tendsto (fun n => ENNReal.ofReal ((L n) ^ (-(η/2)))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        ENNReal.tendsto_ofReal ((tendsto_rpow_neg_atTop (half_pos hη)).comp hLlim)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henv
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hc.eventually (gt_mem_nhds (by linarith : γ < γ+η/2))] with n hn
    apply (finiteInformationLaw_determination_tail (a n) (ha n) (ha1 n) (v n) (y n)
      (E n) (A n) (hA n) (hcard n) (hL n) (X n) hd hb (hrep n)).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      (L n) ^ (c n) * (L n) ^ (-(γ+η)) = (L n) ^ (c n - (γ+η)) := by
        rw [sub_eq_add_neg, Real.rpow_add (lt_trans zero_lt_one (hL n))]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hL n).le (by linarith)
  filter_upwards [hbound] with x hx hbx
  apply hx
  rw [hbx]
  norm_num

lemma ae_indicator_in_limit {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto (fun n => finiteInformationLaw (a n) (ha n) (ha1 n) (X n))
      atTop (𝓝 μ)) {b : Ω → ℝ} (hb : Continuous b)
    (hrep : ∀ n s, 0 < a n s → b (X n s) = 0 ∨ b (X n s) = 1) :
    ∀ᵐ x ∂(μ : Measure Ω), b x = 0 ∨ b x = 1 := by
  have heq : (fun x => b x * (b x-1)) =ᵐ[(μ : Measure Ω)] (fun _ => 0) := by
    apply ae_eq_of_weak_limit hμ (hb.mul (hb.sub continuous_const)) continuous_const
    intro n
    apply finiteInformationLaw_ae (a n) (ha n) (ha1 n) (X n)
      (fun x => b x * (b x-1) = 0)
      (isClosed_eq (hb.mul (hb.sub continuous_const)) continuous_const).measurableSet
    intro s hs
    rcases hrep n s hs with h | h <;> simp [h]
  filter_upwards [heq] with x hx
  rcases mul_eq_zero.mp hx with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

section Chain
variable {W : ℕ → Type*} [∀ n, Fintype (W n)]
  (u : (n : ℕ) → S n → W n)

omit [∀ n, Fintype (V n)] in
lemma ae_chain_in_limit {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto (fun n => finiteInformationLaw (a n) (ha n) (ha1 n) (X n))
      atTop (𝓝 μ)) {f g h : Ω → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hrep : ∀ n s,
      f (X n s) = sampledInformation (L n) (a n) (v n) (fun s => (u n s,y n s)) s ∧
      g (X n s) = sampledInformation (L n) (a n) (v n) (u n) s ∧
      h (X n s) = sampledInformation (L n) (a n) (fun s => (v n s,u n s)) (y n) s) :
    f =ᵐ[(μ : Measure Ω)] (fun x => g x + h x) := by
  apply ae_eq_of_weak_limit hμ hf (hg.add hh)
  intro n
  exact finiteInformationLaw_chain (a n) (ha n) (ha1 n) (v n) (u n) (y n)
    (L n) (X n) hf hg hh (hrep n)

end Chain
end PlanarEndpoint.TransverseInformation
end

end OAI
