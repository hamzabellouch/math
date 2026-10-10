import OAI.NumberTheory.JointDickman.Amplification.AmplifiedProfile

namespace OAI

/-! # Amplification profiles along a prescribed bad subsequence -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Countable residue compactness can be taken inside any given sequence. -/
theorem empiricalResidueCoefficient_subsequence_along (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) (r : ℕ → ℕ) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ V : (q : ℕ+) → ZMod (q : ℕ) → ℂ,
      ∀ q a, Tendsto (fun N => empiricalResidueCoefficient H (r (s N)) q a)
        atTop (nhds (V q a)) := by
  let K : Set ((q : ℕ+) → ZMod (q : ℕ) → ℂ) :=
    {V | ∀ (q : ℕ+) (a : ZMod (q : ℕ)), V q a ∈ Metric.closedBall 0 ((q : ℕ)*C)}
  have hK : IsCompact K := isCompact_pi_infinite fun (q : ℕ+) =>
    isCompact_pi_infinite fun (_ : ZMod (q : ℕ)) => isCompact_closedBall 0 ((q : ℕ)*C)
  have hx (N : ℕ) : empiricalResidueCoefficient H (r N) ∈ K := by
    intro q a
    rw [Metric.mem_closedBall,dist_zero_right]
    exact empiricalResidueCoefficient_norm_le H hC hH (r N) q a
  obtain ⟨V,_,s,hs,hlim⟩ := hK.tendsto_subseq hx
  exact ⟨s,hs,V,fun q a => (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim q)) a⟩

/-- The profile is constructed on a further subsequence of the originally
chosen scales. The correlation limit and every amplification test survive. -/
theorem exists_arithmetic_amplification_profile_along (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) (r : ℕ → ℕ) (hr : StrictMono r)
    {β : ℂ} (hmean : Tendsto (fun N => (∑ n ∈ range (r N), H (r N) n)/(r N : ℂ))
      atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ W : ResidueProfile, W.mean = β ∧
      ∀ (B L : ℕ) (τ C' : ℝ) (T : ℕ),
        Tendsto (fun N => (∑ n ∈ range (r (s N)), H (r (s N)) n *
          (arithmeticSubsetAmplification B L τ C' (amplificationSmoothWeight B T) n : ℂ)) /
            (r (s N) : ℂ)) atTop
          (nhds (W.correlation (amplificationPeriod B) (smoothResidueAmplification B L τ C' T))) := by
  obtain ⟨s,hs,V,hV⟩ := empiricalResidueCoefficient_subsequence_along H hC hH r
  let t : ℕ → ℕ := r ∘ s
  have ht : StrictMono t := hr.comp hs
  have hbound (q : ℕ+) (a : ZMod (q : ℕ)) : ‖V q a‖ ≤ C :=
    residueCoefficient_limit_bound H hH ht (hV q a)
  have henergy (q : ℕ+) : residueEnergy (V q) ≤ C^2 := by
    unfold residueEnergy
    have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
    apply (div_le_iff₀ hq).mpr
    calc
      _ ≤ ∑ _a : ZMod (q : ℕ), C^2 := sum_le_sum fun a _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hbound q a) 2
      _ = _ := by simp [mul_comm]
  let W : ResidueProfile := {
    value := V
    compatible := residueCoefficient_limit_compatible H t V hV
    energy_bounded := ⟨C^2, by rintro _ ⟨q,rfl⟩; exact henergy q⟩ }
  have hW (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) := residueCoefficient_test_limit H t V hV q f
  have hm := hW 1 (fun _ => 1)
  simp only [empiricalResidueTest,mul_one] at hm
  have hβ : W.mean = β := tendsto_nhds_unique hm (hmean.comp hs.tendsto_atTop)
  refine ⟨s,hs,W,hβ,?_⟩
  intro B L τ C' T
  have h := hW (amplificationPeriod B) (smoothResidueAmplification B L τ C' T)
  have he (n : ℕ) : smoothResidueAmplification B L τ C' T (n : ZMod (amplificationPeriod B : ℕ)) =
      (arithmeticSubsetAmplification B L τ C' (amplificationSmoothWeight B T) n : ℂ) := by
    exact congrArg (fun x : ℝ => (x : ℂ))
      (residueAmplification_natCast B L n τ C' (amplificationSmoothWeight B T))
  simpa only [empiricalResidueTest,he,ResidueProfile.correlation,t,Function.comp_def] using h

end JointDickman

end OAI
