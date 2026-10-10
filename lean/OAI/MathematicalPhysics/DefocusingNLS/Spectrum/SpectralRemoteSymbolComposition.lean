import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolBilinear

namespace OAI

/-! Smooth functions of uniformly bounded remote coefficients have uniform
fixed-order logarithmic derivative bounds. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_uniform_compact_comp
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {L : ℕ → ℝ} {f : ℕ → ℝ → A} {g : A → B}
    {O C : Set A} (hO : IsOpen O) (hC : IsCompact C) (hCO : C ⊆ O)
    (hg : ContDiffOn ℝ ∞ g O) (hf : HasUniformLogJetBound L 0 f)
    (hmem : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), f n t ∈ C) :
    HasUniformLogJetBound L 0 (fun n t => g (f n t)) := by
  refine ⟨?_,?_⟩
  · filter_upwards [hf.smooth,hmem] with n hn hm
    exact hg.comp hn (fun t ht => hCO (hm t ht))
  · intro k
    let M : A → ℝ := fun x => ∑ i ∈ Finset.range (k+1),
      ‖iteratedFDerivWithin ℝ i g O x‖
    have hMc : ContinuousOn M O := by
      apply continuousOn_finsetSum
      intro i hi
      exact (hg.continuousOn_iteratedFDerivWithin (by simp) hO.uniqueDiffOn).norm
    obtain ⟨C₀,hC₀⟩ := hC.exists_bound_of_continuousOn (hMc.mono hCO)
    let V := max C₀ 0
    have hV : 0 ≤ V := le_max_right _ _
    choose U hU hu using hf.bound
    let D := max (∑ i ∈ Finset.range (k+1), U i) 1
    have hD : 1 ≤ D := le_max_right _ _
    refine ⟨(k.factorial : ℝ)*V*D^k,by positivity,?_⟩
    have hb : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
        ‖iteratedDeriv i (f n) t‖ ≤ U i := by
      simpa only [zero_mul,Real.exp_zero,mul_one] using
        ((eventually_all_finset (Finset.range (k+1))).mpr (fun i _ => hu i))
    filter_upwards [hb,hf.smooth,hmem] with n hn hfn hm
    intro t ht
    have hmaps : MapsTo (f n) (Ioi (L n)) O := fun r hr => hCO (hm r hr)
    have houter (i : ℕ) (hi : i ≤ k) : ‖iteratedFDerivWithin ℝ i g O (f n t)‖ ≤ V := by
      have hh : ‖iteratedFDerivWithin ℝ i g O (f n t)‖ ≤ M (f n t) :=
        Finset.single_le_sum (f := fun j => ‖iteratedFDerivWithin ℝ j g O (f n t)‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      exact hh.trans ((le_abs_self _).trans ((hC₀ _ (hm t ht)).trans (le_max_left _ _)))
    have hinner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
        ‖iteratedFDerivWithin ℝ i (f n) (Ioi (L n)) t‖ ≤ D^i := by
      rw [HasUniformLogJetBound.norm_jet_within _ hfn ht]
      have hsum : U i ≤ ∑ j ∈ Finset.range (k+1), U j :=
        Finset.single_le_sum (f := U) (fun j _ => hU j)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
      exact (hn i (Finset.mem_range.mpr (Nat.lt_succ_of_le hik)) t ht).trans
        (hsum.trans ((le_max_left _ _).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hD hi)))
    have hc := norm_iteratedFDerivWithin_comp_le hg hfn (by simp : (k : ℕ∞ω) ≤ ∞)
      hO.uniqueDiffOn isOpen_Ioi.uniqueDiffOn hmaps ht houter hinner
    rw [HasUniformLogJetBound.norm_jet_within _ (hg.comp hfn hmaps) ht] at hc
    simpa only [zero_mul,Real.exp_zero,mul_one,Function.comp_def] using hc

end DefocusingNLS

end OAI
