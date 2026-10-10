import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteCompositionGrowth

namespace OAI

/-! Composition with a varying smooth family whose fixed spatial jets are
uniformly bounded along the given curves. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_family_composition
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (f : ℕ → ℝ → A) (g : ℕ → A → B)
    (hf : HasUniformLogJetBound L 0 f) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (hjet : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      ‖iteratedFDeriv ℝ k (g n) (f n t)‖ ≤ M) :
    HasUniformLogJetBound L 0 (fun n t => g n (f n t)) := by
  refine ⟨hf.smooth.mono (fun n hn => (hg n).comp_contDiffOn hn),?_⟩
  intro k
  choose U hU hu using hf.bound
  choose V hV hv using hjet
  let D := max (∑ i ∈ Finset.range (k+1), U i) 1
  let K := ∑ i ∈ Finset.range (k+1), V i
  have hD : 1 ≤ D := le_max_right _ _
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => hV i)
  refine ⟨(k.factorial : ℝ)*K*D^k,by positivity,?_⟩
  have hi : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
      ‖iteratedDeriv i (f n) t‖ ≤ U i := by
    simpa only [zero_mul,Real.exp_zero,mul_one] using
      (eventually_all_finset (Finset.range (k+1))).mpr (fun i _ => hu i)
  have ho : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
      ‖iteratedFDeriv ℝ i (g n) (f n t)‖ ≤ V i :=
    (eventually_all_finset (Finset.range (k+1))).mpr (fun i _ => hv i)
  filter_upwards [hi,ho,hf.smooth,hL.eventually (eventually_ge_atTop (0 : ℝ))]
    with n hin hon hfn hLn
  intro t ht
  have houter : ∀ i ≤ k, ‖iteratedFDeriv ℝ i (g n) (f n t)‖ ≤ K := by
    intro i hik
    have him : i ∈ Finset.range (k+1) := Finset.mem_range.mpr (by omega)
    exact (hon i him t ht).trans (Finset.single_le_sum (fun j _ => hV j) him)
  have hinner : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedDeriv i (f n) t‖ ≤ D*Real.exp (0*t) := by
    intro i hi hik
    simp only [zero_mul,Real.exp_zero,mul_one]
    have him : i ∈ Finset.range (k+1) := Finset.mem_range.mpr (by omega)
    exact (hin i him t ht).trans ((Finset.single_le_sum (fun j _ => hU j) him).trans
      (le_max_left _ _))
  have hh := spectralRemote_composition_growth (f n) (g n) (L n) t 0 D K k hfn (hg n)
    ht (hLn.trans ht.le) le_rfl hD houter hinner
  simpa only [mul_zero,zero_mul,Real.exp_zero,mul_one] using hh

end DefocusingNLS

end OAI
