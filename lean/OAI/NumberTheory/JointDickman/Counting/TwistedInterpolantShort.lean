import OAI.NumberTheory.JointDickman.Amplification.TwistedBinSpectral
import OAI.NumberTheory.JointDickman.Counting.ShortAffineLimit
import OAI.NumberTheory.JointDickman.Counting.ShortAffineBudget

namespace OAI

/-! # Unconditional short averages for the nonprincipal interpolants -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Classical Topology

theorem twisted_interpolant_short {ι : Type*} [Fintype ι]
    {J : ℕ} (hJ : 0<J) (j : ι → ℕ) (hj : ∀ i, 1≤j i)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p∈P B → p.Prime)
    (w : ℕ → ℕ → ℝ) (hw : ∀ B p, p∈P B → 0≤w B p ∧ w B p≤1)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ≠1)
    (m : ℕ) (a : ι → Fin m) (A H scale : ℕ → ℝ) (hA : ∀ B, 0<A B)
    (hH : Tendsto H atTop atTop) (hscale : Tendsto scale atTop atTop) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖complexShortAverage (twistedWeightedBinInterpolant
          (fun i => primeBin (scale n) J (j i)) (finitePrimeWeight (P B) (w B)) a χ) (H B) z‖^2)<ε := by
  obtain ⟨C,hC,hs⟩ := twisted_bin_spectral hJ j hj
  let f B x := twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
    (finitePrimeWeight (P B) (w B)) a χ
  have hf : ∀ B x n, ‖f B x n‖≤1 := by
    intro B x n
    apply twistedWeightedBinInterpolant_norm_le
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds (hw B) v).1]
    exact (finitePrimeWeight_bounds (hw B) v).2
  have hpos : ∀ᶠ B in atTop, 0≤4/H B+canonicalAffineBase C (H B) ∧
      0≤canonicalAffineSlope C (H B)+32*Real.exp 1 := by
    filter_upwards [hH.eventually (canonical_affine_nonneg hC.le),hH.eventually_gt_atTop 0] with B hpos hHB
    exact ⟨add_nonneg (by positivity) hpos.1,add_nonneg hpos.2 (by positivity)⟩
  have hbudget := (canonical_affine_application_budget C 4 1 (32*Real.exp 1)).comp hH
  simp only [one_mul] at hbudget
  have hspec : ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      (A B/2)*x≤N → (N:ℝ)≤(2*A B)*x → ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (f B x) t‖^2) ≤
        4/H B+canonicalAffineBase C (H B)+(canonicalAffineSlope C (H B)+32*Real.exp 1)*T/N := by
    filter_upwards [hH.eventually hs] with B hsB
    have hAB := hA B
    obtain ⟨M,hM⟩ := eventually_atTop.mp (hsB (P B) (hP B) q χ hχ (2*A B) (by positivity))
    filter_upwards [eventually_ge_atTop ((M:ℝ)/(A B/2))] with x hx
    intro N hlo hhi T hT
    have hMN : M≤N := by
      have hh := (div_le_iff₀ (show 0<A B/2 by positivity)).mp hx
      have hn : (M:ℝ)≤N := hh.trans (by nlinarith only [hlo])
      exact_mod_cast hn
    exact hM N hMN x ((div_le_iff₀ (by positivity)).mpr (by nlinarith only [hhi]))
      m a (w B) (hw B) T hT
  have he := shortAverage_iterated_affine f hf A H
    (fun B => 4/H B+canonicalAffineBase C (H B))
    (fun B => canonicalAffineSlope C (H B)+32*Real.exp 1) hA hH hpos hbudget hspec
  intro ε hε
  filter_upwards [he ε hε] with B hb
  exact hscale.eventually hb

end JointDickman

end OAI
