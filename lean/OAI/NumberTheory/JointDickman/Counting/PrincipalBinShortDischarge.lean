import OAI.NumberTheory.JointDickman.Amplification.CenteredBinSpectral
import OAI.NumberTheory.JointDickman.Counting.ShortAffineLimit
import OAI.NumberTheory.JointDickman.Counting.ShortAffineBudget
import OAI.NumberTheory.JointDickman.Amplification.HalfArithmetic

namespace OAI

/-! # Unconditional principal short averages for the actual bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Classical Topology

theorem finitePrimeWeight_short_with_center_proved
    {J : ℕ} (hJ : 0<J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1)
    (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p∈P B → p.Prime)
    (w : ℕ → ℕ → ℝ) (hw : ∀ B p, p∈P B → 0≤w B p ∧ w B p≤1)
    (A H scale : ℕ → ℝ) (hA : ∀ B, 0<A B)
    (hH : Tendsto H atTop atTop) (hscale : Tendsto scale atTop atTop) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖weightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (w B)) (H B) z‖^2)<ε := by
  obtain ⟨C,hC,hs⟩ := centered_bin_spectral hJ ζ hζ μ hμ hmean
  let g B x := centeredWeightedBinCoefficient J ζ μ (P B) (w B) x
  let f B x := halfArithmetic (g B x)
  have hf : ∀ B x n, ‖f B x n‖≤1 := fun B x => halfArithmetic_norm _
    (centeredWeightedBinCoefficient_norm ζ hζ hμ (w B) (hw B) x)
  have hpos : ∀ᶠ B in atTop, 0≤17/H B+4*canonicalAffineBase C (H B) ∧
      0≤4*canonicalAffineSlope C (H B)+128*Real.exp 1 := by
    filter_upwards [hH.eventually (canonical_affine_nonneg hC.le),hH.eventually_gt_atTop 0] with B hp hB
    exact ⟨add_nonneg (by positivity) (mul_nonneg (by norm_num) hp.1),
      add_nonneg (mul_nonneg (by norm_num) hp.2) (by positivity)⟩
  have hbudget := (canonical_affine_application_budget C 17 4 (128*Real.exp 1)).comp hH
  have hspec : ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      (A B/2)*x≤N → (N:ℝ)≤(2*A B)*x → ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (f B x) t‖^2) ≤
        17/H B+4*canonicalAffineBase C (H B)+(4*canonicalAffineSlope C (H B)+128*Real.exp 1)*T/N := by
    filter_upwards [hH.eventually hs] with B hsB
    filter_upwards [hsB (P B) (hP B) (w B) (hw B) (A B) (hA B)] with x hx
    intro N hlo hhi T hT
    have he := hx N hlo hhi T hT
    change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (halfArithmetic (g B x)) t‖^2) ≤ _
    rw [halfArithmetic_energy]
    have hn : 0≤∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (g B x) t‖^2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
    exact (show (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (g B x) t‖^2)/4 ≤
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (g B x) t‖^2) by linarith).trans he
  have he := shortAverage_iterated_affine f hf A H
    (fun B => 17/H B+4*canonicalAffineBase C (H B))
    (fun B => 4*canonicalAffineSlope C (H B)+128*Real.exp 1) hA hH hpos hbudget hspec
  intro ε hε
  filter_upwards [he (ε/4) (by positivity)] with B hb
  filter_upwards [hscale.eventually hb] with n hn
  have hid (z : ℝ) : weightedBinAverage
      (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
      (finitePrimeWeight (P B) (w B)) (H B) z = complexShortAverage (g B (scale n)) (H B) z := rfl
  simp_rw [hid]
  rw [halfArithmetic_short_energy]
  change 4*((1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
    ‖complexShortAverage (f B (scale n)) (H B) z‖^2))<ε
  linarith

end JointDickman

end OAI
