import OAI.NumberTheory.JointDickman.Amplification.EndpointFourierBounds
import OAI.NumberTheory.JointDickman.Counting.EndpointScaleWindow

namespace OAI

/-! # Manuscript (35) and the trivial endpoint sum bound -/

namespace JointDickman
open Filter Finset MeasureTheory
open scoped Topology

theorem endpoint_fourier_moments
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ᶠ B : ℕ in atTop,
      ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      Real.log X ≤ (5/2 : ℝ)*B →
      ∀ (g : Finset ℕ → ℝ), (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      ∀ (w : ℝ → ℝ) (M : ℝ), 0 ≤ M → (∀ t, |w t| ≤ M) →
      (∀ θ, ‖endpointFourierSum B a b X g w θ‖ ≤ C₁*M/B) ∧
      (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b X g w θ‖^2) ≤
        C₂*M^2*(B : ℝ)^(-7/4+ε)/X := by
  obtain ⟨D,hD,hdom⟩ := signedSplitProductMass_coefficient_bound hM
  obtain ⟨K₁,hK₁,hfirst⟩ := coefficient_first_moment hSD hM hMP (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨K₂,hK₂,hsecond⟩ := coefficient_second_moment hSD hM hMP
    (by norm_num : (0 : ℝ) < 1/2) hε
  have hb : 0 < b := ha.trans_le hab
  refine ⟨D*K₁*b/a,D^2*K₂*b/a^2,by positivity,by positivity,?_⟩
  filter_upwards [hdom,hfirst,hsecond,endpoint_scale_window hb,eventually_gt_atTop 0]
    with B hdomB hfirstB hsecondB hwindow hB
  intro X hX hloglo hloghi g hg w M hM0 hw
  obtain ⟨hY,hlogY,hsize⟩ := hwindow X hX hloglo hloghi
  have hdom' : ∀ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        D*coefficientWeight B n/((B : ℝ)*n) := by
    intro n hn
    have hlow : a*X < (n : ℝ) := (Nat.floor_lt (mul_pos ha hX).le).mp (mem_Ioc.mp hn).1
    have hn0 : 0 < n := by exact_mod_cast ((mul_pos ha hX).trans hlow)
    have hnY : (n : ℝ) ≤ b*X := (Nat.le_floor_iff (mul_pos hb hX).le).mp (mem_Ioc.mp hn).2
    exact hdomB g hg n hn0 (hnY.trans hsize)
  obtain ⟨hmax,hL2⟩ := endpoint_fourier_bounds hB ha hX hD.le hM0 g w hdom' hw
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hBne := hB0.ne'
  have hXne := hX.ne'
  have hane := ha.ne'
  constructor
  · intro θ
    refine (hmax θ).trans ?_
    calc
      _ ≤ (D*M/((B : ℝ)*(a*X)))*(K₁*(b*X)) :=
        mul_le_mul_of_nonneg_left (hfirstB _ hY hlogY) (by positivity)
      _ = _ := by field_simp
  · refine hL2.trans ?_
    calc
      _ ≤ (D*M/((B : ℝ)*(a*X)))^2*(K₂*(b*X)*(B : ℝ)^(1/4+ε)) :=
        mul_le_mul_of_nonneg_left (hsecondB _ hY hlogY) (sq_nonneg _)
      _ = _ := by
        have hp : (B : ℝ)^(1/4+ε) = (B : ℝ)^(-7/4+ε)*(B : ℝ)^2 := by
          rw [← Real.rpow_natCast,← Real.rpow_add hB0]
          congr 1
          norm_num
          ring
        rw [hp]
        field_simp

end JointDickman

end OAI
