import OAI.Geometry.IsometricImmersion.Taylor.TaylorPolynomialJetBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def taylorInitialRequest (N k : ℕ) : ℕ := k + N * (N + 3)

theorem taylorInitialRequest_step (n k : ℕ) :
    taylorInitialRequest n (k + n + 2) ≤ taylorInitialRequest (n + 1) k := by
  unfold taylorInitialRequest
  nlinarith

theorem uniform_taylorApproximation_jets
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) :
    ∀ N k : ℕ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ) (a : ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, a] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy a u0 u1) ![x, a]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy a u0 u1) ![x, a] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N k, ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N k, ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      ∀ j ≤ k, ∀ p : Coord, p 0 ∈ J → |p 1 - a| ≤ 1 →
        ‖iteratedFDeriv ℝ j (taylorApproximation g a u0 u1 N) p‖ ≤ R := by
  classical
  intro N
  induction N with
  | zero =>
    intro k
    refine ⟨(1 + (2 : ℝ)^k) * B, mul_nonneg (by positivity) hB, ?_⟩
    intro u0 u1 I J a hI hJI h0 h1 _ _ _ h0B h1B j hj p hp ht
    have hpb := linearCauchy_fullJet_bound h0 h1 hI a j (hJI hp) ht hB
      (fun i hi => h0B (p 0) hp i (by simpa only [taylorInitialRequest, zero_mul, Nat.add_zero] using hi.trans hj))
      (fun i hi => h1B (p 0) hp i (by simpa only [taylorInitialRequest, zero_mul, Nat.add_zero] using hi.trans hj))
    exact hpb.trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)) hB)
  | succ n ih =>
    intro k
    obtain ⟨R0, hR0, hprevious⟩ := ih (k + n + 2)
    obtain ⟨C, hC, hcoefficient⟩ := exists_uniform_nextTaylorCoefficient_bound
      hg hU hS hSU M hM hc (k + n)
    let RC : ℝ := ∑ i : Fin (k + 1),
      (R0 + ((i.val + n).factorial : ℝ) * C * (max 1 R0)^(i.val + n))
    have hRC : 0 ≤ RC := Finset.sum_nonneg (fun i _ => by positivity)
    refine ⟨R0 + (2 : ℝ)^k * RC, add_nonneg hR0 (mul_nonneg (by positivity) hRC), ?_⟩
    intro u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B j hj p hp ht
    have hcutU : ∀ x ∈ I, (![x, a] : Coord) ∈ U := fun x hx => hSU (hcut x hx)
    have hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0 := by
      intro x hx hh
      have hd := hden x hx
      rw [hh, abs_zero] at hd
      linarith
    obtain ⟨hP, hjet, _⟩ := taylorApproximation_properties hg hU hI h0 h1 a hcutU hxx n
    have hstateN : ∀ x ∈ I, ‖qSolutionJet (taylorApproximation g a u0 u1 n) ![x, a]‖ ≤ M := by
      intro x hx
      rw [hjet x hx]
      exact hstate x hx
    have hdenN : ∀ x ∈ I,
        c ≤ |covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0| := by
      intro x hx
      rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
      exact hden x hx
    have hxxN : ∀ x ∈ I,
        covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0 ≠ 0 := by
      intro x hx hh
      have hd := hdenN x hx
      rw [hh, abs_zero] at hd
      linarith
    have hprev := hprevious u0 u1 I J a hI hJI h0 h1 hcut hstate hden
      (fun x hx i hi => h0B x hx i (hi.trans (taylorInitialRequest_step n k)))
      (fun x hx i hi => h1B x hx i (hi.trans (taylorInitialRequest_step n k)))
    have hCoeff : ContDiffOn ℝ ∞
        (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) I :=
      nextTaylorCoefficient_contDiffOn hg hU hI hP a n hcutU hxxN
    have hCoeffB : ∀ x ∈ J, ∀ i ≤ k,
        ‖iteratedFDeriv ℝ i (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) x‖ ≤ RC := by
      intro x hx i hi
      have hb := hcoefficient (taylorApproximation g a u0 u1 n) I hI hP a x (hJI hx)
        (hcut x (hJI hx)) (hstateN x (hJI hx)) (hdenN x (hJI hx)) n i (by omega) R0
        (fun l hl => hprev l (by omega) ![x, a] hx (by simp))
      let fi : Fin (k + 1) := ⟨i, by omega⟩
      have hsingle : R0 + ((fi.val + n).factorial : ℝ) * C * (max 1 R0)^(fi.val + n) ≤ RC :=
        Finset.single_le_sum
          (f := fun l : Fin (k + 1) => R0 + ((l.val + n).factorial : ℝ) * C * (max 1 R0)^(l.val + n))
          (fun l _ => by positivity) (Finset.mem_univ fi)
      exact hb.trans hsingle
    have hcorr := separatedTimePower_fullJet_bound hCoeff hI a (n + 2) j (hJI hp) ht hRC
      (fun i hi => hCoeffB (p 0) hp i (hi.trans hj))
    have hprevp := hprev j (by omega) p hp ht
    have hcorrsmooth := taylorCorrection_contDiffOn hCoeff a n
    change ‖iteratedFDeriv ℝ j
      (taylorApproximation g a u0 u1 n +
        taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n) p‖ ≤ _
    rw [iteratedFDeriv_add_apply
      ((hP.contDiffAt ((spatialStrip_isOpen hI).mem_nhds (hJI hp))).of_le (WithTop.coe_le_coe.mpr le_top))
      ((hcorrsmooth.contDiffAt ((spatialStrip_isOpen hI).mem_nhds (hJI hp))).of_le
        (WithTop.coe_le_coe.mpr le_top))]
    exact (norm_add_le _ _).trans (add_le_add hprevp (hcorr.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hRC)))

end SmoothLocal.Taylor

end

end OAI
