import OAI.Analysis.LipschitzHilbert.Packets.AnalyzedReplacement
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedPacketNeighborhood

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LipschitzHilbert.PlanarPacketFamily

theorem analyzed_interval_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (_hderiv : ∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)),
      Monotone d →
      (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
      (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
      ∀ (synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (C c r : ℝ), 0 < C → 0 < r →
      (∀ i y j u k x, ‖synth i j u k y x‖ ≤ C*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k x, ‖deriv (synth i j u k y) x‖ ≤ (C/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
        (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2)) →
      (∀ j u k x t, DifferentiableAt ℝ (fun y => synth 0 j u k y x) t) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ =>
        deriv (fun t => synth 0 j u k t z.2) z.1 -
          (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2)) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching → (∀ j (_u : ι j), P.length j ≤ grid.width) →
      ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) grid.branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
        (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w,
          x ∈ grid.root → |z-c| ≤ r → |w| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
            (fun j u k y x => synth 0 j u k y x) a b x (z+w)‖ ≤ 8*K*(n:ℝ) := by
  obtain ⟨Ab,hAb,hbudget⟩ := uniform_analyzedReplacement_budget hL hlo hhi
  obtain ⟨Am,hAm,hneighborhood⟩ := packet_interval_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hderiv hd hlow hhigh synth frequency C c r hC hr
    hbound hdbound hslow hshigh hcov hcont hdiff hD grid hb hwidth n hn
  dsimp only
  let Q : Fin 2 → ℝ → LinePacketFamily N κ ι := fun i y =>
    P.analyzedReplacement d v hv g hg hg1 y (hderiv y) C hC
      (fun j u k => synth i j u k y) (hbound i y) (hdbound i y)
  have hQbudget (i : Fin 2) (y : ℝ) :
      (Q i y).HasLocalBudget (Ab*P.constant^2*P.coefficientScale⁻¹^2) :=
    hbudget N κ ι P d v hv g hg hg1 y (hderiv y) hd hlow hhigh
      C hC _ (hbound i y) (hdbound i y)
  exact hneighborhood N κ ι
    (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
    (fun j u k y x => synth 0 j u k y x) frequency Q C
    (Ab*P.constant^2*P.coefficientScale⁻¹^2) c r hC (by positivity) hr
    (fun _ _ => rfl) hQbudget hslow hshigh (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl) hcov hcont hdiff hD grid hb (fun _ _ => hwidth) n hn

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
