import OAI.Geometry.EinsteinFour.ScalarPoissonKernelCutoffs

namespace OAI

/-! Local smooth representatives of the original L2 function. The cutoff
is one on a smaller ball, so Fourier regularization returns the given
solution there, not just a solution of a related equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

private def scalarCutoffL2 (φ : S) (u : L2) : L2 :=
  scalarL2Multiply (φ.toLp ∞ volume) u

private theorem scalarCutoffL2_distribution (φ : S) (u : L2) :
    (scalarCutoffL2 φ u : T) = M φ (u : T) := by
  unfold scalarCutoffL2
  rw [SchwartzMap.toLp]
  exact scalarL2Multiply_distribution _ φ.hasTemperateGrowth (φ.memLp ∞ volume) u

private theorem scalarCutoffL2_ae (φ : S) (u : L2) :
    (scalarCutoffL2 φ u : V → ℂ) =ᵐ[volume] fun x => φ x * u x := by
  change (((φ.toLp ∞ volume) • u : L2) : V → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (φ.toLp ∞ volume) u,
    φ.coeFn_toLp ∞ volume] with x hx hφ
  simpa only [smul_eq_mul, Pi.mul_apply, hφ] using hx

/-- All Sobolev orders for an inner localization give a smooth function
agreeing with the original L2 function wherever the cutoff is one. -/
theorem scalar_L2_cutoff_smooth_on (u : L2) (φ : S) (B : Set V)
    (hB : MeasurableSet B) (hone : ∀ x ∈ B, φ x = 1)
    (hreg : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ (u : T))) :
    ∃ f : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (u : V → ℂ) =ᵐ[volume.restrict B] f := by
  have hv : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (scalarCutoffL2 φ u : T) := by
    intro n
    rw [scalarCutoffL2_distribution]
    exact hreg n
  obtain ⟨f, hf, heq⟩ := scalar_L2_sobolev_smooth_representative (scalarCutoffL2 φ u) hv
  refine ⟨f, hf, ?_⟩
  change ∀ᵐ x ∂volume.restrict B, u x = f x
  rw [ae_restrict_iff' hB]
  filter_upwards [heq, scalarCutoffL2_ae φ u] with x hx hprod
  intro hxB
  calc
    u x = φ x * u x := by rw [hone x hxB, one_mul]
    _ = scalarCutoffL2 φ u x := hprod.symm
    _ = f x := hx

private def scalarInnerBump : ContDiffBump (0 : V) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def scalarInnerCutoff : S :=
  (scalarInnerBump.hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp scalarInnerBump.contDiff)

private theorem scalarInnerCutoff_apply (x : V) :
    scalarInnerCutoff x = (scalarInnerBump x : ℂ) := rfl

private theorem scalarInnerCutoff_tsupport :
    tsupport (scalarInnerCutoff : V → ℂ) = closedBall 0 (1 / 2) := by
  have hs : Function.support (scalarInnerCutoff : V → ℂ) =
      Function.support (scalarInnerBump : V → ℝ) := by
    ext x
    simp only [Function.mem_support, scalarInnerCutoff_apply, ne_eq, Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  exact scalarInnerBump.tsupport_eq

private theorem scalarInnerCutoff_one {x : V} (hx : x ∈ ball 0 (1 / 4)) :
    scalarInnerCutoff x = 1 := by
  rw [scalarInnerCutoff_apply]
  have h := scalarInnerBump.one_of_mem_closedBall (ball_subset_closedBall hx)
  simp only [h, Complex.ofReal_one]

/-- A small smooth elliptic perturbation has a smooth representative on a
fixed smaller ball. Hypotheses are local H1 and a regular remainder P u-u. -/
theorem scalar_small_elliptic_local_representative
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : L2)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ (u : T)))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
        MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b (u : T) - (u : T)))) :
    ∃ f : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (u : V → ℂ) =ᵐ[volume.restrict (ball 0 (1 / 4))] f := by
  have hc : HasCompactSupport (scalarInnerCutoff : V → ℂ) := by
    change IsCompact (tsupport (scalarInnerCutoff : V → ℂ))
    rw [scalarInnerCutoff_tsupport]
    exact isCompact_closedBall _ _
  have hr : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M scalarInnerCutoff (u : T)) :=
    scalar_ball_local_sobolev_of_remainder a b δ hδ ha ha1 ha2 hb hb1 hsmall (u : T)
      hH1 hforce (1 / 2) (by norm_num) (by norm_num) scalarInnerCutoff hc
      (by rw [scalarInnerCutoff_tsupport])
  exact scalar_L2_cutoff_smooth_on u scalarInnerCutoff (ball 0 (1 / 4)) isOpen_ball.measurableSet
    (fun _ hx => scalarInnerCutoff_one hx) hr

/-- Real-valued geometric callers take the real part of the constructed
representative, preserving smoothness and equality almost everywhere. -/
theorem scalar_small_elliptic_local_real_representative
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : L2)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ (u : T)))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
        MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b (u : T) - (u : T)))) :
    ∃ f : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (fun x : V => (u x).re) =ᵐ[volume.restrict (ball 0 (1 / 4))] f := by
  obtain ⟨f, hf, heq⟩ := scalar_small_elliptic_local_representative
    a b δ hδ ha ha1 ha2 hb hb1 hsmall u hH1 hforce
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.contDiff.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  change (u x).re = (f x).re
  rw [hx]

end
end PositiveEinsteinFour.Geometry

end OAI
