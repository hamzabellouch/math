import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableFixedPointEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableFrameContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableWeightedLocalContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphParameterSelection

namespace OAI

/-! # Continuous families of actual stable endpoint sequences -/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_continuous_stableGraph_endpoints
    (ζ : P → ℕ → F →L[ℝ] E) (π : P → ℕ → E →L[ℝ] F)
    (A : P → ℕ → E →L[ℝ] E) (D R : F →L[ℝ] F)
    (hR : ‖R‖ ≤ 1) (hinv : ∀ v, D (R v) = v)
    (hπζ : ∀ p n v, π p n (ζ p n v) = v)
    (hA : ∀ p n, ‖stableProjectedBlock (ζ p n) (ζ p (n + 1))
      (π p n) (π p (n + 1)) (A p n)‖ ≤ 1 / 8)
    (hB : ∀ p n, ‖stableMixedBlock (ζ p n) (ζ p (n + 1)) (π p (n + 1)) (A p n)‖ ≤ 1 / 16)
    (hζc : ∀ n, Continuous (fun q : P × F => ζ q.1 n q.2))
    (hπc : ∀ n, Continuous (fun q : P × E => π q.1 n q.2))
    (hAc : ∀ n, Continuous (fun q : P × E => A q.1 n q.2))
    (h : P → ℕ → E → E) (w : P → E) (hw : Continuous w) (hwker : ∀ p, π p 0 (w p) = 0)
    (ρ ε C r : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1) (hζ : ∀ p n, ‖ζ p n‖ ≤ C)
    (hhc : ∀ n, Continuous (fun q : P × {v : E // ‖v‖ ≤ (1 + C) * ρ} => h q.1 n q.2.1))
    (hN : ∀ p n v u, ‖v‖ ≤ ρ → ‖u‖ ≤ ρ →
      ‖stableFrameForwardSource (ζ p) (π p) (h p) n v -
        stableFrameForwardSource (ζ p) (π p) (h p) n u‖ ≤ (1 / 16 : ℝ) * ‖v - u‖)
    (hH : ∀ p n v u, ‖v‖ ≤ ρ → ‖u‖ ≤ ρ →
      ‖stableFrameCoordinateSource (ζ p) (π p) (A p) D (h p) n v -
        stableFrameCoordinateSource (ζ p) (π p) (A p) D (h p) n u‖ ≤
          (1 / 16 : ℝ) * ‖v - u‖)
    (hN0 : ∀ p n, ‖stableFrameForwardSource (ζ p) (π p) (h p) n 0‖ ≤ ε * r ^ n)
    (hH0 : ∀ p n, ‖stableFrameCoordinateSource (ζ p) (π p) (A p) D (h p) n 0‖ ≤ ε * r ^ n)
    (hsmall : ∀ p, ‖w p‖ + 2 * ε ≤ ρ / 2) :
    ∃ z : P → ℕ → E, (∀ n, Continuous (fun p => z p n)) ∧
      (∀ p, stableFrameProjection (ζ p 0) (π p 0) (z p 0) = w p) ∧
      (∀ p n, z p (n + 1) = A p n (z p n) + h p n (z p n)) ∧
      (∀ p n, ‖z p n‖ ≤ (2 * (‖w p‖ + 2 * ε) * (1 + C)) * (1 / 2 : ℝ) ^ n) := by
  let Nf := fun p => stableFrameForwardSource (ζ p) (π p) (h p)
  let Hf := fun p => stableFrameCoordinateSource (ζ p) (π p) (A p) D (h p)
  let N := fun p => stableWeightedPairSource (Nf p) ρ (1 / 16) ε r
    hρ (by norm_num) hε hr hrsmall (hN p) (hN0 p)
  let H := fun p => stableWeightedPairSource (Hf p) ρ (1 / 16) ε r
    hρ (by norm_num) hε hr hrsmall (hH p) (hH0 p)
  have hc := continuous_stableFrame_sources_local ζ π A D h hζc hπc hAc
    ρ ((1 + C) * ρ) C hC hζ le_rfl hhc
  obtain ⟨x, hfix, hx, hbound, _hinit, hxc⟩ := exists_continuous_stableGraph_selection
    (fun p n => stableProjectedBlock (ζ p n) (ζ p (n + 1)) (π p n) (π p (n + 1)) (A p n))
    (fun p n => stableMixedBlock (ζ p n) (ζ p (n + 1)) (π p (n + 1)) (A p n))
    hA hB
    (continuous_stableProjectedBlock_apply ζ π A hζc hπc hAc)
    (continuous_stableMixedBlock_apply ζ π A hζc hπc hAc)
    R hR w hw N H ρ ε hρ hε
    (fun p v u hv hu => stableWeightedPairSource_dist_le (Nf p) ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (hN p) (hN0 p) v u hv hu)
    (fun p v u hv hu => stableWeightedPairSource_dist_le (Hf p) ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (hH p) (hH0 p) v u hv hu)
    (fun p => stableWeightedPairSource_zero_bound (Nf p) ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (hN p) (hN0 p))
    (fun p => stableWeightedPairSource_zero_bound (Hf p) ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (hH p) (hH0 p))
    (fun y hy hy₁ hy₂ n => continuous_stableWeightedPairSource_local Nf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (fun i => (hc i).1) hN hN0 y hy hy₁ hy₂ n)
    (fun y hy hy₁ hy₂ n => continuous_stableWeightedPairSource_local Hf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (fun i => (hc i).2) hH hH0 y hy hy₁ hy₂ n)
    hsmall
  let z := fun p => stableFrameState (ζ p) (stableSequenceValue (x p).1) (stableSequenceValue (x p).2)
  have hz (p : P) := stableGraph_fixedPoint_endpoint (ζ p) (π p) (A p) D R hR hinv
    (hπζ p) (hA p) (hB p) (h p) (w p) (hwker p) (N p) (H p) ε C hC (hζ p)
    (x p) (hfix p) (hbound p)
    (fun n => (stableWeightedPairSource_value (Nf p) ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (hN p) (hN0 p) (x p) (hx p) n).trans
        (stableFrameForwardSource_value (ζ p) (π p) (h p) (x p) n))
    (fun n => (stableWeightedPairSource_value (Hf p) ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall (hH p) (hH0 p) (x p) (hx p) n).trans
        (stableFrameCoordinateSource_value (ζ p) (π p) (A p) D (h p) (x p) n))
  refine ⟨z, ?_, fun p => (hz p).1, fun p => (hz p).2.1, fun p => (hz p).2.2⟩
  intro n
  have hwc : Continuous (fun p => stableSequenceValue (x p).1 n) :=
    continuous_const.smul (continuous_fst.comp (hxc n))
  have huc : Continuous (fun p => stableSequenceValue (x p).2 n) :=
    continuous_const.smul (continuous_snd.comp (hxc n))
  exact hwc.add ((hζc n).comp (continuous_id.prodMk huc))

end DefocusingNLS

end OAI
