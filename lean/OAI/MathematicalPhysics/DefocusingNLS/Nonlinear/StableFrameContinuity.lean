import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphPointSources

namespace OAI

/-! # Strong continuity of projected blocks and local nonlinear sources -/

namespace DefocusingNLS

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuous_stableProjection_apply
    (ζ : P → F →L[ℝ] E) (π : P → E →L[ℝ] F)
    (hζ : Continuous (fun q : P × F => ζ q.1 q.2))
    (hπ : Continuous (fun q : P × E => π q.1 q.2)) :
    Continuous (fun q : P × E => stableFrameProjection (ζ q.1) (π q.1) q.2) :=
  continuous_snd.sub (hζ.comp (continuous_fst.prodMk hπ))

theorem continuous_stableProjectedBlock_apply
    (ζ : P → ℕ → F →L[ℝ] E) (π : P → ℕ → E →L[ℝ] F)
    (A : P → ℕ → E →L[ℝ] E)
    (hζ : ∀ n, Continuous (fun q : P × F => ζ q.1 n q.2))
    (hπ : ∀ n, Continuous (fun q : P × E => π q.1 n q.2))
    (hA : ∀ n, Continuous (fun q : P × E => A q.1 n q.2)) (n : ℕ) :
    Continuous (fun q : P × E => stableProjectedBlock (ζ q.1 n) (ζ q.1 (n + 1))
      (π q.1 n) (π q.1 (n + 1)) (A q.1 n) q.2) := by
  have hp := continuous_stableProjection_apply (fun p => ζ p n) (fun p => π p n) (hζ n) (hπ n)
  exact (continuous_stableProjection_apply (fun p => ζ p (n + 1)) (fun p => π p (n + 1))
    (hζ (n + 1)) (hπ (n + 1))).comp
      (continuous_fst.prodMk ((hA n).comp (continuous_fst.prodMk hp)))

theorem continuous_stableMixedBlock_apply
    (ζ : P → ℕ → F →L[ℝ] E) (π : P → ℕ → E →L[ℝ] F)
    (A : P → ℕ → E →L[ℝ] E)
    (hζ : ∀ n, Continuous (fun q : P × F => ζ q.1 n q.2))
    (hπ : ∀ n, Continuous (fun q : P × E => π q.1 n q.2))
    (hA : ∀ n, Continuous (fun q : P × E => A q.1 n q.2)) (n : ℕ) :
    Continuous (fun q : P × F => stableMixedBlock (ζ q.1 n) (ζ q.1 (n + 1))
      (π q.1 (n + 1)) (A q.1 n) q.2) := by
  exact (continuous_stableProjection_apply (fun p => ζ p (n + 1)) (fun p => π p (n + 1))
    (hζ (n + 1)) (hπ (n + 1))).comp
      (continuous_fst.prodMk ((hA n).comp (continuous_fst.prodMk (hζ n))))

theorem continuous_stableFrameAssembly_apply
    (ζ : P → F →L[ℝ] E) (hζ : Continuous (fun q : P × F => ζ q.1 q.2)) :
    Continuous (fun q : P × (E × F) => stableFrameAssembly (ζ q.1) q.2) :=
  continuous_snd.fst.add (hζ.comp (continuous_fst.prodMk continuous_snd.snd))

theorem continuous_stableFrame_sources_local
    (ζ : P → ℕ → F →L[ℝ] E) (π : P → ℕ → E →L[ℝ] F)
    (A : P → ℕ → E →L[ℝ] E) (D : F →L[ℝ] F) (h : P → ℕ → E → E)
    (hζ : ∀ n, Continuous (fun q : P × F => ζ q.1 n q.2))
    (hπ : ∀ n, Continuous (fun q : P × E => π q.1 n q.2))
    (hA : ∀ n, Continuous (fun q : P × E => A q.1 n q.2))
    (ρ δ C : ℝ) (hC : 0 ≤ C) (hζb : ∀ p n, ‖ζ p n‖ ≤ C)
    (hball : (1 + C) * ρ ≤ δ)
    (hh : ∀ n, Continuous (fun q : P × {v : E // ‖v‖ ≤ δ} => h q.1 n q.2.1)) (n : ℕ) :
    Continuous (fun q : P × {v : E × F // ‖v‖ ≤ ρ} =>
      stableFrameForwardSource (ζ q.1) (π q.1) (h q.1) n q.2.1) ∧
    Continuous (fun q : P × {v : E × F // ‖v‖ ≤ ρ} =>
      stableFrameCoordinateSource (ζ q.1) (π q.1) (A q.1) D (h q.1) n q.2.1) := by
  let v := fun q : P × {v : E × F // ‖v‖ ≤ ρ} => stableFrameAssembly (ζ q.1 n) q.2.1
  have hv : Continuous v := (continuous_stableFrameAssembly_apply (fun p => ζ p n) (hζ n)).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hvb (q : P × {v : E × F // ‖v‖ ≤ ρ}) : ‖v q‖ ≤ δ := by
    exact ((stableFrameAssembly (ζ q.1 n)).le_opNorm q.2.1).trans
      ((mul_le_mul (stableFrameAssembly_norm_le _ C hC (hζb q.1 n)) q.2.2
        (norm_nonneg _) (by positivity)).trans hball)
  have hhcv : Continuous (fun q : P × {v : E × F // ‖v‖ ≤ ρ} => h q.1 n (v q)) :=
    (hh n).comp (continuous_fst.prodMk (hv.subtype_mk hvb))
  refine ⟨?_, ?_⟩
  · exact (continuous_stableProjection_apply (fun p => ζ p (n + 1))
      (fun p => π p (n + 1)) (hζ (n + 1)) (hπ (n + 1))).comp
        (continuous_fst.prodMk hhcv)
  · have hva := (hA n).comp (continuous_fst.prodMk hv)
    have hpa := (hπ (n + 1)).comp (continuous_fst.prodMk hva)
    have hpd := D.continuous.comp ((hπ n).comp (continuous_fst.prodMk hv))
    have hph := (hπ (n + 1)).comp (continuous_fst.prodMk hhcv)
    exact (hpa.sub hpd).add hph

end DefocusingNLS

end OAI
