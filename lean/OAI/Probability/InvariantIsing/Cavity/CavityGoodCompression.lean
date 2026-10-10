import OAI.Probability.InvariantIsing.Cavity.CavityHaarCorrection

namespace OAI

/-! Simultaneous control of the finitely many spectral compression
blocks, obtained from their positive limiting proportions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavityHaarWindow_correction_all {q m : ℕ}
    (N : ℕ → ℕ) (l u : Fin m → ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k) (hle : ∀ a k, l a k ≤ N k)
    (hue : ∀ a k, u a k ≤ N k)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 < ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / N k) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / N k) atTop (𝓝 (ρu a)))
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun k => (μ k).real {U | ∀ a,
      ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k)))⁻¹‖ ≤ L})
      atTop (𝓝 1) := by
  let K := fun a => ‖(CFC.sqrt ((ρu a - ρl a) • (1 : Matrix (Fin q) (Fin q) ℝ)))⁻¹‖
  let L := 1 + ∑ a, K a
  have hK : ∀ a, K a < L := by
    intro a
    have hs : K a ≤ ∑ a, K a :=
      Finset.single_le_sum (f := K) (fun a _ => norm_nonneg _) (Finset.mem_univ a)
    dsimp only [L]
    linarith
  have hL : 0 < L := by
    have hs : 0 ≤ ∑ a, K a := Finset.sum_nonneg fun _ _ => norm_nonneg _
    dsimp only [L]
    linarith
  let A := fun k a => {U : Orthogonal (N k) | ‖(CFC.sqrt (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k)))⁻¹‖ ≤ L}
  have hmA : ∀ k a, MeasurableSet (A k a) := by
    intro k a
    apply measurableSet_le _ measurable_const
    exact ((cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm).comp
      (((continuous_cavityWindowGram (N k) q (l a k) (u a k)).comp
        (continuous_subtype_val.matrix_mul continuous_const)).measurable)
  have hp : ∀ a, Tendsto (fun k => (μ k).real (A k a)) atTop (𝓝 1) := by
    intro a
    exact cavityHaarWindow_correction_probability N (l a) (u a) hN (hu a) (hl a)
      (hlu a) (hle a) (hue a) (ρl a) (ρu a) (hρ a) (hρl a) (hρu a) μ A₀ hA₀ (hK a)
  let G := fun k => ⋂ a, A k a
  have hmG : ∀ k, MeasurableSet (G k) := fun k => MeasurableSet.iInter (hmA k)
  have hpc : ∀ a, Tendsto (fun k => (μ k).real (A k a)ᶜ) atTop (𝓝 0) := by
    intro a
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hp a)
    simpa only [measureReal_compl (hmA _ a), probReal_univ, sub_self] using ht
  have hbound : ∀ k, (μ k).real (G k)ᶜ ≤ ∑ a, (μ k).real (A k a)ᶜ := by
    intro k
    have he : (G k)ᶜ = ⋃ a, (A k a)ᶜ := by ext U; simp [G]
    rw [he]
    exact measureReal_iUnion_fintype_le _
  have hzero : Tendsto (fun k => (μ k).real (G k)ᶜ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) hbound
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun a _ => hpc a)
  refine ⟨L, hL, ?_⟩
  have ht := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hzero
  have he (k : ℕ) : 1 - (μ k).real (G k)ᶜ = (μ k).real (G k) := by
    rw [measureReal_compl (hmG k), probReal_univ]
    ring
  have ht' : Tendsto (fun k => (μ k).real (G k)) atTop (𝓝 1) := by
    simpa only [he, sub_zero] using ht
  convert ht' using 1
  funext k
  congr 1
  ext U
  simp [G, A]

end InvariantIsing

end

end OAI
