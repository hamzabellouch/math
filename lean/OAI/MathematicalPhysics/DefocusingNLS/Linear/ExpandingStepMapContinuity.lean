import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStepMap

namespace OAI

/-! # The continuous nonlinear endpoint map with its quantitative remainder

This combines the exact nonlinear-step estimates and parameter continuity
for the same selected trajectories.  Shrinking the input ball keeps every
selected trajectory inside the fixed state ball used by the local theory.
-/

open Set

universe u

namespace DefocusingNLS

attribute [local irreducible] expandingPicard expandingPerturbationReaction
  expandingProfileTrajectory

theorem exists_expandingNonlinear_stepMap_continuous
    (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (P : Type u) [TopologicalSpace P], ∀
      (L : P → {L : ℝ // 1 ≤ L}) (q g : P → C(Icc (0 : ℝ) T, FourierL2)) (G : P → ℝ),
      Continuous L → Continuous q → Continuous g → (∀ p, 0 ≤ G p) → (∀ p, G p ≤ δ) →
      (hq : ∀ p t, ‖q p t‖ ≤ R) → (∀ p t, ‖g p t‖ ≤ G p) →
      ∃ (V : P × {f : FourierL2 // ‖f‖ ≤ δ} → C(Icc (0 : ℝ) T, FourierL2))
        (h : P × {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2),
        Continuous V ∧ Continuous h ∧
        (∀ z, V z = expandingPicard a b k (L z.1).1 T ha hk (L z.1).2 hT
          (expandingPerturbationReaction a k (L z.1).1 T ha ha1 hk (L z.1).2 m
            (q z.1) (g z.1)) z.2.1 (V z)) ∧
        (∀ z, ‖V z‖ ≤ C * (‖z.2.1‖ + G z.1)) ∧
        (∀ z, V z ⟨T, hT, le_rfl⟩ =
          expandingProfileTrajectory a b k (L z.1).1 T ha ha1 hk (L z.1).2 hT
            m R hR (q z.1) (hq z.1) z.2.1 ⟨T, hT, le_rfl⟩ + h z) ∧
        (∀ z, z.2.1 = 0 → ‖h z‖ ≤ C * G z.1) ∧
        (∀ d : ℝ, 0 < d → d ≤ δ → ∀ p f j, ‖f.1‖ ≤ d → ‖j.1‖ ≤ d →
          ‖h (p, f) - h (p, j)‖ ≤ C * (d + G p) * ‖f.1 - j.1‖) := by
  obtain ⟨δ₀, C, hδ₀, hC, hstep⟩ :=
    exists_expandingNonlinear_stepMap a b k T ha ha1 hk hT m R hR
  let δ := min δ₀ (1 / (4 * C))
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hCδ : C * δ ≤ 1 / 4 := by
    calc
      C * δ ≤ C * (1 / (4 * C)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = 1 / 4 := by field_simp [hC.ne']
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro P inst L q g G hL hq hg hG hGδ hqb hgb
  choose V₀ h₀ hV₀ hVbound₀ hEnd₀ hZero₀ hLip₀ using
    (fun p => hstep (L p).1 (L p).2 (q p) (g p) (G p) (hG p)
      ((hGδ p).trans hδle) (hqb p) (hgb p))
  let lift : {f : FourierL2 // ‖f‖ ≤ δ} → {f : FourierL2 // ‖f‖ ≤ δ₀} :=
    fun f => ⟨f.1, f.2.trans hδle⟩
  let V : P × {f : FourierL2 // ‖f‖ ≤ δ} → C(Icc (0 : ℝ) T, FourierL2) :=
    fun z => V₀ z.1 (lift z.2)
  let h : P × {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2 :=
    fun z => h₀ z.1 (lift z.2)
  have hV z : V z = expandingPicard a b k (L z.1).1 T ha hk (L z.1).2 hT
      (expandingPerturbationReaction a k (L z.1).1 T ha ha1 hk (L z.1).2 m
        (q z.1) (g z.1)) z.2.1 (V z) := hV₀ z.1 (lift z.2)
  have hVbound z : ‖V z‖ ≤ C * (‖z.2.1‖ + G z.1) := hVbound₀ z.1 (lift z.2)
  have hsmall z : ‖V z‖ ≤ 1 := by
    apply (hVbound z).trans
    have he := mul_le_mul_of_nonneg_left (add_le_add z.2.2 (hGδ z.1)) hC.le
    nlinarith
  have hu₀ : Continuous (fun z : P × {f : FourierL2 // ‖f‖ ≤ δ} => z.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hcV : Continuous V := continuous_expandingPerturbation_family
    (P := P × {f : FourierL2 // ‖f‖ ≤ δ}) a b k T R
    ha ha1 hk hT m hR (fun z => L z.1) (hL.comp continuous_fst)
    (fun z => q z.1) (fun z => g z.1) (hq.comp continuous_fst) (hg.comp continuous_fst)
    (fun z => hqb z.1) (fun z => z.2.1) hu₀ V hV hsmall
  have he (z : P × {f : FourierL2 // ‖f‖ ≤ δ}) : h z = V z ⟨T, hT, le_rfl⟩ -
      expandingProfileTrajectory a b k (L z.1).1 T ha ha1 hk (L z.1).2 hT m R hR
        (q z.1) (hqb z.1) z.2.1 ⟨T, hT, le_rfl⟩ := by
    have hz := hEnd₀ z.1 (lift z.2)
    change V z ⟨T, hT, le_rfl⟩ = _ + h z at hz
    rw [hz]
    abel
  have hch : Continuous h := by
    have hc := continuous_expandingStepRemainder_family
      (P := P × {f : FourierL2 // ‖f‖ ≤ δ}) a b k T R ha ha1 hk hT m hR
      (fun z => L z.1) (hL.comp continuous_fst) (fun z => q z.1) (fun z => g z.1)
      (hq.comp continuous_fst) (hg.comp continuous_fst) (fun z => hqb z.1)
      (fun z => z.2.1) hu₀ V hV hsmall
    exact (funext he) ▸ hc
  refine ⟨V, h, hcV, hch, hV, hVbound, ?_, ?_, ?_⟩
  · intro z
    exact hEnd₀ z.1 (lift z.2)
  · intro z hz
    exact hZero₀ z.1 (lift z.2) hz
  · intro d hd hdδ p f j hf hj
    exact hLip₀ p d hd (hdδ.trans hδle) (lift f) (lift j) hf hj

end DefocusingNLS

end OAI
