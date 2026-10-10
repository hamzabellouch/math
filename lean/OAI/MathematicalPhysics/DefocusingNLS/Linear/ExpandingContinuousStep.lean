import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStepExistence

namespace OAI

/-! # A continuous actual nonlinear step for varying scale and initial data

The already proved uniform small-data construction now yields a jointly
continuous selected trajectory and endpoint remainder.  Uniqueness of the
small trajectory makes this independent of the existence proof's choices.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingPicard expandingPerturbationReaction
  expandingProfileTrajectory

theorem exists_expandingContinuous_step
    {P : Type*} [TopologicalSpace P] (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀
      (L : P → {L : ℝ // 1 ≤ L}) (q g : P → C(Icc (0 : ℝ) T, FourierL2)) (G : ℝ),
      Continuous L → Continuous q → Continuous g → 0 ≤ G → G ≤ δ →
      (hq : ∀ p t, ‖q p t‖ ≤ R) → (∀ p t, ‖g p t‖ ≤ G) →
      ∃ (V : P × {f : FourierL2 // ‖f‖ ≤ δ} → C(Icc (0 : ℝ) T, FourierL2))
        (h : P × {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2),
        Continuous V ∧ Continuous h ∧
        (∀ z, V z = expandingPicard a b k (L z.1).1 T ha hk (L z.1).2 hT
          (expandingPerturbationReaction a k (L z.1).1 T ha ha1 hk (L z.1).2 m
            (q z.1) (g z.1)) z.2.1 (V z)) ∧
        (∀ z, ‖V z‖ ≤ A * (‖z.2.1‖ + G)) ∧ (∀ z, ‖V z‖ ≤ 1 / 2) ∧
        (∀ z, V z ⟨T, hT, le_rfl⟩ =
          expandingProfileTrajectory a b k (L z.1).1 T ha ha1 hk (L z.1).2 hT
            m R hR (q z.1) (hq z.1) z.2.1 ⟨T, hT, le_rfl⟩ + h z) := by
  obtain ⟨δ, A, hδ, hA, _, hexists⟩ :=
    exists_expandingPerturbation_step_radius a b k T ha ha1 hk hT m R hR
  refine ⟨δ, A, hδ, hA, ?_⟩
  intro L q g G hL hq hg hG hGδ hqb hgb
  choose V hV hVbound hVhalf using
    (fun z : P × {f : FourierL2 // ‖f‖ ≤ δ} =>
      hexists (L z.1).1 (L z.1).2 (q z.1) (g z.1) G hG hGδ (hqb z.1) (hgb z.1)
        z.2.1 z.2.2)
  let h : P × {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2 := fun z =>
    V z ⟨T, hT, le_rfl⟩ - expandingProfileTrajectory a b k (L z.1).1 T ha ha1 hk
      (L z.1).2 hT m R hR (q z.1) (hqb z.1) z.2.1 ⟨T, hT, le_rfl⟩
  have hu₀ : Continuous (fun z : P × {f : FourierL2 // ‖f‖ ≤ δ} => z.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hcV : Continuous V := continuous_expandingPerturbation_family
    (P := P × {f : FourierL2 // ‖f‖ ≤ δ}) a b k T R
    ha ha1 hk hT m hR (fun z => L z.1) (hL.comp continuous_fst)
    (fun z => q z.1) (fun z => g z.1) (hq.comp continuous_fst) (hg.comp continuous_fst)
    (fun z => hqb z.1) (fun z => z.2.1) hu₀ V hV (fun z => (hVhalf z).trans (by norm_num))
  have hch : Continuous h := continuous_expandingStepRemainder_family
    (P := P × {f : FourierL2 // ‖f‖ ≤ δ}) a b k T R
    ha ha1 hk hT m hR (fun z => L z.1) (hL.comp continuous_fst)
    (fun z => q z.1) (fun z => g z.1) (hq.comp continuous_fst) (hg.comp continuous_fst)
    (fun z => hqb z.1) (fun z => z.2.1) hu₀ V hV (fun z => (hVhalf z).trans (by norm_num))
  refine ⟨V, h, hcV, hch, hV, hVbound, hVhalf, ?_⟩
  intro z
  dsimp [h]
  abel

end DefocusingNLS

end OAI
