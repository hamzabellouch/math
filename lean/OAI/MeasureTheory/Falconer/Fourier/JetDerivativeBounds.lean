import OAI.MeasureTheory.Falconer.Fourier.ReachedMaskJets

namespace OAI

/-! # Derivative bounds for individual ambient mask jets

These estimates retain the order of each differentiated mask. Evaluation
on fixed unit vectors is a contraction, so differentiating a mask jet costs
only the corresponding higher derivative of that same mask.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem norm_iteratedFDeriv_nested {d : ℕ} (f : Space d → ℝ)
    (k t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ =
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_iteratedFDeriv,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,ih]
    rw [show k+1+t = k+(t+1) by omega]

private noncomputable def jetEvaluation {d k : ℕ} (v : Fin k → Space d) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space d) ℝ) →L[ℝ] ℝ where
  toFun L := L v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const v

private theorem jetEvaluation_norm_le {d k : ℕ} (v : Fin k → Space d)
    (hv : ∀ j, ‖v j‖ ≤ 1) : ‖jetEvaluation v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖L v‖ ≤ 1*‖L‖
  have hp : (∏ j, ‖v j‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => norm_nonneg (v j)) (fun j _ => hv j)
  simpa only [one_mul] using (L.le_opNorm v).trans
    (mul_le_of_le_one_right (norm_nonneg L) hp)

 theorem norm_iteratedFDeriv_jetValue_le {d : ℕ} (f : Space d → ℝ)
    (hf : ContDiff ℝ ∞ f) (k t : ℕ) (v : Fin k → Space d)
    (hv : ∀ j, ‖v j‖ ≤ 1) (z : Space d) :
    ‖iteratedFDeriv ℝ t (fun y => (iteratedFDeriv ℝ k f y) v) z‖ ≤
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  have hfd : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) :=
    hf.iteratedFDeriv_right (by simp)
  change ‖iteratedFDeriv ℝ t (jetEvaluation v ∘ iteratedFDeriv ℝ k f) z‖ ≤ _
  rw [(jetEvaluation v).iteratedFDeriv_comp_left hfd.contDiffAt (by simp)]
  calc
    _ ≤ ‖jetEvaluation v‖ * ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (jetEvaluation_norm_le v hv)
    _ = _ := norm_iteratedFDeriv_nested f k t z

 theorem descriptorJetValue_derivatives (d k t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (fun y =>
          (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) z‖ ≤
        C * ((descriptorMaskRadius N σ b)⁻¹)^(k+t) := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientMask_global_derivatives d (k+t)
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x z
  exact (norm_iteratedFDeriv_jetValue_le _
    (descriptorAmbientMask_contDiff Q ρ m N σ J i b S x) k t v hv z).trans
    (hbound Q ρ m N σ J i b S hsep x z)

end Falconer

end OAI
