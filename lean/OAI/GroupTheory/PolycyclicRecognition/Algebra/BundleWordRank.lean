import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleWordCoordinates

namespace OAI

/-! # Independent full-rank source bundles give a full-rank tuple map -/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem pi_map_submersive {ι V W : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (z : ι → V) (hd : ∀ i, DifferentiableAt ℝ f (z i))
    (hs : ∀ i, Function.Surjective (fderiv ℝ f (z i))) :
    Function.Surjective (fderiv ℝ (fun x : ι → V => fun i => f (x i)) z) := by
  have hder : HasFDerivAt (fun x : ι → V => fun i => f (x i))
      (ContinuousLinearMap.pi (fun i => (fderiv ℝ f (z i)).comp (ContinuousLinearMap.proj i))) z :=
    hasFDerivAt_pi.mpr (fun i => (hd i).hasFDerivAt.comp z ((ContinuousLinearMap.proj i : (ι → V) →L[ℝ] V).hasFDerivAt))
  rw [hder.fderiv]
  intro w
  choose v hv using (fun i => hs i (w i))
  exact ⟨v, funext hv⟩

theorem bundleWordEndpoint_submersive {I : Type*} [Fintype I] {n m h c M N : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ))
    (p : WordLawData I n) (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p) t₀)) :
    Function.Surjective (fderiv ℝ (bundleWordEndpoint a letters input output p)
      (input.symm (fun _ => t₀))) := by
  let f := differenceAmplitudeWordEndpoint a letters p
  let z := fun _ : Fin h => t₀
  have hdf : Differentiable ℝ f :=
    ((contDiff_differenceAmplitudeWord (q := 1) a letters).comp
      (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
  have hs' := pi_map_submersive f z (fun i => hdf _) (fun _ => hs)
  have hd : DifferentiableAt ℝ (fun x : Fin h → Fin (m + m) → ℝ => fun i => f (x i)) z :=
    (differentiable_pi.mpr (fun i => hdf.comp (ContinuousLinearMap.proj i).differentiable)) z
  have hd' : HasFDerivAt (fun x : Fin h → Fin (m + m) → ℝ => fun i => f (x i))
      (fderiv ℝ (fun x : Fin h → Fin (m + m) → ℝ => fun i => f (x i)) z)
      (input (input.symm z)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hd.hasFDerivAt
  have h₁ := hd'.comp (input.symm z) input.hasFDerivAt
  have h₂ := output.symm.hasFDerivAt.comp (input.symm z) h₁
  change HasFDerivAt (bundleWordEndpoint a letters input output p) _ (input.symm z) at h₂
  rw [h₂.fderiv]
  exact output.symm.surjective.comp (hs'.comp input.surjective)

end PolycyclicRecognition

end

end OAI
