import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParameterSplit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialFamilies
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialMinorDifferential
import Mathlib.LinearAlgebra.Pi

namespace OAI

/-! # Reordering an actual nonzero minor into the sliced coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory

theorem exists_fin_equiv_extending_injection {n m : ℕ}
    (j : Fin n → Fin m) (hj : Function.Injective j) :
    ∃ k : ℕ, ∃ e : Fin (n + k) ≃ Fin m, ∀ i, e (Fin.castAdd k i) = j i := by
  classical
  let s : Set (Fin m) := range j
  let k := Fintype.card ↥(sᶜ)
  let ec : ↥(sᶜ) ≃ Fin k := Fintype.equivFin _
  let e : Fin (n + k) ≃ Fin m := finSumFinEquiv.symm.trans
    (((Equiv.ofInjective j hj).sumCongr ec.symm).trans (Equiv.Set.sumCompl (range j)))
  refine ⟨k, e, fun i => ?_⟩
  simp [e]

/-- This map permutes coordinates, preserving both the cube and Lebesgue measure. -/
def reindexParameters {l m : ℕ} (e : Fin l ≃ Fin m) :
    (Fin l → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (e.symm j))

@[simp] theorem reindexParameters_apply {l m : ℕ} (e : Fin l ≃ Fin m)
    (x : Fin l → ℝ) (j : Fin m) : reindexParameters e x j = x (e.symm j) := rfl

@[simp] theorem reindexParameters_apply_equiv {l m : ℕ} (e : Fin l ≃ Fin m)
    (x : Fin l → ℝ) (j : Fin l) : reindexParameters e x (e j) = x j := by simp

theorem reindexParameters_norm {l m : ℕ} (e : Fin l ≃ Fin m) (x : Fin l → ℝ) :
    ‖reindexParameters e x‖ = ‖x‖ := by
  have h := (IsometryEquiv.piCongrLeft' (Y := fun _ : Fin l => ℝ) e).isometry.dist_eq x 0
  change dist (reindexParameters e x) (reindexParameters e 0) = dist x 0 at h
  simpa only [map_zero, dist_zero_right] using h

theorem measurePreserving_reindexParameters {l m : ℕ} (e : Fin l ≃ Fin m) :
    MeasurePreserving (reindexParameters e) volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) e using 1
  ext x i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply, reindexParameters_apply_equiv]

theorem HasPolynomialFormula.reindex {P : Type*} {l m : ℕ}
    {f : P → (Fin m → ℝ) → ℝ} (hf : HasPolynomialFormula f) (e : Fin l ≃ Fin m) :
    HasPolynomialFormula (fun a x => f a (reindexParameters e x)) := by
  obtain ⟨D, hD⟩ := hf
  refine ⟨D, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  refine ⟨MvPolynomial.rename e.symm p, (MvPolynomial.totalDegree_rename_le _ _).trans hp, ?_⟩
  intro x
  rw [MvPolynomial.eval_rename]
  exact he _

theorem reindexParameters_single {l m : ℕ} (e : Fin l ≃ Fin m) (j : Fin l) :
    reindexParameters e (Pi.single j 1) = Pi.single (e j) 1 := by
  classical
  ext i
  obtain ⟨i, rfl⟩ := e.surjective i
  simp [Pi.single_apply, e.injective.eq_iff]

/-- The selected column determinant is the derivative determinant after reordering. -/
theorem det_reindexed_slice {n k m : ℕ} (e : Fin (n + k) ≃ Fin m)
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (v : Fin n → ℝ) (z : Fin k → ℝ)
    (hf : DifferentiableAt ℝ f (reindexParameters e (Fin.append v z))) :
    (fderiv ℝ (fun w => f (reindexParameters e (Fin.append w z))) v).det =
      (Matrix.of fun i j => fderiv ℝ f (reindexParameters e (Fin.append v z))
        (Pi.single (e (Fin.castAdd k j)) 1) i).det := by
  have hd := hf.hasFDerivAt.comp v
    ((reindexParameters e).hasFDerivAt.comp v (hasFDerivAt_finAppend v z))
  change HasFDerivAt (fun w => f (reindexParameters e (Fin.append w z))) _ v at hd
  rw [hd.fderiv]
  change (ContinuousLinearMap.comp _ _).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ f _ (reindexParameters e (appendParameterLinear n k (Pi.single j 1))) i = _
  have ha : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [appendParameterLinear, Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [ha, reindexParameters_single]
  rfl

end PolycyclicRecognition

end

end OAI
