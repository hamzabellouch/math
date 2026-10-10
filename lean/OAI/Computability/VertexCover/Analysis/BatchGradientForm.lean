import Mathlib
import OAI.Computability.VertexCover.Reduction.HighVectorsSeparated
import OAI.Computability.VertexCover.Analysis.ListMassHitMaximum

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable def selectionForm (Φ : LabelCover) {d : ℕ}
    (I : Finset (Φ.Coordinate d)) : (Φ.Coordinate d → ℝ) →L[ℝ] ℝ :=
  ∑ p ∈ I, ContinuousLinearMap.proj p

@[simp] theorem selectionForm_apply (Φ : LabelCover) {d : ℕ}
    (I : Finset (Φ.Coordinate d)) (x : Φ.Coordinate d → ℝ) :
    Φ.selectionForm I x = ∑ p ∈ I, x p := by
  simp [selectionForm]

theorem compatibilityNorm_continuous (Φ : LabelCover) (d : ℕ) :
    Continuous (Φ.compatibilityNorm (d := d)) := by
  unfold compatibilityNorm
  apply Continuous.finset_sup'_apply
  intro I hI
  simpa only [Φ.selectionForm_apply] using (Φ.selectionForm I).continuous.abs

theorem distanceTo_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (Φ.distanceTo A hA) := by
  unfold distanceTo
  apply Continuous.finset_inf'_apply
  intro a ha
  exact (Φ.compatibilityNorm_continuous d).comp (continuous_id.sub continuous_const)

abbrev BatchWeights (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :=
  J → Fin (Φ.WeightDimension d) → ℝ

noncomputable def batchSum (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (s : Φ.BatchWeights J) : Φ.Coordinate d → ℝ :=
  ∑ j : J, Φ.increment (Φ.query seed j) (s j)

noncomputable def batchSumCLM (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) : Φ.BatchWeights J →L[ℝ] (Φ.Coordinate d → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := Φ.batchSum seed J
    map_add' := by
      intro s t
      simp only [batchSum, Pi.add_apply, Φ.increment_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a s
      change (∑ j : J, Φ.increment (Φ.query seed j) (fun k => a*s j k)) = _
      simp only [Φ.increment_mul]
      ext p
      simp [batchSum, Finset.mul_sum]
  }

@[simp] theorem batchSumCLM_apply (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (s : Φ.BatchWeights J) :
    Φ.batchSumCLM seed J s = Φ.batchSum seed J s := rfl

noncomputable def batchGradient (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (D : Φ.BatchWeights J →L[ℝ] ℝ) : Φ.BatchWeights J := by
  classical
  exact fun j k => D (Pi.single j (Pi.single k 1))

theorem selectionForm_increment (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (j : Fin d)
    (s : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.selectionForm I (Φ.increment (Φ.query seed j) s) =
      ∑ k, Φ.incidence seed I j k * s k := by
  classical
  rw [Φ.selectionForm_apply]
  by_cases h : ∃ a : (Φ.query seed j).LocalLabel,
      (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I
  · obtain ⟨a, ha⟩ := h
    rw [Finset.sum_eq_single (⟨Φ.query seed j, a⟩ : Φ.Coordinate d)]
    · rw [Φ.increment_same]
      simp_rw [Φ.incidence_eq_single seed hI j a ha]
      simp [truthValue, eq_comm]
    · intro p hp hpa
      apply Φ.increment_other
      intro heq
      exact hpa (hI.1 p hp ⟨_, a⟩ ha heq)
    · intro hn; exact (hn ha).elim
  · have hz : ∀ p ∈ I, Φ.increment (Φ.query seed j) s p = 0 := by
      intro p hp
      apply Φ.increment_other
      intro heq
      rcases p with ⟨i,a⟩
      change i = Φ.query seed j at heq
      subst i
      exact h ⟨a,hp⟩
    rw [Finset.sum_eq_zero hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k hk
    have hi : Φ.incidence seed I j k = 0 := by
      simp only [incidence, truthValue]
      rw [ite_eq_right (fun ⟨label, hlabel, _⟩ => h ⟨label, hlabel⟩)]
    rw [hi, zero_mul]

theorem batchGradient_form (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I)
    (j : J) (k : Fin (Φ.WeightDimension d)) :
    Φ.batchGradient J ((Φ.selectionForm I).comp (Φ.batchSumCLM seed J)) j k =
      Φ.incidence seed I j k := by
  classical
  change Φ.selectionForm I (Φ.batchSum seed J (Pi.single j (Pi.single k 1))) = _
  unfold batchSum
  rw [map_sum]
  simp_rw [Φ.selectionForm_increment seed hI]
  rw [Finset.sum_eq_single j]
  · simp [Pi.single_apply, mul_ite]
  · intro j' hj' hne
    simp [Pi.single_eq_of_ne hne]
  · simp

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
