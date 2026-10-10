import OAI.Analysis.BoundedHochschild.FiniteGroupBarOperators
import OAI.Analysis.BoundedHochschild.FiniteGroupPrefixAverages
import OAI.Analysis.BoundedHochschild.NormalCochainTransport

namespace OAI

/-! Separate normality is retained by finite prefix averaging and by each
bounded bar-insertion operator. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
lemma separatelyNormal_curryMid (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 2)) (hf : SeparatelyNormal e f) (i : Fin (n + 2)) (a : M) :
    SeparatelyNormal e (f.curryMid i a) := by
  intro j x z
  obtain ⟨w, hw⟩ := hf (i.succAbove j) (i.insertNth a x) z
  refine ⟨w, fun b => ?_⟩
  change e.symm (f (i.insertNth a (Function.update x j b))) z = e.symm b w
  rw [Fin.insertNth_update]
  exact hw b

lemma barInsertion_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (u : Fin (n + 3) → unitary M) (i : Fin (n + 2))
    (f : Cochain M (n + 2)) (hf : SeparatelyNormal e f) :
    SeparatelyNormal e (barInsertion u i f) :=
  separatelyNormal_curryMid e _
    (cochainUnitaryTransport_normal e (unitaryPrefix u (i.val + 1)) f hf) i 1

variable {G : Type v} [Group G] [Fintype G]

lemma finiteGroupPrefixAverage_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (ρ : G →* unitary M) (k : ℕ) (f : Cochain M (n + 1)) (hf : SeparatelyNormal e f) :
    SeparatelyNormal e (finiteGroupPrefixAverage ρ k f) := by
  unfold finiteGroupPrefixAverage
  apply separatelyNormal_smul e
  apply separatelyNormal_sum e
  intro g _
  exact cochainUnitaryTransport_normal e _ f hf

lemma finiteGroupBarInsertion_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (ρ : G →* unitary M) (i : Fin (n + 2))
    (f : Cochain M (n + 2)) (hf : SeparatelyNormal e f) :
    SeparatelyNormal e (finiteGroupBarInsertion ρ i f) := by
  unfold finiteGroupBarInsertion
  apply separatelyNormal_smul e
  apply separatelyNormal_sum e
  intro g _
  exact barInsertion_normal e _ i f hf

lemma finiteGroupBarOperator_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (ρ : G →* unitary M) (f : Cochain M (n + 2)) (hf : SeparatelyNormal e f) :
    SeparatelyNormal e (finiteGroupBarOperator ρ f) := by
  unfold finiteGroupBarOperator
  apply separatelyNormal_sum e
  intro i _
  exact separatelyNormal_smul e _ _ (finiteGroupBarInsertion_normal e ρ i f hf)

end BoundedHochschild.KadisonRingrose

end

end OAI
