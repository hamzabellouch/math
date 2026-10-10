import OAI.RepresentationTheory.FoulkesHowe.GeneratorLift
import OAI.RepresentationTheory.FoulkesHowe.FoulkesMultilinear
import OAI.RepresentationTheory.FoulkesHowe.FoulkesSymmetries

namespace OAI

noncomputable section
namespace Problem346

private def rowIndexEquiv {I J : Type*} (i : I) :
    {p : I × J // p.1 = i} ≃ J where
  toFun p := p.1.2
  invFun j := ⟨(i, j), rfl⟩
  left_inv := by
    rintro ⟨⟨i', j⟩, h⟩
    simp only at h
    subst i'
    rfl
  right_inv _ := rfl

/-- Hold all but a single input row of the Foulkes formula fixed. -/
def foulkesRowFormSpanning (a b : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (v : Fin b → Fin a → V) (j : Fin b) :
    MultilinearMap ℂ (fun _ : Fin a => V) (SymPow a (SymPow b V)) := by
  classical
  exact ((foulkesMultilinear a b V).domDomRestrict
    (fun p : Fin b × Fin a => p.1 = j) (fun p => v p.1.1 p.1.2)).domDomCongr
      (rowIndexEquiv j)

@[simp] theorem foulkesRowFormSpanning_apply (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V) (j : Fin b)
    (u : Fin a → V) :
    foulkesRowFormSpanning a b V v j u =
      foulkesFormula a b V (Function.update v j u) := by
  classical
  change foulkesMultilinear a b V
    (fun p => if h : p.1 = j then u p.2 else v p.1 p.2) = _
  rw [foulkesMultilinear_apply]
  congr 1
  funext k i
  by_cases h : k = j
  · subst k
    simp
  · simp [h]

theorem foulkesRowFormSpanning_symmetric (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V) (j : Fin b)
    (σ : Equiv.Perm (Fin a)) (u : Fin a → V) :
    foulkesRowFormSpanning a b V v j (fun i => u (σ i)) =
      foulkesRowFormSpanning a b V v j u := by
  classical
  rw [foulkesRowFormSpanning_apply, foulkesRowFormSpanning_apply]
  have h := foulkesFormula_inner_permute a b V (Function.update v j u)
    (Function.update (fun _ => Equiv.refl (Fin a)) j σ)
  convert h using 1
  congr 1
  funext k i
  by_cases hkj : k = j
  · subst k
    simp
  · simp [Function.update_of_ne hkj]

/-- The specified canonical formula defines a linear map in every bidegree. -/
theorem exists_foulkesMap_from_spanning (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] :
    ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
      IsFoulkesMap a b V μ := by
  classical
  apply exists_symPow_lift_on_spanning (symMonomial a V) (span_symMonomial a V)
    (foulkesFormula a b V)
  · intro v j
    obtain ⟨L, hL⟩ := exists_symPow_lift (foulkesRowFormSpanning a b V v j)
      (foulkesRowFormSpanning_symmetric a b V v j)
    exact ⟨L, fun u => (hL u).trans (foulkesRowFormSpanning_apply a b V v j u)⟩
  · intro σ v
    exact foulkesFormula_outer_permute a b V v σ

end Problem346

end

end OAI
