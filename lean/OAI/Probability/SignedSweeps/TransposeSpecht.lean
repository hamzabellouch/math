import OAI.Probability.SignedSweeps.RestrictionSum2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def transposeLabels {n : ℕ} (lam : Partition n) : SymmetricGroup n where
  toFun i := lam.tableau ⟨(lam.transpose.tableau.symm i).1.swap,
    YoungDiagram.mem_transpose.mp (lam.transpose.tableau.symm i).2⟩
  invFun i := lam.transpose.tableau ⟨(lam.tableau.symm i).1.swap,
    YoungDiagram.mem_transpose.mpr (by simp)⟩
  left_inv i := by simp
  right_inv i := by simp

@[simp] lemma transposeLabels_row {n : ℕ} (lam : Partition n) (i : Fin n) :
    lam.rowOf (transposeLabels lam i) = lam.transpose.colOf i := by
  simp [Partition.rowOf, Partition.colOf, transposeLabels]

@[simp] lemma transposeLabels_col {n : ℕ} (lam : Partition n) (i : Fin n) :
    lam.colOf (transposeLabels lam i) = lam.transpose.rowOf i := by
  simp [Partition.rowOf, Partition.colOf, transposeLabels]

lemma transposeLabels_conj_row {n : ℕ} (lam : Partition n) (g : rowSubgroup lam.transpose) :
    (transposeLabels lam).permCongr g.1 ∈ colSubgroup lam := by
  intro x
  obtain ⟨i, rfl⟩ := (transposeLabels lam).surjective x
  change lam.colOf (transposeLabels lam (g.1 ((transposeLabels lam).symm
    (transposeLabels lam i)))) = _
  rw [Equiv.symm_apply_apply, transposeLabels_col, transposeLabels_col]
  exact g.2 i

lemma transposeLabels_conj_col {n : ℕ} (lam : Partition n) (g : colSubgroup lam.transpose) :
    (transposeLabels lam).permCongr g.1 ∈ rowSubgroup lam := by
  intro x
  obtain ⟨i, rfl⟩ := (transposeLabels lam).surjective x
  change lam.rowOf (transposeLabels lam (g.1 ((transposeLabels lam).symm
    (transposeLabels lam i)))) = _
  rw [Equiv.symm_apply_apply, transposeLabels_row, transposeLabels_row]
  exact g.2 i

@[simp] lemma complexSign_permCongr {n : ℕ} (t g : SymmetricGroup n) :
    complexSign n (t.permCongr g) = complexSign n g := by
  change (((Equiv.Perm.sign (t.permCongr g) : ℤˣ) : ℤ) : ℂ) = _
  rw [Equiv.Perm.sign_permCongr]
  rfl

lemma signTwist_irreducible {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [Nontrivial E] (ρ : Representation ℂ (SymmetricGroup n) E)
    [ρ.IsIrreducible] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) : (signTwist ρ).IsIrreducible := by
  apply irreducible_of_scalar_commutant _ (signTwist_norm ρ hρ)
  intro f
  let k := f.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (by
    intro g x
    have he := Representation.IntertwiningMap.isIntertwining _ _ f g x
    change f (complexSign n g • ρ g x) = complexSign n g • ρ g (f x) at he
    rw [map_smul] at he
    exact (smul_right_injective E (by
      intro hz
      have he := complexSign_mul_self g
      simp [hz] at he)) he)
  have h1 : (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact hx (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hz)
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' _ h1).mp
    (Representation.IsIrreducible.finrank_intertwiningMap_self ρ) k
  refine ⟨z, ?_⟩
  ext x
  exact (congrArg (fun g : Representation.IntertwiningMap ρ ρ => g x) hz).symm

def unconjugateIntertwiner {n : ℕ} {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ (SymmetricGroup n) E)
    (τ : Representation ℂ (SymmetricGroup n) F) (t : SymmetricGroup n)
    (f : Representation.IntertwiningMap ρ (τ.comp t.permCongrHom.toMonoidHom)) :
    Representation.IntertwiningMap ρ τ :=
  (τ t⁻¹ ∘ₗ f.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change τ t⁻¹ (f (ρ g x)) = τ g (τ t⁻¹ (f x))
    rw [f.isIntertwining]
    change (τ t⁻¹ * τ (t.permCongr g)) (f x) = (τ g * τ t⁻¹) (f x)
    rw [← map_mul, ← map_mul]
    congr 2
    ext i
    simp)

theorem specht_transpose_sign_equiv {n : ℕ} (lam : Partition n) :
    Nonempty (Representation.Equiv (spechtRepresentation lam.transpose)
      (signTwist (spechtRepresentation lam))) := by
  let ρ := spechtRepresentation lam
  let τ := signTwist ρ
  let t := transposeLabels lam
  let σ := τ.comp t.permCongrHom.toMonoidHom
  have hσ (g : SymmetricGroup n) (x : Specht lam) : ‖σ g x‖ = ‖x‖ :=
    signTwist_norm ρ (spechtRepresentation_norm lam) (t.permCongr g) x
  obtain ⟨f, hf⟩ := specht_occurs_of_row_average lam.transpose σ hσ
      (spechtRowVector lam) (by
        intro c
        change complexSign n (t.permCongr c.1) •
          ρ (t.permCongr c.1) (spechtRowVector lam) = _
        rw [complexSign_permCongr]
        congr 1
        exact spechtRowVector_invariant lam ⟨_, transposeLabels_conj_col lam c⟩) (by
        let P := groupAverage (ρ.comp (rowSubgroup lam).subtype)
        let Q := groupAverage (σ.comp (rowSubgroup lam.transpose).subtype)
        have hP : P.IsSymmetricProjection := ⟨groupAverage_idempotent _,
          groupAverage_symmetric _ (fun g => spechtRepresentation_norm lam g.1)⟩
        have hQ : Q.IsSymmetric := groupAverage_symmetric _ (fun g => hσ g.1)
        have hQg : Q (spechtGenerator lam) = spechtGenerator lam := by
          apply groupAverage_fixed
          intro a
          change complexSign n (t.permCongr a.1) •
            ρ (t.permCongr a.1) (spechtGenerator lam) = _
          rw [spechtGenerator_column_action lam ⟨_, transposeLabels_conj_row lam a⟩,
            smul_smul, complexSign_mul_self, one_smul]
        exact projection_product_nonzero P Q hP hQ _ hQg (spechtRowVector_ne_zero lam))
  let k := unconjugateIntertwiner (spechtRepresentation lam.transpose) τ t f
  have hk : k ≠ 0 := by
    intro hz
    have he := congrArg (fun j : Representation.IntertwiningMap
      (spechtRepresentation lam.transpose) τ => j (spechtGenerator lam.transpose)) hz
    change τ t⁻¹ (f (spechtGenerator lam.transpose)) = 0 at he
    have he' := congrArg (τ t) he
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at he'
    have hf0 : f (spechtGenerator lam.transpose) = f 0 := by simpa using he'
    exact spechtGenerator_ne_zero _ (hf hf0)
  let : (spechtRepresentation lam.transpose).IsIrreducible := specht_irreducible _
  let : ρ.IsIrreducible := specht_irreducible _
  let : τ.IsIrreducible := signTwist_irreducible ρ (spechtRepresentation_norm lam)
  exact ⟨k.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero k).resolve_right hk)⟩

end SignedSweeps
end

end OAI
