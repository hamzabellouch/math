import Mathlib
import OAI.Analysis.LaughlinFock.FourBasis
import OAI.Analysis.LaughlinFock.FourCopies
import OAI.Analysis.LaughlinFock.ThreeRows

namespace OAI

/-! Copy Average. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem sectorAverage_of_complete_copies {ι μ : Type*} [Fintype ι]
    [Fintype μ] [DecidableEq μ] (κ : ι → Type*) [∀ i, Fintype (κ i)]
    {Q k : ℕ} (n : ι → ℕ) (hn : Function.Injective n)
    (C : ∀ i, κ i → Matrix μ (Fin (n i+1)) ℂ)
    (hC : ∑ i, ∑ r, C i r * (C i r)ᴴ = 1)
    (W : Matrix (SectorOccupation Q k) μ ℂ)
    (hW : ∀ i r s, sectorOneBody Q k (spinGenerator Q s)*(W*C i r) =
      (W*C i r)*spinGenerator (n i) s)
    (M : Matrix μ μ ℂ) :
    sectorAverage Q k (W*M*Wᴴ) = ∑ i, ∑ r, ∑ s,
      (((C i r)ᴴ*M*C i s).trace / (n i+1 : ℂ)) • ((W*C i r)*(W*C i s)ᴴ) := by
  classical
  have hh : (∑ b : Sigma κ, C b.1 b.2 * (C b.1 b.2)ᴴ) = 1 := by
    simpa only [Fintype.sum_sigma] using hC
  rw [matrix_complete_column_sandwich (fun b : Sigma κ => n b.1)
    (fun b => C b.1 b.2) hh W M]
  simp only [Fintype.sum_sigma, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    exact sectorAverage_spin_mixed_sandwich (W*C i r) (W*C i s) (hW i r) (hW i s) _
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro s _
    exact sectorAverage_spin_cross_sandwich (fun hij => hji (hn hij).symm)
      (W*C i r) (W*C j s) (hW i r) (hW j s) _
  · simp

 
theorem full_column_gram_cast {ι : Type*} {n m : ℕ} (h : n=m)
    (C : Matrix ι (Fin m) ℂ) :
    C.submatrix id (Fin.cast h) * (C.submatrix id (Fin.cast h))ᴴ = C*Cᴴ := by
  subst m
  rfl

 

theorem fourSpinColumns_complete {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ b : FourSpinIndex Q, fourSpinColumns Q b * (fourSpinColumns Q b)ᴴ) = 1 := by
  classical
  rw [Fintype.sum_sigma]
  have hi (r : CopyLabel Q) :
      (∑ z : Fin (2*Q-2*r.val.val+1), fourSpinColumns Q ⟨r,z⟩ *
        (fourSpinColumns Q ⟨r,z⟩)ᴴ) =
      composedCouplingMatrix Q r.val.val * (composedCouplingMatrix Q r.val.val)ᴴ := by
    have hr := r.val.isLt
    have hr0 := r.property.pos
    have hmin : min (2*Q-2) (2*Q-2*r.val.val) = 2*Q-2*r.val.val := by omega
    ext x y
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      composedCouplingMatrix, fourSpinColumns, CoupledIndex, Fintype.sum_sigma]
    rw [hmin]
  simp_rw [hi]
  exact composedCouplingMatrix_complete Q

 

theorem fourCopyColumns_complete {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ D : Fin (2*Q), ∑ r : CopyLabel D.val,
      fourCopyColumns Q D.val r * (fourCopyColumns Q D.val r)ᴴ) = 1 := by
  classical
  let f : ((D : Fin (2*Q)) × CopyLabel D.val) →
      Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ :=
    fun b => fourCopyColumns Q b.1.val b.2 * (fourCopyColumns Q b.1.val b.2)ᴴ
  change (∑ D, ∑ r, f ⟨D,r⟩) = 1
  rw [← Fintype.sum_sigma f]
  rw [← sum_subtype_support (fun b : (D : Fin (2*Q)) × CopyLabel D.val =>
    b.1.val+b.2.val.val ≤ 2*Q) f]
  · rw [← (fourSpinCopyEquiv hQ).sum_comp]
    have hh (b : FourSpinIndex Q) : f (fourSpinCopyEquiv hQ b).val =
        fourSpinColumns Q b * (fourSpinColumns Q b)ᴴ := by
      rw [fourSpinColumns_eq_copy hQ, full_column_gram_cast]
    simp_rw [hh]
    exact fourSpinColumns_complete hQ
  · intro b hb
    simp [f, fourCopyColumns, hb]

 
theorem fourSpinDegree_injective {Q : ℕ} (_hQ : 1 ≤ Q) :
    Function.Injective (fun D : Fin (2*Q) => fourSpinDegree Q D.val) := by
  intro a b hab
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  dsimp [fourSpinDegree] at hab
  omega

 

theorem sectorAverage_four_kernel {Q : ℕ} (hQ : 1 ≤ Q)
    (M : Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ) :
    sectorAverage Q 4 (wideFourWedgeMatrix Q*M*(wideFourWedgeMatrix Q)ᴴ) =
      ∑ D : Fin (2*Q), ∑ r : CopyLabel D.val, ∑ s : CopyLabel D.val,
        (((fourCopyColumns Q D.val r)ᴴ*M*fourCopyColumns Q D.val s).trace /
          (fourSpinDegree Q D.val+1 : ℂ)) •
            (fourCopyWedge Q D.val r*(fourCopyWedge Q D.val s)ᴴ) := by
  exact sectorAverage_of_complete_copies (fun D : Fin (2*Q) => CopyLabel D.val)
    (fun D => fourSpinDegree Q D.val) (fourSpinDegree_injective hQ)
    (fun D => fourCopyColumns Q D.val) (fourCopyColumns_complete hQ)
    (wideFourWedgeMatrix Q) (fun D r s => fourCopyWedge_intertwines hQ r s) M

end LaughlinFock
end

end OAI
