import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateTerms

namespace OAI

/-! Full-space rational private subdivision with distinct physical pairs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPrivate
open Matrix
open scoped BigOperators Classical
variable {n m : ℕ}

def basis : (Fin (n+m) → Fin 2) ≃ ((Fin n ⊕ Fin m) → Fin 2) :=
  Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin 2))

theorem term_matrix (e : Fin m) (t : QMAXZTerm n) (k : Fin 4) :
    (term e t k).matrix =
      (qmaPauliWord (qmaXZSubdivisionWord (left t).word (right t).word e k)).submatrix basis basis := by
  rw [← QMAXZTerm.word_matrix]
  ext s u
  change (∏ i, qmaPauli ((term e t k).word i) (s i) (u i)) =
    ∏ j, qmaPauli (qmaXZSubdivisionWord (left t).word (right t).word e k j)
      (s (finSumFinEquiv j)) (u (finSumFinEquiv j))
  exact (Fintype.prod_equiv finSumFinEquiv _ _ (by intro i; rw [term_word])).symm

theorem term_support (e : Fin m) (t : QMAXZTerm n) (k : Fin 4) :
    qmaPauliSupport (term e t k).word =
      (qmaPauliSupport (qmaXZSubdivisionWord (left t).word (right t).word e k)).map
        finSumFinEquiv.toEmbedding := by
  ext i
  simp only [Finset.mem_map_equiv,qmaPauliSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  have h := term_word e t k (finSumFinEquiv.symm i)
  simpa only [Equiv.apply_symm_apply] using not_congr (congrArg (fun a => a = 0) h).to_iff

theorem term_private (t : Fin m → QMAXZTerm n) (p q : Fin m × Fin 4)
    (hp : (qmaPauliSupport (term p.1 (t p.1) p.2).word).card = 2)
    (he : qmaPauliSupport (term p.1 (t p.1) p.2).word =
      qmaPauliSupport (term q.1 (t q.1) q.2).word) : p = q := by
  rw [term_support,Finset.card_map] at hp
  rw [term_support,term_support] at he
  have he' := Finset.map_injective finSumFinEquiv.toEmbedding he
  obtain ⟨h₁,h₂⟩ := qmaXZSubdivision_private_pair
    (fun e => (left (t e)).word) (fun e => (right (t e)).word)
    (fun e => disjoint (t e)) p.1 q.1 p.2 q.2 hp he'
  exact Prod.ext h₁ h₂

theorem accuracy (N : ℕ) (hN : 0 < N) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    |MediatorGraph.normalizedBottom (∑ p : Fin m × Fin 4,
        (weight (scale N J) (J p.1) p.2:ℂ) • (term p.1 (t p.1) p.2).matrix)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 1/(N:ℝ) := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hc (e : Fin m) : qmaPauliWord (left (t e)).word*qmaPauliWord (right (t e)).word =
      qmaPauliWord (right (t e)).word*qmaPauliWord (left (t e)).word :=
    qmaPauliWord_disjoint_commute _ _ (by
      intro i
      by_cases hi : (left (t e)).word i = 0
      · exact Or.inl hi
      · right
        by_contra hj
        have hi' : i ∈ qmaPauliSupport (left (t e)).word := by simp [qmaPauliSupport,hi]
        have hj' : i ∈ qmaPauliSupport (right (t e)).word := by simp [qmaPauliSupport,hj]
        exact Finset.disjoint_left.mp (disjoint (t e)) hi' hj')
  have h := qmaXZSubdivision_accuracy (fun e => (left (t e)).word) (fun e => (right (t e)).word)
    (fun e => (J e:ℝ)) hc hN'
  dsimp only at h
  rw [← scale_cast] at h
  simp only [factor] at h
  have hs : (∑ p : Fin m × Fin 4,
      (weight (scale N J) (J p.1) p.2:ℂ) • (term p.1 (t p.1) p.2).matrix) =
      (∑ p : Fin m × Fin 4, (qmaXZSubdivisionWeight (scale N J:ℝ) (J p.1:ℝ) p.2:ℂ) •
        qmaPauliWord (qmaXZSubdivisionWord (left (t p.1)).word (right (t p.1)).word p.1 p.2)).submatrix
        basis basis := by
    rw [MediatorGraph.submatrix_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [term_matrix,MediatorGraph.submatrix_smul_apply]
    congr 1
    exact (show (weight (scale N J) (J p.1) p.2:ℂ) = _ from by
      rw [← weight_cast]; rfl)
  rw [hs,MediatorGraph.normalizedBottom_reindex]
  exact_mod_cast h

end ContinuumCoulomb.QuantumPrivate

end

end OAI
