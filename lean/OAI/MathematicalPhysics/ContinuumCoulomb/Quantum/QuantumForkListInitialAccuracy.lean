import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialCalibration

namespace OAI

/-! The actual initial odd subdivision changes the full-space ground energy
by at most 1/N. Together with the literal fork iteration this is (k+1)/N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

theorem initial_accuracy (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (c N : ℚ) (hN : 0 < N) :
    |normalizedBottom (matrix (initial n bs c N))-normalizedBottom (rawMatrix n (bs,c))| ≤
      1/(N:ℝ) := by
  let left : Fin bs.length → Fin n := (SourceBondLists.bonds n bs hb).left
  let right : Fin bs.length → Fin n := (SourceBondLists.bonds n bs hb).right
  let J : Fin bs.length → ℚ := fun e => (bs.get e).2.2
  have hneq : ∀ e, left e ≠ right e := SourceBondLists.bonds_noLoops n bs hb hn
  have h := qmaPathsGraph_accuracy (fun a : Fin 0 => Fin.elim0 a)
    (fun a : Fin 0 => Fin.elim0 a) (fun a => Fin.elim0 a) (fun _ => 0) (c:ℝ)
    (qmaOriginalSite left right) (qmaOriginalSite_injective left right hneq)
    (fun _ => false) (fun e => (J e:ℝ)) (show (0:ℝ) < N by exact_mod_cast hN)
  dsimp only at h
  have hscale : (initialScale N bs c:ℝ)=
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|))
        (|(c:ℝ)|+4*∑ e, (1+|(J e:ℝ)|)^2) (N:ℝ) := initialScale_cast N bs c
  simp only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero,zero_add] at h
  rw [← hscale] at h
  have hout : normalizedBottom (matrix (initial n bs c N))=
      normalizedBottom (qmaPathsGraph (fun a : Fin 0 => Fin.elim0 a)
        (fun a : Fin 0 => Fin.elim0 a) (fun _ => 0) (c:ℝ) (initialScale N bs c:ℝ)
        (qmaOriginalSite left right) (fun _ => false) (fun e => (J e:ℝ))) := by
    rw [initial_bottom_physical n bs hb c N]
    unfold rawBottom
    exact congrArg normalizedBottom (initialPhysical_matrix left right J c (initialScale N bs c))
  have hin : rawMatrix n (bs,c)=qmaExchangeMatrix left right (fun e => (J e:ℝ)) (c:ℝ) := by
    rw [rawMatrix_eq_matrix]
    exact (QuantumListGraph.ofBonds_matrix n bs c hb hn).symm
  have hJ : ∀ e, ((J e:ℝ):ℂ)=(J e:ℂ) := by intro e; norm_cast
  have hc : ((c:ℝ):ℂ)=(c:ℂ) := by norm_cast
  simp only [qmaExchangeMatrix,Finset.univ_eq_empty,Finset.sum_empty,zero_add] at h
  have hin' : rawMatrix n (bs,c)=
      ∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e)+(c:ℂ) • 1 := by
    simpa only [qmaExchangeMatrix,hJ,hc] using hin
  change |normalizedBottom _-normalizedBottom _| ≤ 1/(N:ℝ) at h
  rw [← hout] at h
  have heq : (c:ℂ) • (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)+
      ∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e)=rawMatrix n (bs,c) := by
    rw [hin']
    exact add_comm _ _
  simpa only [qmaOriginalSite,Matrix.cons_val_zero,Matrix.cons_val_one,hJ,hc,heq] using h

theorem initial_iterated_accuracy (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (hn : ∀ b ∈ bs, b.1 ≠ b.2.1) (c N : ℚ) (hN : 0 < N) (k : ℕ) :
    |normalizedBottom (matrix (iterate N k (initial n bs c N)))-
      normalizedBottom (rawMatrix n (bs,c))| ≤ ((k:ℝ)+1)/(N:ℝ) := by
  calc
    _ ≤ |normalizedBottom (matrix (iterate N k (initial n bs c N)))-
        normalizedBottom (matrix (initial n bs c N))|+
        |normalizedBottom (matrix (initial n bs c N))-normalizedBottom (rawMatrix n (bs,c))| :=
      abs_sub_le _ _ _
    _ ≤ (k:ℝ)/(N:ℝ)+1/(N:ℝ) :=
      add_le_add (initial_iterate_accuracy n bs c N hN k) (initial_accuracy n bs hb hn c N hN)
    _ = ((k:ℝ)+1)/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
