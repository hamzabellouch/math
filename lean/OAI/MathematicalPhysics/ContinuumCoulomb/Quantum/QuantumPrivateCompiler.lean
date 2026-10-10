import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateList

namespace OAI

/-! The complete rational X/Z-to-Heisenberg compiler, without a private-pair input assumption. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPrivate
open QuantumRawExchange Matrix
open scoped BigOperators Classical
variable {n m : ℕ}

theorem rawBudget_packed (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    rawBudget (packed t J) = budget J := by
  simp only [rawBudget,packed,List.map_ofFn,List.sum_ofFn,Function.comp_apply,pack_weight,budget]

theorem rawScale_packed (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    rawScale N (packed t J) = scale N J := by
  simp only [rawScale,rawBudget_packed,scale]

private theorem map_range_eq_ofFn {α : Type} (f : ℕ → α) :
    (List.range m).map f = List.ofFn (fun i : Fin m => f i.val) := by
  simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
    (List.ofFn_getElem_eq_map (List.range m) f).symm

theorem subdivide_packed (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    subdivide (n,N,packed t J) = packed (familyTerm t) (familyWeight N J) := by
  change ((List.range (packed t J).length).map (fun e =>
    rawBlock n e (rawScale N (packed t J)) (((packed t J).drop e).headD zeroRaw))).flatten = _
  rw [rawScale_packed]
  have hlen : (packed t J).length = m := List.length_ofFn
  rw [hlen,map_range_eq_ofFn]
  have hget (e : Fin m) : ((packed t J).drop e.val).headD zeroRaw = pack (t e) (J e) := by
    simp only [List.headD_eq_head?_getD,List.head?_drop,packed,
      List.getElem?_ofFn,show e.val < m from e.isLt,↓reduceDIte,Option.getD_some]
  simp only [hget,rawBlock]
  unfold packed
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*4+j.val,by omega⟩ : Fin (m*4)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*4+j.val = j.val+4*i.val
    omega
  simp only [familyTerm,familyWeight,he,Equiv.symm_apply_apply]
  exact rawTerm_pack i (t i) (scale N J) (J i) j

theorem output_packed (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    output (n,N,packed t J) = (n+m,N,packed (familyTerm t) (familyWeight N J)) := by
  rw [output,subdivide_packed]
  simp only [packed,List.length_ofFn]

theorem compile_accuracy (N : ℕ) (hN : 0 < N) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    |MediatorGraph.normalizedBottom (rawMatrix ((n+m)*4) (compile (n,N,packed t J)))-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 3/(N:ℝ) := by
  rw [compile,output_packed]
  exact compiled_accuracy N hN t J

theorem compile_valid (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (b : MediatorListProgram.Bond) (hb : b ∈ (compile (n,N,packed t J)).1) :
    b.1 < (n+m)*4 ∧ b.2.1 < (n+m)*4 ∧ b.1 ≠ b.2.1 := by
  rw [compile,output_packed] at hb
  exact QuantumRawExchange.compile_valid N (familyTerm t) (familyWeight N J) b hb

end ContinuumCoulomb.QuantumPrivate

end

end OAI
