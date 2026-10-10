import OAI.Combinatorics.ContingencyTables.Dense.DenseCanonicalProgram

namespace OAI

/-! # Correctness of dense sampling with computed initialization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

def canonicalOrigin (q d : ℕ) (hd : 0 < d) : Grid (I := Fin q) (4*d^8) :=
  fun _ => ⟨0,le_rfl,by
    have hp : 1≤4*d^8 := by
      have := one_le_pow₀ (n := 8) (Nat.succ_le_iff.mpr hd)
      omega
    have hz : (1:ℤ)≤(4*d^8:ℕ) := by exact_mod_cast hp
    omega⟩

lemma zeroGrid_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 0 < d) :
    zeroGrid (marginCode R,marginCode P)=gridNatCode (canonicalOrigin (m*n) d hd) := by
  apply List.ext_getElem
  · simp only [zeroGrid,ProfilePrograms.cellPairs,List.length_map,List.length_range,
      marginCode,List.tail_cons,List.length_ofFn,gridNatCode]
  · intro i hi hj
    simp only [zeroGrid,List.getElem_map,gridNatCode,List.getElem_ofFn,corner,
      canonicalOrigin,Int.toNat_zero]

def canonicalFallback {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j) : Table R P :=
  (tableReindex (finSuccEquiv m) (finSuccEquiv n) R P).symm
    (GreedyFeasibleTable.table (fun i => R (finSuccEquiv m i))
      (fun j => P (finSuccEquiv n j)) (by
        rw [(finSuccEquiv m).sum_comp,(finSuccEquiv n).sum_comp]
        exact htotal))

lemma canonicalFallback_output {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j) :
    tableOutput (canonicalFallback R P htotal)=
      GreedyFeasibleTable.listMatrix (marginCode R) (marginCode P) := by
  rw [marginCode_ofFn,marginCode_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  unfold tableOutput canonicalFallback
  change matrixCode (fun i j =>
    GreedyFeasibleTable.matrix (fun i => R (finSuccEquiv m i))
      (fun j => P (finSuccEquiv n j))
      ((finSuccEquiv m).symm (finSuccEquiv m i))
      ((finSuccEquiv n).symm (finSuccEquiv n j)))=_
  simp only [Equiv.symm_apply_apply,matrixCode]

lemma canonicalInput_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 0 < d) (htotal : (∑ i,R i)=∑ j,P j) (h : ℕ) (bits : List Bool) :
    canonicalInput (((marginCode R,marginCode P),(d,h)),bits)=
      drawInput R P h (canonicalOrigin (m*n) d hd) (canonicalFallback R P htotal) bits := by
  unfold canonicalInput drawInput
  rw [zeroGrid_code R P hd,canonicalFallback_output]

/-- No caller-supplied grid or feasible fallback is needed by the
binary dense program. Every output is the analyzed table-valued draw. -/
theorem canonicalDenseDraw_eq {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (htotal : (∑ i,R i)=∑ j,P j) (h : ℕ)
    (bits : Fin (normalizedDrawBits R P d h) → Bool) :
    canonicalDenseDraw (((marginCode R,marginCode P),(d,h)),List.ofFn bits)=
      tableOutput (normalizedBooleanDraw R P hd hR hP htotal h
        (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal) bits) := by
  unfold canonicalDenseDraw
  rw [canonicalInput_code R P (by omega) htotal]
  exact normalizedDenseCode_eq R P hd hR hP htotal h _ _ bits

/-- The initialized dense call retains the stated error for every
margin ordering and uses only the published analytic inputs. -/
theorem canonicalDenseDraw_variation {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (hdimR : Fintype.card (Option (Fin m))≤d) (hdimP : Fintype.card (Option (Fin n))≤d)
    (hfree : Fintype.card (Fin m×Fin n)≤d) (htotal : (∑ i,R i)=∑ j,P j)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m*n))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (m*n)) (4*d^8))) (h : ℕ) :
    let _ : Nonempty (Table R P) := ⟨canonicalFallback R P htotal⟩
    (variation (mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
      (normalizedBooleanDraw R P hd hR hP htotal h
        (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal)))
      (uniformLaw (α := Table R P)) : ℝ)≤(2:ℝ)^(-(h:ℝ)) :=
  normalizedBooleanDraw_variation R P hd hR hP hdimR hdimP hfree htotal hPL hCheeger h _ _

end
end ContingencyTables.DensePrograms

end OAI
