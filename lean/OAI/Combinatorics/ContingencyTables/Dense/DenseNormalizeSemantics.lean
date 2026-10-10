import OAI.Combinatorics.ContingencyTables.Dense.DenseNormalizeProgram
import OAI.Combinatorics.ContingencyTables.Transport.TableReindex

namespace OAI

/-! # Correctness of computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

lemma marginCode_ofFn {m : ℕ} (R : Option (Fin m) → ℕ) :
    marginCode R=List.ofFn (fun i : Fin (m+1) => R (finSuccEquiv m i)) := by
  rw [List.ofFn_succ]
  simp only [marginCode,finSuccEquiv_zero,finSuccEquiv_succ]

def marginPosition {m : ℕ} (R : Option (Fin m) → ℕ) : Fin (m+1) :=
  maximumPosition (fun i => R (finSuccEquiv m i))

def indexPermutation {m : ℕ} (p : Fin (m+1)) : Option (Fin m) ≃ Option (Fin m) :=
  (finSuccEquiv m).symm.trans ((Equiv.swap 0 p).trans (finSuccEquiv m))

def normalizedMargin {m : ℕ} (R : Option (Fin m) → ℕ) : Option (Fin m) → ℕ :=
  fun i => R (indexPermutation (marginPosition R) i)

lemma finSuccEquiv_symm_none (m : ℕ) : (finSuccEquiv m).symm none=0 := by
  apply (finSuccEquiv m).injective
  simp only [Equiv.apply_symm_apply,finSuccEquiv_zero]

lemma normalizedMargin_max {m : ℕ} (R : Option (Fin m) → ℕ) (i : Fin m) :
    normalizedMargin R (some i)≤normalizedMargin R none := by
  unfold normalizedMargin indexPermutation
  simp only [Equiv.trans_apply,finSuccEquiv_symm_none,Equiv.swap_apply_left]
  exact maximumPosition_spec (fun i => R (finSuccEquiv m i)) _

lemma normalizedMargin_lower {m : ℕ} (R : Option (Fin m) → ℕ) (L : ℕ)
    (hR : ∀ i,L≤R i) : ∀ i,L≤normalizedMargin R i := fun _ => hR _

lemma normalizedMargin_total {m : ℕ} (R : Option (Fin m) → ℕ) :
    ∑ i,normalizedMargin R i=∑ i,R i := (indexPermutation (marginPosition R)).sum_comp R

lemma marginPosition_val {m : ℕ} (R : Option (Fin m) → ℕ) :
    (marginPosition R).val=maximumIndex (marginCode R) := by
  rw [marginCode_ofFn]
  rfl

lemma marginCode_swap {m : ℕ} (R : Option (Fin m) → ℕ) (p : Fin (m+1)) :
    swapZeroList (p.val,marginCode R)=marginCode (fun i => R (indexPermutation p i)) := by
  rw [marginCode_ofFn,swapZeroList_ofFn,marginCode_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [indexPermutation,Equiv.trans_apply,Equiv.symm_apply_apply]

lemma indexPermutation_finSucc {m : ℕ} (p i : Fin (m+1)) :
    indexPermutation p (finSuccEquiv m i)=finSuccEquiv m (Equiv.swap 0 p i) := by
  change finSuccEquiv m (Equiv.swap 0 p ((finSuccEquiv m).symm (finSuccEquiv m i)))=_
  rw [Equiv.symm_apply_apply]

lemma indexPermutation_symm_finSucc {m : ℕ} (p i : Fin (m+1)) :
    (indexPermutation p).symm (finSuccEquiv m i)=finSuccEquiv m (Equiv.swap 0 p i) := by
  change finSuccEquiv m (Equiv.swap 0 p ((finSuccEquiv m).symm (finSuccEquiv m i)))=_
  rw [Equiv.symm_apply_apply]

lemma tableOutput_swap {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (p : Fin (m+1)) (q : Fin (n+1)) (X : Table R P) :
    swapMatrix ((p.val,q.val),tableOutput X)=
      tableOutput (tableReindex (indexPermutation p) (indexPermutation q) R P X) := by
  unfold tableOutput
  rw [swapMatrix_code]
  apply congrArg matrixCode
  funext i j
  change X.val (finSuccEquiv m (Equiv.swap 0 p i)) (finSuccEquiv n (Equiv.swap 0 q j))=
    X.val (indexPermutation p (finSuccEquiv m i)) (indexPermutation q (finSuccEquiv n j))
  rw [indexPermutation_finSucc,indexPermutation_finSucc]

lemma tableOutput_inverse_swap {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (p : Fin (m+1)) (q : Fin (n+1))
    (X : Table (fun i => R (indexPermutation p i)) (fun j => P (indexPermutation q j))) :
    swapMatrix ((p.val,q.val),tableOutput X)=
      tableOutput ((tableReindex (indexPermutation p) (indexPermutation q) R P).symm X) := by
  unfold tableOutput
  rw [swapMatrix_code]
  apply congrArg matrixCode
  funext i j
  change X.val (finSuccEquiv m (Equiv.swap 0 p i)) (finSuccEquiv n (Equiv.swap 0 q j))=
    X.val ((indexPermutation p).symm (finSuccEquiv m i)) ((indexPermutation q).symm (finSuccEquiv n j))
  rw [indexPermutation_symm_finSucc,indexPermutation_symm_finSucc]

lemma drawIndices_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P) (bits : List Bool) :
    drawIndices (drawInput R P h a fallback bits)=((marginPosition R).val,(marginPosition P).val) := by
  simp only [drawIndices,drawInput,marginIndices,marginPosition_val]

lemma permuteDrawData_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P) (bits : List Bool) :
    permuteDrawData (((marginPosition R).val,(marginPosition P).val),
      drawInput R P h a fallback bits)=
      drawInput (normalizedMargin R) (normalizedMargin P) h a
        (tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P fallback) bits := by
  unfold permuteDrawData swapFlatData swapMargins drawInput
  rw [marginCode_swap,marginCode_swap,tableOutput_swap]
  rfl

def normalizedDrawBits {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d h : ℕ) : ℕ := denseDrawBits (normalizedMargin R) (normalizedMargin P) d finProdFinEquiv h

def normalizedBooleanDraw {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : Fin (normalizedDrawBits R P d h) → Bool) : Table R P :=
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  E.symm (denseBooleanDraw (normalizedMargin R) (normalizedMargin P) d hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP) finProdFinEquiv
    (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h a (E fallback) bits)

/-- The computed maximum and both physical permutations agree with the
finite table-valued experiment on every Boolean input. -/
theorem normalizedDenseCode_eq {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : Fin (normalizedDrawBits R P d h) → Bool) :
    normalizedDenseCode (drawInput R P h a fallback (List.ofFn bits))=
      tableOutput (normalizedBooleanDraw R P hd hR hP htotal h a fallback bits) := by
  unfold normalizedDenseCode normalizedDraw preparedDraw
  rw [drawIndices_code,permuteDrawData_code]
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  let fb : Table (normalizedMargin R) (normalizedMargin P) := E fallback
  have ht : (∑ i,normalizedMargin R i)=∑ j,normalizedMargin P j := by
    rw [normalizedMargin_total,normalizedMargin_total]
    exact htotal
  have hs := denseDrawCode_eq (normalizedMargin R) (normalizedMargin P) hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP) ht h a fb bits
  refine (congrArg (fun X => swapMatrix (((marginPosition R).val,(marginPosition P).val),X)) hs).trans ?_
  exact tableOutput_inverse_swap R P _ _ _

/-- The computed choice of maximal rows and columns retains the dense
sampler's uniform-error guarantee for arbitrary original row order. -/
theorem normalizedBooleanDraw_variation {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (hdimR : Fintype.card (Option (Fin m))≤d) (hdimP : Fintype.card (Option (Fin n))≤d)
    (hfree : Fintype.card (Fin m×Fin n)≤d) (htotal : ∑ i,R i=∑ j,P j)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m*n))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (m*n)) (4*d^8)))
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P) :
    let _ : Nonempty (Table R P) := ⟨fallback⟩
    (variation (mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
      (normalizedBooleanDraw R P hd hR hP htotal h a fallback))
      (uniformLaw (α := Table R P)) : ℝ)≤(2:ℝ)^(-(h:ℝ)) := by
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  let : Nonempty (Table R P) := ⟨fallback⟩
  let : Nonempty (Table (normalizedMargin R) (normalizedMargin P)) := ⟨E fallback⟩
  have ht : (∑ i,normalizedMargin R i)=∑ j,normalizedMargin P j := by
    rw [normalizedMargin_total,normalizedMargin_total]
    exact htotal
  have he := denseBooleanDraw_variation (normalizedMargin R) (normalizedMargin P) d hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
    (normalizedMargin_max R) (normalizedMargin_max P) hdimR hdimP hfree ht
    finProdFinEquiv hPL hCheeger h a (E fallback)
  dsimp only at ⊢
  change (variation (mapLaw (uniformLaw (α := Fin (denseDrawBits (normalizedMargin R)
    (normalizedMargin P) d finProdFinEquiv h) → Bool))
    (fun bits => E.symm (denseBooleanDraw (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E fallback) bits))) (uniformLaw (α := Table R P)) : ℝ)≤_
  rw [mapLaw_equiv_output]
  change (variation (equivLaw E.symm (denseBooleanDrawLaw (normalizedMargin R) (normalizedMargin P)
    d hd (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
    finProdFinEquiv ht h a (E fallback))) (uniformLaw (α := Table R P)) : ℝ)≤_
  rw [←uniform_equiv E.symm,variation_equiv]
  exact he

theorem normalizedDrawBits_polynomial {m n : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (d C b h : ℕ)
    (hq : m*n≤d) (hR : ∀ i,R i≤C) (hb : Nat.clog 2 (C+2)≤b) :
    normalizedDrawBits R P d h≤25*(d+b+h+1)^62 := by
  apply denseDrawBits_polynomial (normalizedMargin R) (normalizedMargin P) d C b h
    finProdFinEquiv hq
  · intro p
    exact (Nat.div_le_self _ _).trans ((min_le_left _ _).trans (hR _))
  · exact hb

end
end ContingencyTables.DensePrograms

end OAI
