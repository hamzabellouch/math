import OAI.Algebra.Determinantal.GateCoefficients

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
abbrev SelectorOuter (I : Type*) (h : ℕ) := I ⊕ (Fin 2 × (I ⊕ Fin h))
abbrev SelectorLabels (I : Type*) (h : ℕ) := (I × I) ⊕
  (Fin 2 × ((I × Fin h) ⊕ (Fin h × I)))
abbrev SelectorGateVars (I : Type*) (h : ℕ) := Fin 2 × ((I ⊕ Fin h) ⊕ (I ⊕ Fin h))

noncomputable def selectorSrc (h : ℕ) : SelectorLabels I h → SelectorOuter I h
  | .inl (i,_) => .inl i
  | .inr (c,.inl (i,_)) => .inr (c,.inl i)
  | .inr (c,.inr (j,_)) => .inr (c,.inr j)
noncomputable def selectorDst (h : ℕ) : SelectorLabels I h → SelectorOuter I h
  | .inl (_,i) => .inl i
  | .inr (c,.inl (_,j)) => .inr (c,.inr j)
  | .inr (c,.inr (_,i)) => .inr (c,.inl i)
noncomputable def selectorBaseWeight (M : Matrix I I R) (h : ℕ) : SelectorLabels I h → R
  | .inl (i,j) => M i j
  | .inr _ => 1
noncomputable def selectorWeight (θ : I → R) (g : Fin 2 × I) : R :=
  if g.1=0 then 1 else θ g.2
noncomputable def selectorMain (h : ℕ) (g : Fin 2 × I) : SelectorOuter I h := .inl g.2
noncomputable def selectorGate (h : ℕ) (g : Fin 2 × I) : SelectorOuter I h := .inr (g.1,.inl g.2)

noncomputable def selectorMatrix (M : Matrix I I R) (θ : I → R) (h : ℕ) :=
  expandedMatrix (selectorSrc h) (selectorDst h) (selectorBaseWeight M h)
    (selectorWeight θ) (selectorMain h) (selectorGate h) (selectorMain h) (selectorGate h)

noncomputable def selectorBoundary (M : Matrix I I R) (θ : I → R) (h : ℕ) :
    MvPolynomial (SelectorOuter I h ⊕ SelectorOuter I h) R :=
  baseEdges (selectorSrc h) (selectorDst h) (selectorBaseWeight M h) *
  ∏ g : Fin 2 × I, (1 + C (selectorWeight θ g) *
    X (.inl (selectorMain h g))*X (.inl (selectorGate h g))*
    X (.inr (selectorMain h g))*X (.inr (selectorGate h g)))

def selectorSplitEquiv (h : ℕ) : (SelectorOuter I h ⊕ SelectorOuter I h) ≃
    (SelectorGateVars I h ⊕ (I ⊕ I)) where
  toFun
  | .inl (.inl i) => .inr (.inl i)
  | .inr (.inl i) => .inr (.inr i)
  | .inl (.inr (c,v)) => .inl (c,.inl v)
  | .inr (.inr (c,v)) => .inl (c,.inr v)
  invFun
  | .inr (.inl i) => .inl (.inl i)
  | .inr (.inr i) => .inr (.inl i)
  | .inl (c,.inl v) => .inl (.inr (c,v))
  | .inl (c,.inr v) => .inr (.inr (c,v))
  left_inv x := by rcases x with (i|⟨c,v⟩)|(i|⟨c,v⟩) <;> rfl
  right_inv x := by rcases x with ⟨c,v|v⟩|(i|i) <;> rfl

noncomputable def selectorSplit (h : ℕ) : MvPolynomial (SelectorOuter I h ⊕ SelectorOuter I h) R →+*
    MvPolynomial (SelectorGateVars I h) (MvPolynomial (I ⊕ I) R) :=
  (sumRingEquiv R _ _).toRingHom.comp ((rename (selectorSplitEquiv h)).toRingHom)
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_C (h : ℕ) (r : R) : selectorSplit (I := I) h (C r) = C (C r) := by
  simp [selectorSplit]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_main_left (h : ℕ) (i : I) :
    selectorSplit h (X (.inl (.inl i)) : MvPolynomial _ R) = C (X (.inl i)) := by
  simp [selectorSplit, selectorSplitEquiv]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_main_right (h : ℕ) (i : I) :
    selectorSplit h (X (.inr (.inl i)) : MvPolynomial _ R) = C (X (.inr i)) := by
  simp [selectorSplit, selectorSplitEquiv]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_gate_left (h : ℕ) (c : Fin 2) (v : I ⊕ Fin h) :
    selectorSplit h (X (.inl (.inr (c,v))) : MvPolynomial _ R) = X (c,.inl v) := by
  simp [selectorSplit, selectorSplitEquiv]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_gate_right (h : ℕ) (c : Fin 2) (v : I ⊕ Fin h) :
    selectorSplit h (X (.inr (.inr (c,v))) : MvPolynomial _ R) = X (c,.inr v) := by
  simp [selectorSplit, selectorSplitEquiv]

omit [DecidableEq I] in
 theorem selectorSplit_coeff (h : ℕ) (p : MvPolynomial (SelectorOuter I h ⊕ SelectorOuter I h) R) :
    p.coeff (allOnes _) = ((selectorSplit h p).coeff (allOnes (SelectorGateVars I h))).coeff (allOnes (I ⊕ I)) := by
  have hr := coeff_rename_mapDomain (selectorSplitEquiv h) (selectorSplitEquiv h).injective p (allOnes _)
  rw [allOnes_map_equiv] at hr
  rw [← hr]
  have ho : allOnes (SelectorGateVars I h ⊕ (I ⊕ I)) =
    (allOnes (SelectorGateVars I h)).sumElim (allOnes (I ⊕ I)) := by ext v; cases v <;> rfl
  rw [ho, coeff_nested]
  rfl

noncomputable def selectorBoundaryWeight (θ : I → R) (c : Fin 2) (i : I) : MvPolynomial (I ⊕ I) R :=
  C (selectorWeight θ (c,i))*X (.inl i)*X (.inr i)

omit [DecidableEq I] in
 theorem selectorSplit_base (M : Matrix I I R) (h : ℕ) :
    selectorSplit h (baseEdges (selectorSrc h) (selectorDst h) (selectorBaseWeight M h)) =
    C (edgeProduct M) * ∏ c : Fin 2,
      ((∏ i : I, ∏ j : Fin h, (1 + X (c,.inl (.inl i))*X (c,.inr (.inr j)))) *
       (∏ j : Fin h, ∏ i : I, (1 + X (c,.inl (.inr j))*X (c,.inr (.inl i))))) := by
  classical
  have hm (i j : SelectorOuter I h) (r : R) : monomial (edgeExponent (i,j)) r =
      C r * X (.inl i) * X (.inr j) := by
    rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
    simp only [edgeExponent, mul_one]
  simp only [baseEdges, hm, map_prod, map_add, map_one, map_mul, Fintype.prod_sum_type,
    Fintype.prod_prod_type, selectorSrc, selectorDst, selectorBaseWeight,
    selectorSplit_C, selectorSplit_main_left, selectorSplit_main_right,
    selectorSplit_gate_left, selectorSplit_gate_right, one_mul]
  apply congrArg₂ (·*·)
  · simp only [edgeProduct, Fintype.prod_prod_type, map_prod, map_add, map_one]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    have hx : monomial (edgeExponent (i,j)) (M i j) = C (M i j)*X (.inl i)*X (.inr j) := by
      rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
      simp only [edgeExponent, mul_one]
    rw [hx, map_mul, map_mul]
  · simp only

omit [DecidableEq I] in
 theorem selectorSplit_choices (θ : I → R) (h : ℕ) :
    selectorSplit h (∏ g : Fin 2 × I, (1 + C (selectorWeight θ g) *
      X (.inl (selectorMain h g))*X (.inl (selectorGate h g))*
      X (.inr (selectorMain h g))*X (.inr (selectorGate h g)))) =
    ∏ c : Fin 2, ∏ i : I, (1 + C (selectorBoundaryWeight θ c i)*
      X (c,.inl (.inl i))*X (c,.inr (.inl i))) := by
  simp only [map_prod, map_add, map_one, map_mul, Fintype.prod_prod_type,
    selectorMain, selectorGate, selectorSplit_C, selectorSplit_main_left,
    selectorSplit_main_right, selectorSplit_gate_left, selectorSplit_gate_right,
    selectorBoundaryWeight]
  apply Finset.prod_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro i _
  ring

omit [DecidableEq I] in
 theorem selectorSplit_boundary (M : Matrix I I R) (θ : I → R) (h : ℕ) :
    selectorSplit h (selectorBoundary M θ h) =
    C (edgeProduct M) * ∏ c : Fin 2, rename (fun v => (c,v))
      (Gates.fullGateEdges (selectorBoundaryWeight θ c) h) := by
  rw [selectorBoundary, map_mul, selectorSplit_base, selectorSplit_choices, mul_assoc,
    ← Finset.prod_mul_distrib]
  apply congrArg (C (edgeProduct M)*·)
  apply Finset.prod_congr rfl
  intro c _
  simp only [Gates.fullGateEdges, map_mul, map_prod, map_add, map_one, rename_X, rename_C]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
 theorem allOnes_block {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] :
    allOnes (A × B) = blockExponent (fun _ : A => allOnes B) := by
  ext ⟨a,b⟩
  simp

 theorem two_gates_count (a : Fin 2 → I → R) (q : ℕ) (hq : q ≤ Fintype.card I) :
    (∏ c : Fin 2, rename (fun v => (c,v))
      (Gates.fullGateEdges (a c) (Fintype.card I-q))).coeff (allOnes _) =
    (((Fintype.card I-q).factorial : R)^4) *
      (elementaryBoundary (a 0) q * elementaryBoundary (a 1) q) := by
  rw [allOnes_block, coeff_independent_blocks]
  have hc (c : Fin 2) : (Gates.fullGateEdges (a c) (Fintype.card I-q)).coeff (allOnes _) =
    (((Fintype.card I-q).factorial : R)^2) * elementaryBoundary (a c) q :=
      Gates.full_gate_count (a c) q hq
  simp_rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one]
  ring

 theorem selector_boundary_coeff (M : Matrix I I R) (θ : I → R) (q : ℕ)
    (hq : q ≤ Fintype.card I) :
    (selectorBoundary M θ (Fintype.card I-q)).coeff (allOnes _) =
      (((Fintype.card I-q).factorial : R)^4) * diagonalCoefficient M θ q := by
  rw [selectorSplit_coeff, selectorSplit_boundary, coeff_C_mul, two_gates_count _ q hq]
  have h0 : selectorBoundaryWeight θ 0 = fun i => X (.inl i)*X (.inr i) := by
    funext i; simp [selectorBoundaryWeight, selectorWeight]
  have h1 : selectorBoundaryWeight θ 1 = fun i => C (θ i)*X (.inl i)*X (.inr i) := by
    funext i; simp [selectorBoundaryWeight, selectorWeight]
  rw [h0,h1]
  have hc : (((Fintype.card I-q).factorial : MvPolynomial (I ⊕ I) R)^4) =
    C (((Fintype.card I-q).factorial : R)^4) := by simp only [map_pow, map_natCast]
  rw [hc]
  have hp (p a b : MvPolynomial (I ⊕ I) R) (c : R) : p * (C c * (a*b)) = C c * (p*a*b) := by ring
  rw [hp, coeff_C_mul, ← diagonalCoefficient_boundary]

 theorem selector_matrix_permanent (M : Matrix I I R) (θ : I → R) (q : ℕ)
    (hq : q ≤ Fintype.card I) :
    (selectorMatrix M θ (Fintype.card I-q)).permanent =
    ((-2:R)^(2 * Fintype.card I) * ((Fintype.card I-q).factorial : R)^4) *
      diagonalCoefficient M θ q := by
  rw [selectorMatrix, expanded_permanent]
  change (-2:R)^Fintype.card (Fin 2 × I) *
    (selectorBoundary M θ (Fintype.card I-q)).coeff (allOnes _) = _
  rw [selector_boundary_coeff M θ q hq]
  simp only [Fintype.card_prod, Fintype.card_fin, mul_assoc]

omit [DecidableEq I] in
 theorem selector_matrix_card (q : ℕ) (hq : q ≤ Fintype.card I) :
    Fintype.card (ExpandedVertex (SelectorOuter I (Fintype.card I-q)) (Fin 2 × I)) =
      11 * Fintype.card I - 2*q := by
  simp only [ExpandedVertex, SelectorOuter, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [CommSemiring R]
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
 theorem rename_inner (p : MvPolynomial A R) :
    sumRingEquiv R A B (rename Sum.inl p) = map C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
 theorem rename_outer (p : MvPolynomial B R) :
    sumRingEquiv R A B (rename Sum.inr p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

 theorem permanent_block_diagonal (P : Matrix A A R) (Q : Matrix B B R) :
    (Matrix.fromBlocks P 0 0 Q).permanent = P.permanent * Q.permanent := by
  rw [← row_product_permanent]
  have hp : (∏ i, ∑ j, C (Matrix.fromBlocks P 0 0 Q i j) * X j) =
      rename Sum.inl (∏ i, ∑ j, C (P i j)*X j) *
      rename Sum.inr (∏ i, ∑ j, C (Q i j)*X j) := by
    simp [Fintype.prod_sum_type, Fintype.sum_sum_type, Matrix.fromBlocks]
  rw [hp]
  have hones : allOnes (A ⊕ B) = (allOnes A).sumElim (allOnes B) := by
    ext i; cases i <;> rfl
  rw [hones, coeff_nested, map_mul, rename_inner, rename_outer, mul_comm, coeff_C_mul,
    coeff_map, mul_comm, coeff_C_mul, row_product_permanent, row_product_permanent]

 theorem permanent_reindex_equiv (P : Matrix A A R) (e : B ≃ A) :
    (P.submatrix e e).permanent = P.permanent := by
  classical
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ ?_
  intro σ
  simpa only [Matrix.submatrix_apply, Equiv.permCongr_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply] using
    (e.prod_comp (fun i => P ((Equiv.permCongr e σ) i) i))
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
abbrev SelectorVertex (I : Type*) (h : ℕ) := ExpandedVertex (SelectorOuter I h) (Fin 2 × I)
noncomputable def selectorLinearEntries (M : Matrix I I R) (h : ℕ) :
    Matrix (SelectorVertex I h) (SelectorVertex I h) R
  | .inl (.inl i), .inl (.inl j) => M i j
  | _, _ => 0

 theorem selectorMatrix_affine (M : Matrix I I R) (θ : I → R) (h : ℕ)
    (r c : SelectorVertex I h) :
    selectorMatrix M θ h r c = selectorMatrix 0 θ h r c + selectorLinearEntries M h r c := by
  classical
  simp only [selectorMatrix, expandedMatrix, graphMatrix, Fintype.sum_sum_type,
    Fintype.sum_prod_type, expandedWeight, selectorBaseWeight, expandedSrc, expandedDst,
    selectorSrc, selectorDst]
  rcases r with (a|a)|a <;> rcases c with (b|b)|b <;>
    simp [selectorLinearEntries, ite_and]
end PermanentBorder.Selector
namespace PermanentBorder.Selector
open MvPolynomial
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

 theorem gadgetH_map (f : R →+* S) (r c : Fin 3) :
    f (gadgetH (R := R) r c) = gadgetH r c := by
  fin_cases r <;> fin_cases c <;> simp [gadgetH]

 theorem selectorMatrix_map (f : R →+* S) (M : Matrix I I R) (θ : I → R) (h : ℕ)
    (r c : SelectorVertex I h) :
    selectorMatrix (M.map f) (fun i => f (θ i)) h r c = f (selectorMatrix M θ h r c) := by
  classical
  simp only [selectorMatrix, expandedMatrix, graphMatrix, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [apply_ite f, map_zero]
  split_ifs
  · rcases e with (⟨i,j⟩|⟨c,⟨i,j⟩|⟨j,i⟩⟩)|⟨g,b|r|⟨r,c⟩⟩ <;>
      simp only [expandedWeight, selectorBaseWeight, Matrix.map_apply, selectorWeight] <;>
      (try split_ifs) <;> simp_all [gadgetH_map, map_ofNat]
  · rfl

noncomputable def selectorCoefficientMatrix (h : ℕ) (ij : I × I) :
    Matrix (SelectorVertex I h) (SelectorVertex I h) R :=
  fun r c => if r = .inl (.inl ij.1) ∧ c = .inl (.inl ij.2) then 1 else 0

 theorem selectorLinearEntries_sum (M : Matrix I I R) (h : ℕ)
    (r c : SelectorVertex I h) :
    selectorLinearEntries M h r c = ∑ ij, selectorCoefficientMatrix h ij r c * M ij.1 ij.2 := by
  classical
  rcases r with (a|a)|a <;> rcases c with (b|b)|b <;>
    simp [selectorLinearEntries, selectorCoefficientMatrix, Fintype.sum_prod_type, ite_and]

 theorem selector_polynomial_affine (θ : I → R) (h : ℕ) (r c : SelectorVertex I h) :
    selectorMatrix (Matrix.of fun i j => X (i,j)) (fun i => C (θ i)) h r c =
      C (selectorMatrix 0 θ h r c) +
        ∑ ij : I × I, C (selectorCoefficientMatrix h ij r c) * X ij := by
  rw [selectorMatrix_affine]
  have hm : (0 : Matrix I I R).map (C : R →+* MvPolynomial (I × I) R) = 0 := by ext; simp
  rw [← hm, selectorMatrix_map]
  congr 1
  rw [selectorLinearEntries_sum]
  apply Finset.sum_congr rfl
  intro ij _
  unfold selectorCoefficientMatrix
  split_ifs <;> simp_all
end PermanentBorder.Selector

namespace PermanentBorder
open MvPolynomial
variable {σ V T : Type*} [Fintype σ] [Fintype V] [DecidableEq V]

 theorem affineSubstitution_permanent (m : ℕ) (b : Variables m → ℂ)
    (B : Variables m → σ → ℂ) :
    affineSubstitution b B (permanentPolynomial m) =
      (Matrix.of fun i j => C (b (i,j)) + ∑ w, C (B (i,j) w)*X w).permanent := by
  classical
  unfold permanentPolynomial affineSubstitution
  simp only [map_sum, map_prod, aeval_X]
  exact Matrix.permanent_transpose
    (Matrix.of fun i j => C (b (i,j)) + ∑ w, C (B (i,j) w)*X w)

omit [Fintype V] [DecidableEq V] in
 theorem polynomial_fromBlocks_affine [Fintype T] [DecidableEq T]
    (P : Matrix V V (Poly σ)) (A₀ : Matrix V V ℂ) (A : σ → Matrix V V ℂ)
    (hP : ∀ i j, P i j = C (A₀ i j) + ∑ w, C (A w i j)*X w)
    (i j : V ⊕ T) :
    Matrix.fromBlocks P 0 0 1 i j =
      C (Matrix.fromBlocks A₀ 0 0 (1 : Matrix T T ℂ) i j) +
      ∑ w, C (Matrix.fromBlocks (A w) 0 0 (0 : Matrix T T ℂ) i j)*X w := by
  classical
  rcases i with i|i <;> rcases j with j|j
  · exact hP i j
  · simp [Matrix.fromBlocks]
  · simp [Matrix.fromBlocks]
  · simp [Matrix.fromBlocks, Matrix.one_apply]

 theorem exists_affine_permanent_padding (m : ℕ) (hm : Fintype.card V ≤ m)
    (P : Matrix V V (Poly σ)) (A₀ : Matrix V V ℂ) (A : σ → Matrix V V ℂ)
    (hP : ∀ i j, P i j = C (A₀ i j) + ∑ w, C (A w i j)*X w) :
    ∃ (b : Variables m → ℂ) (B : Variables m → σ → ℂ),
      affineSubstitution b B (permanentPolynomial m) = P.permanent := by
  classical
  let T := V ⊕ Fin (m-Fintype.card V)
  let e : Fin m ≃ T := Fintype.equivOfCardEq (by
    simp only [T, Fintype.card_fin, Fintype.card_sum]
    omega)
  let C₀ : Matrix T T ℂ := Matrix.fromBlocks A₀ 0 0 1
  let A' : σ → Matrix T T ℂ := fun w => Matrix.fromBlocks (A w) 0 0 0
  let P' : Matrix T T (Poly σ) := Matrix.fromBlocks P 0 0 1
  let b : Variables m → ℂ := fun ij => C₀ (e ij.1) (e ij.2)
  let B : Variables m → σ → ℂ := fun ij w => A' w (e ij.1) (e ij.2)
  refine ⟨b,B,?_⟩
  rw [affineSubstitution_permanent]
  have he : (Matrix.of fun i j => C (b (i,j)) + ∑ w, C (B (i,j) w)*X w) =
      P'.submatrix e e := by
    funext i j
    exact (polynomial_fromBlocks_affine P A₀ A hP (e i) (e j)).symm
  rw [he, Selector.permanent_reindex_equiv, Selector.permanent_block_diagonal,
    Matrix.permanent_one, mul_one]
end PermanentBorder

namespace PermanentBorder
open MvPolynomial

noncomputable def coefficientPolynomial (k q : ℕ) (θ : Fin k → ℂ) : Poly (Variables k) :=
  Selector.diagonalCoefficient (Matrix.of fun i j => X (i,j)) (fun i => C (θ i)) q

noncomputable def selectorScalar (k q : ℕ) : ℂ :=
  (-2)^(2*k) * ((k-q).factorial : ℂ)^4

 theorem selectorScalar_ne_zero (k q : ℕ) : selectorScalar k q ≠ 0 := by
  unfold selectorScalar
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

 theorem exists_selector_affine_projection (k q m : ℕ) (hq : q ≤ k)
    (hm : 11*k-2*q ≤ m) (θ : Fin k → ℂ) :
    ∃ (b : Variables m → ℂ) (B : Variables m → Variables k → ℂ),
      affineSubstitution b B (permanentPolynomial m) =
        selectorScalar k q • coefficientPolynomial k q θ := by
  classical
  let V := Selector.SelectorVertex (Fin k) (Fintype.card (Fin k)-q)
  let P : Matrix V V (Poly (Variables k)) :=
    Selector.selectorMatrix (Matrix.of fun i j => X (i,j)) (fun i => C (θ i)) (Fintype.card (Fin k)-q)
  have hcard : Fintype.card V = 11*k-2*q := by
    simpa only [V, Selector.SelectorVertex, Fintype.card_fin] using
      (Selector.selector_matrix_card (I := Fin k) q (by simpa using hq))
  obtain ⟨b,B,h⟩ := exists_affine_permanent_padding m (by omega : Fintype.card V ≤ m) P
    (Selector.selectorMatrix 0 θ (Fintype.card (Fin k)-q)) (Selector.selectorCoefficientMatrix (Fintype.card (Fin k)-q))
    (Selector.selector_polynomial_affine θ (Fintype.card (Fin k)-q))
  refine ⟨b,B,h.trans ?_⟩
  have he := Selector.selector_matrix_permanent
    (Matrix.of fun i j : Fin k => (X (i,j) : Poly (Variables k)))
    (fun i => C (θ i)) q (by simpa using hq)
  simp only [Fintype.card_fin] at he
  change P.permanent = _ at he
  rw [he, smul_eq_C_mul]
  simp only [selectorScalar, coefficientPolynomial, map_mul, map_pow, map_neg,
    map_ofNat, map_natCast]

 theorem HasBorderDeterminant.coefficientPolynomial {k q m n : ℕ}
    (h : HasBorderDeterminant n (permanentPolynomial m)) (hq : q ≤ k)
    (hm : 11*k-2*q ≤ m) (θ : Fin k → ℂ) :
    HasBorderDeterminant n (coefficientPolynomial k q θ) := by
  obtain ⟨b,B,hproj⟩ := exists_selector_affine_projection k q m hq hm θ
  have hg := (h.affineSubstitution b B).smul (selectorScalar k q)⁻¹
  rw [hproj, smul_smul, inv_mul_cancel₀ (selectorScalar_ne_zero k q), one_smul] at hg
  exact hg
end PermanentBorder

end OAI
