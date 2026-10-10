import Mathlib
import OAI.Combinatorics.StripMass.NodalEmpty

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma polynomial_eval₂_fin {K L:Type*} [CommRing K] [CommRing L]
    (f:K →+* L) (P:Polynomial K) (x:L) (n:ℕ) (h:∀k,n≤k → P.coeff k=0) :
    P.eval₂ f x=∑j:Fin n,f (P.coeff j.val)*x^j.val := by
  rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def,Fin.sum_univ_eq_sum_range (fun k =>f (P.coeff k)*x^k) n]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range]
    by_contra hnot
    exact Polynomial.mem_support_iff.mp hk (h k (Nat.le_of_not_gt hnot))
  · intro k hk hnot
    rw [(not_ne_iff.mp (fun hne =>hnot (Polynomial.mem_support_iff.mpr hne))),map_zero,zero_mul]

 
def polynomialVacuumVector : (n:ℕ) → Pairing n → Laurent n
  | 0 =>fun _ =>1
  | n+1 =>(vacuumData n).W

lemma polynomialVacuumVector_eval (n:ℕ) (p:Pairing n) :
    evalLaurent (polynomialVacuumVector n p)=rationalVacuum n p := by
  cases n with
  | zero =>rw [rationalVacuum_zero]; exact map_one _
  | succ n =>exact (vacuumData n).eval_P p

lemma vacuumData_leading (n:ℕ) (p:Pairing n) :
    ((vacuumData n).P p.padTop).coeff n=polynomialVacuumVector n p := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  rw [←Polynomial.coeff_map,(vacuumData n).map_P,rationalNodalPolynomial_leading]
  exact (polynomialVacuumVector_eval n p).symm

 

theorem vacuum_degree : PolynomialVacuum := by
  refine ⟨polynomialVacuumVector,rfl,?_,?_,?_,?_⟩
  · exact polynomialVacuumVector_eval
  · intro n p e he i
    cases n with
    | zero =>exact Fin.elim0 i
    | succ n =>
      have h:LaurentBox ((vacuumData n).W p) (fun _ =>2*n):=(vacuumData n).box p
      exact abs_le.mpr (h e (Finsupp.mem_support_iff.mp he) i)
  · intro n p
    refine ⟨fun j =>((vacuumData n).P p.padTop).coeff j.val,?_⟩
    change lastLaurent p.padTop ((vacuumData n).P p.padTop)=_
    simp only [lastLaurent,Pairing.padTop_not_occupied_last,ite_false,one_mul]
    rw [polynomial_eval₂_fin (liftLaurentHom n) _ _ (n+1) (fun k hk =>
      (vacuumData n).degree p.padTop k (by simp only [Pairing.padTop_not_occupied_last,ite_false]; omega))]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,liftLaurentHom_apply,vacuumData_leading]
    exact add_comm _ _
  · intro n p hp
    refine ⟨fun j =>((vacuumData n).P p).coeff j.val,?_⟩
    change lastLaurent p ((vacuumData n).P p)=_
    rw [lastLaurent,ite_eq_left hp]
    rw [polynomial_eval₂_fin (liftLaurentHom n) _ _ n (fun k hk =>
      (vacuumData n).degree p k (by simpa only [hp,ite_true] using hk))]
    rfl

end

 

 
theorem vacuum_degree_remaining : PolynomialVacuum := vacuum_degree

 
theorem vacuum_interpolation_stationary_remaining (n : ℕ) :
    rationalInterpolationResidual n = 0 := by
  funext p
  exact vacuum_interpolation_stationary n p


 

noncomputable section
open scoped BigOperators Classical

 

abbrev SourcePairing (n : ℕ) := {p : Pairing (n+1) // p.Occupied (Fin.last n)}

@[simp] lemma SourcePairing.occupied {n : ℕ} (p : SourcePairing n) :
    p.val.Occupied (Fin.last n) := p.property

lemma SourcePairing.ne_empty {n : ℕ} (p : SourcePairing n) : p.val ≠ empty (n+1) := by
  intro h
  exact empty_not_occupied (Fin.last n) (h ▸ p.property)

def sourceTopEquiv (n : ℕ) : SourcePairing n ≃ Pairing.TopOccupiedNonempty n where
  toFun p := ⟨⟨p.val, p.ne_empty⟩, not_not.mpr p.property⟩
  invFun p := ⟨p.val.val, not_not.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sourceTopSplit (n : ℕ) : NonemptyPairing n ⊕ SourcePairing n ≃ NonemptyPairing (n+1) :=
  (Equiv.sumCongr (Equiv.refl _) (sourceTopEquiv n)).trans (Pairing.nonemptyTopSplit n)

@[simp] lemma sourceTopSplit_inl {n : ℕ} (p : NonemptyPairing n) :
    sourceTopSplit n (Sum.inl p) = Pairing.nonemptyPadTop p := rfl

@[simp] lemma sourceTopSplit_inr_val {n : ℕ} (p : SourcePairing n) :
    (sourceTopSplit n (Sum.inr p)).val = p.val := rfl

 

def horizontalWeights {K : Type*} [Zero K] [One K] : Weights K := ⟨0,1,0,0,0⟩

def sourceTransfer {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Tile → K) :
    Matrix (SourcePairing n) (SourcePairing n) K :=
  fun q p => lastCoefficient w q.val p.val

def northSource {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Tile → K) :
    Matrix (SourcePairing n) (Pairing n) K :=
  fun q p => lastCoefficient w q.val p.padTop

lemma horizontal_column_blocks {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) :
    (restrictedColumn (Fin.snoc w horizontalWeights)).submatrix (sourceTopSplit n) (sourceTopSplit n) =
      Matrix.fromBlocks (restrictedColumn w) 0 0 (sourceTransfer (fun i => (w i).tile)) := by
  ext q p
  have hw : (fun i => ((Fin.snoc w horizontalWeights : Fin (n+1) → Weights K) i).tile) =
      Fin.snoc (fun i => (w i).tile) (horizontalWeights : Weights K).tile := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  change rawColumn _ _ _ = _
  rw [hw, rawColumn_last_factor]
  cases q with
  | inl q =>
    cases p with
    | inl p => simp [lastCoefficient_padTop, lastTile, Weights.tile,
        restrictedColumn, sourceTopSplit_inl, Pairing.nonemptyPadTop]; rfl
    | inr p => simp [Matrix.fromBlocks, lastTile, p.property, horizontalWeights, Weights.tile,
        Pairing.nonemptyPadTop]
  | inr q =>
    cases p with
    | inl p => simp [Matrix.fromBlocks, lastTile, q.property, horizontalWeights, Weights.tile,
        Pairing.nonemptyPadTop]
    | inr p => simp [Matrix.fromBlocks, lastTile, q.property, p.property, horizontalWeights,
        Weights.tile, sourceTransfer]

lemma det_horizontal_column {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Weights K) :
    (1 - restrictedColumn (Fin.snoc w horizontalWeights)).det =
      (1 - restrictedColumn w).det * (1 - sourceTransfer (fun i => (w i).tile)).det := by
  rw [← Matrix.det_submatrix_equiv_self (sourceTopSplit n)]
  simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv, horizontal_column_blocks]
  have h : 1 - Matrix.fromBlocks (restrictedColumn w) 0 0 (sourceTransfer (fun i => (w i).tile)) =
      Matrix.fromBlocks (1 - restrictedColumn w) 0 0
        (1 - sourceTransfer (fun i => (w i).tile)) := by
    ext q p
    cases q <;> cases p <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  rw [h, Matrix.det_fromBlocks_zero₂₁]

lemma sourceTransfer_regular_of_horizontal {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → Weights K) (h : VacuumRegular (Fin.snoc w horizontalWeights)) :
    (1 - sourceTransfer (fun i => (w i).tile)).det ≠ 0 := by
  unfold VacuumRegular at h
  rw [det_horizontal_column] at h
  exact (mul_ne_zero_iff.mp h).2

lemma horizontal_spectral_regular (n : ℕ) :
    VacuumRegular (Fin.snoc (spectralWeights n) horizontalWeights) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n)) (IsFractionRing.injective _ _)
    (flatEval n).toRingHom (Fin.snoc rowDenominator 1)
    (Fin.snoc rowNumerator (horizontalWeights : Weights (SpectralRing n)).tile)
    (Fin.snoc (spectralWeights n) horizontalWeights)
    (Fin.snoc (fun _ => deletionWeights) horizontalWeights)
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · simpa using flatEval_rowDenominator_ne_zero i
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro t; cases t <;> simp [horizontalWeights, Weights.tile]
    · intro t; simpa using rowNumerator_map i t
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro t; cases t <;> simp [horizontalWeights, Weights.tile]
    · intro t; simpa using rowNumerator_flatEval i t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro i j hi hj
      have hh : ∀ k : Fin (n+1),
          ¬((Fin.snoc (fun _ : Fin n => (deletionWeights : Weights ℂ)) horizontalWeights : Fin (n+1) → Weights ℂ) k).IsFlat →
          k = Fin.last n := by
        intro k
        refine Fin.lastCases ?_ (fun k => ?_) k
        · intro _; rfl
        · intro hk; exact (hk (Or.inr (by simp))).elim
      exact (hh i hi).trans (hh j hj).symm

 

lemma spectral_source_regular (n : ℕ) :
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile)).det ≠ 0 :=
  sourceTransfer_regular_of_horizontal _ (horizontal_spectral_regular n)

lemma rationalResidualCoefficient_zero (n : ℕ) (p : Pairing (n+1)) :
    rationalResidualCoefficient n p = 0 := by
  have h := rationalInterpolationResidual_factor p
  rw [vacuum_interpolation_stationary] at h
  have hden : (∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2 ≠ 0 :=
    div_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => rowDenominator_map_ne_zero i.castSucc))
      (by norm_num)
  have hs : (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1) ≠ 0 := by
    split_ifs
    · exact torusSin_monomial_ne_zero _ (by
        intro hh
        have hh' := congrFun hh (Fin.last n)
        simp [variableExponent] at hh') 1 one_ne_zero
    · exact one_ne_zero
  have hnod : (Lagrange.nodal Finset.univ (@deletionBeta n)).eval₂
      (liftSpectral n) (spectralA (Fin.last n)) ≠ 0 := by
    simp only [Lagrange.nodal, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hi : liftSpectral n (deletionBeta i) = deletionBeta i.castSucc := by
      simp [deletionBeta, deletionNode, map_div₀]
    rw [hi]
    exact sub_ne_zero.mpr (spectralA_ne_beta i.castSucc (Fin.last n))
  have hh : liftSpectral n (rationalResidualCoefficient n p) = 0 := by
    rcases mul_eq_zero.mp h.symm with h | h
    · exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hden hs)
    · exact (hnod h).elim
  exact (liftSpectral n).injective (by simpa using hh)

 

lemma rationalResidualPolynomial_zero (n : ℕ) (p : Pairing (n+1)) :
    rationalResidualPolynomial n p = 0 := by
  rw [rationalResidualPolynomial_factor, rationalResidualCoefficient_zero]
  simp

def vacantTopEquiv (n : ℕ) :
    Pairing n ≃ {p : Pairing (n+1) // ¬p.Occupied (Fin.last n)} where
  toFun p := ⟨p.padTop, p.padTop_not_occupied_last⟩
  invFun p := p.val.restrict Fin.castSuccOrderEmb
  left_inv _ := Pairing.restrict_map _ _
  right_inv p := Subtype.ext (Pairing.padTop_restrict _ p.property)

def pairingTopSplit (n : ℕ) : Pairing n ⊕ SourcePairing n ≃ Pairing (n+1) :=
  (Equiv.sumCongr (vacantTopEquiv n)
    (Equiv.subtypeEquivRight (fun _ => not_not.symm))).trans
      (Equiv.sumCompl (fun p : Pairing (n+1) => ¬p.Occupied (Fin.last n)))

@[simp] lemma pairingTopSplit_inl {n : ℕ} (p : Pairing n) :
    pairingTopSplit n (Sum.inl p) = p.padTop := rfl

@[simp] lemma pairingTopSplit_inr {n : ℕ} (p : SourcePairing n) :
    pairingTopSplit n (Sum.inr p) = p.val := rfl

 

lemma lastTransform_source_leading {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K) (P : Pairing (n+1) → Polynomial K)
    (hP : LastDegree n P) (hn : 1 ≤ n) (q : SourcePairing n) :
    (lastTransform w d c C P q.val).coeff n =
      (sourceTransfer w).mulVec (fun p => (P p.val).coeff (n-1)) q +
        (2*d) * (northSource w).mulVec (fun p => (P p.padTop).coeff n) q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [lastTransform_coeff_succ, ← (pairingTopSplit (k+1)).sum_comp]
  simp only [Fintype.sum_sum_type, pairingTopSplit_inl, pairingTopSplit_inr,
    q.property, Pairing.padTop_not_occupied_last, ite_true, ite_false]
  have hzero (p : SourcePairing (k+1)) : (P p.val).coeff (k+1) = 0 :=
    hP p.val (k+1) (by simp [p.property])
  simp only [hzero, mul_zero, sub_zero, sourceTransfer,
    northSource, Matrix.mulVec, dotProduct, Finset.mul_sum]
  simp only [SourcePairing.occupied, ite_true, Nat.succ_sub_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

 
def northNumerator (n : ℕ) (p : SourcePairing n) : SpectralField n :=
  (rationalNodalPolynomial n p.val).coeff (n-1)

lemma northNumerator_equation (n : ℕ) :
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile)).mulVec (northNumerator n) =
      (2*constF n d) • (northSource (fun i => (spectralWeights n i).tile)).mulVec (rationalVacuum n) := by
  classical
  by_cases hn : 1 ≤ n
  · have hs (q : SourcePairing n) := congrArg (fun p : Polynomial (SpectralField n) => p.coeff n)
      (sub_eq_zero.mp (rationalResidualPolynomial_zero n q.val))
    funext q
    have hz (k : ℕ) (hk : n ≤ k) : (rationalNodalPolynomial n q.val).coeff k = 0 :=
      rationalNodalPolynomial_degree n q.val k (by simpa [q.property] using hk)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hh := hs q
    change (lastTransform _ _ _ _ _ q.val).coeff (k+1) =
      ((Polynomial.X + Polynomial.C _) * rationalNodalPolynomial (k+1) q.val).coeff (k+1) at hh
    rw [lastTransform_source_leading _ _ _ _ _ (rationalNodalPolynomial_degree _) (by omega)] at hh
    simp only [rationalNodalPolynomial_leading, add_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, hz (k+1) (by omega), mul_zero, add_zero] at hh
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      northNumerator]
    change (rationalNodalPolynomial (k+1) q.val).coeff k -
      (sourceTransfer (fun i => (spectralWeights (k+1) i).tile)).mulVec
        (fun p => (rationalNodalPolynomial (k+1) p.val).coeff k) q = _
    simp only [Nat.add_sub_cancel] at hh
    linear_combination -hh
  · have hn : n = 0 := by omega
    subst n
    funext p
    exact (p.ne_empty (p.val.eq_empty_of_le_one (by omega))).elim

 

def integratedNorthSource (n : ℕ) : SourcePairing n → SpectralField n :=
  (1 - sourceTransfer (fun i => (spectralWeights n i).tile))⁻¹.mulVec
    ((northSource (fun i => (spectralWeights n i).tile)).mulVec
      (normalizedVacuum (spectralWeights n)))

lemma northNumerator_eq_integrated (n : ℕ) :
    northNumerator n = (2*constF n d * spectralNormalization n) • integratedNorthSource n := by
  have h := congrArg (fun v =>
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile))⁻¹.mulVec v)
      (northNumerator_equation n)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (spectral_source_regular n)),
    Matrix.one_mulVec, Matrix.mulVec_smul] at h
  change _ = (2*constF n d) •
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile))⁻¹.mulVec
      ((northSource (fun i => (spectralWeights n i).tile)).mulVec
        (spectralNormalization n • normalizedVacuum (spectralWeights n))) at h
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul] at h
  exact h

 

def polynomialNorthSource (n : ℕ) (p : SourcePairing n) : Laurent n :=
  constantL n (1/(2*(d:ℂ))) * ((vacuumData n).P p.val).coeff (n-1)

lemma polynomialNorthSource_eval (n : ℕ) (p : SourcePairing n) :
    evalLaurent (polynomialNorthSource n p) =
      spectralNormalization n * integratedNorthSource n p := by
  have hd : constF n d ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (by exact_mod_cast d_ne_zero)
  have ht := congrFun (northNumerator_eq_integrated n) p
  simp only [Pi.smul_apply, smul_eq_mul] at ht
  unfold polynomialNorthSource
  rw [show evalLaurent ((constantL n (1/(2*(d:ℂ)))) * ((vacuumData n).P p.val).coeff (n-1)) =
      evalLaurent (constantL n (1/(2*(d:ℂ)))) * evalLaurent (((vacuumData n).P p.val).coeff (n-1)) from
        (algebraMap (SpectralRing n) (SpectralField n)).map_mul _ _, show evalLaurent (constantL n (1/(2*(d:ℂ)))) = 1/(2*constF n d) by
    rw [evalLaurent, map_constantL]
    change (algebraMap ℂ (SpectralField n)) (1/(2*(d:ℂ))) = _
    rw [map_div₀, map_one, map_mul, map_ofNat]
    rfl]
  have hc : evalLaurent (((vacuumData n).P p.val).coeff (n-1)) = northNumerator n p := by
    rw [evalLaurent, ←Polynomial.coeff_map, (vacuumData n).map_P]
    rfl
  rw [hc, ht]
  field_simp

 

theorem polynomialNorthSource_box (n : ℕ) (p : SourcePairing n) :
    LaurentBox (polynomialNorthSource n p) (fun _ => 2*n) := by
  simpa only [polynomialNorthSource, zero_add] using (LaurentBox.constant (1/(2*(d:ℂ)))).mul
    ((vacuumData n).box_P p.val (n-1))

end


 

noncomputable section
open scoped Classical BigOperators

namespace Graph

 
def DrainsAt {V : Type*} (r : V → V → Prop) (root : V) : Prop :=
  ∀ v w, r v w → Relation.ReflTransGen r v root

lemma DrainsAt.mono_root {V : Type*} {r : V → V → Prop} {a b : V}
    (h : DrainsAt r a) (hab : Relation.ReflTransGen r a b) : DrainsAt r b :=
  fun _ _ hvw => (h _ _ hvw).trans hab

lemma DrainsAt.map {V W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (e : V ≃ W) (he : ∀ v w, s (e v) (e w) ↔ r v w) {root : V}
    (h : DrainsAt r root) : DrainsAt s (e root) := by
  intro x y hxy
  obtain ⟨v,rfl⟩ := e.surjective x
  obtain ⟨w,rfl⟩ := e.surjective y
  exact Graph.map_reach e (fun v w hvw => .single ((he v w).mpr hvw))
    (h v w ((he v w).mp hxy))

 

def boundaryClosure {V : Type*} {n : ℕ} (r : V → V → Prop) (a : Fin n → V)
    (q : Pairing n) (v w : V) : Prop :=
  r v w ∨ ∃ i j, q.Adj i j ∧ a i = v ∧ a j = w

lemma closure_lift {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {q : Pairing n} {v w : V} (h : Relation.ReflTransGen r v w) :
    Relation.ReflTransGen (boundaryClosure r a q) v w :=
  Relation.ReflTransGen.mono (fun _ _ hh => Or.inl hh) _ _ h

 

end Graph
end
end CriticalStrip.Diagram

end OAI
