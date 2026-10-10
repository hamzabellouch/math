import Mathlib
import OAI.Combinatorics.StripMass.SwapVacancy

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

 
def inverseRowDenominator {n : ℕ} (i : Fin n) : Laurent n :=
  sineL (-variableExponent i) (phase^(2:ℤ)) *
    sineL (-variableExponent i) (phase^(3:ℤ))

def inverseRowNumerator {n : ℕ} (i : Fin n) : Tile → Laurent n
  | .vacant => inverseRowDenominator i
  | .vertical₀ | .vertical₁ =>
      constantL n d * sineL (variableExponent i) (phase^(3:ℤ))
  | .diagonal₀ | .diagonal₁ =>
      sineL (-variableExponent i) (phase^(0:ℤ)) *
        sineL (variableExponent i) (phase^(3:ℤ))
  | .cap | .cup => constantL n d * sineL (-variableExponent i) (phase^(0:ℤ))
  | .verticalPair =>
      sineL (variableExponent i) (phase^(3:ℤ)) *
        sineL (variableExponent i) (phase^(2:ℤ))
  | .capCup =>
      sineL (-variableExponent i) (phase^(-1:ℤ)) *
        sineL (-variableExponent i) (phase^(0:ℤ))

theorem inverseRowDenominator_flat {n : ℕ} (i : Fin n) :
    flatEval n (inverseRowDenominator i) =
      (Real.sin (2*lambda) : ℂ) * (Real.sin (3*lambda) : ℂ) := by
  simp only [inverseRowDenominator, map_mul, flatEval_sine_phase, Int.cast_ofNat]

theorem inverseRowDenominator_flat_ne_zero {n : ℕ} (i : Fin n) :
    flatEval n (inverseRowDenominator i) ≠ 0 := by
  simpa only [inverseRowDenominator_flat, flatEval_rowDenominator, mul_comm] using
    flatEval_rowDenominator_ne_zero i

theorem inverseRowDenominator_map {n : ℕ} (i : Fin n) :
    evalLaurent (inverseRowDenominator i) = torusL (variableF i)⁻¹ := by
  simp only [evalLaurent, inverseRowDenominator, map_mul, zpow_ofNat,
    map_sine_neg_variable_nat, torusL, div_eq_mul_inv]

theorem inverseRowDenominator_map_ne_zero {n : ℕ} (i : Fin n) :
    evalLaurent (inverseRowDenominator i) ≠ 0 := by
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  exact inverseRowDenominator_flat_ne_zero i (by rw [h, map_zero])

theorem inverseRowNumerator_flat {n : ℕ} (i : Fin n) (t : Tile) :
    flatEval n (inverseRowNumerator i t) =
      flatEval n (inverseRowDenominator i) * (identityWeights : Weights ℂ).tile t := by
  have hd : (d : ℂ) = (Real.sin (2*lambda) : ℂ) := by
    congr 1
    rw [d, ← Real.sin_pi_div_two_sub]
    congr 1
    unfold lambda
    ring
  cases t <;> simp only [inverseRowNumerator, map_mul, flatEval_constant,
    flatEval_sine_phase, inverseRowDenominator_flat, identityWeights, Weights.tile,
    Int.cast_ofNat, Int.cast_zero, zero_mul, Real.sin_zero, Complex.ofReal_zero,
    mul_zero, mul_one]
  all_goals try rw [hd]
  all_goals ring

theorem inverseRowNumerator_map {n : ℕ} (i : Fin n) (t : Tile) :
    evalLaurent (inverseRowNumerator i t) =
      evalLaurent (inverseRowDenominator i) * (torusWeights (variableF i)⁻¹).tile t := by
  have hx := variableF_ne_zero i
  have hq := constF_phase_ne_zero n
  have hL : torusL (variableF i)⁻¹ ≠ 0 := by
    rw [← inverseRowDenominator_map]
    exact inverseRowDenominator_map_ne_zero i
  have h₃ : constF n phase ^ 3 / (variableF i)⁻¹ = constF n phase ^ 3 * variableF i := by simp
  have h₂ : constF n phase ^ 2 / (variableF i)⁻¹ = constF n phase ^ 2 * variableF i := by simp
  have hd : algebraMap (SpectralRing n) (SpectralField n) (inverseRowDenominator i) =
      torusL (variableF i)⁻¹ := inverseRowDenominator_map i
  cases t <;> simp only [evalLaurent, inverseRowNumerator, map_mul, map_constantL,
    zpow_ofNat, map_sine_variable_nat, map_sine_neg_variable_nat,
    zpow_neg_one, hd, torusWeights, Weights.tile,
    h₃, h₂, mul_one]
  all_goals try simp only [← one_div (variableF i)] at hL
  all_goals try field_simp [hL]
  rw [sineL_map _ _ (one_div_ne_zero phase_ne_zero), map_monomialL_neg_variable]
  simp only [constF, div_eq_mul_inv, mul_inv_rev]
  simp only [mul_one, one_mul, map_inv₀, mul_comm]

theorem nodalWeights_last {n : ℕ} (i : Fin n) :
    nodalWeights i (Fin.last n) = torusWeights (variableF i)⁻¹ := by
  simp only [nodalWeights, Fin.snoc_last, deletionNode]
  congr 1
  field_simp [constF_phase_ne_zero]

theorem nodal_regular {n : ℕ} (i : Fin n) : VacuumRegular (nodalWeights i) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _) (flatEval n).toRingHom
    (Fin.snoc rowDenominator (inverseRowDenominator i))
    (Fin.snoc rowNumerator (inverseRowNumerator i))
    (nodalWeights i) (Fin.snoc (fun _ => deletionWeights) identityWeights)
  · intro j
    induction j using Fin.lastCases with
    | last => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_last] using inverseRowDenominator_flat_ne_zero i
    | cast j => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_castSucc] using flatEval_rowDenominator_ne_zero j
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [evalLaurent, Fin.snoc_last, nodalWeights_last] using inverseRowNumerator_map i t
    | cast j => simpa only [Fin.snoc_castSucc, nodalWeights] using rowNumerator_map j t
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_last] using inverseRowNumerator_flat i t
    | cast j => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_castSucc] using rowNumerator_flatEval j t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro j k hj hk
      induction j using Fin.lastCases with
      | last => exact (hj (Or.inl (Fin.snoc_last ..))).elim
      | cast j => exact (hj (Or.inr (Fin.snoc_castSucc ..))).elim

theorem nodalVacuum_stationary {n : ℕ} (i : Fin n) :
    (column (nodalWeights i)).mulVec (nodalVacuum i) = nodalVacuum i := by
  have h := (normalizedVacuum_stationary (nodalWeights i) (nodal_regular i)).2
  change (column (nodalWeights i)).mulVec (nodalScalar i • normalizedVacuum (nodalWeights i)) =
    nodalScalar i • normalizedVacuum (nodalWeights i)
  rw [Matrix.mulVec_smul, h]


 

 

open scoped Classical

 

lemma spectral_regular_reindex {n m : ℕ} (f : Fin n → Fin m) :
    VacuumRegular (fun i => spectralWeights m (f i)) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing m) (SpectralField m))
    (IsFractionRing.injective _ _) (flatEval m).toRingHom
    (fun i => rowDenominator (f i)) (fun i => rowNumerator (f i))
    (fun i => spectralWeights m (f i)) (fun _ => deletionWeights)
  · intro i; exact flatEval_rowDenominator_ne_zero (f i)
  · intro i; exact rowNumerator_map (f i)
  · intro i; exact rowNumerator_flatEval (f i)
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro i j hi; exact (hi (Or.inr rfl)).elim

lemma map_monomialL_sub_variable {n : ℕ} (i j : Fin n) (z : ℂ) :
    evalLaurent (monomialL (variableExponent j-variableExponent i) z)=
      constF n z*(variableF j/variableF i) := by
  have hm : monomialL (variableExponent j-variableExponent i) z =
      monomialL (variableExponent j) z * monomialL (-variableExponent i) 1 := by
    simp only [monomialL_mul,mul_one,sub_eq_add_neg]
  rw [hm,evalLaurent,map_mul,map_monomialL_variable,map_monomialL_neg_variable]
  simp only [constF,map_one,div_eq_mul_inv,mul_assoc,one_mul]

lemma torusL_ratio_ne_zero {n : ℕ} (i j : Fin n) : torusL (variableF j/variableF i)≠0 := by
  let e := variableExponent j-variableExponent i
  let D : Laurent n := sineL e (phase^2)*sineL e (phase^3)
  have hev : evalLaurent D=torusL (variableF j/variableF i) := by
    simp only [D,evalLaurent,map_mul,torusL]
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero),
      sineL_map _ _ (pow_ne_zero _ phase_ne_zero),
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^2))=
        constF n (phase^2)*(variableF j/variableF i) from map_monomialL_sub_variable i j _,
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^3))=
        constF n (phase^3)*(variableF j/variableF i) from map_monomialL_sub_variable i j _]
    simp only [constF,map_pow]
  have hf : flatEval n D=(Real.sin (2*lambda):ℂ)*(Real.sin (3*lambda):ℂ) := by
    change (flatEval n (sineL e (phase^(2:ℤ))*sineL e (phase^(3:ℤ))))=_
    simp only [map_mul,flatEval_sine_phase,Int.cast_ofNat]
  rw [←hev]
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  have hne:=flatEval_rowDenominator_ne_zero i
  apply hne
  rw [flatEval_rowDenominator]
  have hh : flatEval n D=0 := by rw [h,map_zero]
  rw [hf] at hh
  simpa only [mul_comm] using hh

 

theorem spectral_vacuum_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    normalizedVacuum (spectralWeights n) =
      (localR (PartialColumn.rowPosition r hr)
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
        (normalizedVacuum (fun i => spectralWeights n
          (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i))) := by
  apply normalizedVacuum_torus_exchange r hr
    (fun i => constF n phase^3/variableF i)
    (variableF ⟨r+1,by omega⟩/variableF ⟨r,by omega⟩)
  · exact div_ne_zero (variableF_ne_zero _) (variableF_ne_zero _)
  · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)
  · exact torusL_ratio_ne_zero _ _
  · rw [← rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · rw [← rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · field_simp [variableF_ne_zero]
  · exact spectral_regular n
  · exact spectral_regular_reindex _

end

 

 

noncomputable section
open scoped Classical

 
def insertedNodeWeights {n : ℕ} (i : Fin n) (j : Fin (n+1)) :
    Fin (n+1) → Weights (SpectralField n) :=
  Fin.insertNth j (torusWeights (variableF i)⁻¹) (spectralWeights n)

lemma insertedNodeWeights_last {n : ℕ} (i : Fin n) :
    insertedNodeWeights i (Fin.last n)=nodalWeights i := by
  rw [insertedNodeWeights,Fin.insertNth_last']
  funext j
  induction j using Fin.lastCases with
  | last => rw [Fin.snoc_last,nodalWeights_last]
  | cast j => simp [nodalWeights]

 

lemma insertedNode_regular {n : ℕ} (i : Fin n) (j : Fin (n+1)) :
    VacuumRegular (insertedNodeWeights i j) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _) (flatEval n).toRingHom
    (Fin.insertNth j (inverseRowDenominator i) rowDenominator)
    (Fin.insertNth j (inverseRowNumerator i) rowNumerator)
    (insertedNodeWeights i j) (Fin.insertNth j identityWeights (fun _ => deletionWeights))
  · intro k
    refine Fin.succAboveCases j ?_ (fun l => ?_) k <;> simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    · exact inverseRowDenominator_flat_ne_zero i
    · exact flatEval_rowDenominator_ne_zero l
  · intro k t
    refine Fin.succAboveCases j ?_ (fun l => ?_) k <;> simp only [insertedNodeWeights,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    · exact inverseRowNumerator_map i t
    · exact rowNumerator_map _ t
  · intro k t
    refine Fin.succAboveCases j ?_ (fun l => ?_) k <;> simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    · exact inverseRowNumerator_flat i t
    · exact rowNumerator_flatEval _ t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro k l hk
      rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨a,rfl⟩
      · exact (hk (Or.inl (Fin.insertNth_apply_same ..))).elim
      · exact (hk (Or.inr (Fin.insertNth_apply_succAbove ..))).elim

lemma insertedNode_deletion {n : ℕ} (i : Fin (n+1)) :
    normalizedVacuum (insertedNodeWeights i i.succ) =
      (deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
        (normalizedVacuum (fun k => spectralWeights (n+1) (i.succAbove k))) := by
  have hrows : (fun k => insertedNodeWeights i i.succ
      (i.succ.succAbove (i.succAbove k)))=(fun k => spectralWeights (n+1) (i.succAbove k)) := by
    funext k; exact Fin.insertNth_apply_succAbove _ _ _ _
  have h₀ : insertedNodeWeights i i.succ ⟨i.val,by omega⟩=
      torusWeights (constF (n+1) phase^3*(variableF i)⁻¹) := by
    have hi : i.succ.succAbove i=i.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ
    change insertedNodeWeights i i.succ i.castSucc=_
    rw [←hi]
    simp only [insertedNodeWeights,Fin.insertNth_apply_succAbove,spectralWeights,div_eq_mul_inv]
  have h₁ : insertedNodeWeights i i.succ ⟨i.val+1,by omega⟩=torusWeights (variableF i)⁻¹ :=
    Fin.insertNth_apply_same ..
  have hL : torusL (constF (n+1) phase^3*(variableF i)⁻¹)≠0 := by
    rw [←div_eq_mul_inv,←rowDenominator_map]
    exact rowDenominator_map_ne_zero i
  have h := normalizedVacuum_deletion i.val (show i.val+2≤n+2 by omega)
    (insertedNodeWeights i i.succ) (variableF i)⁻¹
    (inv_ne_zero (variableF_ne_zero i))
    (by rw [←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i) hL
    h₀ h₁ (insertedNode_regular i i.succ)
    (by change VacuumRegular (fun k => insertedNodeWeights i i.succ
        (i.succ.succAbove (i.succAbove k)))
        rw [hrows]; exact spectral_regular_reindex i.succAbove)
  change normalizedVacuum (insertedNodeWeights i i.succ) =
    (deletionMap i.val _).mulVec (normalizedVacuum
      (fun k => insertedNodeWeights i i.succ (i.succ.succAbove (i.succAbove k)))) at h
  rw [hrows] at h
  exact h


 

 


lemma Fin.insertNth_swap_adjacent {α : Type*} {n : ℕ} (a b : Fin (n+1))
    (hab : a.val+1=b.val) (x : α) (w : Fin n → α) :
    (Fin.insertNth b x w) ∘ Equiv.swap a b=Fin.insertNth a x w := by
  rw [Fin.eq_insertNth_iff]
  constructor
  · simp
  · funext i
    have h : Equiv.swap a b (a.succAbove i)=b.succAbove i := by
      rw [←Fin.swap_succAbove_adjacent a b hab i,Equiv.swap_apply_self]
    simp only [Fin.removeNth,Function.comp_apply,h,Fin.insertNth_apply_succAbove]

lemma torusL_deletion_ratio_ne_zero {n : ℕ} (i j : Fin n) :
    torusL (constF n phase^3*(variableF i/variableF j))≠0 := by
  let e:=variableExponent i-variableExponent j
  let D : Laurent n:=sineL e (phase^5)*sineL e (phase^6)
  have hev : evalLaurent D=torusL (constF n phase^3*(variableF i/variableF j)) := by
    simp only [D,evalLaurent,map_mul,torusL]
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero),sineL_map _ _ (pow_ne_zero _ phase_ne_zero),
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^5))=
        constF n (phase^5)*(variableF i/variableF j) from map_monomialL_sub_variable j i _,
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^6))=
        constF n (phase^6)*(variableF i/variableF j) from map_monomialL_sub_variable j i _]
    simp only [constF,map_pow]
    congr 1 <;> congr 1 <;> ring
  have hf : flatEval n D=flatEval n (rowDenominator i) := by
    change (flatEval n (sineL e (phase^(5:ℤ))*sineL e (phase^(6:ℤ))))=_
    simp only [rowDenominator,map_mul,flatEval_sine_phase]
  rw [←hev]
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  exact flatEval_rowDenominator_ne_zero i (by rw [←hf,h,map_zero])

 

theorem insertedNode_move {n : ℕ} (i j : Fin n) :
    normalizedVacuum (insertedNodeWeights i j.succ)=
      (localR (PartialColumn.rowPosition j.val (show j.val+2≤n+1 by omega))
        (torusWeights (constF n phase^3 * (variableF i/variableF j)))).mulVec
          (normalizedVacuum (insertedNodeWeights i j.castSucc)) := by
  let a : Fin (n+1):=j.castSucc
  let b : Fin (n+1):=j.succ
  let x : Fin (n+1) → SpectralField n := Fin.insertNth b (variableF i)⁻¹ (fun k => constF n phase^3/variableF k)
  let z := constF n phase^3*(variableF i/variableF j)
  have h₀ : x a=constF n phase^3/variableF j := by
    have h : b.succAbove j=a := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ
    rw [←h]
    exact Fin.insertNth_apply_succAbove ..
  have h₁ : x b=(variableF i)⁻¹ := Fin.insertNth_apply_same ..
  have hw : (fun k => torusWeights (x k))=insertedNodeWeights i b := by
    funext k
    refine Fin.succAboveCases b ?_ (fun l => ?_) k <;>
      simp only [x,insertedNodeWeights,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,spectralWeights]
  have hx : z*x b=x a := by
    rw [h₀,h₁]
    dsimp only [z]
    field_simp [variableF_ne_zero]
  have hL₀ : torusL (x a)≠0 := by
    rw [h₀,←rowDenominator_map]; exact rowDenominator_map_ne_zero j
  have hL₁ : torusL (x b)≠0 := by
    rw [h₁,←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i
  have hswap : (insertedNodeWeights i b) ∘ Equiv.swap a b=insertedNodeWeights i a :=
    Fin.insertNth_swap_adjacent a b rfl _ _
  have hh := normalizedVacuum_torus_exchange j.val (show j.val+2≤n+1 by omega) x z
    (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _))
      (div_ne_zero (variableF_ne_zero _) (variableF_ne_zero _)))
    (by change x b≠0; rw [h₁]; exact inv_ne_zero (variableF_ne_zero i))
    (torusL_deletion_ratio_ne_zero i j) hL₁ hL₀ hx
    (by rw [hw]; exact insertedNode_regular i b)
    (by change VacuumRegular ((fun k => torusWeights (x k)) ∘ Equiv.swap a b)
        rw [hw,hswap]; exact insertedNode_regular i a)
  rw [hw] at hh
  have hs : (fun k => torusWeights (x (Equiv.swap ⟨j.val,by omega⟩ ⟨j.val+1,by omega⟩ k)))=
      insertedNodeWeights i a := by
    change (fun k => torusWeights (x k)) ∘ Equiv.swap a b=insertedNodeWeights i a
    rw [hw,hswap]
  rw [hs] at hh
  exact hh


 

 


 

def movingBoxes {n : ℕ} (i : Fin n) : ℕ → Matrix (Pairing (n+1)) (Pairing (n+1)) (SpectralField n)
  | 0 => 1
  | k+1 => if h : i.val < k ∧ k < n then
      localR (PartialColumn.rowPosition k (by omega))
        (torusWeights (constF n phase^3*(variableF i/variableF ⟨k,h.2⟩))) * movingBoxes i k
    else movingBoxes i k

lemma movingBoxes_initial {n : ℕ} (i : Fin n) (k : ℕ) (hk : k ≤ i.val+1) :
    movingBoxes i k=1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [movingBoxes, dite_eq_right (by omega),ih (by omega)]

lemma insertedNode_moved {n : ℕ} (i : Fin n) (k : ℕ)
    (hk : i.val+1 ≤ k) (hkn : k ≤ n) :
    normalizedVacuum (insertedNodeWeights i ⟨k,by omega⟩)=
      (movingBoxes i k).mulVec (normalizedVacuum (insertedNodeWeights i i.succ)) := by
  induction k, hk using Nat.le_induction with
  | base =>
      rw [movingBoxes_initial i _ le_rfl,Matrix.one_mulVec]
      rfl
  | succ k hk ih =>
      have hstep:=insertedNode_move i (⟨k,show k<n by omega⟩ : Fin n)
      change normalizedVacuum (insertedNodeWeights i ⟨k+1,by omega⟩)=_
      rw [movingBoxes,dite_eq_left (by omega),←Matrix.mulVec_mulVec]
      rw [←ih (by omega)]
      exact hstep

 

theorem nodalVacuum_movingBoxes {n : ℕ} (i : Fin (n+1)) :
    normalizedVacuum (nodalWeights i)=
      (movingBoxes i (n+1)).mulVec
        ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
          (normalizedVacuum (fun k => spectralWeights (n+1) (i.succAbove k)))) := by
  rw [←insertedNodeWeights_last]
  have h:=insertedNode_moved i (n+1) (by omega) le_rfl
  rw [insertedNode_deletion] at h
  exact h


 

 


def topPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  σ.viaEmbedding Fin.castSuccEmb

@[simp] lemma topPerm_cast {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    topPerm σ i.castSucc=(σ i).castSucc :=
  Equiv.Perm.viaEmbedding_apply σ Fin.castSuccEmb i

@[simp] lemma topPerm_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    topPerm σ (Fin.last n)=Fin.last n := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,hi⟩
  exact Fin.castSucc_ne_last i hi

@[simp] lemma permSpectral_deletionNode {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (deletionNode i)=deletionNode (σ i) := by simp [deletionNode]

@[simp] lemma permSpectral_deletionBeta {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (deletionBeta i)=deletionBeta (σ i) := by simp [deletionBeta,map_div₀]

lemma permSpectral_nodalWeights {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (fun j => (nodalWeights i j).map (permSpectral σ))=
      (fun j => nodalWeights (σ i) (topPerm σ j)) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [nodalWeights,map_div₀]
  | cast j => simp [nodalWeights]

lemma scalarPolynomial_eval_reindex {K : Type*} [Field K] {n : ℕ}
    (f : ℂ →+* K) (a : Fin n → K) (σ : Equiv.Perm (Fin n)) (dd rr : ℂ) (hd : dd≠0) :
    MvPolynomial.eval₂Hom f (a ∘ σ) (scalarPolynomial n dd rr hd)=
      MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hd) := by
  rw [←MvPolynomial.eval₂Hom_rename,scalarPolynomial_rename]

lemma permSpectral_nodalScalar {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (nodalScalar i)=nodalScalar (σ i) := by
  have hc : (permSpectral σ).comp (algebraMap ℂ (SpectralField n))=
      algebraMap ℂ (SpectralField n) := by
    ext z
    exact permSpectral_const σ z
  have hv : (fun j : Fin (n+1) => permSpectral σ ((Fin.snoc spectralA (deletionBeta i) : Fin (n+1) → SpectralField n) j))=
      (Fin.snoc spectralA (deletionBeta (σ i)) : Fin (n+1) → SpectralField n) ∘ topPerm σ := by
    funext j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  rw [nodalScalar,MvPolynomial.map_eval₂Hom,hc,hv,scalarPolynomial_eval_reindex]
  rfl

lemma nodal_regular_reindex {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    VacuumRegular (fun j => nodalWeights (σ i) (topPerm σ j)) := by
  rw [←permSpectral_nodalWeights]
  exact (nodal_regular i).map (permSpectral σ) (nodalWeights i)

lemma permSpectral_nodalVacuum {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (p : Pairing (n+1)) :
    permSpectral σ (nodalVacuum i p)=nodalScalar (σ i)*
      normalizedVacuum (fun j => nodalWeights (σ i) (topPerm σ j)) p := by
  rw [nodalVacuum,map_mul,permSpectral_nodalScalar]
  have hh:=congrFun (normalizedVacuum_map (permSpectral σ) (nodalWeights i) (nodal_regular i)) p
  rw [permSpectral_nodalWeights] at hh
  rw [hh]

end

 

 

noncomputable section

 

def deletionPerm {n : ℕ} (i : Fin (n+1)) : Equiv.Perm (Fin (n+2)) :=
  Equiv.ofBijective (twoCons i.castSucc (Fin.last (n+1)) (fun j => (i.succAbove j).castSucc))
    (Finite.injective_iff_bijective.mp (by
      intro a b h
      induction a using Fin.cases with
      | zero =>
          induction b using Fin.cases with
          | zero => rfl
          | succ b =>
              induction b using Fin.cases with
              | zero => exact (Fin.castSucc_ne_last i (by simp at h)).elim
              | succ b =>
                  have hh : i=i.succAbove b := (by simp at h)
                  exact (Fin.succAbove_ne i b hh.symm).elim
      | succ a =>
          induction a using Fin.cases with
          | zero =>
              induction b using Fin.cases with
              | zero => exact (Fin.castSucc_ne_last i (by simpa using h.symm)).elim
              | succ b =>
                  induction b using Fin.cases with
                  | zero => rfl
                  | succ b => exact (Fin.castSucc_ne_last (i.succAbove b) (by simpa using h.symm)).elim
          | succ a =>
              induction b using Fin.cases with
              | zero =>
                  have hh : i.succAbove a=i := (by simp at h)
                  exact (Fin.succAbove_ne i a hh).elim
              | succ b =>
                  induction b using Fin.cases with
                  | zero => exact (Fin.castSucc_ne_last (i.succAbove a) (by simp at h)).elim
                  | succ b =>
                      have hh : i.succAbove a=i.succAbove b := (by simpa using h)
                      exact congrArg (fun j : Fin n => j.succ.succ) (Fin.succAbove_right_injective hh)))

lemma deletionPerm_tuple {K : Type*} {n : ℕ} (i : Fin (n+1)) (a : Fin (n+1) → K) (b : K) :
    (Fin.snoc a b) ∘ deletionPerm i=twoCons (a i) b (fun k => a (i.succAbove k)) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [deletionPerm]
  | succ j =>
      induction j using Fin.cases with
      | zero => simp [deletionPerm]
      | succ j => simp [deletionPerm]

lemma scalarPolynomial_snoc_delete_reindex {K : Type*} [Field K] {n : ℕ} (f : ℂ →+* K)
    (i : Fin (n+1)) (a : Fin (n+1) → K) (b : K) (dd rr : ℂ) (hd : dd≠0) :
    MvPolynomial.eval₂Hom f (Fin.snoc a b) (scalarPolynomial (n+2) dd rr hd)=
      MvPolynomial.eval₂Hom f (twoCons (a i) b (fun k => a (i.succAbove k)))
        (scalarPolynomial (n+2) dd rr hd) := by
  rw [←deletionPerm_tuple,scalarPolynomial_eval_reindex]

end
end CriticalStrip.Diagram

end OAI
