import Mathlib
import OAI.Combinatorics.StripMass.SpecializationPolynomial

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma topPerm_symm {n:ℕ} (σ:Equiv.Perm (Fin n)) : (topPerm σ).symm=topPerm σ.symm := by
  apply Equiv.ext
  intro i
  apply (topPerm σ).injective
  induction i using Fin.lastCases <;> simp

lemma permLaurent_lift {n:ℕ} (σ:Equiv.Perm (Fin n)) (f:Laurent n) :
    permLaurent (topPerm σ) (liftLaurent f)=liftLaurent (permLaurent σ f) := by
  have he:(permLaurent (topPerm σ)).comp (liftLaurentHom n)=
      (liftLaurentHom n).comp (permLaurent σ) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change permLaurent (topPerm σ) (liftLaurent (monomialL _ _))=liftLaurent (permLaurent σ (monomialL _ _))
    all_goals rw [liftLaurent_monomial,permLaurent_monomial,permLaurent_monomial,liftLaurent_monomial]
    all_goals congr 1; funext i; induction i using Fin.lastCases <;> simp [topPerm_symm]
  exact DFunLike.congr_fun he f

lemma permSpectral_lift {n:ℕ} (σ:Equiv.Perm (Fin n)) (f:SpectralField n) :
    permSpectral (topPerm σ) (liftSpectral n f)=liftSpectral n (permSpectral σ f) := by
  have he:(permSpectral (topPerm σ)).comp (liftSpectral n)=
      (liftSpectral n).comp (permSpectral σ) := by
    apply IsFractionRing.ringHom_ext (A:=SpectralRing n)
    intro P
    change permSpectral (topPerm σ) (liftSpectral n (evalLaurent P))=liftSpectral n (permSpectral σ (evalLaurent P))
    rw [liftSpectral_evalLaurent,permSpectral_evalLaurent,permSpectral_evalLaurent,liftSpectral_evalLaurent,permLaurent_lift]
  exact DFunLike.congr_fun he f

lemma localR_map_hom {K L:Type*} [CommRing K] [CommRing L] {n:ℕ}
    (f:K →+* L) (a:Position n) (w:Weights K) :
    (localR a w).map f=localR a (w.map f) := by
  ext p q
  simp only [localR,Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,smul_eq_mul,map_sum,map_mul,Weights.map_tile]
  apply Finset.sum_congr rfl
  intro t _
  unfold optionMatrix
  split_ifs <;> simp

lemma permSpectral_interpolant {n:ℕ} (σ:Equiv.Perm (Fin n)) (p:Pairing (n+1)) :
    permSpectral (topPerm σ) (rationalInterpolant n p)=
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1)*
        ((rationalNodalPolynomial n p).map (permSpectral σ)).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
  have hm:(permSpectral (topPerm σ)).comp (liftSpectral n)=(liftSpectral n).comp (permSpectral σ) :=
    RingHom.ext (permSpectral_lift σ)
  simp only [rationalInterpolant,map_mul,Polynomial.hom_eval₂,hm,Polynomial.eval₂_map,
    permSpectral_spectralA,topPerm_last]
  split_ifs <;> simp

 

theorem rationalInterpolant_covariance {n:ℕ} (r:ℕ) (hr:r+2≤n) :
    rationalInterpolant n=
      (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc /
          variableF (⟨r,by omega⟩:Fin n).castSucc))).mulVec
      (fun p =>permSpectral (topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)) (rationalInterpolant n p)) := by
  let σ:=Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩
  let a:=PartialColumn.rowPosition r hr
  let w:=torusWeights (variableF (⟨r+1,by omega⟩:Fin n)/variableF (⟨r,by omega⟩:Fin n))
  have hw:w.map (liftSpectral n)=torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc/variableF (⟨r,by omega⟩:Fin n).castSucc) := by
    simp only [w,torusWeights,Weights.map,map_div₀,map_mul,map_pow,liftSpectral_const,liftSpectral_variable,
      liftSpectral_torusSin,torusL,map_mul,map_pow,liftSpectral_const,
      liftSpectral_torusSin,map_div₀,liftSpectral_variable]
  have hM:(localR a.padTop w).map (liftSpectral n)=localR a.padTop (w.map (liftSpectral n)):=localR_map_hom _ _ _
  funext p
  have hp:=congrArg (fun P:Polynomial (SpectralField n) =>P.eval₂ (liftSpectral n) (spectralA (Fin.last n)))
    (congrFun (rationalNodalPolynomial_covariance r hr) p)
  simp only [nodalExchangePolynomial,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,Polynomial.eval₂_C] at hp
  simp_rw [permSpectral_interpolant]
  change (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1)*
    (rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n))=_
  rw [hp,Finset.mul_sum]
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  have he:liftSpectral n (localR a.padTop w p q)=localR a.padTop (w.map (liftSpectral n)) p q := congrFun (congrFun hM p) q
  change _ * (liftSpectral n (localR a.padTop w p q)*_)=_
  rw [he,hw]
  by_cases ho:p.Occupied (Fin.last n) ↔ q.Occupied (Fin.last n)
  · simp only [ho]; ring
  · have hh:=localR_padTop_zero_last a (w.map (liftSpectral n)) q p ho
    rw [hw] at hh
    rw [hh,zero_mul,mul_zero,zero_mul]

end

 

 

noncomputable section
open Finset


 
theorem pfaffian_eq_zero_of_equal_rows {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, M j i = -M i j)
    (a b : Fin n) (hab : a ≠ b) (hrows : ∀ j, M a j = M b j) : pfaffian M = 0 := by
  have hr (i j : Fin n) : M (Equiv.swap a b i) j = M i j := by
    by_cases hi : i = a
    · subst i; simpa using (hrows j).symm
    by_cases hi' : i = b
    · subst i; simpa using hrows j
    rw [Equiv.swap_apply_of_ne_of_ne hi hi']
  have hc (i j : Fin n) : M i (Equiv.swap a b j) = M i j := by
    rw [hM, hr, hM, neg_neg]
  have hm : (fun i j => M (Equiv.swap a b i) (Equiv.swap a b j)) = M := by
    funext i j
    rw [hr, hc]
  have h := pfaffian_reindex M (Equiv.swap a b)
  rw [hm, Equiv.Perm.sign_swap hab] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  have hz : (2:K)*pfaffian M = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

 

def replaceFirst {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (v : Fin (n+1) → K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K := fun i j =>
  if i = 0 then v j else if j = 0 then -v i else M i j

@[simp] theorem replaceFirst_row {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (v : Fin (n+1) → K) (j : Fin (n+1)) :
    replaceFirst M v 0 j = v j := by simp [replaceFirst]

@[simp] theorem replaceFirst_rest {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (v : Fin (n+1) → K) (i j : Fin n) :
    replaceFirst M v i.succ j.succ = M i.succ j.succ := by
  simp [replaceFirst, Fin.succ_ne_zero]

theorem replaceFirst_skew {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (hM : ∀ i j, M j i = -M i j)
    (v : Fin (n+1) → K) (hv : v 0 = 0) (i j : Fin (n+1)) :
    replaceFirst M v j i = -replaceFirst M v i j := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp only [replaceFirst, hi, hj, ite_true, ite_false]
  all_goals first | exact hM i j | simp only [hv, neg_zero, neg_neg]

theorem pfaffian_replaceFirst_add {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (v w : Fin (2*(m+1)) → K) (hv : v 0 = 0) (hw : w 0 = 0) :
    pfaffian (replaceFirst M (v+w)) = pfaffian (replaceFirst M v) +
      pfaffian (replaceFirst M w) := by
  apply pfaffian_firstRow_add
  · exact replaceFirst_skew M hM _ (by simp [hv,hw])
  · exact replaceFirst_skew M hM v hv
  · exact replaceFirst_skew M hM w hw
  · intro j; simp
  · intro i j; simp only [replaceFirst_rest]
  · intro i j; simp only [replaceFirst_rest]

theorem pfaffian_replaceFirst_smul {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (v : Fin (2*(m+1)) → K) (hv : v 0 = 0) (t : K) :
    pfaffian (replaceFirst M (t • v)) = t * pfaffian (replaceFirst M v) := by
  rw [pfaffian_eq_block (m := m+1) (replaceFirst M (t • v)),
    pfaffian_eq_block (m := m+1) (replaceFirst M v),
    blockSummand_sum_fixedZero _ (replaceFirst_skew M hM _ (by simp [hv])),
    blockSummand_sum_fixedZero _ (replaceFirst_skew M hM v hv)]
  simp only [blockSummand_fixZero, replaceFirst_row, replaceFirst_rest, Pi.smul_apply,
    smul_eq_mul]
  simp only [mul_left_comm _ t, mul_assoc, ← Finset.mul_sum]

theorem skew_diagonal_zero {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, M j i = -M i j) (i : Fin n) :
    M i i = 0 := by
  have h := hM i i
  have hz : (2:K)*M i i = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

 

theorem pfaffian_replaceFirst_otherRow {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (r : Fin (2*(m+1))) (hr : r ≠ 0) :
    pfaffian (replaceFirst M (fun j => if j = 0 then 0 else M r j)) = 0 := by
  apply pfaffian_eq_zero_of_equal_rows _ (replaceFirst_skew M hM _ (by simp)) 0 r hr.symm
  intro j
  by_cases hj : j = 0
  · subst j
    simp [replaceFirst, hr, skew_diagonal_zero M hM r]
  · simp [replaceFirst, hr, hj]

 

theorem pfaffian_firstRow_add_other {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (r : Fin (2*(m+1))) (hr : r ≠ 0) (t : K) :
    pfaffian (replaceFirst M (fun j => if j = 0 then 0 else M 0 j + t * M r j)) =
      pfaffian M := by
  let v : Fin (2*(m+1)) → K := fun j => M 0 j
  let w : Fin (2*(m+1)) → K := fun j => if j = 0 then 0 else M r j
  have hv : v 0 = 0 := skew_diagonal_zero M hM 0
  have hw : w 0 = 0 := by simp [w]
  have he : (fun j => if j = 0 then 0 else M 0 j + t * M r j) = v + t • w := by
    funext j
    by_cases hj : j = 0
    · subst j; simp [v,w,skew_diagonal_zero M hM 0]
    · simp [v,w,hj]
  apply Eq.trans (congrArg (fun x => pfaffian (replaceFirst M x)) he)
  have hw0 : pfaffian (replaceFirst M w) = 0 :=
    pfaffian_replaceFirst_otherRow M hM r hr
  rw [pfaffian_replaceFirst_add M hM v _ hv (by simp [hw]),
    pfaffian_replaceFirst_smul M hM w hw t, hw0,
    mul_zero, add_zero]
  congr 1
  funext i j
  by_cases hi : i = 0
  · subst i; simp [v]
  by_cases hj : j = 0
  · subst j; simp only [replaceFirst,hi,ite_false,ite_true,v]
    exact (hM 0 i).symm
  · simp [replaceFirst,hi,hj]


 

 


 
def frontBorder {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  fun i j => Fin.cases (Fin.cases 0 (fun _ => v) j)
    (fun i => Fin.cases (-v) (M i) j) i

def backBorder {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  fun i j => Fin.lastCases (Fin.lastCases 0 (fun _ => -1) j)
    (fun i => Fin.lastCases 1 (M i) j) i

@[simp] theorem frontBorder_zero_zero {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) : frontBorder M v 0 0 = 0 := rfl
@[simp] theorem frontBorder_zero_succ {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (j : Fin n) : frontBorder M v 0 j.succ = v := rfl
@[simp] theorem frontBorder_succ_zero {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (i : Fin n) : frontBorder M v i.succ 0 = -v := rfl
@[simp] theorem frontBorder_succ_succ {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (i j : Fin n) :
    frontBorder M v i.succ j.succ = M i j := rfl
@[simp] theorem backBorder_last_last {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : backBorder M (Fin.last n) (Fin.last n) = 0 := by
  simp [backBorder]
@[simp] theorem backBorder_cast_last {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i : Fin n) : backBorder M i.castSucc (Fin.last n) = 1 := by
  simp [backBorder]
@[simp] theorem backBorder_last_cast {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (j : Fin n) : backBorder M (Fin.last n) j.castSucc = -1 := by
  simp [backBorder]
@[simp] theorem backBorder_cast_cast {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) : backBorder M i.castSucc j.castSucc = M i j := by
  simp [backBorder]

theorem frontBorder_skew {R : Type*} [AddGroup R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (hM : ∀ i j, M j i = -M i j) :
    ∀ i j, frontBorder M v j i = -frontBorder M v i j := by
  intro i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp only [frontBorder_zero_zero,frontBorder_zero_succ,frontBorder_succ_zero,
      frontBorder_succ_succ,neg_zero,neg_neg]
  exact hM _ _

theorem backBorder_skew {R : Type*} [AddGroupWithOne R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, M j i = -M i j) :
    ∀ i j, backBorder M j i = -backBorder M i j := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [backBorder_last_last,backBorder_last_cast,backBorder_cast_last,
      backBorder_cast_cast,neg_zero,neg_neg]
  exact hM _ _

@[simp] theorem rotateInv_zero (n : ℕ) : (finRotate (n+1)).symm 0 = Fin.last n := by
  apply (finRotate (n+1)).injective
  rw [Equiv.apply_symm_apply, finRotate_last]

@[simp] theorem rotateInv_succ {n : ℕ} (i : Fin n) :
    (finRotate (n+1)).symm i.succ = i.castSucc := by
  apply (finRotate (n+1)).injective
  rw [Equiv.apply_symm_apply]
  exact (finRotate_of_lt i.isLt).symm

theorem backBorder_rotate {R : Type*} [AddGroupWithOne R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    (fun i j => backBorder M ((finRotate (n+1)).symm i) ((finRotate (n+1)).symm j)) =
      frontBorder M (-1) := by
  funext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp only [rotateInv_zero,rotateInv_succ,backBorder_last_last,backBorder_cast_last,
      backBorder_last_cast,backBorder_cast_cast,frontBorder_zero_zero,frontBorder_zero_succ,
      frontBorder_succ_zero,frontBorder_succ_succ,neg_neg]

theorem pfaffian_frontBorder_scale {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*m+1)) (Fin (2*m+1)) K) (hM : ∀ i j, M j i = -M i j) (v t : K) :
    pfaffian (frontBorder M (t*v)) = t * pfaffian (frontBorder M v) := by
  let A := frontBorder M v
  have hA := frontBorder_skew M v hM
  have he : replaceFirst A (t • (fun j => A 0 j)) = frontBorder M (t*v) := by
    funext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [replaceFirst,A]
  have he' : replaceFirst A (fun j => A 0 j) = A := by
    funext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp [replaceFirst,A]
  have h := pfaffian_replaceFirst_smul A hA (fun j => A 0 j) (by simp [A]) t
  calc
    _ = pfaffian (replaceFirst A (t • (fun j => A 0 j))) := congrArg pfaffian he.symm
    _ = _ := h
    _ = _ := congrArg (fun X => t * pfaffian X) he'

 

theorem pfaffian_front_back {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*m+1)) (Fin (2*m+1)) K) (hM : ∀ i j, M j i = -M i j) :
    pfaffian (frontBorder M 1) = pfaffian (backBorder M) := by
  have h := pfaffian_reindex (backBorder M) (finRotate (2*m+1+1)).symm
  rw [backBorder_rotate] at h
  have hs : Equiv.Perm.sign (finRotate (2*m+1+1)).symm = -1 := by
    change Equiv.Perm.sign ((finRotate (2*m+1+1))⁻¹) = -1
    rw [Equiv.Perm.sign_inv,sign_finRotate]
    simp [pow_add,pow_mul]
  rw [hs] at h
  simp only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul] at h
  have hv := pfaffian_frontBorder_scale M hM (1:K) (-1)
  simp only [neg_one_mul] at hv
  rw [hv] at h
  exact neg_injective h

 

def tailRotateInv (n : ℕ) : Equiv.Perm (Fin (n+2)) :=
  Equiv.Perm.decomposeFin.symm (0,(finRotate (n+1)).symm)

@[simp] theorem tailRotateInv_zero (n : ℕ) : tailRotateInv n 0 = 0 := by
  simp [tailRotateInv]
@[simp] theorem tailRotateInv_one (n : ℕ) : tailRotateInv n 1 = (Fin.last n).succ := by
  simp only [tailRotateInv,Equiv.Perm.decomposeFin_symm_apply_one,Equiv.swap_self,
    Equiv.refl_apply,rotateInv_zero]
@[simp] theorem tailRotateInv_succ_succ {n : ℕ} (i : Fin n) :
    tailRotateInv n i.succ.succ = i.castSucc.succ := by
  simp only [tailRotateInv,Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.swap_self,
    Equiv.refl_apply,rotateInv_succ]

theorem sign_tailRotateInv (n : ℕ) : Equiv.Perm.sign (tailRotateInv n) = (-1)^n := by
  rw [tailRotateInv,Equiv.Perm.decomposeFin.symm_sign,ite_eq_left rfl,one_mul]
  change Equiv.Perm.sign ((finRotate (n+1))⁻¹) = _
  rw [Equiv.Perm.sign_inv,sign_finRotate,Nat.add_sub_cancel]

 

theorem pfaffian_doubleBorder {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) (hM : ∀ i j, M j i = -M i j) :
    pfaffian (frontBorder (backBorder M) 1) = pfaffian M := by
  let A := frontBorder (backBorder M) 1
  let r : Fin (2*m+2) := (Fin.last (2*m)).succ
  let v := fun j => if j = 0 then 0 else A 0 j + A r j
  let B := replaceFirst A v
  let σ := tailRotateInv (2*m)
  let T := fun i j => B (σ i) (σ j)
  have hA : ∀ i j, A j i = -A i j := frontBorder_skew _ _ (backBorder_skew M hM)
  have hv : v 0 = 0 := by simp [v]
  have hB : ∀ i j, B j i = -B i j := replaceFirst_skew A hA v hv
  have hT : ∀ i j, T j i = -T i j := fun i j => hB (σ i) (σ j)
  have hzero : ∀ j, j ≠ 1 → T 0 j = 0 := by
    intro j hj
    induction j using Fin.cases with
    | zero => simp only [T,σ,tailRotateInv_zero,B,replaceFirst_row,hv]
    | succ j =>
      induction j using Fin.cases with
      | zero => exact (hj rfl).elim
      | succ j =>
        simp only [T,σ,tailRotateInv_zero,tailRotateInv_succ_succ,B,replaceFirst_row,v,
          Fin.succ_ne_zero,ite_false,A,frontBorder_zero_succ,r,frontBorder_succ_succ,
          backBorder_last_cast,add_neg_cancel]
  have h01 : T 0 1 = 1 := by
    simp only [T,σ,tailRotateInv_zero,tailRotateInv_one,B,replaceFirst_row,v,
      Fin.succ_ne_zero,ite_false,A,frontBorder_zero_succ,r,frontBorder_succ_succ,
      backBorder_last_last,add_zero]
  have htail : (fun i j : Fin (2*m) => T i.succ.succ j.succ.succ) = M := by
    funext i j
    simp only [T,σ,tailRotateInv_succ_succ,B,replaceFirst_rest,A,
      frontBorder_succ_succ,backBorder_cast_cast]
  have hep : pfaffian T = pfaffian M := by
    have h := pfaffian_isolated T hT hzero
    apply Eq.trans h
    apply Eq.trans (congrArg (fun z => z * pfaffian (fun i j : Fin (2*m) =>
      T i.succ.succ j.succ.succ)) h01)
    rw [one_mul]
    exact congrArg pfaffian htail
  have hσ : Equiv.Perm.sign σ = 1 := by simp [σ,sign_tailRotateInv,pow_mul]
  have htp : pfaffian T = pfaffian B := by
    have h := pfaffian_reindex B σ
    change pfaffian T = _ at h
    simpa only [hσ,Units.val_one,Int.cast_one,one_mul] using h
  have hbp : pfaffian B = pfaffian A := by
    apply Eq.trans ?_ (pfaffian_firstRow_add_other A hA r (Fin.succ_ne_zero _) 1)
    congr 1
    funext i j
    simp only [B,v,one_mul,replaceFirst]
  exact hbp.symm.trans (htp.symm.trans hep)


 

 


theorem back_front_row {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (t : K) (j : Fin (n+1)) :
    backBorder (frontBorder M t) 0 j.succ = Fin.lastCases 1 (fun _ => t) j := by
  change backBorder (frontBorder M t) (0 : Fin (n+1)).castSucc j.succ = _
  induction j using Fin.lastCases with
  | last => rw [Fin.succ_last,backBorder_cast_last]; simp only [Fin.lastCases_last]
  | cast j => rw [Fin.succ_castSucc,backBorder_cast_cast]; simp only [frontBorder_zero_succ,Fin.lastCases_castSucc]

theorem back_front_tail {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (t : K) (i j : Fin (n+1)) :
    backBorder (frontBorder M t) i.succ j.succ = backBorder M i j := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [Fin.succ_last,Fin.succ_castSucc,backBorder_last_last,backBorder_last_cast,
      backBorder_cast_last,backBorder_cast_cast,frontBorder_succ_succ]

theorem back_front_eq_rowAdd {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, M j i = -M i j) (t : K) :
    backBorder (frontBorder M t) =
      replaceFirst (frontBorder (backBorder M) 1)
        (fun j => if j = 0 then 0 else frontBorder (backBorder M) 1 0 j +
          (1-t)*frontBorder (backBorder M) 1 (Fin.last n).succ j) := by
  have hsk := backBorder_skew _ (frontBorder_skew M t hM)
  funext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero =>
      change backBorder (frontBorder M t) (0 : Fin (n+1)).castSucc (0 : Fin (n+1)).castSucc = _
      rw [backBorder_cast_cast, frontBorder_zero_zero]
      simp only [replaceFirst, ite_true]
    | succ j =>
      rw [back_front_row]
      induction j using Fin.lastCases <;>
        simp only [replaceFirst,Fin.succ_ne_zero,ite_true,ite_false,
          frontBorder_zero_succ,frontBorder_succ_succ,backBorder_last_last,
          backBorder_last_cast,Fin.lastCases_last,Fin.lastCases_castSucc] <;> ring
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      rw [hsk 0 i.succ,back_front_row]
      induction i using Fin.lastCases <;>
        simp only [replaceFirst,Fin.succ_ne_zero,ite_true,ite_false,
          frontBorder_zero_succ,frontBorder_succ_succ,backBorder_last_last,
          backBorder_last_cast,Fin.lastCases_last,Fin.lastCases_castSucc] <;> ring
    | succ j => rw [back_front_tail]; simp [replaceFirst]

 

theorem pfaffian_back_front {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) (hM : ∀ i j, M j i = -M i j) (t : K) :
    pfaffian (backBorder (frontBorder M t)) = pfaffian M := by
  apply Eq.trans (congrArg pfaffian (back_front_eq_rowAdd M hM t))
  apply Eq.trans (pfaffian_firstRow_add_other _
    (frontBorder_skew _ _ (backBorder_skew M hM)) (Fin.last (2*m)).succ (Fin.succ_ne_zero _) (1-t))
  exact pfaffian_doubleBorder M hM

def plainKernel {K : Type*} [Field K] {n : ℕ} (dd rr : K) (a : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => (a i-a j)*(a i+a j+rr)/discriminant dd (a i) (a j)

theorem plainKernel_skew {K : Type*} [Field K] {n : ℕ} (dd rr : K) (a : Fin n → K) :
    ∀ i j, plainKernel dd rr a j i = -plainKernel dd rr a i j := by
  intro i j
  unfold plainKernel discriminant
  have hD : a j^2+a i^2+2*dd*a j*a i-dd^2 = a i^2+a j^2+2*dd*a i*a j-dd^2 := by ring
  rw [hD,← neg_div]
  congr 1
  ring

theorem pfaffian_augmented_even {K : Type*} [Field K] (m : ℕ) (dd rr : K) (a : Fin (2*m) → K) :
    pfaffian (augmentedKernel dd rr a) = pfaffian (plainKernel dd rr a) := by
  have hs : 2*m+(2*m)%2 = 2*m := by omega
  apply Eq.trans (pfaffian_cast hs (augmentedKernel dd rr a)).symm
  congr 1
  funext i j
  simp only [augmentedKernel,Fin.val_cast,i.isLt,j.isLt,dite_eq_left]
  rfl

theorem pfaffian_augmented_odd {K : Type*} [Field K] (m : ℕ) (dd rr : K) (a : Fin (2*m+1) → K) :
    pfaffian (augmentedKernel dd rr a) = pfaffian (backBorder (plainKernel dd rr a)) := by
  have hs : (2*m+1)+(2*m+1)%2 = (2*m+1)+1 := by omega
  apply Eq.trans (pfaffian_cast hs (augmentedKernel dd rr a)).symm
  congr 1
  funext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [augmentedKernel,Fin.val_cast,Fin.val_last,Fin.val_castSucc,
      lt_self_iff_false,dite_false,ite_true,ite_false,Fin.isLt,dite_eq_left,backBorder_last_last,
      backBorder_last_cast,backBorder_cast_last,backBorder_cast_cast,plainKernel]

end
end CriticalStrip.Diagram

end OAI
