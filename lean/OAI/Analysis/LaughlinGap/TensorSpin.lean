import Mathlib
import OAI.Analysis.LaughlinGap.SpinWork

namespace OAI

/-! Tensor Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def ladderStep (n : ℕ) (p : Fin n) : ℝ :=
  Real.sqrt (((p.val : ℝ)+1) * ((n : ℝ)-p.val))

lemma ladderStep_sq (n : ℕ) (p : Fin n) :
    ladderStep n p ^ 2 = ((p.val : ℝ)+1) * ((n : ℝ)-p.val) := by
  have h : (p.val : ℝ) ≤ n := by exact_mod_cast p.isLt.le
  exact Real.sq_sqrt (mul_nonneg (by positivity) (by linarith))

noncomputable def lowering (n : ℕ) : Module.End ℝ (Fin (n+1) → ℝ) where
  toFun x := Fin.cases 0 (fun p => ladderStep n p * x p.castSucc)
  map_add' x y := by
    funext p
    cases p using Fin.cases <;> simp [mul_add]
  map_smul' r x := by
    funext p
    cases p using Fin.cases <;> simp [mul_left_comm]

noncomputable def raising (n : ℕ) : Module.End ℝ (Fin (n+1) → ℝ) where
  toFun x := Fin.lastCases 0 (fun p => ladderStep n p * x p.succ)
  map_add' x y := by
    funext p
    cases p using Fin.lastCases <;> simp [mul_add]
  map_smul' r x := by
    funext p
    cases p using Fin.lastCases <;> simp [mul_left_comm]

noncomputable def weight (n : ℕ) : Module.End ℝ (Fin (n+1) → ℝ) where
  toFun x p := ((n : ℝ)-2*p.val) * x p
  map_add' x y := by funext p; simp [mul_add]
  map_smul' r x := by funext p; simp [mul_left_comm]

@[simp] lemma lowering_zero (n : ℕ) (x : Fin (n+1) → ℝ) : lowering n x 0 = 0 := rfl
@[simp] lemma lowering_succ (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin n) :
    lowering n x p.succ = ladderStep n p * x p.castSucc := rfl
@[simp] lemma raising_castSucc (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin n) :
    raising n x p.castSucc = ladderStep n p * x p.succ := by simp [raising]
@[simp] lemma raising_last (n : ℕ) (x : Fin (n+1) → ℝ) :
    raising n x (Fin.last n) = 0 := by simp [raising]
@[simp] lemma weight_apply (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin (n+1)) :
    weight n x p = ((n : ℝ)-2*p.val) * x p := rfl

lemma raising_lowering_apply (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin (n+1)) :
    raising n (lowering n x) p =
      (((p.val : ℝ)+1) * ((n : ℝ)-p.val)) * x p := by
  cases p using Fin.lastCases with
  | last => simp
  | cast p =>
    rw [raising_castSucc, lowering_succ, ← mul_assoc, ← pow_two, ladderStep_sq]
    rfl

lemma lowering_raising_apply (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin (n+1)) :
    lowering n (raising n x) p =
      ((p.val : ℝ) * ((n : ℝ)-p.val+1)) * x p := by
  cases p using Fin.cases with
  | zero => simp
  | succ p =>
    rw [lowering_succ, raising_castSucc, ← mul_assoc, ← pow_two, ladderStep_sq]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem raising_lowering_commutator (n : ℕ) (x : Fin (n+1) → ℝ) :
    raising n (lowering n x) = lowering n (raising n x) + weight n x := by
  funext p
  simp only [raising_lowering_apply, lowering_raising_apply, Pi.add_apply, weight_apply]
  ring

theorem weight_lowering_commutator (n : ℕ) (x : Fin (n+1) → ℝ) :
    weight n (lowering n x) = lowering n (weight n x) - (2 : ℝ) • lowering n x := by
  funext p
  cases p using Fin.cases with
  | zero => simp
  | succ p =>
    simp only [weight_apply, lowering_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring

theorem lowering_raising_dot (n : ℕ) (x y : Fin (n+1) → ℝ) :
    dotProduct (lowering n x) y = dotProduct x (raising n y) := by
  unfold dotProduct
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [lowering_zero, zero_mul, zero_add, lowering_succ, raising_last, mul_zero,
    add_zero, raising_castSucc]
  apply Finset.sum_congr rfl
  intro p hp
  ring

structure LadderSystem (ι : Type*) [Fintype ι] where
  lower : Module.End ℝ (ι → ℝ)
  raise : Module.End ℝ (ι → ℝ)
  weight : Module.End ℝ (ι → ℝ)
  adjoint : ∀ x y, dotProduct (lower x) y = dotProduct x (raise y)
  raise_lower : ∀ x, raise (lower x) = lower (raise x) + weight x
  weight_lower : ∀ x, weight (lower x) = lower (weight x) - (2 : ℝ) • lower x

noncomputable def standardLadderSystem (n : ℕ) : LadderSystem (Fin (n+1)) where
  lower := lowering n
  raise := raising n
  weight := weight n
  adjoint := lowering_raising_dot n
  raise_lower := raising_lowering_commutator n
  weight_lower := weight_lowering_commutator n

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

noncomputable def raw (S : LadderSystem ι) (x : ι → ℝ) (l : ℕ) : ι → ℝ :=
  (S.lower ^ l) x

@[simp] lemma raw_zero (S : LadderSystem ι) (x : ι → ℝ) : S.raw x 0 = x := rfl
lemma raw_succ (S : LadderSystem ι) (x : ι → ℝ) (l : ℕ) :
    S.raw x (l+1) = S.lower (S.raw x l) := by rw [raw, pow_succ']; rfl

lemma weight_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hx : S.weight x = μ • x) (l : ℕ) :
    S.weight (S.raw x l) = (μ - 2*l) • S.raw x l := by
  induction l with
  | zero => simpa using hx
  | succ l ih =>
    rw [raw_succ, S.weight_lower, ih, map_smul, ← sub_smul,
      Nat.cast_add, Nat.cast_one]
    congr 1
    ring

lemma raise_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hx : S.weight x = μ • x) (he : S.raise x = 0) (l : ℕ) :
    S.raise (S.raw x (l+1)) = (((l : ℝ)+1)*(μ-l)) • S.raw x l := by
  induction l with
  | zero => simpa [raw_succ, S.raise_lower, he] using hx
  | succ l ih =>
    rw [raw_succ, S.raise_lower, ih, S.weight_raw hx (l+1), map_smul,
      ← raw_succ, ← add_smul, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem raw_norm_sq (S : LadderSystem ι) {x : ι → ℝ} {d l : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (hl : l ≤ d+1) :
    dotProduct (S.raw x l) (S.raw x l) =
      (l.factorial : ℝ) * (d.descFactorial l : ℝ) * dotProduct x x := by
  induction l with
  | zero => simp [dotProduct]
  | succ l ih =>
    have hld : l ≤ d := by omega
    rw [raw_succ, S.adjoint, ← raw_succ, S.raise_raw hw he]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    have hsum : (∑ i : ι, S.raw x l i *
        ((((l : ℝ)+1)*((d : ℝ)-l))*S.raw x l i)) =
        (((l : ℝ)+1)*((d : ℝ)-l)) * dotProduct (S.raw x l) (S.raw x l) := by
      simp only [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, ih (by omega), Nat.factorial_succ, Nat.descFactorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sub hld]
    unfold dotProduct
    ring

noncomputable def normalizationFactor (d l : ℕ) : ℝ :=
  (l.factorial : ℝ) * (d.descFactorial l : ℝ)

lemma normalizationFactor_pos {d l : ℕ} (hl : l ≤ d) :
    0 < normalizationFactor d l :=
  mul_pos (by exact_mod_cast l.factorial_pos)
    (by exact_mod_cast Nat.descFactorial_pos.mpr hl)

lemma normalizationFactor_succ {d l : ℕ} (hl : l ≤ d) :
    normalizationFactor d (l+1) =
      (((l : ℝ)+1)*((d : ℝ)-l)) * normalizationFactor d l := by
  rw [normalizationFactor, Nat.factorial_succ, Nat.descFactorial_succ,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hl, Nat.cast_add, Nat.cast_one]
  unfold normalizationFactor
  ring

noncomputable def normalized (S : LadderSystem ι) (x : ι → ℝ) (d l : ℕ) : ι → ℝ :=
  (1 / Real.sqrt (normalizationFactor d l)) • S.raw x l

@[simp] lemma normalized_zero (S : LadderSystem ι) (x : ι → ℝ) (d : ℕ) :
    S.normalized x d 0 = x := by simp [normalized, normalizationFactor]

lemma normalized_succ (S : LadderSystem ι) (x : ι → ℝ) {d l : ℕ} (hl : l < d) :
    S.normalized x d (l+1) =
      (1 / Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l))) • S.lower (S.normalized x d l) := by
  have hα : 0 ≤ ((l : ℝ)+1)*((d : ℝ)-l) := by
    have hld : (l : ℝ) < d := by exact_mod_cast hl
    positivity
  simp only [normalized, raw_succ, normalizationFactor_succ hl.le,
    Real.sqrt_mul hα, map_smul, smul_smul, one_div_mul_one_div]

lemma normalized_weight (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (l : ℕ) :
    S.weight (S.normalized x d l) = ((d : ℝ)-2*l) • S.normalized x d l := by
  simp only [normalized, map_smul, S.weight_raw hw]
  exact smul_comm _ _ _

theorem normalized_norm_sq (S : LadderSystem ι) {x : ι → ℝ} {d l : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (hl : l ≤ d) :
    dotProduct (S.normalized x d l) (S.normalized x d l) = dotProduct x x := by
  have hf : 0 < normalizationFactor d l := normalizationFactor_pos hl
  have hs : Real.sqrt (normalizationFactor d l) ≠ 0 := (Real.sqrt_pos.mpr hf).ne'
  have heq := Real.sq_sqrt hf.le
  simp only [normalized, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    S.raw_norm_sq hw he (by omega : l ≤ d+1)]
  change (1 / Real.sqrt (normalizationFactor d l)) *
    ((1 / Real.sqrt (normalizationFactor d l)) *
      (normalizationFactor d l * dotProduct x x)) = dotProduct x x
  field_simp
  rw [heq]

end LadderSystem

noncomputable def onFirstEnd {ι κ : Type*} (A : Module.End ℝ (ι → ℝ)) :
    Module.End ℝ ((ι × κ) → ℝ) where
  toFun x pq := A (fun p => x (p, pq.2)) pq.1
  map_add' x y := by
    funext pq
    exact congrFun (A.map_add (fun p => x (p,pq.2)) (fun p => y (p,pq.2))) pq.1
  map_smul' r x := by
    funext pq
    exact congrFun (A.map_smul r (fun p => x (p,pq.2))) pq.1

noncomputable def onSecondEnd {ι κ : Type*} (A : Module.End ℝ (κ → ℝ)) :
    Module.End ℝ ((ι × κ) → ℝ) where
  toFun x pq := A (fun q => x (pq.1, q)) pq.2
  map_add' x y := by
    funext pq
    exact congrFun (A.map_add (fun q => x (pq.1,q)) (fun q => y (pq.1,q))) pq.2
  map_smul' r x := by
    funext pq
    exact congrFun (A.map_smul r (fun q => x (pq.1,q))) pq.2

@[simp] lemma onFirstEnd_apply {ι κ : Type*} (A : Module.End ℝ (ι → ℝ))
    (x : (ι × κ) → ℝ) (p : ι) (q : κ) :
    onFirstEnd A x (p,q) = A (fun i => x (i,q)) p := rfl

@[simp] lemma onSecondEnd_apply {ι κ : Type*} (A : Module.End ℝ (κ → ℝ))
    (x : (ι × κ) → ℝ) (p : ι) (q : κ) :
    onSecondEnd A x (p,q) = A (fun j => x (p,j)) q := rfl

lemma tensor_factor_commute {ι κ : Type*} [Fintype ι]
    (A : Module.End ℝ (ι → ℝ)) (B : Module.End ℝ (κ → ℝ)) (x : (ι×κ) → ℝ) :
    onFirstEnd A (onSecondEnd B x) = onSecondEnd B (onFirstEnd A x) := by
  classical
  funext ⟨p,q⟩
  simp only [onFirstEnd_apply, onSecondEnd_apply]
  have hfun : (fun j => A (fun i => x (i,j)) p) =
      ∑ i : ι, (A (fun k => if i = k then 1 else 0) p) • (fun j => x (i,j)) := by
    funext j
    rw [A.pi_apply_eq_sum_univ (fun i => x (i,j))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, map_sum, A.pi_apply_eq_sum_univ (fun i => B (fun j => x (i,j)) q)]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

namespace LadderSystem
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def onFirst (S : LadderSystem ι) : LadderSystem (ι × κ) where
  lower := onFirstEnd S.lower
  raise := onFirstEnd S.raise
  weight := onFirstEnd S.weight
  adjoint x y := by
    simp only [dotProduct, Fintype.sum_prod_type, onFirstEnd_apply]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun p q => x (p,q) * S.raise (fun i => y (i,q)) p)]
    apply Finset.sum_congr rfl
    intro q hq
    exact S.adjoint (fun p => x (p,q)) (fun p => y (p,q))
  raise_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.raise_lower (fun i => x (i,q))) p
  weight_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.weight_lower (fun i => x (i,q))) p

noncomputable def onSecond (S : LadderSystem κ) : LadderSystem (ι × κ) where
  lower := onSecondEnd S.lower
  raise := onSecondEnd S.raise
  weight := onSecondEnd S.weight
  adjoint x y := by
    simp only [dotProduct, Fintype.sum_prod_type, onSecondEnd_apply]
    apply Finset.sum_congr rfl
    intro p hp
    exact S.adjoint (fun q => x (p,q)) (fun q => y (p,q))
  raise_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.raise_lower (fun j => x (p,j))) q
  weight_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.weight_lower (fun j => x (p,j))) q

noncomputable def tensor (S : LadderSystem ι) (T : LadderSystem κ) :
    LadderSystem (ι × κ) where
  lower := onFirstEnd S.lower + onSecondEnd T.lower
  raise := onFirstEnd S.raise + onSecondEnd T.raise
  weight := onFirstEnd S.weight + onSecondEnd T.weight
  adjoint x y := by
    simp only [LinearMap.add_apply, add_dotProduct, dotProduct_add]
    exact congrArg₂ (· + ·) (S.onFirst.adjoint x y) (T.onSecond.adjoint x y)
  raise_lower x := by
    simp only [LinearMap.add_apply, map_add]
    rw [show onFirstEnd S.raise (onFirstEnd S.lower x) =
        onFirstEnd S.lower (onFirstEnd S.raise x) + onFirstEnd S.weight x from
          S.onFirst.raise_lower x,
      show onSecondEnd T.raise (onSecondEnd T.lower x) =
        onSecondEnd T.lower (onSecondEnd T.raise x) + onSecondEnd T.weight x from
          T.onSecond.raise_lower x,
      tensor_factor_commute S.raise T.lower x, ← tensor_factor_commute S.lower T.raise x]
    abel
  weight_lower x := by
    simp only [LinearMap.add_apply, map_add, smul_add]
    rw [show onFirstEnd S.weight (onFirstEnd S.lower x) =
        onFirstEnd S.lower (onFirstEnd S.weight x) - (2 : ℝ) • onFirstEnd S.lower x from
          S.onFirst.weight_lower x,
      show onSecondEnd T.weight (onSecondEnd T.lower x) =
        onSecondEnd T.lower (onSecondEnd T.weight x) - (2 : ℝ) • onSecondEnd T.lower x from
          T.onSecond.weight_lower x,
      tensor_factor_commute S.weight T.lower x, ← tensor_factor_commute S.lower T.weight x]
    abel

end LadderSystem

noncomputable def tensorSpin (n m : ℕ) : LadderSystem (Fin (n+1) × Fin (m+1)) :=
  (standardLadderSystem n).tensor (standardLadderSystem m)

noncomputable def highestTensor (n m z : ℕ) : (Fin (n+1) × Fin (m+1)) → ℝ :=
  fun pq => if pq.1.val + pq.2.val = z then highestCoefficient n m z pq.1.val else 0

noncomputable def coupledTensor (n m z l : ℕ) : (Fin (n+1) × Fin (m+1)) → ℝ :=
  fun pq => if pq.1.val + pq.2.val = z+l then coupledCoefficient n m z l pq.1.val else 0

@[simp] lemma coupledTensor_zero (n m z : ℕ) : coupledTensor n m z 0 = highestTensor n m z := by
  rfl

lemma tensorSpin_weight (n m : ℕ) (x : (Fin (n+1) × Fin (m+1)) → ℝ)
    (p : Fin (n+1)) (q : Fin (m+1)) :
    (tensorSpin n m).weight x (p,q) = ((n : ℝ)+m-2*(p.val+q.val)) * x (p,q) := by
  simp only [tensorSpin, LadderSystem.tensor, standardLadderSystem,
    LinearMap.add_apply, onFirstEnd_apply, onSecondEnd_apply, Pi.add_apply, weight_apply]
  ring

lemma tensorSpin_lower (n m : ℕ) (x : (Fin (n+1) × Fin (m+1)) → ℝ)
    (p : Fin (n+1)) (q : Fin (m+1)) :
    (tensorSpin n m).lower x (p,q) =
      lowering n (fun i => x (i,q)) p + lowering m (fun j => x (p,j)) q := rfl

lemma tensorSpin_raise (n m : ℕ) (x : (Fin (n+1) × Fin (m+1)) → ℝ)
    (p : Fin (n+1)) (q : Fin (m+1)) :
    (tensorSpin n m).raise x (p,q) =
      raising n (fun i => x (i,q)) p + raising m (fun j => x (p,j)) q := rfl

lemma raising_apply_of_lt {n : ℕ} (x : Fin (n+1) → ℝ) (p : Fin (n+1))
    (hp : p.val < n) :
    raising n x p =
      Real.sqrt (((p.val : ℝ)+1)*((n : ℝ)-p.val)) * x ⟨p.val+1,by omega⟩ := by
  exact raising_castSucc n x ⟨p.val,hp⟩

lemma raising_apply_of_not_lt {n : ℕ} (x : Fin (n+1) → ℝ) (p : Fin (n+1))
    (hp : ¬p.val < n) : raising n x p = 0 := by
  have he : p = Fin.last n := by ext; simp only [Fin.val_last]; omega
  rw [he, raising_last]

theorem highestTensor_weight {n m z : ℕ} (hz : z ≤ min n m) :
    (tensorSpin n m).weight (highestTensor n m z) =
      ((n+m-2*z : ℕ) : ℝ) • highestTensor n m z := by
  have hzn : z ≤ n := (le_min_iff.mp hz).1
  have hzm : z ≤ m := (le_min_iff.mp hz).2
  have hzsum : 2*z ≤ n+m := by omega
  funext ⟨p,q⟩
  rw [tensorSpin_weight]
  simp only [highestTensor, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · have hc : (p.val : ℝ)+q.val = z := by exact_mod_cast h
    rw [hc, Nat.cast_sub hzsum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  · simp

theorem highestTensor_raise {n m z : ℕ} (hz : z ≤ min n m) :
    (tensorSpin n m).raise (highestTensor n m z) = 0 := by
  have hzn : z ≤ n := (le_min_iff.mp hz).1
  have hzm : z ≤ m := (le_min_iff.mp hz).2
  funext ⟨p,q⟩
  rw [tensorSpin_raise]
  by_cases h : p.val+q.val+1 = z
  · have hp : p.val < n := by omega
    have hq : q.val < m := by omega
    rw [raising_apply_of_lt _ p hp, raising_apply_of_lt _ q hq]
    simp only [highestTensor, show p.val+1+q.val = z by omega,
      show p.val+(q.val+1) = z by omega, ite_true, Pi.zero_apply]
    have hc : (p.val : ℝ)+q.val+1 = z := by exact_mod_cast h
    have he : Real.sqrt (((q.val : ℝ)+1)*((m : ℝ)-q.val)) =
        Real.sqrt (((z : ℝ)-p.val)*((m : ℝ)-z+p.val+1)) := by
      congr 1
      rw [← hc]
      ring
    rw [he]
    simpa only [mul_comm] using highestCoefficient_raising hz (by omega : p.val < z)
  · have h₁ : raising n (fun i => highestTensor n m z (i,q)) p = 0 := by
      by_cases hp : p.val < n
      · rw [raising_apply_of_lt _ p hp]
        simp [highestTensor, show ¬ (p.val+1+q.val = z) by omega]
      · exact raising_apply_of_not_lt _ p hp
    have h₂ : raising m (fun j => highestTensor n m z (p,j)) q = 0 := by
      by_cases hq : q.val < m
      · rw [raising_apply_of_lt _ q hq]
        simp [highestTensor, show ¬ (p.val+(q.val+1) = z) by omega]
      · exact raising_apply_of_not_lt _ q hq
    simp only [h₁, h₂, zero_add, Pi.zero_apply]

theorem highestTensor_norm_sq {n m z : ℕ} (hz : z ≤ min n m) :
    dotProduct (highestTensor n m z) (highestTensor n m z) = 1 := by
  have hzn : z ≤ n := (le_min_iff.mp hz).1
  have hzm : z ≤ m := (le_min_iff.mp hz).2
  have hinner (p : Fin (n+1)) :
      (∑ q : Fin (m+1), highestTensor n m z (p,q) * highestTensor n m z (p,q)) =
        highestCoefficient n m z p.val ^ 2 := by
    by_cases hp : p.val ≤ z
    · let q₀ : Fin (m+1) := ⟨z-p.val, by omega⟩
      rw [Finset.sum_eq_single q₀]
      · simp only [highestTensor, show p.val+q₀.val = z by dsimp [q₀]; omega,
          ite_true, pow_two]
      · intro q hq hne
        have hne' : p.val+q.val ≠ z := by
          intro he
          apply hne
          ext
          dsimp [q₀]
          omega
        simp [highestTensor, hne']
      · simp
    · have hpz : z < p.val := by omega
      rw [highestCoefficient_eq_zero hpz, zero_pow (by omega : (2:ℕ) ≠ 0)]
      apply Finset.sum_eq_zero
      intro q hq
      simp [highestTensor, show p.val+q.val ≠ z by omega]
  unfold dotProduct
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun p => highestCoefficient n m z p ^ 2) (n+1)]
  calc
    _ = ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : z+1 ≤ n+1))
      intro p hp hpn
      simp only [Finset.mem_range, not_lt] at hpn
      rw [highestCoefficient_eq_zero (by omega : z < p), zero_pow (by omega : (2:ℕ) ≠ 0)]
    _ = 1 := highestCoefficient_sum_sq hz

lemma firstLoweringCoefficient_succ (n m z l : ℕ) (p : Fin n) :
    firstLoweringCoefficient n m z l p.succ.val =
      ladderStep n p / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l)) := by
  unfold firstLoweringCoefficient ladderStep
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

lemma secondLoweringCoefficient_succ {n m z l : ℕ} (p : Fin (n+1)) (q : Fin m)
    (h : p.val+q.succ.val = z+(l+1)) :
    secondLoweringCoefficient n m z l p.val =
      ladderStep m q / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l)) := by
  have hc : (p.val : ℝ)+q.val+1 = (z : ℝ)+l+1 := by
    have he : p.val+q.val+1 = z+l+1 := by simpa [Nat.add_assoc] using h
    exact_mod_cast he
  unfold secondLoweringCoefficient ladderStep
  congr 2
  congr 1 <;> linarith

lemma secondLoweringCoefficient_last {n m z l : ℕ} {p : Fin (n+1)}
    (h : p.val = z+(l+1)) : secondLoweringCoefficient n m z l p.val = 0 := by
  have hc : (p.val : ℝ) = (z : ℝ)+l+1 := by exact_mod_cast h
  unfold secondLoweringCoefficient
  rw [show (z : ℝ)+l-p.val+1 = 0 by linarith]
  simp

theorem coupledTensor_succ (n m z l : ℕ) :
    coupledTensor n m z (l+1) =
      (1 / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l))) •
        (tensorSpin n m).lower (coupledTensor n m z l) := by
  funext ⟨p,q⟩
  simp only [Pi.smul_apply, smul_eq_mul, tensorSpin_lower]
  by_cases h : p.val+q.val = z+(l+1)
  · rw [coupledTensor, ite_eq_left h, coupledCoefficient]
    cases p using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, ↓reduceIte, zero_add, lowering_zero]
      cases q using Fin.cases with
      | zero => simp only [Fin.val_zero] at h; omega
      | succ q =>
        have hs := secondLoweringCoefficient_succ (0 : Fin (n+1)) q h
        simp only [Fin.val_zero] at hs
        rw [lowering_succ, hs]
        simp only [coupledTensor, Fin.val_zero, Fin.val_castSucc, zero_add,
          show q.val = z+l by simp only [Fin.val_zero, Fin.val_succ] at h; omega, ite_true]
        ring
    | succ p =>
      simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel, lowering_succ]
      rw [show firstLoweringCoefficient n m z l (p.val+1) =
          ladderStep n p / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l)) from
        firstLoweringCoefficient_succ n m z l p]
      cases q using Fin.cases with
      | zero =>
        have hs := secondLoweringCoefficient_last (m := m)
          (by simpa using h : p.succ.val = z+(l+1))
        simp only [Fin.val_succ] at hs
        rw [hs, lowering_zero]
        simp only [zero_mul, add_zero, coupledTensor, Fin.val_castSucc, Fin.val_zero,
          add_zero, ite_eq_left (by simp only [Fin.val_succ, Fin.val_zero] at h; omega : p.val = z+l)]
        ring
      | succ q =>
        have hs := secondLoweringCoefficient_succ p.succ q h
        simp only [Fin.val_succ] at hs
        rw [lowering_succ, hs]
        have h₁ : p.val+(q.val+1) = z+l := by simp only [Fin.val_succ] at h; omega
        have h₂ : p.val+1+q.val = z+l := by simp only [Fin.val_succ] at h; omega
        simp only [coupledTensor, Fin.val_castSucc, Fin.val_succ, ite_eq_left h₁, ite_eq_left h₂]
        ring
  · rw [coupledTensor, ite_eq_right h]
    have h₁ : lowering n (fun i => coupledTensor n m z l (i,q)) p = 0 := by
      cases p using Fin.cases with
      | zero => rfl
      | succ p =>
        rw [lowering_succ]
        have hn : p.val+q.val ≠ z+l := by simp only [Fin.val_succ] at h; omega
        simp only [coupledTensor, Fin.val_castSucc, ite_eq_right hn, mul_zero]
    have h₂ : lowering m (fun j => coupledTensor n m z l (p,j)) q = 0 := by
      cases q using Fin.cases with
      | zero => rfl
      | succ q =>
        rw [lowering_succ]
        have hn : p.val+q.val ≠ z+l := by simp only [Fin.val_succ] at h; omega
        simp only [coupledTensor, Fin.val_castSucc, ite_eq_right hn, mul_zero]
    simp only [h₁, h₂, zero_add, mul_zero]

theorem coupledTensor_eq_normalized {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    coupledTensor n m z l = (tensorSpin n m).normalized (highestTensor n m z) (n+m-2*z) l := by
  have hzsum : 2*z ≤ n+m := by have := le_min_iff.mp hz; omega
  induction l with
  | zero => simp
  | succ l ih =>
    rw [coupledTensor_succ, ih (by omega), LadderSystem.normalized_succ _ _ (by omega)]
    simp only [Nat.cast_sub hzsum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem coupledTensor_norm_sq {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    dotProduct (coupledTensor n m z l) (coupledTensor n m z l) = 1 := by
  rw [coupledTensor_eq_normalized hz hl, LadderSystem.normalized_norm_sq _
    (highestTensor_weight hz) (highestTensor_raise hz) hl, highestTensor_norm_sq hz]

theorem coupledTensor_weight {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    (tensorSpin n m).weight (coupledTensor n m z l) =
      (((n+m-2*z : ℕ) : ℝ)-2*l) • coupledTensor n m z l := by
  rw [coupledTensor_eq_normalized hz hl]
  exact LadderSystem.normalized_weight _ (highestTensor_weight hz) l

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

lemma raise_adjoint (S : LadderSystem ι) (x y : ι → ℝ) :
    dotProduct (S.raise x) y = dotProduct x (S.lower y) := by
  rw [dotProduct_comm, ← S.adjoint, dotProduct_comm]

lemma weight_eq (S : LadderSystem ι) (x : ι → ℝ) :
    S.weight x = S.raise (S.lower x) - S.lower (S.raise x) := by
  rw [S.raise_lower]
  abel

lemma weight_adjoint (S : LadderSystem ι) (x y : ι → ℝ) :
    dotProduct (S.weight x) y = dotProduct x (S.weight y) := by
  rw [S.weight_eq x, S.weight_eq y, sub_dotProduct, dotProduct_sub]
  simp only [S.raise_adjoint, S.adjoint]

noncomputable def casimir (S : LadderSystem ι) : Module.End ℝ (ι → ℝ) :=
  S.weight.comp S.weight + (2 : ℝ) • S.weight + (4 : ℝ) • S.lower.comp S.raise

lemma casimir_apply (S : LadderSystem ι) (x : ι → ℝ) :
    S.casimir x = S.weight (S.weight x) + (2 : ℝ) • S.weight x +
      (4 : ℝ) • S.lower (S.raise x) := rfl

lemma casimir_adjoint (S : LadderSystem ι) (x y : ι → ℝ) :
    dotProduct (S.casimir x) y = dotProduct x (S.casimir y) := by
  simp only [casimir_apply, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, S.weight_adjoint, S.adjoint, S.raise_adjoint]

lemma lower_raise_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hw : S.weight x = μ • x) (he : S.raise x = 0) (l : ℕ) :
    S.lower (S.raise (S.raw x l)) = ((l : ℝ)*(μ-l+1)) • S.raw x l := by
  cases l with
  | zero => simp [he]
  | succ l =>
    rw [S.raise_raw hw he, map_smul, raw_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    ring

lemma casimir_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hw : S.weight x = μ • x) (he : S.raise x = 0) (l : ℕ) :
    S.casimir (S.raw x l) = (μ*(μ+2)) • S.raw x l := by
  simp only [casimir_apply, S.lower_raise_raw hw he,
    map_smul, S.weight_raw hw, smul_smul, ← add_smul]
  congr 1
  ring

lemma casimir_normalized (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (l : ℕ) :
    S.casimir (S.normalized x d l) = ((d : ℝ)*(d+2)) • S.normalized x d l := by
  simp only [normalized, map_smul, S.casimir_raw hw he]
  exact smul_comm _ _ _

end LadderSystem

lemma dot_eq_zero_of_distinct_eigenvalues {ι : Type*} [Fintype ι]
    (A : Module.End ℝ (ι → ℝ)) (hA : ∀ x y, dotProduct (A x) y = dotProduct x (A y))
    {x y : ι → ℝ} {μ ν : ℝ} (hx : A x = μ • x) (hy : A y = ν • y) (hμν : μ ≠ ν) :
    dotProduct x y = 0 := by
  have h := hA x y
  rw [hx, hy, smul_dotProduct, dotProduct_smul] at h
  exact (mul_eq_zero.mp (show (μ-ν)*dotProduct x y = 0 by
    simp only [smul_eq_mul] at h; nlinarith)).resolve_left (sub_ne_zero.mpr hμν)

theorem coupledTensor_casimir {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    (tensorSpin n m).casimir (coupledTensor n m z l) =
      (((n+m-2*z : ℕ) : ℝ)*((n+m-2*z : ℕ)+2)) • coupledTensor n m z l := by
  rw [coupledTensor_eq_normalized hz hl]
  exact LadderSystem.casimir_normalized _ (highestTensor_weight hz) (highestTensor_raise hz) l

theorem coupledTensor_orthogonal_same_spin {n m z l k : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) (hk : k ≤ n+m-2*z) (hlk : l ≠ k) :
    dotProduct (coupledTensor n m z l) (coupledTensor n m z k) = 0 := by
  apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).weight_adjoint
    (coupledTensor_weight hz hl) (coupledTensor_weight hz hk)
  intro h
  apply hlk
  have H : (l : ℝ) = k := by linarith
  exact_mod_cast H

theorem coupledTensor_orthogonal_distinct_spin {n m z w l k : ℕ}
    (hz : z ≤ min n m) (hw : w ≤ min n m)
    (hl : l ≤ n+m-2*z) (hk : k ≤ n+m-2*w) (hzw : z ≠ w) :
    dotProduct (coupledTensor n m z l) (coupledTensor n m w k) = 0 := by
  apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).casimir_adjoint
    (coupledTensor_casimir hz hl) (coupledTensor_casimir hw hk)
  have hd : n+m-2*z ≠ n+m-2*w := by
    have := le_min_iff.mp hz
    have := le_min_iff.mp hw
    omega
  have hd' : ((n+m-2*z : ℕ) : ℝ) ≠ (n+m-2*w : ℕ) := by exact_mod_cast hd
  have hsum : 0 < ((n+m-2*z : ℕ) : ℝ)+(n+m-2*w : ℕ)+2 := by positivity
  intro he
  have hh : (((n+m-2*z : ℕ) : ℝ)-(n+m-2*w : ℕ)) *
      (((n+m-2*z : ℕ) : ℝ)+(n+m-2*w : ℕ)+2) = 0 := by nlinarith
  exact hd' (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hsum.ne'))

abbrev CoupledIndex (n m : ℕ) :=
  (z : Fin (min n m + 1)) × Fin (n+m-2*z.val+1)

noncomputable def coupledFamily (n m : ℕ) (i : CoupledIndex n m) :
    EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) :=
  WithLp.toLp 2 (coupledTensor n m i.1.val i.2.val)

theorem coupledFamily_orthonormal (n m : ℕ) : Orthonormal ℝ (coupledFamily n m) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨z,l⟩ ⟨w,k⟩
  simp only [coupledFamily, EuclideanSpace.inner_toLp_toLp, star_trivial]
  rw [dotProduct_comm]
  have hz : z.val ≤ min n m := by omega
  have hw : w.val ≤ min n m := by omega
  have hl : l.val ≤ n+m-2*z.val := by omega
  have hk : k.val ≤ n+m-2*w.val := by omega
  by_cases hzw : z = w
  · subst w
    by_cases hlk : l = k
    · subst k
      rw [ite_eq_left rfl]
      exact coupledTensor_norm_sq hz hl
    · rw [ite_eq_right (by simpa using hlk : (Sigma.mk z l : CoupledIndex n m) ≠ ⟨z,k⟩)]
      exact coupledTensor_orthogonal_same_spin hz hl hk (fun h => hlk (Fin.ext h))
  · rw [ite_eq_right (fun h => hzw (congrArg Sigma.fst h))]
    exact coupledTensor_orthogonal_distinct_spin hz hw hl hk (fun h => hzw (Fin.ext h))

theorem coupledIndex_card (n m : ℕ) : Fintype.card (CoupledIndex n m) = (n+1)*(m+1) := by
  let k := min n m
  have hz (z : Fin (k+1)) : 2*z.val ≤ n+m := by
    have hzn : z.val ≤ n := (Nat.le_of_lt_succ z.isLt).trans (min_le_left n m)
    have hzm : z.val ≤ m := (Nat.le_of_lt_succ z.isLt).trans (min_le_right n m)
    omega
  have hdim (z : Fin (k+1)) : ((n+m-2*z.val+1 : ℕ) : ℝ) =
      (n : ℝ)+m-2*z.val+1 := by
    rw [Nat.cast_add, Nat.cast_sub (hz z), Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
  have hid : (∑ z : Fin (k+1), (z.val : ℝ))*2 = ((k : ℝ)+1)*k := by
    rw [Fin.sum_univ_eq_sum_range]
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Finset.sum_range_id_mul_two (k+1))
    simpa only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using h
  simp only [CoupledIndex, Fintype.card_sigma, Fintype.card_fin]
  apply Nat.cast_injective (R := ℝ)
  change ((∑ z : Fin (k+1), (n+m-2*z.val+1) : ℕ) : ℝ) = (((n+1)*(m+1) : ℕ) : ℝ)
  rw [Nat.cast_sum]
  simp only [hdim, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  rcases le_total n m with h | h
  · have hk : (k : ℝ) = n := by exact_mod_cast min_eq_left h
    nlinarith
  · have hk : (k : ℝ) = m := by exact_mod_cast min_eq_right h
    nlinarith

noncomputable def coupledBasis (n m : ℕ) :
    OrthonormalBasis (CoupledIndex n m) ℝ (EuclideanSpace ℝ (Fin (n+1) × Fin (m+1))) := by
  letI : Nonempty (CoupledIndex n m) := ⟨⟨0,0⟩⟩
  have hc : Fintype.card (CoupledIndex n m) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1) × Fin (m+1))) := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    exact coupledIndex_card n m
  let b := basisOfOrthonormalOfCardEqFinrank (coupledFamily_orthonormal n m) hc
  exact b.toOrthonormalBasis (by simpa [b] using coupledFamily_orthonormal n m)

@[simp] theorem coupledBasis_apply (n m : ℕ) (i : CoupledIndex n m) :
    coupledBasis n m i = coupledFamily n m i := by
  simp [coupledBasis]

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

lemma raw_top_succ (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) : S.raw x (d+1) = 0 := by
  apply dotProduct_self_eq_zero.mp
  rw [S.raw_norm_sq hw he (by omega)]
  simp

lemma normalized_lower (S : LadderSystem ι) (x : ι → ℝ) {d l : ℕ} (hl : l < d) :
    S.lower (S.normalized x d l) =
      Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l)) • S.normalized x d (l+1) := by
  have hα : 0 < ((l : ℝ)+1)*((d : ℝ)-l) := by
    have hld : (l : ℝ) < d := by exact_mod_cast hl
    exact mul_pos (by positivity) (by linarith)
  rw [normalized_succ _ _ hl, smul_smul, mul_one_div_cancel (Real.sqrt_pos.mpr hα).ne', one_smul]

lemma normalized_lower_top (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) :
    S.lower (S.normalized x d d) = 0 := by
  rw [normalized, map_smul, ← raw_succ, S.raw_top_succ hw he, smul_zero]

lemma normalized_raise_zero (S : LadderSystem ι) {x : ι → ℝ} (he : S.raise x = 0) (d : ℕ) :
    S.raise (S.normalized x d 0) = 0 := by simp [he]

lemma normalized_raise_succ (S : LadderSystem ι) {x : ι → ℝ} {d l : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (hl : l < d) :
    S.raise (S.normalized x d (l+1)) =
      Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l)) • S.normalized x d l := by
  have hα : 0 < ((l : ℝ)+1)*((d : ℝ)-l) := by
    have hld : (l : ℝ) < d := by exact_mod_cast hl
    exact mul_pos (by positivity) (by linarith)
  have ha : Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l)) ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
  have hf : Real.sqrt (normalizationFactor d l) ≠ 0 :=
    (Real.sqrt_pos.mpr (normalizationFactor_pos hl.le)).ne'
  simp only [normalized, map_smul, S.raise_raw hw he, smul_smul,
    normalizationFactor_succ hl.le, Real.sqrt_mul hα.le]
  congr 1
  field_simp
  rw [Real.sq_sqrt hα.le]

noncomputable def embedding (S : LadderSystem ι) (x : ι → ℝ) (d : ℕ) :
    (Fin (d+1) → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun a := ∑ l : Fin (d+1), a l • S.normalized x d l.val
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t a := by simp [Finset.smul_sum, smul_smul]

lemma embedding_apply (S : LadderSystem ι) (x : ι → ℝ) (d : ℕ) (a : Fin (d+1) → ℝ) :
    S.embedding x d a = ∑ l : Fin (d+1), a l • S.normalized x d l.val := rfl

theorem embedding_lower (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (a : Fin (d+1) → ℝ) :
    S.lower (S.embedding x d a) = S.embedding x d (lowering d a) := by
  rw [embedding_apply, embedding_apply, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [map_smul, Fin.val_last, S.normalized_lower_top hw he,
    lowering_zero, zero_smul, smul_zero, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [S.normalized_lower _ l.isLt, lowering_succ]
  simp only [ladderStep, smul_smul]
  congr 1
  ring

theorem embedding_raise (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (a : Fin (d+1) → ℝ) :
    S.raise (S.embedding x d a) = S.embedding x d (raising d a) := by
  rw [embedding_apply, embedding_apply, map_sum, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [map_smul, Fin.val_zero, S.normalized_raise_zero he,
    raising_last, zero_smul, smul_zero, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [S.normalized_raise_succ hw he l.isLt, raising_castSucc]
  simp only [ladderStep, smul_smul]
  congr 1
  ring

theorem embedding_weight (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (a : Fin (d+1) → ℝ) :
    S.weight (S.embedding x d a) = S.embedding x d (LaughlinGap.Spin.weight d a) := by
  simp only [embedding_apply, map_sum, map_smul, S.normalized_weight hw, weight_apply,
    smul_smul]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  ring

end LadderSystem

end LaughlinGap.Spin

end

end OAI
