import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.StoredBits
import OAI.Combinatorics.ThinTrees.Normalization.Packing

namespace OAI

/-! Normalization algorithm. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder
variable {m d : ℕ}

def realColumns (v : Fin m → Fin d → ℚ) : Fin m → Fin d → ℝ := fun e i => (v e i : ℝ)
def weights (s : Fin m → ℚ) : Fin m → ℚ := fun e => (s e)^2
noncomputable def realWeights (s : Fin m → ℚ) : Fin m → ℝ := fun e => (s e : ℝ)^2

def decrement (t : ℚ) : ℚ := 1-t^2
def threshold (q : ℕ) (t : ℚ) : ℚ := 1/q+4*decrement t

def testMatrix (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (e : Fin m) : Matrix (Fin d) (Fin d) ℚ :=
  threshold q t • covariance v (weights s)-(s e)^2 • vecMulVec (v e) (v e)

def heavy (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) : Option (Fin m) :=
  (List.finRange m).find? (fun e => (KS.W17.rationalNegativeWitness d (testMatrix q t v s e)).isSome)

def advance (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) : Fin m → ℚ :=
  (heavy q t v s).elim s (fun e => Function.update s e (t*s e))

def scalesAt (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ) (k : ℕ) : Fin m → ℚ :=
  (advance q t v)^[k] (fun _ => 1)

lemma scalesAt_zero (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ) :
    scalesAt q t v 0=(fun _ => 1) := rfl

lemma realWeights_one : realWeights (fun _ : Fin m => 1)=(fun _ => (1:ℝ)) := by
  funext e
  simp only [realWeights,Rat.cast_one,one_pow]

lemma testMatrix_symm (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (e : Fin m) : (testMatrix q t v s e).IsSymm := by
  change (testMatrix q t v s e)ᵀ=testMatrix q t v s e
  simp only [testMatrix,covariance,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_sum,Matrix.transpose_vecMulVec]

lemma testMatrix_cast (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (e : Fin m) :
    (testMatrix q t v s e).map (fun x : ℚ => (x:ℝ)) =
      (threshold q t:ℝ) • covariance (realColumns v) (realWeights s)-
        (s e:ℝ)^2 • vecMulVec (realColumns v e) (realColumns v e) := by
  ext i j
  simp only [testMatrix,covariance,weights,realWeights,realColumns,
    Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.vecMulVec_apply,smul_eq_mul,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_sum]

lemma heavy_none (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (hs : ∀e, 0 < s e)
    (hA : (covariance (realColumns v) (realWeights s)).PosDef)
    (ht : 0 < threshold q t) :
    heavy q t v s=none ↔ ∀e, leverage (realColumns v) (realWeights s) e ≤ (threshold q t:ℝ) := by
  rw [heavy,List.find?_eq_none]
  simp only [List.mem_finRange,forall_const,Option.isSome_iff_ne_none,not_not]
  apply forall_congr'
  intro e
  rw [KS.W17.rationalNegativeWitness_none_iff_psd _ _ (testMatrix_symm ..),testMatrix_cast]
  exact (leverage_test (realColumns v) (realWeights s) e hA
    (sq_pos_of_pos (by exact_mod_cast hs e)) (by exact_mod_cast ht)).symm

lemma heavy_some (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (hs : ∀e, 0 < s e)
    (hA : (covariance (realColumns v) (realWeights s)).PosDef)
    (ht : 0 < threshold q t) {e : Fin m} (he : heavy q t v s=some e) :
    (threshold q t:ℝ) < leverage (realColumns v) (realWeights s) e := by
  have hh := List.find?_some he
  rw [Option.isSome_iff_ne_none] at hh
  simp only [ne_eq, KS.W17.rationalNegativeWitness_none_iff_psd _ _ (testMatrix_symm ..),testMatrix_cast] at hh
  exact lt_of_not_ge (fun hc => hh ((leverage_test (realColumns v) (realWeights s) e hA
    (sq_pos_of_pos (by exact_mod_cast hs e)) (by exact_mod_cast ht)).mp hc))

lemma update_realWeights (s : Fin m → ℚ) (t : ℚ) (e : Fin m) :
    realWeights (Function.update s e (t*s e))=shrink (decrement t:ℝ) (realWeights s) e := by
  funext f
  by_cases h : f=e
  · subst f
    simp only [realWeights,shrink,Function.update_self,decrement,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,Rat.cast_mul]
    ring
  · simp only [realWeights,shrink,Function.update_of_ne h]

lemma advance_box (q : ℕ) {t : ℚ} (ht : 0 < t) (ht1 : t ≤ 1)
    (v : Fin m → Fin d → ℚ) (s : Fin m → ℚ)
    (hs : ∀e, 0 < s e ∧ s e ≤ 1) : ∀e, 0 < advance q t v s e ∧ advance q t v s e ≤ 1 := by
  unfold advance
  cases he : heavy q t v s with
  | none => simpa only [Option.elim_none] using hs
  | some f =>
    intro e
    simp only [Option.elim_some]
    by_cases h : e=f
    · subst e
      simp only [Function.update_self]
      exact ⟨mul_pos ht (hs f).1,(mul_le_of_le_one_left (hs f).1.le ht1).trans (hs f).2⟩
    · simpa only [Function.update_of_ne h] using hs e

lemma scalesAt_box (q : ℕ) {t : ℚ} (ht : 0 < t) (ht1 : t ≤ 1)
    (v : Fin m → Fin d → ℚ) (k : ℕ) : ∀e, 0 < scalesAt q t v k e ∧ scalesAt q t v k e ≤ 1 := by
  induction k with
  | zero => simp [scalesAt]
  | succ k ih =>
    change ∀e, 0 < ((advance q t v)^[k+1] (fun _ => 1)) e ∧
      ((advance q t v)^[k+1] (fun _ => 1)) e ≤ 1
    rw [Function.iterate_succ_apply']
    exact advance_box q ht ht1 v _ ih

lemma realWeights_box {s : Fin m → ℚ} (hs : ∀e, 0 < s e ∧ s e ≤ 1) :
    (∀e, 0 < realWeights s e) ∧ (∀e, realWeights s e ≤ 1) := by
  have hr (e : Fin m) : (0:ℝ) < s e ∧ (s e:ℝ) ≤ 1 := by exact_mod_cast hs e
  constructor
  · intro e;exact sq_pos_of_pos (hr e).1
  · intro e;exact pow_le_one₀ (hr e).1.le (hr e).2

lemma scalesAt_terminates (q : ℕ) {t : ℚ} (ht : 0 < t) (ht1 : t < 1)
    (hδ : 0 < decrement t) (hδ1 : decrement t ≤ 1/2)
    (v : Fin m → Fin d → ℚ) (B : ContainedPacking (realColumns v) q)
    (hsize : ∀e, realColumns v e ⬝ᵥ realColumns v e ≤ 2) (N : ℕ)
    (hN : 2*(m:ℝ) < N*(decrement t:ℝ)^2) :
    heavy q t v (scalesAt q t v N)=none := by
  have hq : 1 ≤ q := B.positive
  have hth : 0 < threshold q t := by
    unfold threshold
    have hq0 : (0:ℚ)<q := by exact_mod_cast B.positive
    positivity
  have hbox (k : ℕ) := realWeights_box (scalesAt_box q ht ht1.le v k)
  have hbound (k : ℕ) : heavy q t v (scalesAt q t v k)=none ∨
      objective q (realColumns v) (realWeights (scalesAt q t v k)) ≤
        2*m-k*(decrement t:ℝ)^2 := by
    induction k with
    | zero =>
      right
      rw [scalesAt_zero,realWeights_one]
      simpa only [Nat.cast_zero,zero_mul,sub_zero,Fintype.card_fin] using B.initial_gap hsize
    | succ k ih =>
      have heq : scalesAt q t v (k+1)=advance q t v (scalesAt q t v k) :=
        Function.iterate_succ_apply' _ _ _
      cases hh : heavy q t v (scalesAt q t v k) with
      | none =>
        left
        rw [heq,advance,hh,Option.elim_none,hh]
      | some e =>
        right
        have hi := ih.resolve_left (by rw [hh];simp)
        have hp := B.covariance_posDef _ (hbox k).1
        have hheavy := heavy_some q t v _ (fun e => (scalesAt_box q ht ht1.le v k e).1) hp hth hh
        have hstep : scalesAt q t v (k+1)=Function.update (scalesAt q t v k) e
            (t*scalesAt q t v k e) := by rw [heq,advance,hh,Option.elim_some]
        have hweights : realWeights (scalesAt q t v (k+1)) =
            shrink (decrement t:ℝ) (realWeights (scalesAt q t v k)) e := by
          rw [hstep,update_realWeights]
        have hp' := B.covariance_posDef _ (hbox (k+1)).1
        rw [hweights] at hp'
        have hd := objective_drop q hq (realColumns v) _ (hbox k).1 e (decrement t:ℝ)
          (by exact_mod_cast hδ) (by
            have hh : (decrement t:ℝ) ≤ (((1:ℚ)/2:ℚ):ℝ) := Rat.cast_le.mpr hδ1
            norm_num at hh ⊢
            exact hh) hp hp' (by
            simpa only [threshold,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
              Rat.cast_mul,Rat.cast_ofNat] using hheavy)
        rw [hweights]
        push_cast
        nlinarith only [hi,hd]
  rcases hbound N with h|h
  · exact h
  · have h0 := B.objective_nonneg _ (hbox N).1 (hbox N).2
    linarith only [h,h0,hN]

lemma scalesAt_parts (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    {b : ℕ} (ht : CurrentKS.RationalBits.Parts b t) (k : ℕ) :
    ∀e, CurrentKS.RationalBits.Parts (k*b) (scalesAt q t v k e) := by
  induction k with
  | zero => intro e;norm_num [scalesAt,CurrentKS.RationalBits.Parts]
  | succ k ih =>
    intro e
    change CurrentKS.RationalBits.Parts ((k+1)*b) (((advance q t v)^[k+1] (fun _ => 1)) e)
    rw [Function.iterate_succ_apply']
    change CurrentKS.RationalBits.Parts ((k+1)*b) (advance q t v (scalesAt q t v k) e)
    unfold advance
    cases hh : heavy q t v (scalesAt q t v k) with
    | none => exact (ih e).mono (Nat.mul_le_mul_right b (Nat.le_succ k))
    | some f =>
      simp only [Option.elim_some]
      by_cases h : e=f
      · subst e
        simpa only [Function.update_self,Nat.add_mul,Nat.one_mul,Nat.add_comm] using ht.mul (ih f)
      · simpa only [Function.update_of_ne h] using (ih e).mono (Nat.mul_le_mul_right b (Nat.le_succ k))

def multiplier (r : ℕ) : ℚ := 1-1/(16*(r:ℚ)^2)
def normalizationLength (m r : ℕ) : ℕ := (2*m+1)*256*r^4
def normalizedScales (q r : ℕ) (v : Fin m → Fin d → ℚ) : Fin m → ℚ :=
  scalesAt q (multiplier r) v (normalizationLength m r)

end AlgorithmicThinTrees.Normalization
end

end OAI
