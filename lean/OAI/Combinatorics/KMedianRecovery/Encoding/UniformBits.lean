import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalExpected

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

def uniformBits : (b : ℕ) → (Fin b → Bool) ≃ Fin (2^b)
  | 0 => (Equiv.ofUnique (Fin 0 → Bool) (Fin 1)).trans (finCongr (by simp))
  | b+1 => (Fin.consEquiv (fun _ : Fin (b+1) => Bool)).symm |>.trans
      ((Equiv.prodCongr finTwoEquiv.symm (uniformBits b)).trans
        (finProdFinEquiv.trans (finCongr (by simp [Nat.pow_succ, Nat.mul_comm]))))

abbrev BinaryOracleIndex (E : Type*) (a b L : ℕ) :=
  ((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b

instance binaryOracleIndexFintype {E : Type*} [Fintype E] {a b L : ℕ} :
    Fintype (BinaryOracleIndex E a b L) :=
  inferInstanceAs (Fintype (((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b))

instance binaryOracleIndexDecidableEq {E : Type*} [DecidableEq E] {a b L : ℕ} :
    DecidableEq (BinaryOracleIndex E a b L) :=
  inferInstanceAs (DecidableEq (((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b))

def binarySeedEquiv (E : Type*) (a b L : ℕ) :
    (BinaryOracleIndex E a b L → Bool) ≃
      (Fin (2^b) → OracleSeed E a (2^b) L) × (Fin a → Fin (2^b)) where
  toFun bits := (fun t e l j => uniformBits b (fun i => bits (.inl (t,e,l,j),i)),
    fun j => uniformBits b (fun i => bits (.inr j,i)))
  invFun s := fun idx => match idx.1 with
    | .inl (t,e,l,j) => (uniformBits b).symm (s.1 t e l j) idx.2
    | .inr j => (uniformBits b).symm (s.2 j) idx.2
  left_inv bits := by
    funext idx
    rcases idx with ⟨idx,i⟩
    rcases idx with ⟨t,e,l,j⟩ | j <;> simp
  right_inv s := by
    apply Prod.ext
    · funext t e l j
      exact (uniformBits b).apply_symm_apply _
    · funext j
      exact (uniformBits b).apply_symm_apply _

lemma binaryOracleIndex_card {E : Type*} [Fintype E] (a b L : ℕ) :
    Fintype.card (BinaryOracleIndex E a b L) =
      ((2^b)*Fintype.card E*L*a+a)*b := by
  simp only [BinaryOracleIndex, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_fin]
  ring

noncomputable def binaryGreedyOutput {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (bits : BinaryOracleIndex E a b L → Bool) : Finset E :=
  greedyOutput part hp g (binarySeedEquiv E a b L bits)

lemma binaryGreedyOutput_feasible {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (bits : BinaryOracleIndex E a b L → Bool) :
    PartitionFeasible part (binaryGreedyOutput part hp g bits) :=
  greedyOutput_feasible part hp g _

lemma binaryGreedyOutput_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*(2^b:ℕ)) (hL : 0 < L)
    (hcount : ((2^b:ℕ):ℝ)*Fintype.card E*a^2/(4*tau^3) ≤ L)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - 4*tau) * g S ≤
      average (fun bits : BinaryOracleIndex E a b L → Bool =>
        g (binaryGreedyOutput part hp g bits)) := by
  simp only [binaryGreedyOutput]
  rw [average_equiv (binarySeedEquiv E a b L) _
    (fun seed => g (greedyOutput part hp g seed)) (fun _ => rfl)]
  exact categorical_expected part hp g hmono hsub hg0 ha htau htau1 hscale hL hcount S hS

end MetricKMedianRecovery.Categorical

end OAI
