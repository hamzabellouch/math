import OAI.Probability.EntangledGames.ExponentialBounds

namespace OAI

universe u_I u_X u_Y

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law
namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]
def coeff (S : Strategy X Y A B) : Matrix (Fin (S.dimA+1)) (Fin (S.dimB+1)) ℂ := fun i j => S.state (i,j)
lemma coeff_unit (S : Strategy X Y A B) : hsSq S.coeff = 1 := by
  simpa only [hsSq, coeff, Fintype.sum_prod_type] using S.state_unit
lemma born_eq_prob (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b = prob S.coeff (S.alice x a) (S.bob y b) := by
  rw [S.born_eq_quadratic]
  rfl

def repetitionModel {x y a b k : ℕ} (S : RepeatedStrategy x y a b k) (G : Game x y a b) :
    RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) (Fin k)
      (Fin (S.dimA+1)) (Fin (S.dimB+1)) where
  μ := G.questionLaw
  C := S.coeff
  hC := S.coeff_unit
  P xs := ⟨S.alice xs, S.alice_pos xs, S.alice_total xs⟩
  Q ys := ⟨S.bob ys, S.bob_pos ys, S.bob_total ys⟩
  V := G.accepts
end Strategy

lemma sum_profiles {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]
    (f : (I→X×Y) → ℝ) :
    (∑ z, f z) = ∑ xs : I → X, ∑ ys : I → Y, f (fun i => (xs i,ys i)) := by
  let e : (I→X×Y) ≃ (I→X)×(I→Y) := {
    toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
    invFun := fun t i => (t.1 i,t.2 i)
    left_inv := fun z => by funext i; exact Prod.eta _
    right_inv := fun t => by rcases t with ⟨xs,ys⟩; rfl }
  calc
    (∑ z, f z) = ∑ t : (I→X)×(I→Y), f (e.symm t) := (e.symm.sum_comp f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

namespace Strategy
variable {x y a b k : ℕ} (S : RepeatedStrategy x y a b k) (G : Game x y a b)
lemma rate_eq_wins [Nonempty (Fin k)] (z : Profile (Fin k) (Fin (x+1)) (Fin (y+1)))
    (as : Fin k → Fin (a+1)) (bs : Fin k → Fin (b+1)) :
    Tests.rate (S.repetitionModel G).winsAt (z,as,bs) =
      (wins G (fun i => (z i).1) (fun i => (z i).2) as bs : ℝ)/(k : ℝ) := by
  rw [Tests.rate, uniform_avg, Fintype.card_fin, one_div, inv_mul_eq_div]
  congr 1
  unfold wins
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl; intro i _
  change (if G.accepts (z i).1 (z i).2 (as i) (bs i) then (1:ℝ) else 0) = _
  split_ifs <;> norm_num

lemma threshold_eq_model [Nonempty (Fin k)] (hk : 0 < k) (δ : ℝ) :
    thresholdProbability G δ S =
      Tests.threshold (S.repetitionModel G).joint
        (S.repetitionModel G).winsAt (entangledValue G+δ) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  symm
  unfold Tests.threshold
  rw [RepeatedModel.joint_avg]
  simp only [S.rate_eq_wins G, le_div_iff₀ hk', ← Nat.ceil_le]
  simp only [avg, pi, RepeatedModel.answers, outcomeLaw, Strategy.repetitionModel,
    smul_eq_mul, Fintype.sum_prod_type]
  rw [sum_profiles]
  unfold thresholdProbability
  apply Finset.sum_congr rfl; intro xs _
  apply Finset.sum_congr rfl; intro ys _
  congr 1
  apply Finset.sum_congr rfl; intro as _
  apply Finset.sum_congr rfl; intro bs _
  rw [S.born_eq_prob]
  split_ifs <;> simp
end Strategy
end ThresholdParallelRepetition

end

end OAI
