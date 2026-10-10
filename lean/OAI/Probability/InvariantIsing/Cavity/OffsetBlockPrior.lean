import OAI.Probability.InvariantIsing.Cavity.ConsecutiveBlockTransport

namespace OAI

/-! A fixed initial remainder followed by repeated constrained blocks.
Adding a new last block preserves this exact finite spin family. -/
noncomputable section
open IsingPerceptron
namespace InvariantIsing

def offsetBlockConstraint {r n : ℕ} (K : ℕ) (R : Finset (Spin r))
    (C : Finset (Spin n)) : Finset (Spin (r+K*n)) :=
  cavityProductSlice R (consecutiveBlockConstraint n K C)

lemma offsetBlockConstraint_nonempty {r n K : ℕ} (R : Finset (Spin r))
    (hR : R.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) :
    (offsetBlockConstraint K R C).Nonempty :=
  cavityProductSlice_nonempty R hR _ (consecutiveBlockConstraint_nonempty C hC)

lemma mem_offsetBlockConstraint {r n K : ℕ} (R : Finset (Spin r))
    (C : Finset (Spin n)) (σ : Spin (r+K*n)) :
    σ∈offsetBlockConstraint K R C ↔
      (fun i => σ (Fin.castAdd (K*n) i))∈R ∧
        ∀ b : Fin K, (fun i => σ (Fin.natAdd r (finProdFinEquiv (b,i))))∈C := by
  rw [offsetBlockConstraint,mem_cavityProductSlice,mem_consecutiveBlockConstraint]
  rfl

def offsetBlockJoin (r n K : ℕ) : Spin ((r+K*n)+n) ≃ Spin (r+(K+1)*n) :=
  spinDimensionCast (by simp only [Nat.add_mul,Nat.one_mul]; omega)

lemma offsetBlockJoin_mem {r n K : ℕ} (R : Finset (Spin r)) (C : Finset (Spin n))
    (σ : Spin ((r+K*n)+n)) :
    offsetBlockJoin r n K σ ∈ offsetBlockConstraint (K+1) R C ↔
      σ∈cavityProductSlice (offsetBlockConstraint K R C) C := by
  rw [mem_offsetBlockConstraint,mem_cavityProductSlice,mem_offsetBlockConstraint]
  have hR : (fun i => offsetBlockJoin r n K σ (Fin.castAdd ((K+1)*n) i)) =
      (fun i => (cavitySpinSplit (r+K*n) n σ).1 (Fin.castAdd (K*n) i)) := by
    funext i
    apply congrArg σ
    apply Fin.ext
    rfl
  have hl (b : Fin K) :
      (fun i => offsetBlockJoin r n K σ (Fin.natAdd r (finProdFinEquiv (b.castSucc,i)))) =
      (fun i => (cavitySpinSplit (r+K*n) n σ).1 (Fin.natAdd r (finProdFinEquiv (b,i)))) := by
    funext i
    apply congrArg σ
    apply Fin.ext
    rfl
  have hr :
      (fun i => offsetBlockJoin r n K σ (Fin.natAdd r (finProdFinEquiv (Fin.last K,i)))) =
      (cavitySpinSplit (r+K*n) n σ).2 := by
    funext i
    apply congrArg σ
    apply Fin.ext
    change r+(i.val+n*K)=(r+K*n)+i.val
    simp [Nat.mul_comm,Nat.add_comm,Nat.add_left_comm]
  rw [hR]
  constructor
  · rintro ⟨hR,hC⟩
    exact ⟨⟨hR,fun b => hl b ▸ hC b.castSucc⟩,hr ▸ hC (Fin.last K)⟩
  · rintro ⟨⟨hR,hC⟩,hlast⟩
    refine ⟨hR,fun b => ?_⟩
    refine Fin.lastCases ?_ (fun b => ?_) b
    · rw [hr]
      exact hlast
    · rw [hl]
      exact hC b

lemma offsetBlockConstraint_succ {r n K : ℕ} (R : Finset (Spin r)) (C : Finset (Spin n)) :
    offsetBlockConstraint (K+1) R C =
      (cavityProductSlice (offsetBlockConstraint K R C) C).map (offsetBlockJoin r n K).toEmbedding := by
  ext σ
  rw [Finset.mem_map]
  constructor
  · intro hσ
    exact ⟨(offsetBlockJoin r n K).symm σ,(offsetBlockJoin_mem R C _).mp (by simpa using hσ),by simp⟩
  · rintro ⟨τ,hτ,rfl⟩
    exact (offsetBlockJoin_mem R C τ).mpr hτ

lemma offsetBlockConstraint_card {r n K : ℕ} (R : Finset (Spin r)) (C : Finset (Spin n)) :
    (offsetBlockConstraint K R C).card=R.card*C.card^K := by
  rw [offsetBlockConstraint,cavityProductSlice_card,consecutiveBlockConstraint_card]

lemma offsetBlockConstraint_log_mass {r n K : ℕ} (R : Finset (Spin r))
    (hR : R.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) :
    Real.log (offsetBlockConstraint K R C).card-(r+K*n:ℕ)*Real.log 2=
      (Real.log R.card-r*Real.log 2)+(K:ℝ)*(Real.log C.card-n*Real.log 2) := by
  rw [offsetBlockConstraint_card,Nat.cast_mul,Real.log_mul
    (Nat.cast_ne_zero.mpr hR.card_pos.ne') (by positivity),Nat.cast_pow,Real.log_pow]
  push_cast
  ring

lemma offset_spin_family_succ {α : Sort*}
    (F : (N : ℕ) → Finset (Spin N) → α) {r n : ℕ} (K : ℕ)
    (R : Finset (Spin r)) (C : Finset (Spin n)) :
    F (r+(K+1)*n) (offsetBlockConstraint (K+1) R C)=
      F ((r+K*n)+n) (cavityProductSlice (offsetBlockConstraint K R C) C) := by
  rw [offsetBlockConstraint_succ]
  exact spin_family_dimension_cast F (by simp only [Nat.add_mul,Nat.one_mul]; omega) _

end InvariantIsing

end

end OAI
