import Mathlib

namespace OAI

noncomputable section

namespace ConvexSkorokhod

open Set

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Body where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier

variable {E}

noncomputable def project (B : Body E) (v : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex B.nonempty B.closed.isComplete B.convex v)

noncomputable def walk (B : Body E) (x₀ : E) (w : ℕ → E) : ℕ → E
  | 0 => x₀
  | n+1 => project B (walk B x₀ w n+(w (n+1)-w n))

def regulator (B : Body E) (x₀ : E) (w : ℕ → E) (n : ℕ) : E :=
  walk B x₀ w n-x₀-(w n-w 0)

def variation (k : ℕ → E) (N : ℕ) : ℝ := ∑i∈Finset.range N,‖k (i+1)-k i‖

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma project_mem (B : Body E) (v : E) : project B v∈B.carrier :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex B.nonempty B.closed.isComplete B.convex v)).1

lemma project_variational (B : Body E) (v : E) (q : E) (hq : q∈B.carrier) :
    ⟪project B v-v,q-project B v⟫≥0 := by
  have hm := (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex B.nonempty B.closed.isComplete B.convex v)).2
  have hv := (norm_eq_iInf_iff_real_inner_le_zero B.convex (project_mem B v)).mp hm q hq
  rw [show project B v-v=-(v-project B v) by abel,inner_neg_left]
  linarith

lemma walk_mem (B : Body E) (x₀ : E) (hx₀ : x₀∈B.carrier) (w : ℕ → E) (n : ℕ) : walk B x₀ w n∈B.carrier := by
  cases n with
  | zero => exact hx₀
  | succ n => exact project_mem B _

lemma regulator_zero (B : Body E) (x₀ : E) (w : ℕ → E) : regulator B x₀ w 0=0 := by simp [regulator,walk]

lemma regulator_increment (B : Body E) (x₀ : E) (w : ℕ → E) (n : ℕ) :
    regulator B x₀ w (n+1)-regulator B x₀ w n=
      walk B x₀ w (n+1)-(walk B x₀ w n+(w (n+1)-w n)) := by dsimp [regulator];abel

lemma regulator_normal (B : Body E) (x₀ : E) (w : ℕ → E) (n : ℕ) (q : E) (hq : q∈B.carrier) :
    0≤⟪regulator B x₀ w (n+1)-regulator B x₀ w n,q-walk B x₀ w (n+1)⟫ := by
  rw [regulator_increment]
  exact project_variational B _ q hq

omit [CompleteSpace E]

lemma ball_normal_impulse (K : Set E) (c y d : E) (r : ℝ) (hr : 0≤r)
    (hball : Metric.closedBall c r⊆K) (hn : ∀q∈K,0≤⟪d,q-y⟫) :
    r*‖d‖≤⟪d,c-y⟫ := by
  by_cases hd : d=0
  · simp [hd]
  have hd0 : 0<‖d‖ := norm_pos_iff.mpr hd
  let q := c-(r/‖d‖) • d
  have hq : q∈K := by
    apply hball
    rw [Metric.mem_closedBall,dist_eq_norm]
    have he : q-c=-((r/‖d‖) • d) := by dsimp [q];abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hr hd0.le),div_mul_cancel₀ _ hd0.ne']
  have hi := hn q hq
  have he : q-y=(c-y)-(r/‖d‖) • d := by dsimp [q];abel
  rw [he,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq] at hi
  have hmul : r/‖d‖*‖d‖^2=r*‖d‖ := by field_simp
  rw [hmul] at hi
  linarith

lemma sum_inner_increment (k : ℕ → E) (N : ℕ) (c : E) :
    (∑i∈Finset.range N,⟪k (i+1)-k i,c⟫)=⟪k N-k 0,c⟫ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    rw [← inner_add_left]
    congr 1;abel

lemma sum_inner_energy (k : ℕ → E) (N : ℕ) :
    2*(∑i∈Finset.range N,⟪k (i+1)-k i,k (i+1)⟫)=
      ‖k N‖^2-‖k 0‖^2+∑i∈Finset.range N,‖k (i+1)-k i‖^2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have he := norm_sub_sq_real (k (N+1)) (k N)
    rw [inner_sub_left,real_inner_self_eq_norm_sq]
    rw [real_inner_comm (k N) (k (N+1))] at he
    nlinarith

end ConvexSkorokhod

end

end OAI
