import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodStability
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodVariation

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def sampledDriver (w : ℝ → E) (N : ℕ) (i : ℕ) : E := w ((i:ℝ)/N)

noncomputable def mesh (B : Body E) (x₀ : E) (w : ℝ → E) (N : ℕ) (t : ℝ) : E :=
  walk B x₀ (sampledDriver w N) ⌊t*N⌋₊

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma project_eq_self (B : Body E) (x : E) (hx : x∈B.carrier) : project B x=x := by
  have h := project_variational B x x hx
  rw [show x-project B x=-(project B x-x) by abel,inner_neg_right,real_inner_self_eq_norm_sq] at h
  have : ‖project B x-x‖=0 := by nlinarith [norm_nonneg (project B x-x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma walk_reindex (B : Body E) (x₀ : E) (hx₀ : x₀∈B.carrier) (w : ℕ → E)
    (q : ℕ → ℕ) (hq₀ : q 0=0) (hq : ∀n,q (n+1)=q n ∨ q (n+1)=q n+1) :
    ∀n,walk B x₀ (w ∘ q) n=walk B x₀ w (q n) := by
  intro n
  induction n with
  | zero => simp [walk,hq₀]
  | succ n ih =>
    rw [walk,ih]
    rcases hq n with h|h
    · simp only [Function.comp_apply,h,sub_self,add_zero]
      exact project_eq_self B _ (walk_mem B x₀ hx₀ w _)
    · simp only [Function.comp_apply,h,walk]

lemma div_step (N : ℕ) (hN : 0 < N) (i : ℕ) :
    (i+1)/N=i/N ∨ (i+1)/N=i/N+1 := by
  have h₀ := Nat.div_le_div_right (by omega : i ≤ i+1) (c:=N)
  have h₁ : (i+1)/N ≤ i/N+1 := by
    have h := Nat.div_le_div_right (by omega : i+1 ≤ i+N) (c:=N)
    simpa [Nat.add_div_right _ hN] using h
  omega

lemma walk_repeat (B : Body E) (x₀ : E) (hx₀ : x₀∈B.carrier) (w : ℕ → E)
    (N : ℕ) (hN : 0 < N) (i : ℕ) :
    walk B x₀ (fun i => w (i/N)) i=walk B x₀ w (i/N) :=
  walk_reindex B x₀ hx₀ w (fun i => i/N) (by simp) (div_step N hN) i

lemma floor_product_div (t : ℝ) (m n : ℕ) (hn : 0 < n) :
    ⌊t*((m*n:ℕ):ℝ)⌋₊/n=⌊t*m⌋₊ := by
  rw [← Nat.floor_div_natCast]
  congr 1
  push_cast
  field_simp

lemma sampled_time_bounds (i m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hi : i ≤ m*n) :
    ((i/n:ℕ):ℝ)/m∈Icc (0:ℝ) 1 := by
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0:ℝ) < m)).mpr
    exact_mod_cast (Nat.div_le_div_right hi (c:=n) |>.trans_eq (Nat.mul_div_cancel m hn))

lemma sampled_time_error (i m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    |((i/n:ℕ):ℝ)/m-((i/m:ℕ):ℝ)/n| ≤ 1/m+1/n := by
  have hm' : (0:ℝ) < m := by positivity
  have hn' : (0:ℝ) < n := by positivity
  have hi₀ := Nat.mod_add_div i n
  have hi₁ := Nat.mod_add_div i m
  have hi₂ := Nat.mod_lt i hn
  have hi₃ := Nat.mod_lt i hm
  have e₀ : (i:ℝ)=(i%n:ℕ)+(n:ℝ)*(i/n:ℕ) := by exact_mod_cast hi₀.symm
  have e₁ : (i:ℝ)=(i%m:ℕ)+(m:ℝ)*(i/m:ℕ) := by exact_mod_cast hi₁.symm
  have b₀ : (i%n:ℕ) < (n:ℝ) := by exact_mod_cast hi₂
  have b₁ : (i%m:ℕ) < (m:ℝ) := by exact_mod_cast hi₃
  have he : ((1:ℝ)/m+1/n)*((m:ℝ)*n)=(m:ℝ)+n := by field_simp;ring
  rw [div_sub_div _ _ hm'.ne' hn'.ne',abs_div,abs_of_pos (mul_pos hm' hn'),div_le_iff₀ (mul_pos hm' hn'),he,abs_le]
  constructor <;> nlinarith [(Nat.cast_nonneg (i%n : ℕ) : (0:ℝ) ≤ (i%n:ℕ)),(Nat.cast_nonneg (i%m : ℕ) : (0:ℝ) ≤ (i%m:ℕ))]

end ConvexSkorokhod

end OAI
