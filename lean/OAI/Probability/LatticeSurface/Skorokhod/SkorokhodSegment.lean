import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodMesh

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E]

lemma variation_nonneg (k : ℕ → E) (N : ℕ) : 0 ≤ variation k N :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma variation_add (k : ℕ → E) (a n : ℕ) :
    variation k (a+n)=variation k a+variation (fun i => k (a+i)) n := by
  unfold variation
  rw [Finset.sum_range_add]
  congr 1

lemma variation_mono (k : ℕ → E) : Monotone (variation k) := by
  intro a b hab
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [variation_add]
  exact le_add_of_nonneg_right (variation_nonneg _ _)

variable [InnerProductSpace ℝ E] [CompleteSpace E]

lemma walk_shift (B : Body E) (x₀ : E) (w : ℕ → E) (a n : ℕ) :
    walk B (walk B x₀ w a) (fun i => w (a+i)) n=walk B x₀ w (a+n) := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    rw [walk,ih]
    change project B (walk B x₀ w (a+n)+(w (a+(n+1))-w (a+n)))=walk B x₀ w ((a+n)+1)
    rw [walk,Nat.add_assoc a n 1]

lemma regulator_shift (B : Body E) (x₀ : E) (w : ℕ → E) (a i : ℕ) :
    regulator B (walk B x₀ w a) (fun j => w (a+j)) i=
      regulator B x₀ w (a+i)-regulator B x₀ w a := by
  simp only [regulator,walk_shift,Nat.add_zero]
  abel

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma variation_sub_const (k : ℕ → E) (c : E) (N : ℕ) :
    variation (fun i => k i-c) N=variation k N := by
  unfold variation
  apply Finset.sum_congr rfl
  intro i hi
  rw [sub_sub_sub_cancel_right]

lemma regulator_shift_variation (B : Body E) (x₀ : E) (w : ℕ → E) (a n N : ℕ)
    (hN : a+n ≤ N) :
    variation (regulator B (walk B x₀ w a) (fun j => w (a+j))) n ≤ variation (regulator B x₀ w) N := by
  have he : regulator B (walk B x₀ w a) (fun j => w (a+j))=
      fun i => regulator B x₀ w (a+i)-regulator B x₀ w a := by funext i;exact regulator_shift B x₀ w a i
  rw [he,variation_sub_const]
  have ha := variation_nonneg (regulator B x₀ w) a
  have hb := variation_mono (regulator B x₀ w) hN
  rw [variation_add] at hb
  linarith

lemma walk_constant (B : Body E) (x₀ : E) (hx₀ : x₀∈B.carrier) (c : E) :
    ∀n,walk B x₀ (fun _ => c) n=x₀ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [walk,ih,sub_self,add_zero,project_eq_self B x₀ hx₀]

lemma walk_segment_displacement (B : Body E) (x₀ : E) (hx₀ : x₀∈B.carrier) (w : ℕ → E)
    (a n N : ℕ) (hN : a+n ≤ N) (δ C : ℝ) (hδ : 0 ≤ δ)
    (hvar : variation (regulator B x₀ w) N ≤ C)
    (hosc : ∀i ≤ n,‖w (a+i)-w a‖ ≤ δ) :
    ‖walk B x₀ w (a+n)-walk B x₀ w a‖ ≤ δ+Real.sqrt (2*δ*C) := by
  let y := walk B x₀ w a
  have hy : y∈B.carrier := walk_mem B x₀ hx₀ w a
  have hb := walk_driver_stability B y y hy hy (fun i => w (a+i)) (fun _ => (0:E)) n δ hδ
    (by intro i hi; simpa only [Nat.add_zero,sub_zero,add_zero,add_sub_cancel_left] using hosc i hi)
  have hc : variation (regulator B y (fun _ => (0:E))) n=0 := by
    simp only [variation,regulator,walk_constant B y hy,sub_self,norm_zero,Finset.sum_const_zero]
  rw [hc,add_zero,walk_constant B y hy,walk_shift] at hb
  have he := (regulator_shift_variation B x₀ w a n N hN).trans hvar
  exact hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left he (by positivity))))

end ConvexSkorokhod

end OAI
