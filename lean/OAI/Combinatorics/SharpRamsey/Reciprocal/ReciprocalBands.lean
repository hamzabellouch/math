import Mathlib

namespace OAI

section
namespace SharpLogRamsey.ReciprocalBands
open Real
noncomputable section

def clamp (d : ℕ) (σ x : ℝ) : ℝ := max σ (min ((d:ℝ)*σ) x)

lemma clamp_range {d : ℕ} (hd : 1≤d) {σ x : ℝ} (hσ : 0≤σ) :
    σ≤clamp d σ x ∧ clamp d σ x≤(d:ℝ)*σ := by
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  exact ⟨le_max_left _ _,max_le (by nlinarith) (min_le_left _ _)⟩

theorem clamped_caps {d : ℕ} (hd : 1≤d) {σ a b C : ℝ}
    (hσ : 0≤σ) (hb : 0<b) (hC : 1≤C)
    (ha : a≤C*exp ((d:ℝ)*σ)) (hbnd : b≤C*exp ((d:ℝ)*σ))
    (hab : a*b≤C*exp (((d:ℝ)+1)*σ)) :
    σ≤clamp d σ (log b) ∧ clamp d σ (log b)≤(d:ℝ)*σ ∧
    a≤C*exp (((d:ℝ)+1)*σ-clamp d σ (log b)) ∧
    b≤C*exp (clamp d σ (log b)) := by
  have hr := clamp_range hd (x:=log b) hσ
  have hCp : 0≤C := le_trans zero_le_one hC
  refine ⟨hr.1,hr.2,?_,?_⟩
  · by_cases hx : log b≤σ
    · have hu : clamp d σ (log b)=σ := max_eq_left ((min_le_right _ _).trans hx)
      rw [hu]
      convert ha using 1
      congr 2
      ring
    · have hxu : clamp d σ (log b)≤log b := max_le (le_of_not_ge hx) (min_le_right _ _)
      have ha' : a≤C*exp (((d:ℝ)+1)*σ-log b) := by
        rw [exp_sub,exp_log hb,←mul_div_assoc]
        exact (le_div_iff₀ hb).mpr hab
      exact ha'.trans (mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (sub_le_sub_left hxu _)) hCp)
  · by_cases hx : log b≤(d:ℝ)*σ
    · have hu : log b≤clamp d σ (log b) := by
        unfold clamp
        rw [min_eq_right hx]
        exact le_max_right _ _
      calc
        b = exp (log b) := (exp_log hb).symm
        _ ≤ exp (clamp d σ (log b)) := exp_le_exp.mpr hu
        _ ≤ C*exp (clamp d σ (log b)) := le_mul_of_one_le_left (exp_nonneg _) hC
    · have hu : clamp d σ (log b)=(d:ℝ)*σ := by
        unfold clamp
        rw [min_eq_left (le_of_not_ge hx)]
        exact max_eq_right (hr.1.trans hr.2)
      rw [hu]
      exact hbnd

def IntegerBand (r : ℕ) (σ K u : ℝ) : Prop := |u-(r:ℝ)*σ|≤K
def OpenBand (r : ℕ) (σ K u : ℝ) : Prop :=
  ((r:ℝ)-1)*σ+K<u ∧ u<(r:ℝ)*σ-K

theorem cover {d : ℕ} {σ K u : ℝ} (hσ : 0<σ) (hK : 0≤K)
    (hlo : σ≤u) (hhi : u≤(d:ℝ)*σ) :
    ∃ r : ℕ,1≤r ∧ r≤d ∧ (IntegerBand r σ K u ∨ (2≤r ∧ OpenBand r σ K u)) := by
  induction d with
  | zero => simp only [Nat.cast_zero,zero_mul] at hhi; linarith
  | succ d ih =>
    by_cases hprev : u≤(d:ℝ)*σ
    · obtain ⟨r,h₁,h₂,h₃⟩ := ih hprev
      exact ⟨r,h₁,h₂.trans (Nat.le_succ d),h₃⟩
    have hhi' : u≤((d:ℝ)+1)*σ := by simpa only [Nat.cast_add,Nat.cast_one] using hhi
    by_cases hnext : ((d:ℝ)+1)*σ-K≤u
    · refine ⟨d+1,by omega,le_rfl,Or.inl ?_⟩
      rw [IntegerBand,abs_le]
      simp only [Nat.cast_add,Nat.cast_one]
      constructor <;> linarith
    have hd : 1≤d := by
      by_contra hn
      have hz : d=0 := by omega
      simp only [hz,Nat.cast_zero,zero_add,one_mul] at hnext
      linarith
    by_cases hleft : u≤(d:ℝ)*σ+K
    · refine ⟨d,hd,by omega,Or.inl ?_⟩
      rw [IntegerBand,abs_le]
      constructor <;> linarith
    · refine ⟨d+1,by omega,le_rfl,Or.inr ⟨by omega,?_⟩⟩
      unfold OpenBand
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
      exact ⟨lt_of_not_ge hleft,lt_of_not_ge hnext⟩

end
end SharpLogRamsey.ReciprocalBands

end

end OAI
