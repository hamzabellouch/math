import Mathlib

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

inductive RoutineKind where
  | mean | sample
  deriving DecidableEq

structure RoutineLabel where
  kind : RoutineKind
  b : ℝ
  p : ℝ

def RoutineLabel.terminal (L : RoutineLabel) : Prop := L.p≤L.b

inductive RoutineStep (t : ℝ) : RoutineLabel → RoutineLabel → Prop where
  | meanFinal (b p : ℝ) : RoutineStep t ⟨.mean,b,p⟩ ⟨.mean,b+t,p⟩
  | sampleFinal (b p : ℝ) : RoutineStep t ⟨.sample,b,p⟩ ⟨.mean,b,p⟩
  | internal (k k' : RoutineKind) (b p : ℝ) :
      RoutineStep t ⟨k,b,p⟩ ⟨k',b-10*t,p-1/4⟩

def RoutineLabel.rank (t : ℝ) (L : RoutineLabel) : ℕ :=
  2*⌈(L.p-L.b)/t⌉₊+(match L.kind with | .mean => 0 | .sample => 1)

lemma ceil_gap_drop {t x y : ℝ} (ht : 0<t) (hx : 0<x) (hy : y≤x-t) :
    ⌈y/t⌉₊<⌈x/t⌉₊ := by
  have hp : 0<x/t := div_pos hx ht
  have hxy : y/t≤x/t-1 := by
    simpa only [sub_div,div_self ht.ne'] using (div_le_div_of_nonneg_right hy ht.le)
  have hn : 0<⌈x/t⌉₊ := Nat.ceil_pos.mpr hp
  have hc := Nat.le_ceil (x/t)
  have hm : y/t≤(⌈x/t⌉₊-1:ℕ) := by
    rw [Nat.cast_sub (by omega : 1≤⌈x/t⌉₊),Nat.cast_one]
    linarith
  exact lt_of_le_of_lt (Nat.ceil_le.mpr hm) (Nat.sub_lt hn (by omega))

lemma RoutineStep.rank_lt {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    {P C : RoutineLabel} (hP : ¬P.terminal) (h : RoutineStep t P C) :
    C.rank t<P.rank t := by
  cases h with
  | meanFinal b p =>
    have hd := ceil_gap_drop ht (show 0<p-b by simpa [RoutineLabel.terminal] using hP)
      (y:=p-(b+t)) (by linarith)
    simp only [RoutineLabel.rank]
    omega
  | sampleFinal b p => simp [RoutineLabel.rank]
  | internal k k' b p =>
    have hd := ceil_gap_drop ht (show 0<p-b by simpa [RoutineLabel.terminal] using hP)
      (y:=p-1/4-(b-10*t)) (by linarith)
    cases k <;> cases k' <;> simp only [RoutineLabel.rank] <;> omega

theorem routine_induction {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    (P : RoutineLabel → Prop) (hbase : ∀L,L.terminal → P L)
    (hstep : ∀L,¬L.terminal → (∀C,RoutineStep t L C → P C) → P L) : ∀L,P L := by
  intro L
  induction hn : L.rank t using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hL : L.terminal
    · exact hbase L hL
    · apply hstep L hL
      intro C hc
      exact ih _ (hn ▸ hc.rank_lt ht hs hL) C rfl
end LogConcaveSampling.OracleCompiler

end

end

end OAI
