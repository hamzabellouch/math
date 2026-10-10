import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def neumann (T : F →L[ℝ] F) : F →L[ℝ] F := ∑' n : ℕ, T^n
lemma neumann_equation (T : F →L[ℝ] F) (hT : ‖T‖<1) (y : F) :
    neumann T y - T (neumann T y) = y := by
  have hh := congrArg (fun A : F →L[ℝ] F => A y) (mul_neg_geom_series T hT)
  simpa only [neumann,sub_apply,mul_apply_eq_comp,
    one_apply_eq_self] using hh
omit [CompleteSpace F] in
lemma neumann_norm (T : F →L[ℝ] F) {q : ℝ} (hq0 : 0≤q) (hq : q<1)
    (hT : ‖T‖≤q) : ‖neumann T‖ ≤ 1/(1-q) := by
  have hs := summable_geometric_of_lt_one hq0 hq
  have hb (n : ℕ) : ‖T^n‖ ≤ q^n := by
    cases n with
    | zero =>
      rw [pow_zero,pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n =>
      exact (norm_pow_le' T (Nat.succ_pos n)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hT (n+1))
  have ht : Summable (fun n : ℕ => ‖T^n‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  calc
    ‖neumann T‖ ≤ ∑' n : ℕ, ‖T^n‖ := norm_tsum_le_tsum_norm ht
    _ ≤ ∑' n : ℕ, q^n := ht.tsum_le_tsum hb hs
    _ = 1/(1-q) := by rw [tsum_geometric_of_lt_one hq0 hq,one_div]

def tailOperator (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) : F →L[ℝ] F := D+K.comp (L.comp B)
def tailSolution (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) : F :=
  neumann (tailOperator L B K D) (s+K (L r))
def finiteSolution (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) : E :=
  L (r+B (tailSolution L B K D r s))
omit [CompleteSpace E] in
lemma solution_equations (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) (h : ‖tailOperator L B K D‖<1) :
    tailSolution L B K D r s = D (tailSolution L B K D r s)+
      K (finiteSolution L B K D r s)+s := by
  have hh := neumann_equation (tailOperator L B K D) h (s+K (L r))
  change tailSolution L B K D r s - _ = _ at hh
  simp only [tailOperator,add_apply,ContinuousLinearMap.comp_apply] at hh
  simp only [finiteSolution,map_add]
  rw [sub_eq_iff_eq_add] at hh
  calc
    _ = s+K (L r)+(D (tailSolution L B K D r s)+K (L (B (tailSolution L B K D r s)))) := hh
    _ = _ := by abel
end AtomicTriangular.Schur
end

end OAI
