import OAI.NumberTheory.TotientAsymptotic.StrictSlackCost

namespace OAI

/-! The full-dimensional thin region associated with a failure of strict slack. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def strictTopWidth (x : ℝ) : ℝ := 2*boxTopError x+B x/(m x : ℝ)^4

def strictSlackWidth (x : ℝ) (i : ℕ) : ℝ :=
  2*boxSlackError x i+(11/10 : ℝ)*bandScale x i/((m x-i : ℕ) : ℝ)^4

lemma strictTopWidth_nonneg {x : ℝ} (hB : 0 ≤ B x) : 0 ≤ strictTopWidth x := by
  exact add_nonneg (mul_nonneg (by norm_num) (boxTopError_nonneg hB)) (div_nonneg hB (by positivity))

lemma strictSlackWidth_nonneg (x : ℝ) (i : ℕ) : 0 ≤ strictSlackWidth x i := by
  exact add_nonneg (mul_nonneg (by norm_num) (boxSlackError_nonneg x i))
    (div_nonneg (mul_nonneg (by norm_num) (bandScale_nonneg x i)) (by positivity))

def strictSlackShell (x : ℝ) (R N : ℕ) (hRN : R ≤ N) : Set (Fin N → ℝ) :=
  (additiveBoxSimplex x N \
    prefixRegion N (B x+boxTopError x-strictTopWidth x) 0
      (fun i => -boxSlackError x (i.val+1))) ∪
  ⋃ i : Fin R, additiveBoxSimplex x N \
    prefixRegion N (B x+boxTopError x) 0
      (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
        (strictSlackWidth x (i.val+1)))

lemma strictSlackShell_volume_ne_top (x : ℝ) {R N : ℕ} (hRN : R ≤ N) (hN : 0 < N) :
    volume (strictSlackShell x R N hRN) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (additiveBoxSimplex_volume_ne_top x hN)
  apply measure_mono
  intro u hu
  rcases hu with hu | hu
  · exact hu.1
  · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
    exact hi.1

theorem strictSlackShell_volume_bound {x : ℝ} {R N : ℕ}
    (hB : 0 < B x) (hN : 0 < N) (hRN : R ≤ N) :
    volume.real (strictSlackShell x R N hRN) ≤
      ((N : ℝ)/B x*(strictTopWidth x+
        ∑ i : Fin R, g (i.val+1)*strictSlackWidth x (i.val+1)))*
      Real.exp ((N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N := by
  let F := Real.exp ((N : ℝ)/B x*(boxTopError x+
    ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N
  have htop := additive_top_shell_bound hB hN (boxTopError x)
    (fun i => boxSlackError x (i.val+1)) (boxTopError_nonneg hB.le)
    (fun i => boxSlackError_nonneg _ _) (strictTopWidth_nonneg hB.le)
  have htop' : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x+boxTopError x-strictTopWidth x) 0
        (fun i => -boxSlackError x (i.val+1))) ≤ (strictTopWidth x*N/B x)*F := by
    simpa only [Pi.neg_def, additiveBoxSimplex, F, mul_assoc] using htop
  have hrow (i : Fin R) : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x+boxTopError x) 0
        (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
          (strictSlackWidth x (i.val+1)))) ≤
      (strictSlackWidth x (i.val+1)*N*g (i.val+1)/B x)*F := by
    have hh := additive_slack_shell_bound hB hN (boxTopError x)
      (fun j => boxSlackError x (j.val+1)) (boxTopError_nonneg hB.le)
      (fun j => boxSlackError_nonneg _ _) (Fin.castLE hRN i)
      (strictSlackWidth_nonneg x (i.val+1))
    simpa only [Pi.neg_def, Fin.val_castLE, additiveBoxSimplex, F, mul_assoc] using hh
  apply (measureReal_union_le _ _).trans
  apply (add_le_add htop' ((measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun i _ => hrow i)))).trans_eq
  have heq : (∑ i : Fin R, strictSlackWidth x (i.val+1)*N*g (i.val+1)/B x) =
      ((N : ℝ)/B x)*∑ i : Fin R, g (i.val+1)*strictSlackWidth x (i.val+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.sum_mul, heq]
  dsimp [F]
  ring

end TotientAsymptotic

end

end OAI
