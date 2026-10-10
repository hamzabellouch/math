import OAI.NumberTheory.TotientAsymptotic.AdditiveShell
import OAI.NumberTheory.TotientAsymptotic.AdditiveCost

namespace OAI

/-! Summing all retained slack slices in one enlarged full-dimensional simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def additiveBoxSimplex (x : ℝ) (N : ℕ) : Set (Fin N → ℝ) :=
  prefixRegion N (B x+boxTopError x) 0 (fun i => -boxSlackError x (i.val+1))

def additiveBoxShell (x : ℝ) (R N : ℕ) (hRN : R ≤ N) : Set (Fin N → ℝ) :=
  (additiveBoxSimplex x N \
    prefixRegion N (B x-boxTopError x) 0 (fun i => -boxSlackError x (i.val+1))) ∪
  ⋃ i : Fin R, additiveBoxSimplex x N \
    prefixRegion N (B x+boxTopError x) 0
      (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
        (2*boxSlackError x (i.val+1)))

lemma additiveBoxSimplex_volume_ne_top (x : ℝ) {N : ℕ} (hN : 0 < N) :
    volume (additiveBoxSimplex x N) ≠ ⊤ := by
  rw [additiveBoxSimplex, volume_prefixRegion_explicit _ hN]
  exact ENNReal.ofReal_ne_top

lemma additiveBoxShell_volume_ne_top (x : ℝ) {R N : ℕ} (hRN : R ≤ N) (hN : 0 < N) :
    volume (additiveBoxShell x R N hRN) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (additiveBoxSimplex_volume_ne_top x hN)
  apply measure_mono
  intro u hu
  rcases hu with hu | hu
  · exact hu.1
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
    exact hi.1

/-- The union of all retained coordinate slices costs their sum, not the
number of tail witnesses or full-dimensional boxes. -/
theorem additiveBoxShell_volume_bound {x : ℝ} {R N : ℕ}
    (hB : 0 < B x) (hN : 0 < N) (hRN : R ≤ N) :
    volume.real (additiveBoxShell x R N hRN) ≤
      (2*(N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin R, g (i.val+1)*boxSlackError x (i.val+1)))*
      Real.exp ((N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N := by
  let F := Real.exp ((N : ℝ)/B x*(boxTopError x+
    ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N
  have htop := additive_top_shell_bound hB hN (boxTopError x)
    (fun i => boxSlackError x (i.val+1)) (boxTopError_nonneg hB.le)
    (fun i => boxSlackError_nonneg _ _) (t := 2*boxTopError x) (mul_nonneg (by norm_num) (boxTopError_nonneg hB.le))
  have htop' : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x-boxTopError x) 0 (fun i => -boxSlackError x (i.val+1))) ≤
      (2*boxTopError x*N/B x)*F := by
    have he : B x+boxTopError x-2*boxTopError x = B x-boxTopError x := by ring
    simpa only [he, Pi.neg_def, additiveBoxSimplex, F, mul_assoc] using htop
  have hrow (i : Fin R) : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x+boxTopError x) 0
        (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
          (2*boxSlackError x (i.val+1)))) ≤
      (2*boxSlackError x (i.val+1)*N*g (i.val+1)/B x)*F := by
    have hh := additive_slack_shell_bound hB hN (boxTopError x)
      (fun j => boxSlackError x (j.val+1)) (boxTopError_nonneg hB.le)
      (fun j => boxSlackError_nonneg _ _) (Fin.castLE hRN i)
      (t := 2*boxSlackError x (i.val+1)) (mul_nonneg (by norm_num) (boxSlackError_nonneg _ _))
    simpa only [Pi.neg_def, Fin.val_castLE, additiveBoxSimplex, F, mul_assoc] using hh
  apply (measureReal_union_le _ _).trans
  apply (add_le_add htop' ((measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun i _ => hrow i)))).trans_eq
  have heq : (∑ i : Fin R, 2*boxSlackError x (i.val+1)*N*g (i.val+1)/B x) =
      (2*(N : ℝ)/B x)*∑ i : Fin R, g (i.val+1)*boxSlackError x (i.val+1) := by
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
