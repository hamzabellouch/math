import OAI.MeasureTheory.Falconer.Estimates.ScalarDyadicPowers

namespace OAI

/-! Place actual scalar points in the existing half-open dyadic tree. -/
namespace Falconer.Regularization

noncomputable def scalarUnitPoint (x : ℝ) : Space 1 := WithLp.toLp 2 (fun _ => x)

 theorem scalar_point_has_path (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    ∃ p ∈ cubePaths 1 N, scalarUnitPoint x ∈ ((⟨0,1⟩ : DyadicCube 1).descendant p).carrier := by
  apply (⟨0,1⟩ : DyadicCube 1).mem_descendant_at_depth N
  intro i
  simpa only [DyadicCube.carrier,scalarUnitPoint,PiLp.toLp_apply,PiLp.zero_apply,zero_add] using hx

noncomputable def scalarPointPath (N : ℕ) (x : ℝ) : CellPath 1 :=
  if hx : 0 ≤ x ∧ x < 1 then Classical.choose (scalar_point_has_path N hx)
  else List.replicate N (fun _ => false)

 theorem scalarPointPath_mem (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    scalarPointPath N x ∈ cubePaths 1 N := by
  simp only [scalarPointPath,dite_eq_left hx]
  exact (Classical.choose_spec (scalar_point_has_path N hx)).1

 theorem scalarPointPath_contains (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    scalarUnitPoint x ∈ ((⟨0,1⟩ : DyadicCube 1).descendant (scalarPointPath N x)).carrier := by
  simp only [scalarPointPath,dite_eq_left hx]
  exact (Classical.choose_spec (scalar_point_has_path N hx)).2

 theorem scalar_point_path_error (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    |x-scalarPathCenter (scalarPointPath N x)| ≤ (1/2:ℝ)^N/2 := by
  have hp := (mem_cubePaths 1 N _).mp (scalarPointPath_mem N hx)
  have hm := scalarPointPath_contains N hx 0
  have hs : ((⟨0,1⟩ : DyadicCube 1).descendant (scalarPointPath N x)).side = (1/2:ℝ)^N := by
    rw [DyadicCube.descendant_side,hp]
    simp only [div_pow,one_pow]
  change _ ≤ x ∧ x < _ at hm
  change |x-(_+_/2)| ≤ _
  rw [hs]
  rw [hs] at hm
  rw [abs_le]
  constructor <;> linarith

 theorem scalar_point_path_same {N : ℕ} {x y : ℝ} (hx : 0 ≤ x ∧ x < 1)
    (hy : 0 ≤ y ∧ y < 1) (heq : scalarPointPath N x = scalarPointPath N y) :
    |x-y| < (1/2:ℝ)^N := by
  have hp := (mem_cubePaths 1 N _).mp (scalarPointPath_mem N hx)
  have hm := scalarPointPath_contains N hx 0
  have hn := scalarPointPath_contains N hy 0
  rw [← heq] at hn
  have hs : ((⟨0,1⟩ : DyadicCube 1).descendant (scalarPointPath N x)).side = (1/2:ℝ)^N := by
    rw [DyadicCube.descendant_side,hp]
    simp only [div_pow,one_pow]
  change _ ≤ x ∧ x < _ at hm
  change _ ≤ y ∧ y < _ at hn
  rw [hs] at hm hn
  rw [abs_lt]
  constructor <;> linarith

end Falconer.Regularization

end OAI
