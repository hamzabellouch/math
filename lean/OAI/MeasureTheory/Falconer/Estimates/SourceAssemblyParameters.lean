import OAI.MeasureTheory.Falconer.Shells.SmoothShellPartition

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem exists_source_assembly_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ β lam sig kap : ℝ, β = δ/10 ∧ 0 < lam ∧ lam < δ/1000 ∧ 0 < sig ∧
      0 < kap ∧ 1000000*kap < β ∧ sig < kap/1000 ∧
      10000000*(lam+sig)/kap < β/100 := by
  let kap := δ/1000000000
  let lam := δ^2/1000000000000000000000000
  have hd2 : 0 < δ^2 := sq_pos_of_pos hδ
  have hd2δ : δ^2 < δ := by nlinarith
  have hkap : 0 < kap := by dsimp only [kap]; positivity
  refine ⟨δ/10,lam,lam,kap,rfl,?_,?_,?_,hkap,?_,?_,?_⟩
  · dsimp only [lam]; positivity
  · dsimp only [lam]; nlinarith
  · dsimp only [lam]; positivity
  · dsimp only [kap]; linarith
  · dsimp only [lam,kap]; nlinarith
  · apply (div_lt_iff₀ hkap).mpr
    dsimp only [lam,kap]
    nlinarith

noncomputable def assemblyShellBump : ContDiffBump (5/4 : ℝ) where
  rIn := 3/4
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem exists_assembly_shell_cutoff :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ (∀ x, 0 ≤ Ψ x) ∧
      (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) ∧
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) := by
  refine ⟨assemblyShellBump,assemblyShellBump.contDiff,fun _ => assemblyShellBump.nonneg,?_,?_⟩
  · intro x hx
    have hh : dist x (5/4:ℝ) < 1 := by
      by_contra hn
      exact hx (assemblyShellBump.zero_of_le_dist (not_lt.mp hn))
    rw [Real.dist_eq,abs_lt] at hh
    constructor <;> linarith
  · intro x hx
    have hh : x ∈ closedBall (5/4:ℝ) assemblyShellBump.rIn := by
      change dist x (5/4:ℝ) ≤ 3/4
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [hx.1,hx.2]
    rw [assemblyShellBump.one_of_mem_closedBall hh]

end PlanarFalconer

end OAI
