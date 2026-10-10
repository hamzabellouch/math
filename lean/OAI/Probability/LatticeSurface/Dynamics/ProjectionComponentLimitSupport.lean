import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionComponentMesh
import OAI.Probability.LatticeSurface.Dynamics.ProjectionLimitSupport

namespace OAI

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V]

lemma pathMesh_grid (S : System V E) (b h : V → ℝ) (hh : h∈feasible S b)
    (w : ℝ → FreeSpace S) (N : ℕ) (hN : 0<N) (i : ℕ) :
    pathMesh S b h hh w N ((i:ℝ)/N)=recursion S b ⟨h,hh⟩ h (pathIncrement S w N) i := by
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp [pathMesh,div_mul_cancel₀ (i:ℝ) hN0]

lemma pathMesh_cut_eventually (S : System V E) (W : Set V)
    (b h : V → ℝ) (hh : h∈feasible S b) (w : ℝ → FreeSpace S) (u : ℝ → V → ℝ)
    (hlim : TendstoUniformlyOn (fun n => pathMesh S b h hh w (n+1)) u atTop (Icc 0 1))
    (δ : ℝ) (hδ : 0<δ)
    (hcut : ∀t∈Icc (0:ℝ) 1,∀e,S.cost e-(u t (S.left e)-u t (S.right e))≤δ →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W)) :
    ∀ᶠ n in atTop,∀i<n+1,∀e,
      recursion S b ⟨h,hh⟩ h (pathIncrement S w (n+1)) (i+1) (S.left e)-
        recursion S b ⟨h,hh⟩ h (pathIncrement S w (n+1)) (i+1) (S.right e)=S.cost e →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W) := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (δ/4) (by linarith)] with n hn i hi e he hl hr
  have hN : (0:ℝ)<((n+1:ℕ):ℝ) := by positivity
  have ht : ((i+1:ℕ):ℝ)/((n+1:ℕ):ℝ)∈Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hN).mpr
      exact_mod_cast (Nat.succ_le_of_lt hi)
  have hb (x : V) : |recursion S b ⟨h,hh⟩ h (pathIncrement S w (n+1)) (i+1) x-u (((i+1:ℕ):ℝ)/((n+1:ℕ):ℝ)) x|<δ/4 := by
    have hhx := (dist_le_pi_dist _ _ x).trans_lt (hn _ ht)
    rw [pathMesh_grid S b h hh w (n+1) (Nat.succ_pos n)] at hhx
    simpa only [Real.dist_eq,abs_sub_comm] using hhx
  apply hcut _ ht e _ hl hr
  have hbl := abs_lt.mp (hb (S.left e))
  have hbr := abs_lt.mp (hb (S.right e))
  linarith

end ProjectionComparison

end OAI
