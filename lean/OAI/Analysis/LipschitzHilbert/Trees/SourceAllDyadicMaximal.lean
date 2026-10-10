import OAI.Analysis.LipschitzHilbert.Trees.SourceStrongDyadicMaximal
import OAI.Analysis.LipschitzHilbert.Trees.SourceMonotoneMaximal

namespace OAI

/-! Dyadic maximal averages over all integer scales. Uniform finite
estimates give the countable-scale estimate without any scale loss. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem dyadicWindow_mono (q : ℤ) (f : ℝ → ℝ) :
    Monotone (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f) := by
  apply monotone_nat_of_le_succ
  intro N x
  change (Finset.range (2*N+1)).sup' Finset.nonempty_range_add_one
    (fun j : ℕ => |cellMean q ((N:ℤ)-(j:ℤ)) f x|) ≤ _
  apply (Finset.sup'_le_iff _ _).mpr
  intro j hj
  have hj' : j≤2*N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have heq : (N:ℤ)-(j:ℤ)=((N+1:ℕ):ℤ)-((j+1:ℕ):ℤ) := by omega
  change |cellMean q ((N:ℤ)-(j:ℤ)) f x|≤_
  rw [heq]
  exact abs_cellMean_le_dyadicMaximal q (N+1:ℕ) (2*(N+1)) (j+1) (by omega) f x

def allDyadicMaximal (q : ℤ) (f : ℝ → ℝ) : ℝ → ℝ :=
  monotoneMaximal (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f)

theorem allDyadicMaximal_measurable (q : ℤ) (f : ℝ → ℝ) :
    Measurable (allDyadicMaximal q f) :=
  monotoneMaximal_measurable _ (fun N => dyadicMaximal_measurable q N (2*N) f)

theorem allDyadicMaximal_nonneg (q : ℤ) (f : ℝ → ℝ) (x : ℝ) :
    0≤allDyadicMaximal q f x := Real.sqrt_nonneg _

theorem cellMean_le_window (q k : ℤ) (f : ℝ → ℝ) (x : ℝ) :
    |cellMean q k f x|≤dyadicMaximal q (k.natAbs:ℤ) (2*k.natAbs) f x := by
  let N := k.natAbs
  let j := ((N:ℤ)-k).toNat
  have hk : -(N:ℤ)≤k ∧ k≤N := by
    dsimp only [N]
    rw [Int.natCast_natAbs]
    exact ⟨neg_abs_le k,le_abs_self k⟩
  have hj : (j:ℤ)=(N:ℤ)-k := Int.toNat_of_nonneg (by omega)
  have hbound : j≤2*N := by omega
  have hscale : (N:ℤ)-(j:ℤ)=k := by omega
  have hcell := abs_cellMean_le_dyadicMaximal q (N:ℤ) (2*N) j hbound f x
  rw [hscale] at hcell
  exact hcell

/-- The genuine dyadic maximal operator is L² bounded, and dominates
all integer-scale averages simultaneously outside a single null set. -/
theorem allDyadicMaximal_energy (q : ℤ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (allDyadicMaximal q f) 2 volume ∧
    (∫ x, (allDyadicMaximal q f x)^2)≤4*∫ x, (f x)^2 ∧
    ∀ᵐ x ∂volume, ∀ k : ℤ, |cellMean q k f x|≤allDyadicMaximal q f x := by
  have h := monotoneMaximal_energy volume
    (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f)
    (4*∫ x, (f x)^2) (mul_nonneg (by norm_num) (integral_nonneg (fun x => sq_nonneg (f x))))
    (fun N => dyadicMaximal_measurable q N (2*N) f)
    (fun N x => dyadicMaximal_nonneg q N (2*N) f x)
    (dyadicWindow_mono q f)
    (fun N => (dyadicMaximal_energy q N (2*N) hf).1)
    (fun N => (dyadicMaximal_energy q N (2*N) hf).2)
  refine ⟨h.1,h.2.1,?_⟩
  filter_upwards [h.2.2] with x hx
  intro k
  exact (cellMean_le_window q k f x).trans (hx k.natAbs)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
