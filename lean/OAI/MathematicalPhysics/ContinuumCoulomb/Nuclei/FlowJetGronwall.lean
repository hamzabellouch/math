import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowHigherComposition

namespace OAI

/-! A coarse positive-coefficient Gronwall bound for inhomogeneous jets. -/

noncomputable section
open Set
namespace ContinuumCoulomb

theorem flow_inhomogeneous_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u du : ℝ → E) (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (du t) (Icc (0:ℝ) 1) t)
    (hzero : ‖u 0‖ = 0)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖du t‖ ≤ B*‖u t‖+A)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖u t‖ ≤ A * Real.exp (B+1) := by
  have hright (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt u (du s) (Ici s) s := by
    apply (hd s ⟨hs.1,hs.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  have hb (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      ‖du s‖ ≤ (B+1)*‖u s‖+A :=
    (hbound s ⟨hs.1,hs.2.le⟩).trans (by nlinarith [norm_nonneg (u s)])
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivWithinAt.continuousOn hd) hright (show ‖u 0‖ ≤ 0 by rw [hzero]) hb t ht
  have hpos : 0 < B+1 := by linarith
  simp only [gronwallBound,hpos.ne',↓reduceIte,zero_mul,zero_add,sub_zero] at h
  have ha : A/(B+1) ≤ A := (div_le_iff₀ hpos).mpr (by nlinarith)
  have hexp : 0 ≤ Real.exp ((B+1)*t)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hpos.le ht.1))
  have he : Real.exp ((B+1)*t) ≤ Real.exp (B+1) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.2])
  apply h.trans
  calc
    A/(B+1)*(Real.exp ((B+1)*t)-1) ≤ A*(Real.exp ((B+1)*t)-1) :=
      mul_le_mul_of_nonneg_right ha hexp
    _ ≤ A*Real.exp ((B+1)*t) := mul_le_mul_of_nonneg_left (by linarith) hA
    _ ≤ A*Real.exp (B+1) := mul_le_mul_of_nonneg_left he hA

end ContinuumCoulomb

end

end OAI
