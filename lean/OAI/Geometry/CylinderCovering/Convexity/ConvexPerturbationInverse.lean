import OAI.Geometry.CylinderCovering.Convexity.ThresholdInversion

namespace OAI

open Set
open scoped NNReal

namespace CylinderCovering.ConvexPerturbationInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_nonexpansive_projection {C : Set E} (hCne : C.Nonempty)
    (hCcomplete : IsComplete C) (hCconvex : Convex ℝ C) :
    ∃ P : E → E, (∀ y, P y ∈ C) ∧ LipschitzWith 1 P ∧
      ∀ y, ∀ w ∈ C, inner ℝ (y - P y) (w - P y) ≤ 0 := by
  classical
  choose P hPmem hPmin using
    (exists_norm_eq_iInf_of_complete_convex hCne hCcomplete hCconvex)
  have hnormal : ∀ y, ∀ w ∈ C, inner ℝ (y - P y) (w - P y) ≤ 0 := by
    intro y
    exact (norm_eq_iInf_iff_real_inner_le_zero hCconvex (hPmem y)).mp (hPmin y)
  refine ⟨P, hPmem, LipschitzWith.of_dist_le_mul ?_, hnormal⟩
  intro y z
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hy := hnormal y (P z) (hPmem z)
  have hz := hnormal z (P y) (hPmem y)
  have hy' : 0 ≤ inner ℝ (y - P y) (P y - P z) := by
    have heq : P z - P y = -(P y - P z) := by abel
    rw [heq, inner_neg_right] at hy
    linarith
  have hidentity : y - z = (y - P y) - (z - P z) + (P y - P z) := by abel
  have hlower : ‖P y - P z‖ ^ 2 ≤ inner ℝ (y - z) (P y - P z) := by
    rw [hidentity, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  have hupper := real_inner_le_norm (y - z) (P y - P z)
  by_cases hzero : ‖P y - P z‖ = 0
  · rw [hzero]
    exact norm_nonneg _
  · have hpos : 0 < ‖P y - P z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

theorem normal_residual_eq_zero {C : Set E} {p y v : E}
    (hy : y ∈ C)
    (hnormal : ∀ w ∈ C, inner ℝ (y - (p + v)) (w - p) ≤ 0)
    (htangent : ∃ η : ℝ, 0 < η ∧ p + η • v ∈ C ∧ p - η • v ∈ C) :
    p + v = y := by
  obtain ⟨η, hη, hplus, hminus⟩ := htangent
  have hp := hnormal (p + η • v) hplus
  have hm := hnormal (p - η • v) hminus
  have hsubplus : p + η • v - p = η • v := by abel
  have hsubminus : p - η • v - p = -(η • v) := by abel
  rw [hsubplus, inner_smul_right] at hp
  rw [hsubminus, inner_neg_right, inner_smul_right] at hm
  have hperp : inner ℝ (y - (p + v)) v = 0 := by nlinarith
  have hyinner := hnormal y hy
  have hdecomp : y - p = (y - (p + v)) + v := by abel
  rw [hdecomp, inner_add_right, hperp, add_zero, real_inner_self_eq_norm_sq] at hyinner
  have hzero : y - (p + v) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (y - (p + v))]
  exact (sub_eq_zero.mp hzero).symm

theorem existsUnique_inverse_of_tangent {C : Set E} (hCne : C.Nonempty)
    (hCcomplete : IsComplete C) (hCconvex : Convex ℝ C)
    {g : E → E} {c : ℝ≥0} (hc : c < 1) (hLip : LipschitzOnWith c g C)
    (htangent : ∀ p ∈ C, ∃ η : ℝ, 0 < η ∧ p + η • g p ∈ C ∧ p - η • g p ∈ C)
    {y : E} (hy : y ∈ C) :
    ∃! p : E, p ∈ C ∧ p + g p = y := by
  obtain ⟨P, hPmem, hPlip, hPnormal⟩ :=
    exists_nonexpansive_projection hCne hCcomplete hCconvex
  let f : E → E := fun p => P (y - g p)
  have hmaps : MapsTo f C C := by
    intro p _
    exact hPmem _
  have hf : ContractingWith c (hmaps.restrict f C C) := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro p q
    change dist (P (y - g p)) (P (y - g q)) ≤ (c : ℝ) * dist (p : E) (q : E)
    calc
      dist (P (y - g p)) (P (y - g q)) ≤ dist (y - g p) (y - g q) := by
        simpa only [NNReal.coe_one, one_mul] using hPlip.dist_le_mul (y - g p) (y - g q)
      _ = dist (g p) (g q) := dist_sub_left _ _ _
      _ ≤ (c : ℝ) * dist (p : E) (q : E) := hLip.dist_le_mul p p.property q q.property
  obtain ⟨p₀, hp₀⟩ := hCne
  obtain ⟨p, hp, hfix, _⟩ :=
    ContractingWith.exists_fixedPoint' hCcomplete hmaps hf hp₀ (edist_ne_top _ _)
  have hfix' : P (y - g p) = p := hfix
  have hnormal : ∀ w ∈ C, inner ℝ (y - (p + g p)) (w - p) ≤ 0 := by
    intro w hw
    have hn := hPnormal (y - g p) w hw
    rw [hfix'] at hn
    have hsame : y - g p - p = y - (p + g p) := by abel
    rwa [hsame] at hn
  have hpeq : p + g p = y := normal_residual_eq_zero hy hnormal (htangent p hp)
  refine ⟨p, ⟨hp, hpeq⟩, ?_⟩
  intro q hq
  apply ThresholdInversion.inverse_unique (show (c : ℝ) < 1 by exact_mod_cast hc) hq.2 hpeq
  simpa only [dist_eq_norm] using hLip.dist_le_mul p hp q hq.1

end CylinderCovering.ConvexPerturbationInverse

end OAI
