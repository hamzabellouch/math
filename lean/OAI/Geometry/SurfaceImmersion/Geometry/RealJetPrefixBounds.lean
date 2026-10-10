import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadPrefixBounds
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartStability

namespace OAI

/-! Two-jet bounds retain the two unscaled derivatives of a smoothed immersion. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates FiniteOrderSmoothing

theorem realTwoJet_prefix_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+2, WeightedBound univ 1 j (C/s^(j-2)) F) :
    WeightedBound univ s m C (realTwoJet F) := by
  have hfirst (v : Base) (hv : ‖v‖ = 1) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound univ 1 j (C/s^(j-1)) (coordDeriv v F) := by
    have hh := (hb (j+1) (by omega)).directional isOpen_univ zero_lt_one hF.contDiffOn v
    change WeightedBound univ 1 j (C/s^(j-1)) (fun x => fderiv ℝ F x v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hv,one_mul,div_one,he] using hh
  have hfirst' (v : Base) (hv : ‖v‖ = 1) :
      WeightedBound univ s m C (coordDeriv v F) := by
    apply prefix_directional_bound hF hs hC _ v hv.le
    intro j hj
    apply (hb j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have hsecond (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      WeightedBound univ s m C (coordDeriv v (coordDeriv w F)) :=
    prefix_directional_bound (contDiff_real_coordDeriv hF w) hs hC (hfirst w hw) v hv.le
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  change WeightedBound univ s m C (fun x i => realTwoJet F x i)
  apply WeightedBound.pi uniqueDiffOn_univ hs hC
  · intro i
    fin_cases i <;> first
      | exact (contDiff_real_coordDeriv hF _).contDiffOn
      | exact (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF _) _).contDiffOn
  · intro i
    fin_cases i
    · exact hfirst' dx hx
    · exact hfirst' dy hy
    · exact hsecond dx dx hx hx
    · exact hsecond dx dy hx hy
    · exact hsecond dy dy hy hy

/-- Fixed smooth coordinates preserve the shifted two-derivative bound.
The constant is independent of the map and of the smoothing scale. -/
theorem compact_realTwoJet_comp_prefix_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (K : Compacts Base) {U : Set Base} (hU : IsOpen U) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4), ContDiff ℝ ∞ F → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound univ 1 j (C/s^(j-2)) F) →
      WeightedBound U s m (D*C) (realTwoJet (F ∘ T)) := by
  obtain ⟨B,hB,hb⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) hT.contDiffOn (m+2)
  let D : ℝ := ((m+2).factorial : ℝ)*B^(m+2)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m+2))) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro F hF s C hs hs1 hC hp
  have hcomp (j : ℕ) (hj : j ≤ m+2) :
      WeightedBound U 1 j (D*C/s^(j-2)) (F ∘ T) := by
    have hc (k : ℕ) (_ : 1 ≤ k) (hk : k ≤ j) (x : Base) (hx : x ∈ U) :
        ‖iteratedFDerivWithin ℝ k T U x‖ ≤ B := by
      simpa only [one_pow,one_mul] using hb 1 zero_le_one le_rfl k (hk.trans hj) x hx
    have hh := (hp j hj).comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ
      zero_lt_one le_rfl hB (div_nonneg hC (pow_nonneg hs.le _))
      hT.contDiffOn hF.contDiffOn (mapsTo_univ _ _) hc
    apply hh.mono_const
    calc
      (j.factorial : ℝ)*(C/s^(j-2))*B^j = ((j.factorial : ℝ)*B^j)*C/s^(j-2) := by ring
      _ ≤ D*C/s^(j-2) := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
        apply mul_le_mul_of_nonneg_right _ hC
        dsimp [D]
        gcongr
  have hfirst (v : Base) (hv : ‖v‖ = 1) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (D*C/s^(j-1)) (coordDeriv v (F ∘ T)) := by
    have hh := (hcomp (j+1) (by omega)).directional hU zero_lt_one (hF.comp hT).contDiffOn v
    change WeightedBound U 1 j (D*C/s^(j-1)) (fun x => fderiv ℝ (F ∘ T) x v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hv,one_mul,div_one,he] using hh
  have hC' : 0 ≤ D*C := mul_nonneg (zero_le_one.trans hD) hC
  have hd (f : RField 4) (hf : ContDiff ℝ ∞ f)
      (hf' : ∀ j ≤ m+1, WeightedBound U 1 j (D*C/s^(j-1)) f)
      (v : Base) (hv : ‖v‖ = 1) : WeightedBound U s m (D*C) (coordDeriv v f) := by
    intro j hj x hx
    have hh := ((hf' (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
      j le_rfl x hx
    simp only [one_pow,one_mul,div_one,hv,Nat.add_sub_cancel] at hh
    calc
      _ ≤ s^j*(D*C/s^j) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ = D*C := by field_simp
  have hf (v : Base) (hv : ‖v‖ = 1) :
      WeightedBound U s m (D*C) (coordDeriv v (F ∘ T)) := by
    apply hd (F ∘ T) (hF.comp hT) _ v hv
    intro j hj
    apply (hcomp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC' (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have hdd (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      WeightedBound U s m (D*C) (coordDeriv v (coordDeriv w (F ∘ T))) :=
    hd _ (contDiff_real_coordDeriv (hF.comp hT) w) (hfirst w hw) v hv
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  change WeightedBound U s m (D*C) (fun x i => realTwoJet (F ∘ T) x i)
  apply WeightedBound.pi hU.uniqueDiffOn hs hC'
  · intro i
    fin_cases i <;> first
      | exact (contDiff_real_coordDeriv (hF.comp hT) _).contDiffOn
      | exact (contDiff_real_coordDeriv (contDiff_real_coordDeriv (hF.comp hT) _) _).contDiffOn
  · intro i
    fin_cases i
    · exact hf dx hx
    · exact hf dy hy
    · exact hdd dx dx hx hx
    · exact hdd dx dy hx hy
    · exact hdd dy dy hy hy

end ClosedSurfaceR4.RealModes

end

end OAI
