import OAI.Geometry.SurfaceImmersion.Geometry.RealJetPrefixBounds
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetPrefixBounds
import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseChart

namespace OAI

/-! Fixed phase charts transfer original-coordinate prefix bounds to the
two-jet profiles needed by the actual mean and quadratic solvers. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4
open WeightedEstimates

namespace RealModes
open SmallModes

theorem realTwoJet_prefix_bound_on {U : Set Base} (hU : IsOpen U)
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m + 2, WeightedBound U 1 j (C / s ^ (j - 2)) F) :
    WeightedBound U s m C (realTwoJet F) := by
  have hfirst (v : Base) (hv : ‖v‖ = 1) (j : ℕ) (hj : j ≤ m + 1) :
      WeightedBound U 1 j (C / s ^ (j - 1)) (coordDeriv v F) := by
    have hh := (hb (j + 1) (by omega)).directional hU zero_lt_one hF.contDiffOn v
    change WeightedBound U 1 j (C / s ^ (j - 1)) (fun x => fderiv ℝ F x v)
    have he : j + 1 - 2 = j - 1 := by omega
    simpa only [hv,one_mul,div_one,he] using hh
  have hfirst' (v : Base) (hv : ‖v‖ = 1) :
      WeightedBound U s m C (coordDeriv v F) := by
    apply directional_of_prefix hU hF hs hC _ v hv.le
    intro j hj
    apply (hb j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have hsecond (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      WeightedBound U s m C (coordDeriv v (coordDeriv w F)) :=
    directional_of_prefix hU (contDiff_real_coordDeriv hF w) hs hC (hfirst w hw) v hv.le
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  change WeightedBound U s m C (fun x i => realTwoJet F x i)
  apply WeightedBound.pi hU.uniqueDiffOn hs hC
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

end RealModes

namespace JetPolynomial.Perturbation
open RealModes PhaseGeometry

theorem local_realTwoJet_comp_prefix_bound
    {T : SmallModes.Base → Base} (hT : ContDiff ℝ ∞ T)
    (K : Compacts SmallModes.Base) {V : Set SmallModes.Base} (hV : IsOpen V)
    (hVK : V ⊆ K) {U₀ : Set Base} (hU₀ : IsOpen U₀)
    (hTU : MapsTo T V U₀) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m + 2, WeightedBound U₀ 1 j (C / s ^ (j - 2)) G) →
      WeightedBound V s m (D * C) (realTwoJet (G ∘ T)) := by
  obtain ⟨B,hB,hb⟩ := compact_local_weighted_bound hV isOpen_univ K.isCompact hVK
    (subset_univ _) hT.contDiffOn (m + 2)
  let D : ℝ := ((m + 2).factorial : ℝ) * B ^ (m + 2)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m + 2))) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro G hG s C hs hs1 hC hp
  apply realTwoJet_prefix_bound_on hV (hG.comp hT) hs hs1
    (mul_nonneg (zero_le_one.trans hD) hC)
  intro j hj
  have hc (k : ℕ) (_ : 1 ≤ k) (hkj : k ≤ j) (x : SmallModes.Base) (hx : x ∈ V) :
      ‖iteratedFDerivWithin ℝ k T V x‖ ≤ B := by
    simpa only [one_pow,one_mul] using hb 1 zero_le_one le_rfl k (hkj.trans hj) x hx
  have hh := (hp j hj).comp_coordinates hV.uniqueDiffOn hU₀.uniqueDiffOn zero_lt_one le_rfl
    hB (div_nonneg hC (pow_nonneg hs.le _)) hT.contDiffOn hG.contDiffOn hTU hc
  apply hh.mono_const
  calc
    (j.factorial : ℝ) * (C / s ^ (j - 2)) * B ^ j =
        ((j.factorial : ℝ) * B ^ j) * C / s ^ (j - 2) := by ring
    _ ≤ D * C / s ^ (j - 2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
      apply mul_le_mul_of_nonneg_right _ hC
      dsimp [D]
      gcongr

/-- The profiles work simultaneously at every order, so evaluating the
same conclusion at `m + 1` supplies the quadratic solver's input profile. -/
theorem linear_phase_twoJet_profiles {ι : Type*}
    (ξ : ι → SmallModes.Base) (hξ : ∀ i, ξ i ≠ 0)
    (U : ι → Set SmallModes.Base) (hU : ∀ i, IsOpen (U i))
    (K : ι → Compacts SmallModes.Base) (hUK : ∀ i, U i ⊆ K i)
    {U₀ : Set Base} (hU₀ : IsOpen U₀)
    (hinto : ∀ i x, x ∈ U i → planeCoordinateIsometry.symm x ∈ U₀)
    (Pjet : ℕ → ℝ) (hPjet : ∀ m, 0 ≤ Pjet m) :
    ∃ H : ι → ℕ → ℝ, (∀ i m, 1 ≤ H i m) ∧
      ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j (Pjet m / s ^ (j - 2)) G) →
      ∀ i m, WeightedBound (linearPhaseChart (ξ i) (hξ i) (U i) (hU i)).target
        s m (H i m) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
          (linearPhaseChart (ξ i) (hξ i) (U i) (hU i)).symm)) := by
  classical
  let e := fun i => linearPhaseChart (ξ i) (hξ i) (U i) (hU i)
  let T := fun i => planeCoordinateIsometry.symm ∘ (e i).symm
  let KV := fun i => (K i).map (e i) (linearPhaseChart_smooth (ξ i) (hξ i) (U i) (hU i)).1.continuous
  have hT (i : ι) : ContDiff ℝ ∞ (T i) :=
    planeCoordinateIsometry.symm.contDiff.comp
      (linearPhaseChart_smooth (ξ i) (hξ i) (U i) (hU i)).2
  have hVK (i : ι) : (e i).target ⊆ KV i := by
    exact image_mono (hUK i)
  have hTU (i : ι) : MapsTo (T i) (e i).target U₀ := by
    intro x hx
    exact hinto i ((e i).symm x) ((e i).map_target hx)
  choose D hD hd using fun i m => local_realTwoJet_comp_prefix_bound (hT i)
    (KV i) (e i).open_target (hVK i) hU₀ (hTU i) m
  let H := fun i m => 1 + D i m * Pjet m
  refine ⟨H,?_,?_⟩
  · intro i m
    exact le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans (hD i m)) (hPjet m))
  · intro G hG s hs hs1 hp i m
    have hh := hd i m G hG s (Pjet m) hs hs1 (hPjet m) (hp m)
    apply (show WeightedBound (e i).target s m (D i m * Pjet m)
      (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘ (e i).symm)) from hh).mono_const
    exact le_add_of_nonneg_left zero_le_one

end JetPolynomial.Perturbation
end ClosedSurfaceR4

end

end OAI
