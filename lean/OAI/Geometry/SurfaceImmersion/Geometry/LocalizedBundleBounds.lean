import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedCompositionBounds

namespace OAI

/-! Weighted bounds for localized vector-bundle transition operators. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private lemma restricted_weighted_bound {U O : Set Base} (hU : IsOpen U)
    (hO : IsOpen O) (hUO : closure U ⊆ O) {f : Base → V}
    (hf : ContDiffOn ℝ ∞ f O) {m : ℕ} {A : ℝ}
    (hb : ∀ j ≤ m, ∀ x ∈ closure U, ‖iteratedFDerivWithin ℝ j f O x‖ ≤ A)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : WeightedBound U s m A f := by
  intro j hj x hx
  have ht : ContDiffAt ℝ (j : ℕ∞ω) f x :=
    (hf.of_le (by simp)).contDiffAt (hO.mem_nhds (hUO (subset_closure hx)))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
  have h := hb j hj x (subset_closure hx)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht
    (hUO (subset_closure hx))] at h
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h

/-- Smooth changes of fiber coordinates and base coordinates together cost
only a fixed constant in each weighted norm. -/
theorem compact_localized_clm_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {L : Base → V →L[ℝ] W} (hL : ContDiffOn ℝ ∞ L O)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • L x (f (T x))) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hL m
  obtain ⟨E, hE, hbE⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * (2 ^ m * B * ((m.factorial : ℝ) * E ^ m)), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ E := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by simp)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbE j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb := restricted_weighted_bound hU hO hUO hχ.contDiffOn hbA hs hs1
  have hLb := restricted_weighted_bound hU hO hUO hL hbB hs hs1
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hE hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hlc := hLb.clm_apply hU.uniqueDiffOn hs.le (zero_le_one.trans hB)
    (by positivity) (hL.mono hsub) hcomp hc
  have hlcs : ContDiffOn ℝ ∞ (fun x => L x (f (T x))) U :=
    (hL.mono hsub).clm_apply hcomp
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hlcs hlc
  have hlocal := hχ.contDiffOn.smul hlcs
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • L x (f (T x))) x :=
      (hlocal.of_le (by simp)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    ring
  · have hxχ : x ∉ tsupport χ := fun h => hx (hKU (hχK h))
    have heq : (fun y => χ y • L y (f (T y))) =ᶠ[𝓝 x] (fun _ => (0 : W)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
