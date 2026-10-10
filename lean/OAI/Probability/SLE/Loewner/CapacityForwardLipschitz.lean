import OAI.Probability.SLE.Loewner.InitialForwardIncrement
import OAI.Probability.SLE.Loewner.InitialCapacityClock
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! On any strictly surviving prefix, the exact forward flow is Lipschitz
in its capacity parameter. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialForwardChart_im_pos (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    0<(initialForwardChart p hi h0 hH T z).im :=
  initialForwardChart_mem_upper p hi h0 hH T hz

theorem initialForward_prefix_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T))
    {s t : unitInterval} (hs : s≤T) (ht : t≤T) :
    ‖initialForwardChart p hi h0 hH t z-initialForwardChart p hi h0 hH s z‖≤
      |initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s|/
        (initialForwardChart p hi h0 hH T z).im := by
  have hy : 0<(initialForwardChart p hi h0 hH T z).im :=
    initialForwardChart_mem_upper p hi h0 hH T hz
  have hdom (r : unitInterval) (hr : r≤T) :
      z∈upperHalfPlane \ range (initialSubarc p r) :=
    ⟨hz.1,fun he => hz.2 (initialSubarc_range_mono p hr he)⟩
  have hordered (a b : unitInterval) (hb : b≤T) (hab : a≤b) :
      ‖initialForwardChart p hi h0 hH b z-initialForwardChart p hi h0 hH a z‖≤
        |initialCapacity p hi h0 hH b-initialCapacity p hi h0 hH a|/
          (initialForwardChart p hi h0 hH T z).im := by
    have hc : 0 ≤ initialCapacity p hi h0 hH b-initialCapacity p hi h0 hH a :=
      sub_nonneg.mpr (initialCapacity_monotone p hi h0 hH hab)
    rw [abs_of_nonneg hc]
    obtain rfl | hab := hab.eq_or_lt
    · simp only [sub_self,norm_zero,zero_div,le_refl]
    have hh := initialForward_increment_bound p hi h0 hH hab (hb.trans_lt hT) (hdom b hb)
    exact hh.trans (div_le_div_of_nonneg_left hc hy
      (initialForward_height_antitone p hi h0 hH hb hT hz))
  rcases le_total s t with hst | hts
  · exact hordered s t ht hst
  · simpa only [norm_sub_rev,abs_sub_comm] using hordered t s hs hts

noncomputable def prefixCapacityTime (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (c : Icc 0 (initialCapacity p hi h0 hH T)) : unitInterval :=
  (initialCapacityHomeomorph p hi h0 hH).symm
    ⟨c.1,c.2.1,c.2.2.trans (initialCapacity_monotone p hi h0 hH le_top)⟩

@[simp] lemma prefixCapacityTime_capacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (c : Icc 0 (initialCapacity p hi h0 hH T)) :
    initialCapacity p hi h0 hH (prefixCapacityTime p hi h0 hH T c)=(c:ℝ) :=
  initialCapacityHomeomorph_symm_capacity p hi h0 hH _

lemma prefixCapacityTime_le (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (c : Icc 0 (initialCapacity p hi h0 hH T)) :
    prefixCapacityTime p hi h0 hH T c≤T := by
  apply (initialCapacity_strictMono p hi h0 hH).le_iff_le.mp
  rw [prefixCapacityTime_capacity]
  exact c.2.2

theorem capacityForward_lipschitz (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    LipschitzWith (NNReal.mk ((initialForwardChart p hi h0 hH T z).im)⁻¹
      (inv_nonneg.mpr (le_of_lt (initialForwardChart_im_pos p hi h0 hH T hz))))
      (fun c : Icc 0 (initialCapacity p hi h0 hH T) =>
        initialForwardChart p hi h0 hH (prefixCapacityTime p hi h0 hH T c) z) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  rw [dist_eq_norm,Subtype.dist_eq]
  change ‖initialForwardChart p hi h0 hH (prefixCapacityTime p hi h0 hH T c) z-
      initialForwardChart p hi h0 hH (prefixCapacityTime p hi h0 hH T d) z‖≤
    ((initialForwardChart p hi h0 hH T z).im)⁻¹*dist (c:ℝ) (d:ℝ)
  have hh := initialForward_prefix_bound p hi h0 hH hT hz
    (prefixCapacityTime_le p hi h0 hH T d) (prefixCapacityTime_le p hi h0 hH T c)
  rw [prefixCapacityTime_capacity,prefixCapacityTime_capacity] at hh
  simpa only [Real.dist_eq,div_eq_mul_inv,mul_comm] using hh

end SLEExactGauge

end

end OAI
