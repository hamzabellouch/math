import OAI.Combinatorics.ProgressionColoring.AdaptiveMeshCounting
import OAI.Combinatorics.ProgressionColoring.TernarySign
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Literal three-way breakpoint factorization. All sets below are the actual
endpoint/threshold sets from `AdaptiveMeshCounting`. In particular an equality
at a truncation threshold keeps the original half-open label. -/

namespace QuantitativeVanDerWaerden

theorem continuous_rho : Continuous rho := by
  have h : LipschitzWith 1 rho := LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using rho_lipschitz x y)
  exact h.continuous

/-- Equal ternary signs exclude every closed-interval breakpoint when the
two evaluation points are distinct. Equality signs are essential here. -/
theorem no_breakpoint_of_same_signs {B : Finset ℝ} {x y : ℝ} (hxy : x < y)
    (hs : ∀ b ∈ B, ternarySign (x - b) = ternarySign (y - b)) :
    ∀ b ∈ B, ¬ (x ≤ b ∧ b ≤ y) := by
  intro b hb hbetween
  by_cases he : x = b
  · have hone : ternarySign (x - b) = 1 := (ternarySign_eq_one _).mpr (by rw [he]; ring)
    have hy : y - b = 0 := (ternarySign_eq_one _).mp ((hs b hb).symm.trans hone)
    linarith
  · have hx : x < b := lt_of_le_of_ne hbetween.1 he
    have hzero : ternarySign (x - b) = 0 := (ternarySign_eq_zero _).mpr (by linarith)
    have hy : y - b < 0 := (ternarySign_eq_zero _).mp ((hs b hb).symm.trans hzero)
    linarith [hbetween.2]

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

theorem meshLabel_eq_of_no_endpoint {x y : ℝ} (hxy : x ≤ y)
    (hno : ∀ r : ℝ, x ≤ r → r ≤ y →
      ∀ (i : A.Label) (z : ℤ), r ≠ A.left i + z) :
    A.meshLabel x = A.meshLabel y := by
  obtain ⟨i, z, hi⟩ := A.exists_lift_mem x
  have hxlo : A.left i + z ≤ x := by linarith [hi.1]
  have hxhi : x < A.right i + z := by linarith [hi.2]
  have hyhi : y < A.right i + z := by
    by_contra hy
    obtain ⟨j, w, hj⟩ := A.right_is_lifted_endpoint i z
    exact hno (A.right i + z) hxhi.le (le_of_not_gt hy) j w hj
  have hycell : A.Contains i (y - z) := ⟨by linarith, by linarith⟩
  exact (A.label_of_lift_mem i z hi).trans (A.label_of_lift_mem i z hycell).symm

theorem endpoints_determine_label (u v : ℝ) {x y : ℝ}
    (hx : u ≤ x ∧ x ≤ v) (hy : u ≤ y ∧ y ≤ v)
    (hs : ∀ b ∈ A.endpointsBetween u v,
      ternarySign (x - b) = ternarySign (y - b)) : A.meshLabel x = A.meshLabel y := by
  have hordered : ∀ p q : ℝ, u ≤ p ∧ p ≤ v → u ≤ q ∧ q ≤ v → p < q →
      (∀ b ∈ A.endpointsBetween u v, ternarySign (p - b) = ternarySign (q - b)) →
      A.meshLabel p = A.meshLabel q := by
    intro p q hp hq hpq hsign
    have hnone := no_breakpoint_of_same_signs hpq hsign
    apply A.meshLabel_eq_of_no_endpoint hpq.le
    intro r hpr hrq i z he
    have hr : r ∈ A.endpointsBetween u v := (A.mem_endpointsBetween u v r).mpr
      ⟨hp.1.trans hpr, hrq.trans hq.2, i, z, he⟩
    exact hnone r hr ⟨hpr, hrq⟩
  rcases lt_trichotomy x y with h | h | h
  · exact hordered x y hx hy h hs
  · rw [h]
  · exact (hordered y x hy hx h (fun b hb => (hs b hb).symm)).symm

noncomputable def truncatedLabel (η x : ℝ) : Option A.Label := by
  classical
  exact if η ≤ rho x then some (A.meshLabel x) else none

theorem truncatedLabel_eq_none_iff (η x : ℝ) :
    A.truncatedLabel η x = none ↔ rho x < η := by
  classical
  simp [truncatedLabel, not_le]

theorem truncatedLabel_add_int (η x : ℝ) (z : ℤ) :
    A.truncatedLabel η (x + z) = A.truncatedLabel η x := by
  classical
  simp only [truncatedLabel, rho_add_int, A.meshLabel_add_int]

theorem mem_thresholdPoints_of_rho_eq (η u v x : ℝ)
    (hx : u ≤ x ∧ x ≤ v) (he : rho x = η) : x ∈ thresholdPoints η u v := by
  classical
  let z : ℤ := ⌊x + 1 / 2⌋
  have hrep : centered x = x - z := rfl
  have hr : 1 / 2 - |centered x| = η := he
  rcases le_total (centered x) 0 with hn | hp
  · rw [abs_of_nonpos hn] at hr
    apply Finset.mem_union_left
    apply (mem_integerTranslatesBetween (η - 1 / 2) u v x).mpr
    exact ⟨hx.1, hx.2, z, by linarith⟩
  · rw [abs_of_nonneg hp] at hr
    apply Finset.mem_union_right
    apply (mem_integerTranslatesBetween (1 / 2 - η) u v x).mpr
    exact ⟨hx.1, hx.2, z, by linarith⟩

theorem truncatedBreakpoints_determine_label (η u v : ℝ) {x y : ℝ}
    (hx : u ≤ x ∧ x ≤ v) (hy : u ≤ y ∧ y ≤ v)
    (hs : ∀ b ∈ A.truncatedBreakpoints η u v,
      ternarySign (x - b) = ternarySign (y - b)) :
    A.truncatedLabel η x = A.truncatedLabel η y := by
  classical
  have hordered : ∀ p q : ℝ, u ≤ p ∧ p ≤ v → u ≤ q ∧ q ≤ v → p < q →
      (∀ b ∈ A.truncatedBreakpoints η u v,
        ternarySign (p - b) = ternarySign (q - b)) →
      A.truncatedLabel η p = A.truncatedLabel η q := by
    intro p q hp hq hpq hsign
    have hnone := no_breakpoint_of_same_signs hpq hsign
    have hthreshold : ∀ b : ℝ, p ≤ b → b ≤ q → rho b ≠ η := by
      intro b hpb hbq he
      have hb := mem_thresholdPoints_of_rho_eq η u v b
        ⟨hp.1.trans hpb, hbq.trans hq.2⟩ he
      exact hnone b (Finset.mem_union_right _ hb) ⟨hpb, hbq⟩
    have hactive : η ≤ rho p ↔ η ≤ rho q := by
      constructor
      · intro hpactive
        apply le_of_not_gt
        intro hqactive
        obtain ⟨b, hb, he⟩ := intermediate_value_Icc' hpq.le continuous_rho.continuousOn
          (show η ∈ Set.Icc (rho q) (rho p) from ⟨hqactive.le, hpactive⟩)
        exact hthreshold b hb.1 hb.2 he
      · intro hqactive
        apply le_of_not_gt
        intro hpactive
        obtain ⟨b, hb, he⟩ := intermediate_value_Icc hpq.le continuous_rho.continuousOn
          (show η ∈ Set.Icc (rho p) (rho q) from ⟨hpactive.le, hqactive⟩)
        exact hthreshold b hb.1 hb.2 he
    by_cases hpactive : η ≤ rho p
    · have hqactive := hactive.mp hpactive
      have hallactive : ∀ b : ℝ, p ≤ b → b ≤ q → η ≤ rho b := by
        intro b hpb hbq
        apply le_of_not_gt
        intro hbactive
        obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hpb continuous_rho.continuousOn
          (show η ∈ Set.Icc (rho b) (rho p) from ⟨hbactive.le, hpactive⟩)
        exact hthreshold t ht.1 (ht.2.trans hbq) he
      have hlabel : A.meshLabel p = A.meshLabel q := by
        apply A.meshLabel_eq_of_no_endpoint hpq.le
        intro b hpb hbq i z he
        have hb : b ∈ A.activeEndpoints η u v := Finset.mem_filter.mpr
          ⟨(A.mem_endpointsBetween u v b).mpr
            ⟨hp.1.trans hpb, hbq.trans hq.2, i, z, he⟩,
            hallactive b hpb hbq⟩
        exact hnone b (Finset.mem_union_left _ hb) ⟨hpb, hbq⟩
      simp only [truncatedLabel, ite_eq_left hpactive, ite_eq_left hqactive, hlabel]
    · have hqactive : ¬ η ≤ rho q := fun h => hpactive (hactive.mpr h)
      simp only [truncatedLabel, ite_eq_right hpactive, ite_eq_right hqactive]
  rcases lt_trichotomy x y with h | h | h
  · exact hordered x y hx hy h hs
  · rw [h]
  · exact (hordered y x hy hx h (fun b hb => (hs b hb).symm)).symm

/-- A fixed 49-point breakpoint set for the closed neighborhood of an anchor
cell. It is chosen before either free affine parameter is selected. -/
theorem stationary_breakpoint_factorization (i : A.Label) (z : ℤ) :
    ∃ B : Finset ℝ, B.card ≤ 49 ∧
      ∀ x y : ℝ,
        A.left i + z - A.width i ≤ x ∧ x ≤ A.right i + z + A.width i →
        A.left i + z - A.width i ≤ y ∧ y ≤ A.right i + z + A.width i →
        (∀ b ∈ B, ternarySign (x - b) = ternarySign (y - b)) →
        A.meshLabel x = A.meshLabel y := by
  refine ⟨A.neighborhoodEndpoints i z, A.neighborhoodEndpoints_card i z, ?_⟩
  intro x y hx hy hs
  exact A.endpoints_determine_label _ _ hx hy hs

/-- The rotating-coordinate bound is uniform in the location of the target
interval, including intervals crossing the circle cut. -/
theorem rotating_breakpoint_factorization (D : ℕ) (hD : 0 < D) (u v : ℝ)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    ∃ B : Finset ℝ, B.card ≤ 16004 * D ∧
      ∀ x y : ℝ, u ≤ x ∧ x ≤ v → u ≤ y ∧ y ≤ v →
        (∀ b ∈ B, ternarySign (x - b) = ternarySign (y - b)) →
        A.truncatedLabel (1 / (1000 * (D : ℝ))) x =
          A.truncatedLabel (1 / (1000 * (D : ℝ))) y := by
  refine ⟨A.truncatedBreakpoints (1 / (1000 * (D : ℝ))) u v,
    A.truncatedBreakpoints_card D hD u v huv hlen, ?_⟩
  intro x y hx hy hs
  exact A.truncatedBreakpoints_determine_label _ u v hx hy hs

end AdaptiveMesh
end QuantitativeVanDerWaerden

end OAI
