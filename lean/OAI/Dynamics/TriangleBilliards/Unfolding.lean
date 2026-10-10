import OAI.Dynamics.TriangleBilliards.AngularMeasure

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

namespace TriangularBilliards

def phaseWord (Q : Triangle) (w : List (Fin 3)) (z : Phase) : Phase :=
  w.foldr (wallPhase Q) z

lemma measurePreserving_phaseWord (Q : Triangle) (w : List (Fin 3)) :
    MeasurePreserving (phaseWord Q w) ambientMeasure ambientMeasure := by
  induction w with
  | nil => exact MeasurePreserving.id ambientMeasure
  | cons i w hw => exact (measurePreserving_wallPhase Q i).comp hw

lemma wallPhase_involutive (Q : Triangle) (i : Fin 3) (z : Phase) :
    wallPhase Q i (wallPhase Q i z) = z := by
  apply Prod.ext
  · exact wallReflection_involutive Q i z.1
  · apply Subtype.ext
    exact reflect_involutive (Q.tangent_ne_zero i) z.2

namespace FlightChain

def line {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) : Phase :=
  (c.point n + (t - c.time n) • (c.direction n : ℂ), c.direction n)

lemma line_zero {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    c.line 0 t = freeFlow t z := by
  apply Prod.ext
  · change c.point 0 + (t - c.time 0) • (c.direction 0 : ℂ) =
      z.1 + t • (z.2 : ℂ)
    rw [c.start_point, c.start_direction, sub_smul, neg_smul]
    abel
  · exact c.start_direction.symm

lemma line_succ {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    c.line (n + 1) t = wallPhase Q (c.wall (n + 1)) (c.line n t) := by
  have hv : (c.direction (n + 1) : ℂ) =
      reflect (Q.tangent (c.wall (n + 1))) (c.direction n : ℂ) := by
    simpa using c.specular (n + 1)
  apply Prod.ext
  · have hf := wallReflection_fixed_side Q (c.on_side (n + 1))
    have hd := wallReflection_sub Q (c.wall (n + 1))
      (c.point n + (t - c.time n) • (c.direction n : ℂ)) (c.point (n + 1))
    rw [hf, c.flight n] at hd
    have he : c.point n + (t - c.time n) • (c.direction n : ℂ) -
        (c.point n + (c.time (n + 1) - c.time n) • (c.direction n : ℂ)) =
        (t - c.time (n + 1)) • (c.direction n : ℂ) := by
      simp only [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      ring
    rw [he, reflect_real_smul, ← hv] at hd
    change c.point (n + 1) + (t - c.time (n + 1)) • (c.direction (n + 1) : ℂ) = _
    rw [c.flight n]
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hd).symm
  · exact Subtype.ext hv

lemma line_pred {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    c.line (n - 1) t = wallPhase Q (c.wall n) (c.line n t) := by
  have hh := c.line_succ (n - 1) t
  simp only [sub_add_cancel] at hh
  rw [hh, wallPhase_involutive]

lemma line_unfold {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    ∃ w : List (Fin 3), c.line n t = phaseWord Q w (freeFlow t z) := by
  induction n using Int.induction_on with
  | zero => exact ⟨[], c.line_zero t⟩
  | succ n hn =>
    obtain ⟨w, hw⟩ := hn
    exact ⟨c.wall (n + 1) :: w, (c.line_succ n t).trans (congrArg _ hw)⟩
  | pred n hn =>
    obtain ⟨w, hw⟩ := hn
    exact ⟨c.wall (-n) :: w, (c.line_pred (-n) t).trans (congrArg _ hw)⟩

/-- Every fixed-time endpoint is the value of one of countably many genuine
ambient measure-preserving Euclidean reflection/free-flight maps. -/
lemma at_unfold {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    ∃ w : List (Fin 3), c.at t = phaseWord Q w (freeFlow t z) := by
  obtain ⟨n, hn⟩ := c.exists_flight t
  rw [c.at_of_flight hn]
  exact c.line_unfold n t

end FlightChain

end TriangularBilliards

namespace TriangularBilliards

lemma phaseMeasure_eq_restrict (Q : Triangle) :
    phaseMeasure Q = (volume Q.table)⁻¹ • ambientMeasure.restrict (Q.table ×ˢ univ) := by
  rw [phaseMeasure, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ]
  rfl

lemma phaseMeasure_absolutelyContinuous (Q : Triangle) : phaseMeasure Q ≪ ambientMeasure := by
  rw [phaseMeasure_eq_restrict]
  exact Measure.absolutelyContinuous_restrict.smul_left _

lemma side_mem_frontier (Q : Triangle) {i : Fin 3} {x : ℂ} (hx : x ∈ Q.side i) :
    x ∈ frontier (convexHull ℝ (range Q.vertex)) := by
  rw [frontier, mem_sdiff]
  refine ⟨subset_closure ?_, Q.side_not_table hx⟩
  exact (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (mem_range_self i))
    (subset_convexHull ℝ _ (mem_range_self (i + 1))) (openSegment_subset_segment _ _ _ hx)

/-- All boundary-position phases form a measurable ambient-null set. -/
def boundaryPhase (Q : Triangle) : Set Phase :=
  frontier (convexHull ℝ (range Q.vertex)) ×ˢ univ

lemma measurableSet_boundaryPhase (Q : Triangle) : MeasurableSet (boundaryPhase Q) :=
  isClosed_frontier.measurableSet.prod MeasurableSet.univ

lemma ambientMeasure_boundaryPhase (Q : Triangle) : ambientMeasure (boundaryPhase Q) = 0 := by
  rw [ambientMeasure, boundaryPhase, Measure.prod_prod,
    (convex_convexHull ℝ (range Q.vertex)).addHaar_frontier volume, zero_mul]

/-- A countable explicit null superset of all trajectories at a boundary
at a prescribed time; it is defined without making trajectory choices. -/
def collisionExceptional (Q : Triangle) (t : ℝ) : Set Phase :=
  ⋃ w : List (Fin 3), (phaseWord Q w ∘ freeFlow t) ⁻¹' boundaryPhase Q

lemma measurableSet_collisionExceptional (Q : Triangle) (t : ℝ) :
    MeasurableSet (collisionExceptional Q t) :=
  MeasurableSet.iUnion fun w => (measurableSet_boundaryPhase Q).preimage
    ((measurePreserving_phaseWord Q w).comp (measurePreserving_freeFlow t)).measurable

lemma phaseMeasure_collisionExceptional (Q : Triangle) (t : ℝ) :
    phaseMeasure Q (collisionExceptional Q t) = 0 := by
  apply phaseMeasure_absolutelyContinuous Q
  apply measure_iUnion_null
  intro w
  rw [((measurePreserving_phaseWord Q w).comp (measurePreserving_freeFlow t)).measure_preimage
    (measurableSet_boundaryPhase Q).nullMeasurableSet, ambientMeasure_boundaryPhase]

lemma FlightChain.mem_collisionExceptional {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) {t : ℝ} (ht : t ∈ range c.time) :
    z ∈ collisionExceptional Q t := by
  obtain ⟨n, rfl⟩ := ht
  obtain ⟨w, hw⟩ := c.at_unfold (c.time n)
  refine mem_iUnion.mpr ⟨w, ?_⟩
  change phaseWord Q w (freeFlow (c.time n) z) ∈ boundaryPhase Q
  rw [← hw, c.at_of_flight ⟨le_rfl, c.increasing (by omega)⟩]
  simp only [sub_self, zero_smul, add_zero]
  exact ⟨side_mem_frontier Q (c.on_side n), mem_univ _⟩

/-- Remove only the fixed-time collision set from the conull regular states. -/
def regularAt (Q : Triangle) (t : ℝ) : Set Phase :=
  {z | Nonempty (FlightChain Q z)} \ collisionExceptional Q t

lemma measurableSet_regularAt (Q : Triangle) (t : ℝ) : MeasurableSet (regularAt Q t) :=
  (CodedChain.measurableSet_regular Q).diff (measurableSet_collisionExceptional Q t)

lemma ae_regularAt (Q : Triangle) (t : ℝ) : ∀ᵐ z ∂phaseMeasure Q, z ∈ regularAt Q t := by
  filter_upwards [ae_exists_chain Q, (measure_eq_zero_iff_ae_notMem.mp
    (phaseMeasure_collisionExceptional Q t))] with z hz ht
  exact ⟨hz, ht⟩

lemma regularAt_subset_table (Q : Triangle) (t : ℝ) : regularAt Q t ⊆ Q.table ×ˢ univ := by
  rintro z ⟨⟨c⟩, _⟩
  exact ⟨c.initial_inside, mem_univ _⟩

lemma regularAt_noncollision {Q : Triangle} {t : ℝ} {z : Phase} (hz : z ∈ regularAt Q t)
    (c : FlightChain Q z) : t ∉ range c.time :=
  fun ht => hz.2 (c.mem_collisionExceptional ht)

lemma flow_mem_table_of_regularAt {Q : Triangle} {t : ℝ} {z : Phase}
    (hz : z ∈ regularAt Q t) : billiardFlow Q t z ∈ Q.table ×ˢ univ := by
  obtain ⟨c⟩ := hz.1
  obtain ⟨n, hn⟩ := c.exists_flight t
  have hne : c.time n ≠ t := fun h => regularAt_noncollision hz c ⟨n, h⟩
  have ht : c.time n < t ∧ t < c.time (n + 1) := ⟨lt_of_le_of_ne hn.1 hne, hn.2⟩
  rw [billiardFlow_eq_chain c]
  exact ⟨(c.rebase t n ht).initial_inside, mem_univ _⟩

lemma flow_injective_regularAt (Q : Triangle) (t : ℝ) :
    InjOn (billiardFlow Q t) (regularAt Q t) := by
  intro z hz y hy he
  obtain ⟨c⟩ := hz.1
  obtain ⟨d⟩ := hy.1
  have hc := billiardFlow_add_of_noncollision c (-t) t (regularAt_noncollision hz c)
  have hd := billiardFlow_add_of_noncollision d (-t) t (regularAt_noncollision hy d)
  rw [he] at hc
  simpa only [neg_add_cancel, billiardFlow_zero] using hc.trans hd.symm

/-- The flow law for every real pair, outside a proved null set. -/

lemma billiardFlow_cocycle (Q : Triangle) (s t : ℝ) :
    billiardFlow Q (s + t) =ᵐ[phaseMeasure Q] (billiardFlow Q s ∘ billiardFlow Q t) := by
  filter_upwards [ae_regularAt Q t] with z hz
  obtain ⟨c⟩ := hz.1
  exact billiardFlow_add_of_noncollision c s t (regularAt_noncollision hz c)

end TriangularBilliards

end

end OAI
