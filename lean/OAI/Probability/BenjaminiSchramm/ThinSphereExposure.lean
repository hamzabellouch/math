import OAI.Probability.BenjaminiSchramm.ThinSphere

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_finite_local_nat (Q : Finset E) (f : Set E → ℕ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Measurable f := by
  let g : Set (Q : Set E) → ℕ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  rw [he]
  exact (measurable_of_finite g).comp (measurable_set_restrict (Q : Set E))

theorem measurable_intrinsicSphere_ncard (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (n : ℕ) (hn : 0 < n) :
    Measurable (fun ω => (intrinsicSphere G (ω ∩ S) x n).ncard) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x n).toFinset
  apply measurable_finite_local_nat Q
  intro ω
  have hballs := intrinsicBall_history_eq_of_incident_agreement G
    (ω ∩ S) ((ω ∩ (Q : Set E)) ∩ S) x n (by
      rintro e ⟨a,ha,he⟩
      have haR : a ∈ reachBall G x n := reachBall_mono G x (Nat.sub_le n 1)
        (intrinsicBall_subset_reachBall G (ω ∩ S) x (n-1) ha)
      have heQ : e ∈ Q := (mem_incidentSupport G hloc _ e).mpr
        ⟨a,(finite_reachBall hloc x n).mem_toFinset.mpr haR,he⟩
      simp only [Set.mem_inter_iff,Finset.mem_coe,heQ,and_true])
  rw [intrinsicSphere_eq_ball_sdiff G _ x n hn,intrinsicSphere_eq_ball_sdiff G _ x n hn,
    hballs n le_rfl,hballs (n-1) (Nat.sub_le n 1)]

theorem thinSphereCell_dependsOn (G : BondGraph V E) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    DependsOn
      (fun ω => ω ∈ thinSphereCell G S x r k j U W) (ballIncidentEdges G U) := by
  intro ω η hagree
  apply propext
  have hforward (ω η : Set E)
      (hωη : ∀ e ∈ ballIncidentEdges G U, e ∈ ω ↔ e ∈ η)
      (hω : ω ∈ thinSphereCell G S x r k j U W) :
      η ∈ thinSphereCell G S x r k j U W := by
    obtain ⟨hrj,hj2,hU,hW,hthin,hfirst⟩ := hω
    have hballs := intrinsicBall_history_eq_of_incident_agreement G (ω ∩ S) (η ∩ S) x j (by
      intro e he
      rw [hU] at he
      exact and_congr (hωη e he) Iff.rfl)
    have hspheres (i : ℕ) (hi : r ≤ i) (hij : i ≤ j) :
        intrinsicSphere G (ω ∩ S) x i = intrinsicSphere G (η ∩ S) x i := by
      have hi0 : 0 < i := hr.trans_le hi
      rw [intrinsicSphere_eq_ball_sdiff G _ x i hi0,intrinsicSphere_eq_ball_sdiff G _ x i hi0,
        hballs i hij,hballs (i-1) ((Nat.sub_le i 1).trans hij)]
    refine ⟨hrj,hj2,(hballs (j-1) (Nat.sub_le j 1)).symm.trans hU,
      (hballs j le_rfl).symm.trans hW,?_,?_⟩
    · rw [←hspheres j hrj le_rfl]
      exact hthin
    · intro i hi hij
      rw [←hspheres i hi hij.le]
      exact hfirst i hi hij
  exact ⟨hforward ω η (fun e he => (hagree e he).to_iff),
    hforward η ω (fun e he => (hagree e he).symm.to_iff)⟩

theorem measurableSet_thinSphereCell [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    MeasurableSet (thinSphereCell G S x r k j U W) := by
  by_cases hrj : r ≤ j
  · have hj0 : 0 < j := hr.trans_le hrj
    have hfirst : Measurable (fun ω : Set E => ∀ i, r ≤ i → i < j →
        k < (intrinsicSphere G (ω ∩ S) x i).ncard) := by
      apply Measurable.forall
      intro i
      by_cases hri : r ≤ i
      · exact measurable_const.imp (measurable_const.imp
          (measurable_const.lt (measurable_intrinsicSphere_ncard G hloc S x i (hr.trans_le hri))))
      · have he : (fun ω : Set E => r ≤ i → i < j →
            k < (intrinsicSphere G (ω ∩ S) x i).ncard) = fun _ => True := by
          funext ω; simp [hri]
        rw [he]
        exact measurable_const
    exact (measurable_const.and (measurable_const.and
      ((measurableSet_intrinsicBall_eq G hloc S x (j-1) U).mem.and
      ((measurableSet_intrinsicBall_eq G hloc S x j W).mem.and
      ((measurableSet_le (measurable_intrinsicSphere_ncard G hloc S x j hj0) measurable_const).mem.and hfirst))))).setOf
  · have he : thinSphereCell G S x r k j U W = ∅ := by
      ext ω; simp only [thinSphereCell,Set.mem_ofPred_eq,Set.mem_empty_iff_false]
      simp [hrj]
    rw [he]
    exact MeasurableSet.empty

end Percolation.BenjaminiSchramm

end OAI
