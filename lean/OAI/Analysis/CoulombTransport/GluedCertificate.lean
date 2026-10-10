import OAI.Analysis.CoulombTransport.ComponentCertificate
import OAI.Analysis.CoulombTransport.LocalPotentialBounds
import OAI.Analysis.CoulombTransport.NeighborhoodCertificate

namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- A contact triple on a finite union, with its ordered component labels. -/
def componentContact {ι : Type uIndex} (U : ι → Set E3)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop) (t : Triple) : Prop :=
  ∃ a, t.1 ∈ U a.1 ∧ t.2.1 ∈ U a.2.1 ∧ t.2.2 ∈ U a.2.2 ∧
    Good a ∧ Contact a t

/-- Local good-type certificates and strict bad-center gaps produce an actual
bounded, measurable supporting potential on disjoint small component balls,
with the precise union of the prescribed contact sets. -/
theorem exists_glued_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) ↔
          componentContact U Good Contact (x, (y, z)))) := by
  classical
  have hvAt : ∀ i, ContinuousAt (v i) (p i) :=
    fun i => (hv i).continuousAt ((hV i).mem_nhds (hpV i))
  obtain ⟨rC, hrC, hcert⟩ := finite_component_certificate p v Good Contact hvAt hgood hbad
  obtain ⟨M, hM, rB, hrB, hbound⟩ := exists_uniform_local_potential_bound p v hvAt
  obtain ⟨rV, hrV, hsubV, hdisjV⟩ :=
    Geometry.finite_disjoint_closedBalls_subset p hp V hV hpV
  let r : ℝ := min rC (min rB rV)
  have hr : 0 < r := lt_min hrC (lt_min hrB hrV)
  have hrC' : r ≤ rC := min_le_left _ _
  have hrB' : r ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hrV' : r ≤ rV := (min_le_right _ _).trans (min_le_right _ _)
  let U : ι → Set E3 := fun i => ball (p i) r
  have hUV : ∀ i, U i ⊆ V i := by
    intro i
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV')).trans (hsubV i)
  have hUdisj : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    exact (hdisjV hij).mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV'))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV'))
  have huCont : ∀ i, ContinuousOn (v i) (U i) := fun i => (hv i).mono (hUV i)
  have hUbound : ∀ i, ∀ x ∈ U i, |v i x| ≤ M := by
    intro i x hx
    exact hbound i x (ball_subset_ball hrB' hx)
  refine ⟨r, M, hr, hM, hUV, hUdisj, ?_, ?_, ?_, ?_⟩
  · exact ComponentPotential.measurable_glue (fun _ => isOpen_ball.measurableSet) huCont
  · exact ComponentPotential.continuousOn_glue (fun _ => isOpen_ball) hUdisj huCont
  · exact ComponentPotential.abs_glue_le hM.le hUdisj hUbound
  · intro x hx y hy z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    have hc := hcert (i, (j, k)) x y z
      (ball_subset_ball hrC' hi) (ball_subset_ball hrC' hj) (ball_subset_ball hrC' hk)
    rw [ComponentPotential.glue_eq hUdisj hi, ComponentPotential.glue_eq hUdisj hj,
      ComponentPotential.glue_eq hUdisj hk]
    refine ⟨hc.1, ?_⟩
    constructor
    · intro heq
      exact ⟨(i, (j, k)), hi, hj, hk, (hc.2.mp heq).1, (hc.2.mp heq).2⟩
    · rintro ⟨a, ha₁, ha₂, ha₃, hgooda, hcontact⟩
      have heq := (hcert a x y z (ball_subset_ball hrC' ha₁)
        (ball_subset_ball hrC' ha₂) (ball_subset_ball hrC' ha₃)).2.mpr ⟨hgooda, hcontact⟩
      have hxv : v a.1 x = v i x := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₁, ComponentPotential.glue_eq hUdisj hi]
      have hyv : v a.2.1 y = v j y := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₂, ComponentPotential.glue_eq hUdisj hj]
      have hzv : v a.2.2 z = v k z := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₃, ComponentPotential.glue_eq hUdisj hk]
      simpa only [hxv, hyv, hzv] using heq

end Problem356

end

end OAI
