import OAI.Combinatorics.Crossing.SimilarityCoordinates
import OAI.Combinatorics.Crossing.RadialBoundaryPorts

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_circle_cut_vector {ι : Type*} [Fintype ι] (o : Plane)
    (r : ℝ) (hr : 0 < r) (point : ι → Plane) :
    ∃ u : Plane, u ≠ 0 ∧ squaredLength u=r^2 ∧ ∀ i, point i ≠ o-u := by
  let f : ℝ → Plane := fun t => o+r • circlePoint t
  have hf : Function.Injective f := by
    intro t s h
    have hh := congrArg (fun z : Plane => r⁻¹ • (z-o)) h
    dsimp [f] at hh
    simp only [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ (ne_of_gt hr),one_smul] at hh
    exact circlePoint_injective hh
  have hbad : (f ⁻¹' Set.range point).Finite := Set.Finite.preimage hf.injOn (Set.finite_range point)
  obtain ⟨t,ht⟩ := hbad.exists_notMem
  let u := (-r) • circlePoint t
  have hlen : squaredLength u=r^2 := by
    dsimp [u]
    rw [squaredLength_smul]
    have hunit : squaredLength (circlePoint t)=1 := circlePoint_on_unit_circle t
    rw [hunit,mul_one,neg_sq]
  have hu : u ≠ 0 := by
    intro h
    rw [h] at hlen
    have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
    rw [hz] at hlen
    nlinarith
  refine ⟨u,hu,hlen,?_⟩
  intro i he
  apply ht
  refine ⟨i,?_⟩
  simpa only [u,f,neg_smul,sub_neg_eq_add] using he

theorem exists_finite_circle_coordinates {ι : Type*} [Fintype ι]
    (o : Plane) (r : ℝ) (hr : 0 < r) (point : ι → Plane)
    (hinj : Function.Injective point) (hcircle : ∀ i, squaredLength (point i-o)=r^2) :
    ∃ u : Plane, u ≠ 0 ∧ squaredLength u=r^2 ∧
      ∃ node : ι → ℝ, Function.Injective node ∧ ∀ i, similarityPoint o u (circlePoint (node i))=point i := by
  obtain ⟨u,hu,hlen,hcut⟩ := exists_circle_cut_vector o r hr point
  have hex (i : ι) := circle_similarity_parameter o u (point i) hu ((hcircle i).trans hlen.symm) (hcut i)
  choose node hnode using hex
  refine ⟨u,hu,hlen,node,?_,hnode⟩
  intro i j hij
  apply hinj
  rw [← hnode i,← hnode j,hij]

end Zarankiewicz

end

end OAI
