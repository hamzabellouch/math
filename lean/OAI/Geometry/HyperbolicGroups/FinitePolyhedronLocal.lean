import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedron

namespace OAI

/-! Finite barycentric carriers are strongly locally contractible. The
contracting neighborhoods retain every positive coordinate of their center,
so straight contraction never crosses a missing simplex. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] (K : AbstractSimplicialComplex V)

def wideStar (x : Carrier K) : Set (V → ℝ) :=
  {y | ∀ i, 0 < x.val i → 0 < y i}

lemma wideStar_open (x : Carrier K) : IsOpen (wideStar K x) := by
  have he : wideStar K x = ⋂ i : V, {y : V → ℝ | 0 < x.val i → 0 < y i} := by
    ext y; simp [wideStar]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : 0 < x.val i
  · simpa only [hi, true_implies] using isOpen_lt continuous_const (continuous_apply i)
  · simp [hi]

lemma self_mem_wideStar (x : Carrier K) : x.val ∈ wideStar K x := fun _ hi => hi

lemma supported_on_face (x : Carrier K) {y : V → ℝ} (hy : y ∈ wideStar K x)
    {s : Finset V} (hs : ∀ i, i ∉ s → y i = 0) : x.val ∈ simplex s := by
  refine ⟨x.property.1, x.property.2.1, ?_⟩
  intro i hi
  have hn : ¬ 0 < x.val i := by
    intro h
    have hp := hy i h
    rw [hs i hi] at hp
    exact lt_irrefl _ hp
  exact le_antisymm (not_lt.mp hn) (x.property.1 i)

lemma wideStar_starConvex (x : Carrier K) :
    StarConvex ℝ x.val (carrierSet K ∩ wideStar K x) := by
  rintro y ⟨hy,hxy⟩ a b ha hb hab
  obtain ⟨s,hs,hys⟩ := hy.2.2
  have hx := supported_on_face K x hxy hys
  have hi := simplex_convex s hx ⟨hy.1,hy.2.1,hys⟩ ha hb hab
  refine ⟨simplex_subset_carrier K hs hi,?_⟩
  intro i hxi
  change 0 < a * x.val i + b * y i
  have hyi := hxy i hxi
  by_cases hap : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [hap,hb1] using hyi
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm hap)) hxi) (mul_nonneg hb hyi.le)

/-- Intersection of a straight-contraction star with an arbitrarily small
ambient ball. -/
def smallStar (x : Carrier K) (ε : ℝ) : Set (Carrier K) :=
  {y | y.val ∈ wideStar K x ∧ dist y x < ε}

def smallStarAmbient (x : Carrier K) (ε : ℝ) : Set (V → ℝ) :=
  (carrierSet K ∩ wideStar K x) ∩ Metric.ball x.val ε

lemma smallStarAmbient_starConvex (x : Carrier K) {ε : ℝ} (hε : 0 < ε) :
    StarConvex ℝ x.val (smallStarAmbient K x ε) :=
  (wideStar_starConvex K x).inter ((convex_ball x.val ε).starConvex (Metric.mem_ball_self hε))

lemma smallStarAmbient_mem (x : Carrier K) {ε : ℝ} (hε : 0 < ε) :
    x.val ∈ smallStarAmbient K x ε :=
  ⟨⟨x.property,self_mem_wideStar K x⟩,Metric.mem_ball_self hε⟩

/-- Flatten the two subtypes without changing their subspace topology. -/
def smallStarHomeomorph (x : Carrier K) (ε : ℝ) :
    smallStar K x ε ≃ₜ smallStarAmbient K x ε where
  toFun y := ⟨y.val.val,⟨y.val.property,y.property.1⟩,y.property.2⟩
  invFun y := ⟨⟨y.val,y.property.1.1⟩,y.property.1.2,y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma smallStar_contractible (x : Carrier K) {ε : ℝ} (hε : 0 < ε) :
    ContractibleSpace (smallStar K x ε) := by
  have : ContractibleSpace (smallStarAmbient K x ε) :=
    (smallStarAmbient_starConvex K x hε).contractibleSpace ⟨x.val,smallStarAmbient_mem K x hε⟩
  exact (smallStarHomeomorph K x ε).contractibleSpace

lemma smallStar_nhds (x : Carrier K) {ε : ℝ} (hε : 0 < ε) :
    smallStar K x ε ∈ 𝓝 x := by
  apply IsOpen.mem_nhds
  · exact ((wideStar_open K x).preimage continuous_subtype_val).inter Metric.isOpen_ball
  · exact ⟨self_mem_wideStar K x,by simpa using hε⟩

instance stronglyLocallyContractible : StronglyLocallyContractibleSpace (Carrier K) where
  contractible_basis x := by
    rw [Filter.hasBasis_self]
    intro U hU
    obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
    exact ⟨smallStar K x ε,smallStar_nhds K x hε,smallStar_contractible K x hε,
      fun y hy => hsub hy.2⟩

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
