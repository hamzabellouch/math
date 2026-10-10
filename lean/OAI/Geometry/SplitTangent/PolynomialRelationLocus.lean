import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.HolomorphicCommonZeros
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.ProjectiveHypersurfaces

namespace OAI

/-! Polynomial Relation Locus. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X) {n k : ℕ}
  (Q : Fin n → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k)

def relationPolynomial (c : Fin n → ℂ) : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k :=
  ∑j,c j • Q j

def relationLocus : Set X.Carrier := {x | ∃c : Fin n → ℂ,c≠0 ∧
  closure (L.leaf x) ⊆ e.homogeneousZeroLocus (relationPolynomial e Q c).val}

lemma relation_eval (c : Fin n → ℂ) (w : Fin (e.N+1) → ℂ) :
    MvPolynomial.eval w (relationPolynomial e Q c).val=∑j,MvPolynomial.eval w (Q j).val*c j := by
  simp only [relationPolynomial,Submodule.coe_sum,Submodule.coe_smul,map_sum,MvPolynomial.smul_eval]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_comm]

lemma relation_rectangle_iff {x z : X.Carrier} (i : Fin (e.N+1))
    {U : Set (S.FirstModel x)} {V : Set (S.SecondModel x)}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hrect : U ×ˢ V ⊆ (L.chart x).chart.target)
    (hpatch : ∀t∈U ×ˢ V,(e.map ((L.chart x).chart.symm t)).rep i≠0)
    (hz : z∈(L.chart x).chart.source) (hzUV : (L.chart x).chart z∈U ×ˢ V) :
    z∈L.relationLocus e Q ↔ ∃c : Fin n → ℂ,c≠0 ∧ ∀a : U,
      ∑j,MvPolynomial.eval (projectiveCoordinates i (e.map ((L.chart x).chart.symm
        (a.val,((L.chart x).chart z).2)))) (Q j).val*c j=0 := by
  let P := L.chart x
  constructor
  · rintro ⟨c,hc,hzero⟩
    refine ⟨c,hc,fun a => ?_⟩
    have hrel := L.plaques.related_in_rectangle hUc hrect hzUV.1 a.property hzUV.2
    change L.plaques.Related (P.chart.symm (P.chart z))
      (P.chart.symm (a.val,(P.chart z).2)) at hrel
    rw [P.chart.left_inv hz] at hrel
    have hleaf : P.chart.symm (a.val,(P.chart z).2)∈L.leaf z :=
      Relation.ReflTransGen.single hrel
    have hh := (e.homogeneous_coordinates_zero_iff (relationPolynomial e Q c).property i
      (hpatch (a.val,(P.chart z).2) ⟨a.property,hzUV.2⟩)).mp (hzero (subset_closure hleaf))
    rwa [relation_eval] at hh
  · rintro ⟨c,hc,hzero⟩
    refine ⟨c,hc,?_⟩
    apply L.closure_leaf_subset
      (e.homogeneousZeroLocus_locally_holomorphic (relationPolynomial e Q c).property)
      (e.homogeneousZeroLocus_isClosed (relationPolynomial e Q c).property)
    apply (L.germIn_iff P hz).mpr
    change ∀ᶠa in 𝓝 (P.chart z).1,
      P.chart.symm (a,(P.chart z).2)∈e.homogeneousZeroLocus (relationPolynomial e Q c).val
    filter_upwards [hU.mem_nhds hzUV.1] with a ha
    apply (e.homogeneous_coordinates_zero_iff (relationPolynomial e Q c).property i
      (hpatch (a,(P.chart z).2) ⟨ha,hzUV.2⟩)).mpr
    rw [relation_eval]
    exact hzero ⟨a,ha⟩

 

theorem relationLocus_locally_holomorphic :
    LocallyHolomorphicCommonZeros X (L.relationLocus e Q) := by
  classical
  intro x
  let P := L.chart x
  have hxs : x∈P.chart.source := L.mem_source x
  have hxt : P.chart x∈P.chart.target := P.chart.map_source hxs
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i≠0 at hi
  let patch := {y : X.Carrier | (e.map y).rep i≠0}
  have hpatch : P.chart.symm ⁻¹' patch∈𝓝 (P.chart x) := by
    apply (P.chart.symm.continuousAt hxt).preimage_mem_nhds
    simpa only [P.chart.left_inv hxs] using (e.open_patch i).mem_nhds hi
  obtain ⟨U,V,hU,hUc,hV,hxUV,hrect⟩ := UniformPlaqueSlices.connected_rectangle
    (Filter.inter_mem (P.chart.open_target.mem_nhds hxt) hpatch)
  have hrectT : U ×ˢ V⊆P.chart.target := fun t ht => (hrect ht).1
  have hrectP : ∀t∈U ×ˢ V,(e.map (P.chart.symm t)).rep i≠0 := fun t ht => (hrect ht).2
  let W := P.chart.source ∩ P.chart ⁻¹' (U ×ˢ V)
  have hW : IsOpen W := P.chart.continuousOn.isOpen_inter_preimage P.chart.open_source (hU.prod hV)
  let row : U → X.Carrier → Fin n → ℂ := fun a y j =>
    MvPolynomial.eval (projectiveCoordinates i (e.map (P.chart.symm (a.val,(P.chart y).2)))) (Q j).val
  let f : (Fin n → U) → X.Carrier → ℂ := fun s y => Matrix.det (fun a b => row (s a) y b)
  refine ⟨W,hW,⟨hxs,hxUV⟩,Set.range f,?_,?_⟩
  · rintro _ ⟨s,rfl⟩ y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply HolomorphicDeterminant.contMDiffAt_det
    intro a b
    have hC : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,S.FirstModel x × S.SecondModel x) ω
        (fun z => ((s a).val,(P.chart z).2)) y := by
      apply (contMDiffAt_prod_module_iff _).mpr
      exact ⟨contMDiffAt_const,(contMDiffAt_prod_module_iff _).mp (P.holomorphicAt hy.1) |>.2⟩
    have hI := (P.inverse_holomorphicAt (hrectT (show ((s a).val,(P.chart y).2)∈U ×ˢ V from ⟨(s a).property,hy.2.2⟩))).comp y hC
    have he := ((e.holomorphic i).contMDiffAt ((e.open_patch i).mem_nhds
      (hrectP ((s a).val,(P.chart y).2) ⟨(s a).property,hy.2.2⟩))).comp y hI
    exact _root_.OAI.MvPolynomial.contMDiffAt_eval_comp (ModelWithCorners X) (Q b).val
      (fun j => contMDiffAt_pi_space.mp he j)
  · intro y hy
    have hiff := L.relation_rectangle_iff e Q i hU hUc hrectT hrectP hy.1 hy.2
    rw [hiff,FiniteSampling.relation_iff_det_zero]
    constructor
    · intro hd f' hf'
      obtain ⟨s,rfl⟩ := hf'
      exact hd s
    · intro hd s
      exact hd (f s) ⟨s,rfl⟩

end SplitTangent.LeafJetAtlas

end

end OAI
