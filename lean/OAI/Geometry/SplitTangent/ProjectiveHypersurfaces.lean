import Mathlib
import OAI.Geometry.SplitTangent.HolomorphicHypersurfaces
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.ProjectiveLineFrame
import OAI.Geometry.SplitTangent.RationalCurveFrames

namespace OAI

/-! Projective Hypersurfaces. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent

lemma LocallyHolomorphicZeroSet.isClosed {X : ComplexManifold.{u}} {Z : Set X.Carrier}
    (h : LocallyHolomorphicZeroSet X Z) : IsClosed Z := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U,hU,hxU,f,hf,he⟩ := h x
  have hfc := (hf.contMDiffAt (hU.mem_nhds hxU)).continuousAt
  have hn : f x≠0 := fun hz => hx ((he x hxU).mpr hz)
  have hne := hfc.eventually_ne hn
  filter_upwards [hU.mem_nhds hxU,hne] with y hy hyn
  exact fun hz => hyn ((he y hy).mp hz)

namespace ProjectiveEmbedding
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

def homogeneousZeroLocus (p : MvPolynomial (Fin (e.N+1)) ℂ) : Set X.Carrier :=
  {x | MvPolynomial.eval (e.map x).rep p=0}

lemma homogeneous_coordinates_eval {p : MvPolynomial (Fin (e.N+1)) ℂ} {k : ℕ}
    (hp : p.IsHomogeneous k) (i : Fin (e.N+1)) (x : X.Carrier) :
    MvPolynomial.eval (projectiveCoordinates i (e.map x)) p=
      ((e.map x).rep i)⁻¹^k*MvPolynomial.eval (e.map x).rep p := by
  exact _root_.OAI.MvPolynomial.IsHomogeneous.eval_scale hp ((e.map x).rep i)⁻¹ (e.map x).rep

lemma homogeneous_coordinates_zero_iff {p : MvPolynomial (Fin (e.N+1)) ℂ} {k : ℕ}
    (hp : p.IsHomogeneous k) (i : Fin (e.N+1)) {x : X.Carrier} (hi : (e.map x).rep i≠0) :
    x∈e.homogeneousZeroLocus p ↔ MvPolynomial.eval (projectiveCoordinates i (e.map x)) p=0 := by
  rw [e.homogeneous_coordinates_eval hp]
  exact (mul_eq_zero_iff_left (pow_ne_zero _ (inv_ne_zero hi))).symm

lemma homogeneousZeroLocus_locally_holomorphic
    {p : MvPolynomial (Fin (e.N+1)) ℂ} {k : ℕ} (hp : p.IsHomogeneous k) :
    LocallyHolomorphicZeroSet X (e.homogeneousZeroLocus p) := by
  intro x
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i≠0 at hi
  refine ⟨{y | (e.map y).rep i≠0},e.open_patch i,hi,
    fun y => MvPolynomial.eval (projectiveCoordinates i (e.map y)) p,?_,?_⟩
  · intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply _root_.OAI.MvPolynomial.contMDiffAt_eval_comp (ModelWithCorners X) p
    intro j
    exact contMDiffAt_pi_space.mp
      ((e.holomorphic i).contMDiffAt ((e.open_patch i).mem_nhds hy)) j
  · intro y hy
    exact e.homogeneous_coordinates_zero_iff hp i hy

lemma homogeneousZeroLocus_isClosed
    {p : MvPolynomial (Fin (e.N+1)) ℂ} {k : ℕ} (hp : p.IsHomogeneous k) :
    IsClosed (e.homogeneousZeroLocus p) :=
  (e.homogeneousZeroLocus_locally_holomorphic hp).isClosed

lemma linearFrame_zero_iff
    {p : MvPolynomial (Fin (e.N+1)) ℂ} {k : ℕ} (hp : p.IsHomogeneous k)
    (a : Fin (e.N+1) → ℂ) {x : X.Carrier} (ha : (∑i,a i*(e.map x).rep i)≠0) :
    MvPolynomial.eval (e.linearFrame a x) p=0 ↔ x∈e.homogeneousZeroLocus p := by
  rw [linearFrame,_root_.OAI.MvPolynomial.IsHomogeneous.eval_scale hp]
  exact mul_eq_zero_iff_left (pow_ne_zero _ (inv_ne_zero ha))

lemma linearFrame_denominator_eventually
    (a : Fin (e.N+1) → ℂ) {x : X.Carrier} (ha : (∑i,a i*(e.map x).rep i)≠0) :
    ∀ᶠ y in 𝓝 x,(∑i,a i*(e.map y).rep i)≠0 := by
  have hframe : e.linearFrame a x≠0 :=
    smul_ne_zero (inv_ne_zero ha) (e.map x).rep_nonzero
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hframe
  have hc := (e.linearFrame_holomorphicAt (ModelWithCorners X)
    (f := id) (a := fun _ => a) contMDiffAt_id contMDiffAt_const ha).continuousAt
  have hn := ((continuous_apply j).continuousAt.comp hc).eventually_ne hj
  filter_upwards [hn] with y hy
  intro hh
  apply hy
  change e.linearFrame a y j=0
  simp only [linearFrame,hh,inv_zero,zero_smul,Pi.zero_apply]

end ProjectiveEmbedding
end SplitTangent

end

end OAI
