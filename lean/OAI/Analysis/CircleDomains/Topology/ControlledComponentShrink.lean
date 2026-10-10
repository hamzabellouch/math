import OAI.Analysis.CircleDomains.Topology.ComponentwiseJordanCover
import OAI.Analysis.CircleDomains.Selection.FiniteMappedShrink

namespace OAI

/-! A quantitative shrinking stage for the actual component decomposition.
The old component diameter is used only to keep the forward movement
small. The quotient observation is constant on components and controls
the inverse movement. The new component diameter is arbitrary. -/
open Set Metric Function
noncomputable section
namespace CircleDomainRigidity

lemma exists_controlled_component_shrink
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {F : Set ℂ} (hF : IsCompact F) (hFc : IsConnected Fᶜ)
    (p : ℂ → Y) (q : ℂ → Z) (hp : Continuous p) (hq : Continuous q)
    {δ η ε : ℝ} (hδ : 0<δ) (hη : 0<η) (hε : 0<ε)
    (hsmall : ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x,
      dist (p y) (p x)<δ/2)
    (hconstant : ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x, q y=q x) :
    ∃ (T : ℂ ≃ₜ ℂ) (B : Set ℂ), IsCompact B ∧
      (∀ x ∉ B, T x=x) ∧
      (∀ x, dist (p (T x)) (p x)<δ) ∧
      (∀ x, dist (q (T.symm x)) (q x)<η) ∧
      ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x,
        ∀ z ∈ connectedComponentIn F x, dist (p (T y)) (p (T z))<ε := by
  let O (x : F) : Set ℂ := {z | dist (p z) (p x.val)<δ/2 ∧ dist (q z) (q x.val)<η/2}
  have hO (x : F) : IsOpen (O x) :=
    (isOpen_lt (hp.dist continuous_const) continuous_const).inter
      (isOpen_lt (hq.dist continuous_const) continuous_const)
  have hcomp (x : F) : connectedComponentIn F x.val ⊆ O x := by
    intro y hy
    refine ⟨hsmall x.val x.property y hy,?_⟩
    rw [hconstant x.val x.property y hy,dist_self]
    exact half_pos hη
  obtain ⟨n,H,hcover,hd,hcurves⟩ :=
    exists_componentwise_jordan_cover hsard hsch hF hFc O hO hcomp
  have hdiam (i : Fin n) : ∀ x ∈ jordanInterior (H i), ∀ y ∈ jordanInterior (H i),
      dist (p x) (p y)<δ ∧ dist (q x) (q y)<η := by
    obtain ⟨c,hc⟩ := (hcurves i).2
    intro x hx y hy
    have hxc := hc (subset_closure hx)
    have hyc := hc (subset_closure hy)
    change dist (p x) (p c.val)<δ/2 ∧ dist (q x) (q c.val)<η/2 at hxc
    change dist (p y) (p c.val)<δ/2 ∧ dist (q y) (q c.val)<η/2 at hyc
    constructor
    · have ht := dist_triangle (p x) (p c.val) (p y)
      rw [dist_comm (p c.val) (p y)] at ht
      linarith [hxc.1,hyc.1]
    · have ht := dist_triangle (q x) (q c.val) (q y)
      rw [dist_comm (q c.val) (q y)] at ht
      linarith [hxc.2,hyc.2]
  obtain ⟨T,hfix,hmaps,hnew⟩ := exists_finite_jordan_mapped_shrink H hF hd hcover
    (fun i => (hcurves i).1.symm) p hp hε
  have hpbound : ∀ x, dist (p (T x)) (p x)<δ :=
    supported_displacement_bound T p (fun i => jordanInterior (H i)) hδ hfix hmaps
      (fun i x hx y hy => (hdiam i x hx y hy).1)
  have hqbound : ∀ x, dist (q (T x)) (q x)<η :=
    supported_displacement_bound T q (fun i => jordanInterior (H i)) hη hfix hmaps
      (fun i x hx y hy => (hdiam i x hx y hy).2)
  let B := ⋃ i, closure (jordanInterior (H i))
  refine ⟨T,B,isCompact_iUnion (fun i => isCompact_closure_jordanInterior (H i)),?_,
    hpbound,?_,hnew⟩
  · intro x hx
    apply hfix x
    intro hi
    obtain ⟨i,hi⟩ := mem_iUnion.mp hi
    exact hx (mem_iUnion.mpr ⟨i,subset_closure hi⟩)
  · intro x
    have h := hqbound (T.symm x)
    rw [T.apply_symm_apply,dist_comm] at h
    exact h

end CircleDomainRigidity

end

end OAI
