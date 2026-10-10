import Mathlib
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Rational Cover Lift. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent
variable {X Y : ComplexManifold.{u}} {p : Y.Carrier → X.Carrier}

lemma holomorphic_of_continuous_cover_lift
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    {f : ℂ → X.Carrier} {g : ℂ → Y.Carrier}
    (hf : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω f)
    (hg : Continuous g) (he : ∀z,p (g z)=f z) :
    ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners Y) ω g := by
  intro z
  let h := hp (g z)
  have hinv := h.localInverse_contMDiffAt
  rw [he z] at hinv
  have hh := hinv.comp z (hf z)
  apply hh.congr_of_eventuallyEq
  have hn := hg.continuousAt.preimage_mem_nhds
    (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)
  filter_upwards [hn] with w hw
  change g w=h.localInverse (f w)
  rw [←he w,h.localInverse_left_inv hw]

 

theorem RationalCurve.exists_cover_lift_at (g : RationalCurve X)
    (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (a₀ : ℂ) (y : Y.Carrier) (hy : p y=g.finite a₀) :
    ∃k : RationalCurve Y,k.finite a₀=y ∧
      (∀z,p (k.finite z)=g.finite z) ∧ (∀z,p (k.infinity z)=g.infinity z) := by
  let f : C(ℂ,X.Carrier) := ⟨g.finite,g.finite_holomorphic.continuous⟩
  obtain ⟨F,hF,_⟩ := hcover.existsUnique_continuousMap_lifts f a₀ y hy
  have hF' z : p (F z)=g.finite z := congrFun hF.2 z
  have h1 : p (F 1)=g.infinity 1 := by
    rw [hF' 1,g.overlap 1 one_ne_zero,inv_one]
  let q : C(ℂ,X.Carrier) := ⟨g.infinity,g.infinity_holomorphic.continuous⟩
  obtain ⟨G,hG,_⟩ := hcover.existsUnique_continuousMap_lifts q (1 : ℂ) (F 1) h1
  have hG' z : p (G z)=g.infinity z := congrFun hG.2 z
  have hconn : IsPreconnected {z : ℂ | z≠0} := by
    have hh := (isConnected_compl_singleton_of_one_lt_rank
      (E := ℂ) (by norm_num [Complex.rank_real_complex]) (0 : ℂ)).isPreconnected
    exact hh
  let : PreconnectedSpace {z : ℂ // z≠0} := isPreconnected_iff_preconnectedSpace.mp hconn
  let a : {z : ℂ // z≠0} → Y.Carrier := fun z => F z.val
  let b : {z : ℂ // z≠0} → Y.Carrier := fun z => G z.val⁻¹
  have ha : Continuous a := F.continuous.comp continuous_subtype_val
  have hb : Continuous b := G.continuous.comp
    (continuous_subtype_val.inv₀ (fun z => z.property))
  have hab : p ∘ a=p ∘ b := by
    funext z
    exact (hF' z.val).trans ((g.overlap z.val z.property).trans (hG' z.val⁻¹).symm)
  have hab1 : a ⟨1,one_ne_zero⟩=b ⟨1,one_ne_zero⟩ := by
    change F 1=G 1⁻¹
    rw [inv_one,hG.1]
  have heq : a=b := hcover.eq_of_comp_eq ha hb hab ⟨1,one_ne_zero⟩ hab1
  let k : RationalCurve Y := {
    finite := F
    infinity := G
    finite_holomorphic := holomorphic_of_continuous_cover_lift hp
      g.finite_holomorphic F.continuous hF'
    infinity_holomorphic := holomorphic_of_continuous_cover_lift hp
      g.infinity_holomorphic G.continuous hG'
    overlap z hz := congrFun heq ⟨z,hz⟩ }
  exact ⟨k,hF.1,hF',hG'⟩

 
theorem RationalCurve.exists_cover_lift (g : RationalCurve X)
    (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (y : Y.Carrier) (hy : p y=g.finite 0) :
    ∃k : RationalCurve Y,k.finite 0=y ∧
      (∀z,p (k.finite z)=g.finite z) ∧ (∀z,p (k.infinity z)=g.infinity z) :=
  g.exists_cover_lift_at hcover hp 0 y hy

end SplitTangent

end

end OAI
