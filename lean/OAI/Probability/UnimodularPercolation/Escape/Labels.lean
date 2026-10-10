import Mathlib
import OAI.Probability.UnimodularPercolation.Deformation.AveragedDecrease

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledEscapeExperiment

 

structure EscapeLabel (G : BondGraph V E) (γ : I → V) (endpoint negative : I) (L m : ℕ) where
  first : I → V
  first_mem : first ∈ segmentOrbit G γ
  last : I → V
  last_mem : last ∈ segmentOrbit G γ
  middle : HoldingWalk (openSimpleGraph G Set.univ) L (first endpoint) (last endpoint)
  leftTail : RawFrom (openSimpleGraph G Set.univ) m (first negative)
  rightTail : RawFrom (openSimpleGraph G Set.univ) m (last negative)

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def reverse (ξ : EscapeLabel G γ ep neg L m) : EscapeLabel G γ ep neg L m where
  first := ξ.last
  first_mem := ξ.last_mem
  last := ξ.first
  last_mem := ξ.first_mem
  middle := ξ.middle.reverse
  leftTail := ξ.rightTail
  rightTail := ξ.leftTail

theorem reverse_reverse (ξ : EscapeLabel G γ ep neg L m) : ξ.reverse.reverse = ξ := by
  cases ξ
  simp only [reverse,HoldingWalk.reverse_reverse]

def reverseEquiv : EscapeLabel G γ ep neg L m ≃ EscapeLabel G γ ep neg L m where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

noncomputable def mass (P : V → V → ℝ) (ξ : EscapeLabel G γ ep neg L m) : ℝ :=
  ξ.middle.mass P * ξ.leftTail.2.mass P * ξ.rightTail.2.mass P

theorem mass_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (ξ : EscapeLabel G γ ep neg L m) : 0 ≤ ξ.mass P :=
  mul_nonneg (mul_nonneg (ξ.middle.mass_nonneg P hP) (ξ.leftTail.2.mass_nonneg P hP))
    (ξ.rightTail.2.mass_nonneg P hP)

theorem mass_reverse (P : V → V → ℝ) (hP : ∀ x y, P x y = P y x)
    (ξ : EscapeLabel G γ ep neg L m) : ξ.reverse.mass P = ξ.mass P := by
  simp only [mass,reverse,HoldingWalk.mass_reverse P hP]
  ring

 

def reverseRootedEquiv (center : I) (x y : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} ≃
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = y ∧ ξ.last center = x} where
  toFun ξ := ⟨ξ.1.reverse,ξ.2.2,ξ.2.1⟩
  invFun ξ := ⟨ξ.1.reverse,ξ.2.2,ξ.2.1⟩
  left_inv ξ := Subtype.ext (reverse_reverse ξ.1)
  right_inv ξ := Subtype.ext (reverse_reverse ξ.1)

end EscapeLabel
end LabeledEscapeExperiment
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FiniteRootedLabels
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

noncomputable def RootedLabelCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) : Type (max u w) :=
  Σ s : (segmentAnchors G hloc γ n hdiam center x),
    Σ mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
      Σ h : (segmentAnchors G hloc γ n hdiam ep mid.1),
        RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg)

instance finite_rootedLabelCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite (RootedLabelCode G hloc γ n hdiam center ep neg L m x) := by
  let (z : V) := finite_openSimpleGraph_neighbors G hloc z
  unfold RootedLabelCode
  infer_instance

noncomputable def labelFromCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  have hsm := ((mem_segmentAnchors G hloc γ n hdiam center x s).mp hs).1
  have hsx := ((mem_segmentAnchors G hloc γ n hdiam center x s).mp hs).2
  have hhm := ((mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh).1
  have hhz := ((mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh).2
  subst z
  exact ⟨⟨s,hsm,h,hhm,mid,α,β⟩,hsx⟩

noncomputable def labelToCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}) :
    RootedLabelCode G hloc γ n hdiam center ep neg L m x :=
  ⟨⟨ξ.1.first,(mem_segmentAnchors G hloc γ n hdiam center x ξ.1.first).mpr ⟨ξ.1.first_mem,ξ.2⟩⟩,
    ⟨ξ.1.last ep,ξ.1.middle⟩,
    ⟨ξ.1.last,(mem_segmentAnchors G hloc γ n hdiam ep (ξ.1.last ep) ξ.1.last).mpr ⟨ξ.1.last_mem,rfl⟩⟩,
    ξ.1.leftTail,ξ.1.rightTail⟩

noncomputable def rootedLabelEquiv (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} ≃
      RootedLabelCode G hloc γ n hdiam center ep neg L m x where
  toFun := labelToCode G hloc γ n hdiam center ep neg L m x
  invFun := labelFromCode G hloc γ n hdiam center ep neg L m x
  left_inv ξ := by
    cases ξ with
    | mk ξ hξ => cases ξ; rfl
  right_inv c := by
    rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
    have hh' := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
    obtain ⟨hhm,hhz⟩ := hh'
    subst z
    rfl

theorem finite_rootedEscapeLabels (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} :=
  Finite.of_equiv _ (rootedLabelEquiv G hloc γ n hdiam center ep neg L m x).symm

end FiniteRootedLabels
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem segmentAnchors_card_on_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    (hx : x ∈ vertexOrbit G (γ i)) :
    (segmentAnchors G hloc γ n hdiam i x).card = (segmentAnchors G hloc γ n hdiam i (γ i)).card := by
  obtain ⟨a,b,h,rfl⟩ := hx
  exact segmentAnchors_card_aut G hloc γ n hdiam i (γ i) h

theorem segmentAnchors_card_eq_indicator (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    ((segmentAnchors G hloc γ n hdiam i x).card : ℝ) =
      if x ∈ vertexOrbit G (γ i) then (segmentAnchors G hloc γ n hdiam i (γ i)).card else 0 := by
  split_ifs with hx
  · exact congrArg Nat.cast (segmentAnchors_card_on_orbit G hloc γ n hdiam i x hx)
  · have hh := (segmentAnchors_nonempty_iff G hloc γ n hdiam i x).not.mpr hx
    rw [Finset.not_nonempty_iff_eq_empty.mp hh]
    rfl

noncomputable def segmentReturnMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V) : ℝ :=
  ∑' mid : RawFrom (openSimpleGraph G Set.univ) L x,
    if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0

theorem labelFromCode_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (P : V → V → ℝ)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.mass P =
      c.2.1.2.mass P * c.2.2.2.1.2.mass P * c.2.2.2.2.2.mass P := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem rooted_label_mass_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      ξ.1.mass (walkKernel G hloc a)) =
    ∑ s ∈ segmentAnchors G hloc γ n hdiam center x,
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
        segmentReturnMass G hloc a γ ep L (s ep) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  change (∑' s : (segmentAnchors G hloc γ n hdiam center x), _) = _
  rw [tsum_fintype]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro s _
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  have he (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep)) :
      (∑' h : (segmentAnchors G hloc γ n hdiam ep mid.1),
        ∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
            tails.2.2.mass (walkKernel G hloc a)) =
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
        (if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0) := by
    have ht (h : (segmentAnchors G hloc γ n hdiam ep mid.1)) :
        (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
            tails.2.2.mass (walkKernel G hloc a)) = mid.2.mass (walkKernel G hloc a) := by
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
      simp only [tsum_mul_left,rawFrom_probability_sum G hloc a,mul_one]
    simp only [ht,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    rw [segmentAnchors_card_eq_indicator G hloc γ n hdiam ep mid.1]
    split_ifs <;> ring
  calc
    _ = ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
          (if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0) := by
      apply tsum_congr
      intro mid
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      exact he mid
    _ = _ := tsum_mul_left

end LabeledMass
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledNormalization
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
theorem segmentReturnMass_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) :
    segmentReturnMass G hloc a γ ep L x =
      ∑' y, if y ∈ vertexOrbit G (γ ep) then (matrixCoeff (P^L) x y).re else 0 := by
  have hh := raw_integral_operator G hloc a P hpos hP L x
    (fun y => if y ∈ vertexOrbit G (γ ep) then 1 else 0)
  simpa only [RawFrom.integral,mul_ite,mul_one,mul_zero,segmentReturnMass] using hh

omit [Fintype I] in
theorem segmentReturnMass_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) :
    segmentReturnMass G hloc a γ ep L (g x) = segmentReturnMass G hloc a γ ep L x := by
  rw [segmentReturnMass_operator G hloc a γ ep L (g x) P hpos hP,
    segmentReturnMass_operator G hloc a γ ep L x P hpos hP,←g.tsum_eq]
  apply tsum_congr
  intro y
  rw [mem_vertexOrbit_aut_iff G (γ ep) hg]
  have hh := walkPower_invariant G hloc a P hP L g ⟨b,hg⟩ x y
  rw [hh]

omit [Fintype I] in
theorem segmentReturnMass_on_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (hx : x ∈ vertexOrbit G (γ ep))
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) :
    segmentReturnMass G hloc a γ ep L x = segmentReturnMass G hloc a γ ep L (γ ep) := by
  obtain ⟨g,b,hg,rfl⟩ := hx
  exact segmentReturnMass_aut G hloc a γ ep L (γ ep) P hpos hP hg

 

noncomputable def escapeLabelProbability (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) : ℝ :=
  ξ.mass (walkKernel G hloc a) /
    (((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) *
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
      segmentReturnMass G hloc a γ ep L (γ ep))

theorem rooted_label_probability_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hq : segmentReturnMass G hloc a γ ep L (γ ep) ≠ 0) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) = 1 := by
  have hN (i : I) : ((segmentAnchors G hloc γ n hdiam i (γ i)).card : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i (γ i)).mpr
      (by exact ⟨Equiv.refl V,Equiv.refl E,(fun e => by simp),rfl⟩))
  simp only [escapeLabelProbability,tsum_div_const]
  rw [rooted_label_mass_sum G hloc a γ n hdiam center ep neg L m x]
  have he (s : I → V) (hs : s ∈ segmentAnchors G hloc γ n hdiam center x) :
      segmentReturnMass G hloc a γ ep L (s ep) = segmentReturnMass G hloc a γ ep L (γ ep) := by
    obtain ⟨⟨g,b,hg,rfl⟩,_⟩ := (mem_segmentAnchors G hloc γ n hdiam center x s).mp hs
    exact segmentReturnMass_aut G hloc a γ ep L (γ ep) P hpos hP hg
  rw [Finset.sum_congr rfl (fun s hs => congrArg (fun q => _ * q) (he s hs))]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx,←mul_assoc]
  exact div_self (mul_ne_zero (mul_ne_zero (hN center) (hN ep)) hq)

theorem escapeLabelProbability_reverse (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) :
    escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.reverse =
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ := by
  simp only [escapeLabelProbability,EscapeLabel.mass_reverse _ (walkKernel_symmetric G hloc a)]

end LabeledNormalization
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
theorem isAut_refl (G : BondGraph V E) : IsAut G (Equiv.refl V) (Equiv.refl E) := by
  intro e
  simp

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def autMap {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) : EscapeLabel G γ ep neg L m where
  first := a ∘ ξ.first
  first_mem := (segmentOrbit_aut_iff G γ ξ.first hab).mpr ξ.first_mem
  last := a ∘ ξ.last
  last_mem := (segmentOrbit_aut_iff G γ ξ.last hab).mpr ξ.last_mem
  middle := ξ.middle.map (autSimpleGraph G hab).toHom
  leftTail := ⟨a ξ.leftTail.1,ξ.leftTail.2.map (autSimpleGraph G hab).toHom⟩
  rightTail := ⟨a ξ.rightTail.1,ξ.rightTail.2.map (autSimpleGraph G hab).toHom⟩

theorem autMap_trans {a c : V ≃ V} {b d : E ≃ E} (hab : IsAut G a b) (hcd : IsAut G c d)
    (ξ : EscapeLabel G γ ep neg L m) :
    autMap hcd (autMap hab ξ) = autMap (isAut_trans G hab hcd) ξ := by
  cases ξ
  dsimp only [autMap,autSimpleGraph]
  simp only [HoldingWalk.map_map]
  rfl

theorem autMap_refl (ξ : EscapeLabel G γ ep neg L m) :
    autMap (isAut_refl G) ξ = ξ := by
  cases ξ with
  | mk f hf l hl mid α β =>
    change EscapeLabel.mk f hf l hl (mid.map SimpleGraph.Hom.id)
      ⟨α.1,α.2.map SimpleGraph.Hom.id⟩ ⟨β.1,β.2.map SimpleGraph.Hom.id⟩ = _
    simp only [HoldingWalk.map_id]

theorem autMap_symm {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    autMap (isAut_symm G hab) (autMap hab ξ) = ξ := by
  rw [autMap_trans]
  have ha : a.trans a.symm = Equiv.refl V := by ext x; exact a.symm_apply_apply x
  have hb : b.trans b.symm = Equiv.refl E := by ext x; exact b.symm_apply_apply x
  generalize hp : isAut_trans G hab (isAut_symm G hab) = h
  clear hp
  revert h
  rw [ha,hb]
  intro h
  exact autMap_refl ξ

def autEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) :
    EscapeLabel G γ ep neg L m ≃ EscapeLabel G γ ep neg L m where
  toFun := autMap hab
  invFun := autMap (isAut_symm G hab)
  left_inv := autMap_symm hab
  right_inv := autMap_symm (isAut_symm G hab)

def autRootedEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (center : I) (x : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} ≃
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = a x} where
  toFun ξ := ⟨autMap hab ξ.1,congrArg a ξ.2⟩
  invFun ξ := ⟨autMap (isAut_symm G hab) ξ.1,by
    change a.symm (ξ.1.first center) = x
    rw [ξ.2,a.symm_apply_apply]⟩
  left_inv ξ := Subtype.ext (autMap_symm hab ξ.1)
  right_inv ξ := Subtype.ext (autMap_symm (isAut_symm G hab) ξ.1)

theorem mass_autMap (hloc : LocallyFinite G) (a₀ : ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    (autMap hab ξ).mass (walkKernel G hloc a₀) = ξ.mass (walkKernel G hloc a₀) := by
  change (ξ.middle.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) *
    (ξ.leftTail.2.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) *
    (ξ.rightTail.2.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) = _
  simp only [HoldingWalk.mass_map (autSimpleGraph G hab).toHom _ _ (walkKernel_covariant G hloc a₀ hab)]
  rfl

end EscapeLabel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LazyOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_lazy (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1/2)
    (x : V) : 1/2 ≤ walkKernel G hloc a x x := by
  have hn : ((neighbors G hloc x).card : ℝ) ≤ D := by
    exact_mod_cast (neighbors_card_le_degree G hloc x).trans (hD x)
  have hh := mul_le_mul_of_nonneg_left hn ha
  simp only [walkKernel,ite_true]
  split_ifs <;> linarith

theorem positive_lazy_power_step (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (k : ℕ) (x y : V) :
    (1/2) * (matrixCoeff (P^k) x y).re ≤ (matrixCoeff (P^(k+1)) x y).re := by
  have hs := hpos.mul_hasSum (P^k) x y
  have hh := hs.summable.sum_le_tsum ({x} : Finset V)
    (fun z _ => mul_nonneg (hpos x z).2 ((hpos.pow k) z y).2)
  simp only [Finset.sum_singleton,hs.tsum_eq,←pow_succ'] at hh
  exact (mul_le_mul_of_nonneg_right (hdiag x) ((hpos.pow k) x y).2).trans hh

 

theorem walkPower_orbit_return_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (L : ℕ) :
    (1/2) * (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' y, if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^L) (root i₀) y).re else 0 := by
  have hsum (k : ℕ) : Summable (fun y =>
      if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^k) (root i₀) y).re else 0) := by
    simpa only [mul_ite,mul_one,mul_zero] using finiteKernel_summable_mul
      (fun x y => (matrixCoeff (P^k) x y).re) (walkPower_finite_support G hloc a P hpos hP k)
      (root i₀) (fun y => if y ∈ vertexOrbit G (root i₀) then 1 else 0)
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' L
  · rw [hk]
    have hh := walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k
    have hn : 0 ≤ ∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0 :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hw i | rfl)
    linarith
  · rw [hk]
    have hh := mul_le_mul_of_nonneg_left
      (walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k)
      (show (0:ℝ) ≤ 1/2 by norm_num)
    apply hh.trans
    rw [←tsum_mul_left]
    apply ((hsum (2*k)).mul_left (1/2)).tsum_le_tsum _ (hsum (2*k+1))
    intro y
    split_ifs
    · exact positive_lazy_power_step P hpos hdiag (2*k) (root i₀) y
    · simp only [mul_zero,le_refl]

end LazyOrbitReturn
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section UniformLabeledLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
 

theorem segmentReturnMass_uniform_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (γ : I → V) (ep : I) (L : ℕ) :
    1/(2*c) ≤ segmentReturnMass G hloc a γ ep L (γ ep) := by
  obtain ⟨i,g,hg,hx⟩ := hcov (γ ep)
  obtain ⟨b,hb⟩ := hΓ hg
  have hO := vertexOrbit_eq_of_mem G (root i) (γ ep) ⟨g,b,hb,hx⟩
  rw [←hx,segmentReturnMass_aut G hloc a γ ep L (root i) P hpos hP hb]
  rw [segmentReturnMass_operator G hloc a γ ep L (root i) P hpos hP]
  rw [hO]
  have hh := walkPower_orbit_return_lower G hloc a root weight Γ hΓ htr
    (fun i => (hw i).le) hw1 i (hw i) P hpos hsym hP hdiag L
  have hi : weight i ≤ ∑ r, if root r ∈ vertexOrbit G (root i) then weight r else 0 := by
    have hx' : root i ∈ vertexOrbit G (root i) := ⟨Equiv.refl _,Equiv.refl _,isAut_refl G,rfl⟩
    simpa only [ite_eq_left hx'] using Finset.single_le_sum
      (f := fun r => if root r ∈ vertexOrbit G (root i) then weight r else 0)
      (fun r _ => by split_ifs <;> first | exact (hw r).le | rfl) (Finset.mem_univ i)
  apply le_trans _ hh
  have hct : 0 < 2*c := mul_pos (by norm_num) hc
  apply (div_le_iff₀ hct).mpr
  have hh' := mul_le_mul_of_nonneg_left hi hc.le
  nlinarith [hmin i]

 

theorem rooted_label_probability_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    HasSum (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) 1 := by
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hp : 0 < segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).trans_le hq
  have hs : Summable (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  rw [←rooted_label_probability_sum G hloc a γ n hdiam center ep neg L m x hx P hpos hP (ne_of_gt hp)]
  exact hs.hasSum

end UniformLabeledLaw
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def labelEndpointEquiv (center : I) (x : V) :
    (Σ y : V, {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}) ≃
      {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} where
  toFun ξ := ⟨ξ.2.1,ξ.2.2.1⟩
  invFun ξ := ⟨ξ.1.last center,ξ.1,ξ.2,rfl⟩
  left_inv ξ := by rcases ξ with ⟨y,ξ,hx,hy⟩; subst y; rfl
  right_inv ξ := rfl

def labelAutPairEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (center : I) (x y : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} ≃
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = a x ∧ ξ.last center = a y} where
  toFun ξ := ⟨EscapeLabel.autMap hab ξ.1,congrArg a ξ.2.1,congrArg a ξ.2.2⟩
  invFun ξ := ⟨EscapeLabel.autMap (isAut_symm G hab) ξ.1,by
    change a.symm (ξ.1.first center) = x ∧ a.symm (ξ.1.last center) = y
    rw [ξ.2.1,ξ.2.2,a.symm_apply_apply,a.symm_apply_apply]
    exact ⟨rfl,rfl⟩⟩
  left_inv ξ := Subtype.ext (EscapeLabel.autMap_symm hab ξ.1)
  right_inv ξ := Subtype.ext (EscapeLabel.autMap_symm (isAut_symm G hab) ξ.1)

noncomputable def escapeLabelTransport (center : I) (B : EscapeLabel G γ ep neg L m → ℝ) (x y : V) : ℝ :=
  ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}, B ξ.1

theorem escapeLabelTransport_reverse (center : I) (B : EscapeLabel G γ ep neg L m → ℝ) (x y : V) :
    escapeLabelTransport center B x y =
      escapeLabelTransport center (fun ξ => B ξ.reverse) y x := by
  unfold escapeLabelTransport
  exact (EscapeLabel.reverseRootedEquiv center y x).tsum_eq _ |>.symm

theorem escapeLabelTransport_aut (center : I) (B : EscapeLabel G γ ep neg L m → ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (hB : ∀ ξ, B (EscapeLabel.autMap hab ξ) = B ξ) (x y : V) :
    escapeLabelTransport center B (a x) (a y) = escapeLabelTransport center B x y := by
  unfold escapeLabelTransport
  rw [←(labelAutPairEquiv hab center x y).tsum_eq]
  exact tsum_congr (fun ξ => hB ξ.1)

variable [Fintype I]

theorem finite_pair_label_sigma (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I) (x : V) :
    Finite (Σ y : V, {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}) := by
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  exact Finite.of_equiv _ (labelEndpointEquiv center x).symm

theorem escapeLabelTransport_row_sum (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (x : V) :
    (∑' y, escapeLabelTransport center B x y) =
      ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1 := by
  let := finite_pair_label_sigma hloc n hdiam center (ep := ep) (neg := neg) (L := L) (m := m) x
  have hs : Summable (fun ξ : Σ y : V, {ξ : EscapeLabel G γ ep neg L m //
      ξ.first center = x ∧ ξ.last center = y} => B ξ.2.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  unfold escapeLabelTransport
  rw [←hs.tsum_sigma]
  exact (labelEndpointEquiv (G := G) (γ := γ) (ep := ep) (neg := neg) (L := L) (m := m) center x).tsum_eq (fun ξ => B ξ.1)

theorem escapeLabelTransport_rowSummable (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (x : V) :
    Summable (escapeLabelTransport center B x) := by
  let := finite_pair_label_sigma hloc n hdiam center (ep := ep) (neg := neg) (L := L) (m := m) x
  have hs : Summable (fun ξ : Σ y : V, {ξ : EscapeLabel G γ ep neg L m //
      ξ.first center = x ∧ ξ.last center = y} => B ξ.2.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  exact hs.sigma

theorem escapeLabelTransport_columnSummable (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (y : V) :
    Summable (fun x => escapeLabelTransport center B x y) := by
  simp only [escapeLabelTransport_reverse center B]
  exact escapeLabelTransport_rowSummable hloc n hdiam center (fun ξ => B ξ.reverse) y

end LabeledTransport
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledReRooting
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem EscapeLabel.first_orbit (ξ : EscapeLabel G γ ep neg L m) (i : I) :
    ξ.first i ∈ vertexOrbit G (γ i) := by
  obtain ⟨a,b,h,he⟩ := ξ.first_mem
  exact ⟨a,b,h,(congrFun he i).symm⟩

theorem EscapeLabel.last_orbit (ξ : EscapeLabel G γ ep neg L m) (i : I) :
    ξ.last i ∈ vertexOrbit G (γ i) := by
  obtain ⟨a,b,h,he⟩ := ξ.last_mem
  exact ⟨a,b,h,(congrFun he i).symm⟩

theorem escapeLabelTransport_zero (center : I) (B : EscapeLabel G γ ep neg L m → ℝ)
    (x y : V) (hxy : x ∉ vertexOrbit G (γ center) ∨ y ∉ vertexOrbit G (γ center)) :
    escapeLabelTransport center B x y = 0 := by
  let : IsEmpty {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} :=
    ⟨fun ξ => by
      rcases hxy with hx | hy
      · exact hx (ξ.2.1 ▸ ξ.1.first_orbit center)
      · exact hy (ξ.2.2 ▸ ξ.1.last_orbit center)⟩
  exact tsum_empty

variable [Fintype I]

 

theorem rooted_label_weight_reversal (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (hθ : 0 < ∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)
    (B : EscapeLabel G γ ep neg L m → ℝ)
    (hB : ∀ (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) ξ, B (EscapeLabel.autMap hab ξ) = B ξ)
    (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1) =
      ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1.reverse := by
  let M := escapeLabelTransport center B
  have hM (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (u v : V) : M (a u) (a v) = M u v :=
    escapeLabelTransport_aut center B hab (hB a b hab) u v
  have hr (u : V) : (∑' v, M u v) = if u ∈ vertexOrbit G (γ center) then ∑' v, M (γ center) v else 0 := by
    split_ifs with hu
    · obtain ⟨a,b,hab,rfl⟩ := hu
      rw [←a.tsum_eq]
      exact tsum_congr (fun v => hM a b hab (γ center) v)
    · calc
        _ = ∑' _ : V, (0:ℝ) := tsum_congr (fun v => escapeLabelTransport_zero center B u v (Or.inl hu))
        _ = 0 := tsum_zero
  have hc (v : V) : (∑' u, M u v) = if v ∈ vertexOrbit G (γ center) then ∑' u, M u (γ center) else 0 := by
    split_ifs with hv
    · obtain ⟨a,b,hab,rfl⟩ := hv
      rw [←a.tsum_eq]
      exact tsum_congr (fun u => hM a b hab u (γ center))
    · calc
        _ = ∑' _ : V, (0:ℝ) := tsum_congr (fun u => escapeLabelTransport_zero center B u v (Or.inr hv))
        _ = 0 := tsum_zero
  have ht := htr.real root weight Γ M
    (fun a ha u v => by obtain ⟨b,hb⟩ := hΓ ha; exact hM a b hb u v)
    (escapeLabelTransport_rowSummable hloc n hdiam center B)
    (escapeLabelTransport_columnSummable hloc n hdiam center B)
  have hfactor (f : V → ℝ) (q : ℝ) (he : ∀ u, f u = if u ∈ vertexOrbit G (γ center) then q else 0) :
      (∑ i, weight i*f (root i)) = (∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)*q := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [he]
    split_ifs <;> simp only [mul_zero,zero_mul]
  rw [hfactor _ _ hr,hfactor _ _ hc] at ht
  have hrc := (mul_left_cancel₀ (ne_of_gt hθ)) ht
  have hxe : (∑' v, M x v) = ∑' u, M u x := by
    rw [hr x,hc x,ite_eq_left hx,ite_eq_left hx]
    exact hrc
  calc
    _ = ∑' v, M x v := (escapeLabelTransport_row_sum hloc n hdiam center B x).symm
    _ = ∑' u, M u x := hxe
    _ = ∑' u, escapeLabelTransport center (fun ξ => B ξ.reverse) x u :=
      tsum_congr (fun u => escapeLabelTransport_reverse center B u x)
    _ = _ := escapeLabelTransport_row_sum hloc n hdiam center (fun ξ => B ξ.reverse) x

end LabeledReRooting
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section ExactLabeledReversal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem escapeLabelProbability_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (a₀ : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m (EscapeLabel.autMap hab ξ) =
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ := by
  simp only [escapeLabelProbability,EscapeLabel.mass_autMap]

 

theorem rooted_escape_label_reversal (G : BondGraph V E) (hloc : LocallyFinite G) (a₀ : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I) (L m : ℕ)
    (hθ : 0 < ∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)
    (F : EscapeLabel G γ ep neg L m → ℝ)
    (hF : ∀ (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) ξ, F (EscapeLabel.autMap hab ξ) = F ξ)
    (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ.1 * F ξ.1) =
    ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ.1 * F ξ.1.reverse := by
  have hh := rooted_label_weight_reversal hloc root weight Γ hΓ htr n hdiam center hθ
    (fun ξ => escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ * F ξ)
    (fun a b hab ξ => by rw [escapeLabelProbability_aut G hloc a₀ γ n hdiam center ep neg L m hab,hF a b hab]) x hx
  simpa only [escapeLabelProbability_reverse] using hh

theorem escapeLabelProbability_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) :
    0 ≤ escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ := by
  have hq : 0 ≤ segmentReturnMass G hloc a γ ep L (γ ep) := by
    apply tsum_nonneg
    intro mid
    split_ifs
    · exact mid.2.mass_nonneg _ hP
    · rfl
  exact div_nonneg (ξ.mass_nonneg _ hP) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hq)

end ExactLabeledReversal
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LongGeodesics
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_geodesic_length (G : BondGraph V E) [Infinite V]
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) (N : ℕ) :
    ∃ y : V, ∃ q : (openSimpleGraph G Set.univ).Walk x y,
      q.length = N ∧ q.length = (openSimpleGraph G Set.univ).dist x y := by
  obtain ⟨z,hz⟩ := (finite_reachBall hloc x N).exists_notMem
  have hc := (conn_iff_reachable G Set.univ x z).mp (conn_univ_of_connected G hconn x z)
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist
  have hN : N < q.length := by
    by_contra hh
    have hm := walk_mem_reachBall G Set.univ q 0 (show x ∈ reachBall G x 0 from rfl)
    have hm' : z ∈ reachBall G x q.length := by simpa only [Nat.zero_add] using hm
    exact hz (reachBall_mono_local G x (Nat.le_of_not_gt hh) hm')
  refine ⟨q.getVert N,q.take N,?_,?_⟩
  · simp only [SimpleGraph.Walk.take_length,inf_eq_left.mpr hN.le]
  · exact SimpleGraph.length_eq_dist_of_subwalk hq (q.isSubwalk_take N)

 

theorem geodesic_getVert_dist (H : SimpleGraph V) {x y : V} (q : H.Walk x y)
    (hq : q.length = H.dist x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ q.length) :
    H.dist (q.getVert i) (q.getVert j) = j-i := by
  have hs := SimpleGraph.length_eq_dist_of_subwalk hq
    (((q.drop i).isSubwalk_take (j-i)).trans (q.isSubwalk_drop i))
  have he : (q.drop i).getVert (j-i) = q.getVert j := by
    rw [SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hij]
  rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,he,
    min_eq_left (Nat.sub_le_sub_right hj i)] at hs
  exact hs.symm

end LongGeodesics
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def append : {k l : ℕ} → {x y z : V} → HoldingWalk H k x y → HoldingWalk H l y z → HoldingWalk H (l+k) x z
  | _,_,_,_,_,.nil _,v => v
  | _,_,_,_,_,.hold w,v => .hold (w.append v)
  | _,_,_,_,_,.step h w,v => .step h (w.append v)

def ofWalk : {x y : V} → (w : H.Walk x y) → HoldingWalk H w.length x y
  | _,_,.nil => .nil _
  | _,_,.cons h w => .step h (ofWalk w)

theorem mass_append (P : V → V → ℝ) {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) :
    (w.append v).mass P = w.mass P*v.mass P := by
  induction w with
  | nil => simp only [append,mass,one_mul]
  | hold w ih => simp only [append,mass,ih,mul_assoc]
  | step h w ih => simp only [append,mass,ih,mul_assoc]

theorem mass_ofWalk (P : V → V → ℝ) (a : ℝ) (hP : ∀ x y, H.Adj x y → P x y = a)
    {x y : V} (w : H.Walk x y) : (ofWalk w).mass P = a^w.length := by
  induction w with
  | nil => rfl
  | @cons x z y h w ih => simp only [ofWalk,mass,hP x z h,ih,SimpleGraph.Walk.length_cons,pow_succ'];

theorem ofWalk_vertices {x y : V} (w : H.Walk x y) : (ofWalk w).vertices = w.support := by
  induction w with
  | nil => rfl
  | cons h w ih => simp only [ofWalk,vertices,SimpleGraph.Walk.support_cons,ih]

theorem append_vertices {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) :
    (w.append v).vertices = w.vertices.dropLast ++ v.vertices := by
  induction w with
  | nil => rfl
  | hold w ih =>
    have hn : w.vertices ≠ [] := by cases w <;> simp [vertices]
    simp only [append,vertices,ih,List.dropLast_cons_of_ne_nil hn,List.cons_append]
  | step h w ih =>
    have hn : w.vertices ≠ [] := by cases w <;> simp [vertices]
    simp only [append,vertices,ih,List.dropLast_cons_of_ne_nil hn,List.cons_append]

end HoldingWalk
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GeodesicSegments
attribute [local instance] Classical.propDecidable Classical.decEq

 

def geodesicSegment (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) : Fin (N+1) → V :=
  fun i => q.getVert i

theorem geodesicSegment_adj (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N)
    (i : ℕ) (hi : i < N) :
    (openSimpleGraph G Set.univ).Adj
      (geodesicSegment G q N ⟨i,by omega⟩) (geodesicSegment G q N ⟨i+1,by omega⟩) := by
  change (openSimpleGraph G Set.univ).Adj (q.getVert i) (q.getVert (i+1))
  exact q.adj_getVert_succ (by omega)

theorem geodesicSegment_injective (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N)
    (hq : q.length = (openSimpleGraph G Set.univ).dist x y) :
    Function.Injective (geodesicSegment G q N) := by
  intro i j hh
  apply Fin.ext
  exact (q.isPath_of_length_eq_dist hq).getVert_injOn
    (by change i.val ≤ q.length; omega) (by change j.val ≤ q.length; omega) hh

theorem geodesicSegment_diameter (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N) :
    ∀ i j, geodesicSegment G q N j ∈ reachBall G (geodesicSegment G q N i) N := by
  intro i j
  have hc : (openSimpleGraph G Set.univ).Reachable (q.getVert i) (q.getVert j) :=
    (q.take i).reachable.symm.trans (q.take j).reachable
  obtain ⟨r,hr⟩ := hc.exists_walk_length_eq_dist
  have hd : (openSimpleGraph G Set.univ).dist (q.getVert i) (q.getVert j) ≤ N := by
    rcases le_total i.val j.val with hij | hji
    · have hle := SimpleGraph.dist_le ((q.drop i).take (j-i))
      rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
        SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hij] at hle
      exact hle.trans (by omega)
    · have hle := SimpleGraph.dist_le ((q.drop j).take (i-j))
      rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
        SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hji] at hle
      rw [SimpleGraph.dist_comm] at hle
      exact hle.trans (by omega)
  have hm := walk_mem_reachBall G Set.univ r 0 (show q.getVert i ∈ reachBall G (q.getVert i) 0 from rfl)
  apply reachBall_mono_local G (q.getVert i) (a := r.length) (by omega)
  simpa only [Nat.zero_add, geodesicSegment] using hm

theorem segmentOrbit_adj (G : BondGraph V E) {I : Type*} (γ s : I → V)
    (hs : s ∈ segmentOrbit G γ) (i j : I) (hij : (openSimpleGraph G Set.univ).Adj (γ i) (γ j)) :
    (openSimpleGraph G Set.univ).Adj (s i) (s j) := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  exact (autSimpleGraph G hab).map_rel_iff.mpr hij

theorem walkKernel_step (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {x y : V} (h : (openSimpleGraph G Set.univ).Adj x y) : walkKernel G hloc a x y = a := by
  have hh := (openSimpleGraph_univ_adj G x y).mp h
  simp only [walkKernel,ite_eq_right hh.1,ite_eq_left hh.2,zero_add]

theorem walkKernel_ofWalk_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {x y : V} (q : (openSimpleGraph G Set.univ).Walk x y) :
    (HoldingWalk.ofWalk q).mass (walkKernel G hloc a) = a^q.length :=
  HoldingWalk.mass_ofWalk _ a (fun _ _ h => walkKernel_step G hloc a h) q

end GeodesicSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualTailPotentials
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_tail_twoPoint_expectation (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x b : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * twoPoint G p w.1 b) =
      (matrixCoeff (P^m*A) x b).re := by
  have he : (fun y => twoPoint G p y b) = (fun y => (matrixCoeff A y b).re) := by
    funext y
    rw [matrixCoeff,hA y b,Complex.ofReal_re]
  change RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) m x (twoPoint G p · b) = _
  rw [he,raw_integral_operator G hloc a P hpos hP]
  exact ((hpos.pow m).mul_hasSum A x b).tsum_eq

 

theorem raw_tail_potential_bound [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x : V) (S : Finset V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * ∑ b ∈ S, twoPoint G p w.1 b) ≤
      (S.card:ℝ) * Real.sqrt c * ‖P‖^m := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  have hPinv : KernelInvariant (vertexAut G) P := by
    intro e he x y
    obtain ⟨f,hf⟩ := he
    rw [hP,hP,walkKernel_covariant G hloc a hf]
  calc
    _ = ∑ b ∈ S, (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
        w.2.mass (walkKernel G hloc a) * twoPoint G p w.1 b) := by
      simp only [tsum_fintype,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ b ∈ S, (matrixCoeff (P^m*A) x b).re := by
      apply Finset.sum_congr rfl
      intro b _
      exact raw_tail_twoPoint_expectation G hloc a P A hpos hP p hA m x b
    _ ≤ ∑ _b ∈ S, Real.sqrt c * ‖P‖^m := by
      apply Finset.sum_le_sum
      intro b _
      exact (Complex.re_le_norm _).trans (twoPoint_operator_smoothing G p root weight htr hcov hw hsum c hc hmin A P hA hPinv m x b)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]

end ActualTailPotentials
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AuxiliaryTailMarkov
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_weighted_markov {α : Type*} [Fintype α] (μ F : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x) (t : ℝ) (ht : 0 < t) :
    (∑ x, if t < F x then μ x else 0) ≤ (∑ x, μ x*F x)/t := by
  apply (le_div_iff₀ ht).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · exact mul_le_mul_of_nonneg_left hx.le (hμ x)
  · exact (by simpa only [zero_mul] using mul_nonneg (hμ x) (hF x))

theorem raw_tail_potential_failure [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x : V) (S : Finset V)
    (t : ℝ) (ht : 0 < t) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if t < ∑ b ∈ S, twoPoint G p w.1 b then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((S.card:ℝ) * Real.sqrt c * ‖P‖^m)/t := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hM := finite_weighted_markov
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w => ∑ b ∈ S, twoPoint G p w.1 b)
    (fun w => w.2.mass_nonneg _ hK)
    (fun w => Finset.sum_nonneg (fun b _ => twoPoint_nonneg G p w.1 b)) t ht
  have hB := raw_tail_potential_bound G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m x S
  simp only [tsum_fintype] at hB ⊢
  exact hM.trans (div_le_div_of_nonneg_right hB ht.le)

 

theorem finite_product_failure_union {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (ν : β → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hμ1 : ∑ x, μ x = 1) (hν1 : ∑ y, ν y = 1) (B : α → Prop) (C : β → Prop) :
    (∑ z : α × β, if B z.1 ∨ C z.2 then μ z.1*ν z.2 else 0) ≤
      (∑ x, if B x then μ x else 0) + ∑ y, if C y then ν y else 0 := by
  calc
    _ ≤ ∑ z : α × β, ((if B z.1 then μ z.1 else 0)*ν z.2 + μ z.1*(if C z.2 then ν z.2 else 0)) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hB : B z.1 <;> by_cases hC : C z.2 <;>
        simp [hB,hC]
      exact mul_nonneg (hμ _) (hν _)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,hμ1,hν1,mul_one,one_mul]

end AuxiliaryTailMarkov
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentTailPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem two_raw_tail_potential_failure [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x y : V) (S : Finset V)
    (t : ℝ) (ht : 0 < t) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) m y,
      if (t < ∑ b ∈ S, twoPoint G p w.1.1 b) ∨ (t < ∑ b ∈ S, twoPoint G p w.2.1 b)
      then w.1.2.mass (walkKernel G hloc a) * w.2.2.mass (walkKernel G hloc a) else 0) ≤
      2*((S.card:ℝ) * Real.sqrt c * ‖P‖^m)/t := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m y)
  have hK (u v : V) : 0 ≤ walkKernel G hloc a u v := by
    simpa only [hP,Complex.ofReal_re] using (hpos u v).2
  have hμ := rawFrom_probability_sum G hloc a m x
  have hν := rawFrom_probability_sum G hloc a m y
  simp only [tsum_fintype] at hμ hν
  have hU := finite_product_failure_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w : RawFrom (openSimpleGraph G Set.univ) m y => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK) (fun w => w.2.mass_nonneg _ hK) hμ hν
    (fun w => t < ∑ b ∈ S, twoPoint G p w.1 b)
    (fun w => t < ∑ b ∈ S, twoPoint G p w.1 b)
  have hx := raw_tail_potential_failure G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m x S t ht
  have hy := raw_tail_potential_failure G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m y S t ht
  simp only [tsum_fintype] at hx hy ⊢
  exact hU.trans ((add_le_add hx hy).trans_eq (by ring))

end IndependentTailPotentialTests
end Percolation

 
namespace Percolation
section LogarithmicTailLength

 

theorem logarithmic_tail_power (ρ X : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hX : 0 < X) :
    ρ ^ ⌈(2/(-Real.log ρ))*Real.log X⌉₊ ≤ X^(-2:ℝ) := by
  have hl : Real.log ρ ≠ 0 := ne_of_lt (Real.log_neg hρ hρ1)
  calc
    _ = ρ ^ (⌈(2/(-Real.log ρ))*Real.log X⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ρ ^ ((2/(-Real.log ρ))*Real.log X) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le (Nat.le_ceil _)
    _ = X^(-2:ℝ) := by
      rw [Real.rpow_def_of_pos hρ,Real.rpow_def_of_pos hX]
      congr 1
      field_simp [hl]

 

theorem exists_uniform_logarithmic_tail_cutoff (ρ A : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (kmin : ℕ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ 1 < (-Real.log ρ)*C₁ ∧
      ∃ k₀ : ℕ, kmin ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        A*((k:ℝ)+1)*R*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊ ≤ 1/4 := by
  have hlambda : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  refine ⟨2/(-Real.log ρ),div_pos (by norm_num) hlambda,?_,max kmin ⌈4*A⌉₊,le_max_left _ _,?_⟩
  · rw [mul_div_cancel₀ _ (ne_of_gt hlambda)]
    norm_num
  · intro k hk R hR
    have hk' : ⌈4*A⌉₊ ≤ k := (le_max_right _ _).trans hk
    have hAk : 4*A ≤ (k:ℝ) := (Nat.le_ceil (4*A)).trans (by exact_mod_cast hk')
    have hkpos : 0 < (k:ℝ)+1 := by positivity
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
    let X : ℝ := ((k:ℝ)+1)*R
    have hX : 0 < X := mul_pos hkpos hRp
    have hXk : (k:ℝ)+1 ≤ X := by dsimp [X]; exact le_mul_of_one_le_right hkpos.le hR
    have hp := logarithmic_tail_power ρ X hρ hρ1 hX
    have hneg : X^(-2:ℝ) = (X^2)⁻¹ := by rw [Real.rpow_neg,show (2:ℝ) = (2:ℕ) by norm_num,Real.rpow_natCast]; exact hX.le
    calc
      _ = A*X*ρ^⌈(2/(-Real.log ρ))*Real.log X⌉₊ := by dsimp [X]; ring
      _ ≤ A*X*X^(-2:ℝ) := mul_le_mul_of_nonneg_left hp (mul_nonneg hA hX.le)
      _ = A/X := by rw [hneg]; field_simp [ne_of_gt hX]
      _ ≤ 1/4 := (div_le_iff₀ hX).mpr (by linarith)

end LogarithmicTailLength
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def position : {k : ℕ} → {x y : V} → HoldingWalk H k x y → ℕ → V
  | _,x,_,.nil _,_ => x
  | _,x,_,.hold _,0 => x
  | _,_,_,.hold w,n+1 => w.position n
  | _,x,_,.step _ _,0 => x
  | _,_,_,.step _ w,n+1 => w.position n

@[simp] theorem position_zero {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.position 0 = x := by
  cases w <;> rfl

@[simp] theorem position_length {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.position k = y := by
  induction w with
  | nil => rfl
  | hold w ih => exact ih
  | step h w ih => exact ih

theorem position_mem_vertices {k : ℕ} {x y : V} (w : HoldingWalk H k x y) (i : ℕ) :
    w.position i ∈ w.vertices := by
  induction w generalizing i with
  | nil => simp only [position,vertices,List.mem_singleton]
  | hold w ih => cases i <;> simp only [position,vertices,List.mem_cons,true_or,ih,or_true]
  | step h w ih => cases i <;> simp only [position,vertices,List.mem_cons,true_or,ih,or_true]

theorem mem_vertices_iff_position {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) :
    z ∈ w.vertices ↔ ∃ i : ℕ, i ≤ k ∧ w.position i = z := by
  induction w with
  | nil => simp only [vertices,List.mem_singleton,Nat.le_zero,exists_eq_left,position,eq_comm]
  | @hold k x y w ih =>
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨0,Nat.zero_le _,rfl⟩
      · obtain ⟨i,hi,he⟩ := ih.mp hz
        exact ⟨i+1,Nat.succ_le_succ hi,he⟩
    · rintro ⟨i,hi,he⟩
      cases i with
      | zero => exact List.mem_cons.mpr (Or.inl he.symm)
      | succ i => exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨i,Nat.le_of_succ_le_succ hi,he⟩))
  | @step k x u y h w ih =>
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨0,Nat.zero_le _,rfl⟩
      · obtain ⟨i,hi,he⟩ := ih.mp hz
        exact ⟨i+1,Nat.succ_le_succ hi,he⟩
    · rintro ⟨i,hi,he⟩
      cases i with
      | zero => exact List.mem_cons.mpr (Or.inl he.symm)
      | succ i => exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨i,Nat.le_of_succ_le_succ hi,he⟩))

end HoldingWalk
end Percolation

end OAI
