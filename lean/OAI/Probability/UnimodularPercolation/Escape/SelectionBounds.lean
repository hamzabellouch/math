import Mathlib
import OAI.Probability.UnimodularPercolation.Escape.PositiveEscapes

namespace OAI

/-! Selection Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
section BothEscapeChoiceOrder

 

theorem exists_both_escape_uniform_cutoffs (ρ c ε : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L) < ε := by
  obtain ⟨J,hJ,L₀,hL₀⟩ := exists_first_escape_uniform_cutoffs ρ c (ε/2) hρ hρ1 hc (by positivity)
  refine ⟨J,hJ,L₀,fun L hL => ?_⟩
  have hh := hL₀ L hL
  linarith

end BothEscapeChoiceOrder
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section TailConditioning
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_event_of_tail_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (B : EscapeLabel G γ ep neg L m → Prop) (ε : ℝ)
    (hB : ∀ (s : segmentAnchors G hloc γ n hdiam center x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
      (h : segmentAnchors G hloc γ n hdiam ep mid.1),
      (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
          tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0) ≤ ε) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1 then ξ.1.mass (walkKernel G hloc a) else 0) ≤
      ε * ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
        ξ.1.mass (walkKernel G hloc a) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq,←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  simp only [tsum_fintype,Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro mid _
  apply Finset.sum_le_sum
  intro h _
  have hh := hB s mid h
  simp only [tsum_fintype] at hh
  have ht : (∑ tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a)) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    simpa only [tsum_fintype,mul_one] using congrArg₂ (fun r t : ℝ => r*t)
      (rawFrom_probability_sum G hloc a m (s.val neg))
      (rawFrom_probability_sum G hloc a m (h.val neg))
  calc
    _ = mid.2.mass (walkKernel G hloc a) *
        ∑ tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
            tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tails _
      split_ifs <;> simp only [mul_zero,mul_assoc]
    _ ≤ mid.2.mass (walkKernel G hloc a)*ε := mul_le_mul_of_nonneg_left hh (mid.2.mass_nonneg _ hK)
    _ = _ := by
      simp only [mul_assoc,←Finset.mul_sum]
      rw [ht]
      ring

end TailConditioning
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section NormalizedTailConditioning
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_probability_of_tail_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center)) 
    (B : EscapeLabel G γ ep neg L m → Prop) (ε : ℝ)
    (hB : ∀ (s : segmentAnchors G hloc γ n hdiam center x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
      (h : segmentAnchors G hloc γ n hdiam ep mid.1),
      (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
          tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0) ≤ ε) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1 then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤ ε := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hqp : 0 ≤ segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).le.trans hq
  let D := ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) *
    ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
      segmentReturnMass G hloc a γ ep L (γ ep)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hqp
  have hr := rooted_label_event_of_tail_bound G hloc a hK γ n hdiam center ep neg L m x B ε hB
  have hs := (rooted_label_probability_hasSum G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx).tsum_eq
  have hd := div_le_div_of_nonneg_right hr hD
  have he : (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      ξ.1.mass (walkKernel G hloc a))/D = 1 := by
    simpa only [escapeLabelProbability,tsum_div_const,D] using hs
  simpa only [escapeLabelProbability,tsum_indicator_div,tsum_div_const,D,
    mul_div_assoc,he,mul_one] using hd

end NormalizedTailConditioning
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
def labelPotentialFailure (G : BondGraph V E) (p : unitInterval) (γ : I → V)
    (ep neg : I) (L m : ℕ)
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (t : ℝ) (ξ : EscapeLabel G γ ep neg L m) : Prop :=
  (t < ∑ b ∈ F ξ.first ⟨ξ.last ep,ξ.middle⟩ ξ.last, twoPoint G p ξ.leftTail.1 b) ∨
  (t < ∑ b ∈ F ξ.first ⟨ξ.last ep,ξ.middle⟩ ξ.last, twoPoint G p ξ.rightTail.1 b)

theorem labelFromCode_potential_failure (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (t : ℝ) (s : segmentAnchors G hloc γ n hdiam center x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
    (h : segmentAnchors G hloc γ n hdiam ep mid.1)
    (tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg)) :
    labelPotentialFailure G p γ ep neg L m F t
      (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 ↔
      (t < ∑ b ∈ F s.val mid h.val, twoPoint G p tails.1.1 b) ∨
      (t < ∑ b ∈ F s.val mid h.val, twoPoint G p tails.2.1 b) := by
  rcases s with ⟨s,hs⟩
  rcases mid with ⟨z,mid⟩
  rcases h with ⟨h,hh⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem rooted_label_potential_failure_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelPotentialFailure G p γ ep neg L m F t ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*(N*Real.sqrt c*‖P‖^m)/t := by
  apply rooted_label_probability_of_tail_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx
  intro s mid h
  simp only [labelFromCode_potential_failure]
  have hh := two_raw_tail_potential_failure G hloc a root weight htr hcov (fun r => (hw r).le) hw1
    c hc.le hmin P A hpos hP p hA m (s.val neg) (h.val neg) (F s.val mid h.val) t ht
  apply hh.trans
  gcongr
  exact hN s.val mid h.val

end FullPotentialTests
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CombinedSelectionEvents
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_collision_potential_failure_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (hρ : ‖P‖ < 1) (J : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if (labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse) ∨
        labelPotentialFailure G p γ ep neg L m F t ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
        2*(N*Real.sqrt c*‖P‖^m)/t := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hb := rooted_both_collision_probability_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hw hw1 hcov c hc hmin γ n hdiam center ep neg P hpos hsym hP hdiag hρ m L J x hx posIdx negIdx suffixIdx hsep
  have hp := rooted_label_potential_failure_bound G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA γ n hdiam center ep neg L m x hx F N hN t ht
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}
  have hu := finite_weighted_event_or
    (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1)
    (fun ξ => escapeLabelProbability_nonneg G hloc a hK γ n hdiam center ep neg L m ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
      labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse)
    (fun ξ => labelPotentialFailure G p γ ep neg L m F t ξ.1)
  simp only [tsum_fintype] at hb hp ⊢
  exact hu.trans (add_le_add hb hp)

end CombinedSelectionEvents
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section QuantitativeSelectionMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem finite_weighted_success_lower {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∑ a, μ a = 1) (B : α → Prop) [DecidablePred B] (ε : ℝ)
    (hB : (∑ a, if B a then μ a else 0) ≤ ε) :
    1-ε ≤ ∑ a, if ¬B a then μ a else 0 := by
  have he : (∑ a, if ¬B a then μ a else 0) + (∑ a, if B a then μ a else 0) = 1 := by
    rw [←Finset.sum_add_distrib,←hμ]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : B a <;> simp only [h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,zero_add,add_zero]
  linarith

 

theorem rooted_label_collision_potential_success_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (hρ : ‖P‖ < 1) (J : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    1 - (4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*(N*Real.sqrt c*‖P‖^m)/t) ≤
    ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ¬((labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse) ∨
        labelPotentialFailure G p γ ep neg L m F t ξ.1) then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0 := by
  have hb := rooted_label_collision_potential_failure_bound G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA γ n hdiam center ep neg L m x hx hρ J posIdx negIdx suffixIdx hsep F N hN t ht
  have hs := (rooted_label_probability_hasSum G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx).tsum_eq
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}
  simp only [tsum_fintype] at hs hb ⊢
  exact finite_weighted_success_lower _ hs _ _ hb

end QuantitativeSelectionMass
end Percolation

 
namespace Percolation
section JointSelectionChoiceOrder

 

theorem exists_joint_collision_potential_cutoffs (ρ c d τ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hd : 0 ≤ d) (hτ : 0 < τ) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∃ C₁ : ℝ, 0 < C₁ ∧ 1 < (-Real.log ρ)*C₁ ∧
      ∃ k₀ : ℕ, J+J+L₀ ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^(k-(J+J))) +
          2*((d+1)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) ≤ 3/8 := by
  obtain ⟨J,hJ,L₀,hL₀⟩ := exists_both_escape_uniform_cutoffs ρ c (1/8) hρ.le hρ1 hc (by norm_num)
  let A : ℝ := 2*(d+1)*Real.sqrt c/τ
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg _)) hτ.le
  obtain ⟨C₁,hC₁,hlam,k₀,hk₀,hk⟩ := exists_uniform_logarithmic_tail_cutoff ρ A hρ hρ1 hA (J+J+L₀)
  refine ⟨J,hJ,L₀,C₁,hC₁,hlam,k₀,hk₀,fun k hk' R hR => ?_⟩
  have hL : L₀ ≤ k-(J+J) := by omega
  have hb := hL₀ (k-(J+J)) hL
  have hp := hk k hk' R hR
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have he : 2*((d+1)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) =
      A*((k:ℝ)+1)*R*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊ := by
    dsimp only [A]
    field_simp [hτ.ne',hRp.ne']
  rw [he]
  linarith

end JointSelectionChoiceOrder
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section SpineMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem labelFromCode_anchor_event (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (B : (I → V) → (I → V) → Prop)
    (s : segmentAnchors G hloc γ n hdiam center x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
    (h : segmentAnchors G hloc γ n hdiam ep mid.1)
    (tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg)) :
    B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1.first
      (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1.last ↔ B s.val h.val := by
  rcases s with ⟨s,hs⟩
  rcases mid with ⟨z,mid⟩
  rcases h with ⟨h,hh⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 
theorem rooted_label_anchor_event_marginal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (B : (I → V) → (I → V) → Prop)
    [∀ s h, Decidable (B s h)] :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1.first ξ.1.last then ξ.1.mass (walkKernel G hloc a) else 0) =
    ∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B s.val h.val then mid.2.mass (walkKernel G hloc a) else 0 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  simp only [tsum_fintype,Fintype.sum_sigma,labelFromCode_anchor_event]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro mid _
  apply Finset.sum_congr rfl
  intro h _
  by_cases hb : B s.val h.val
  · simp only [hb,ite_true,Fintype.sum_prod_type,mul_assoc,←Finset.mul_sum,←Finset.sum_mul]
    have hl := rawFrom_probability_sum G hloc a m (s.val neg)
    have hr := rawFrom_probability_sum G hloc a m (h.val neg)
    simp only [tsum_fintype] at hl hr
    rw [hl,hr]
    ring
  · simp only [hb,ite_false,Finset.sum_const_zero]

end SpineMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section EndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
theorem rooted_label_endpoint_marginal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (S : Finset V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ S then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    (∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if h.val center ∈ S then mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
      (((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ)*
        segmentReturnMass G hloc a γ ep L (γ ep)) := by
  simp only [escapeLabelProbability,tsum_indicator_div,tsum_div_const]
  rw [rooted_label_anchor_event_marginal G hloc a γ n hdiam center ep neg L m x (fun _ h => h center ∈ S)]
  ring

end EndpointMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section ActualEndpointSeparation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 

theorem rooted_label_endpoint_hit_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (m L : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (S : Finset V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ S then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(S.card:ℝ)*Real.sqrt c*‖P‖^L := by
  rw [rooted_label_endpoint_marginal G hloc a γ n hdiam center ep neg L m x S]
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam center (γ center)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hqp : 0 < segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).trans_le hq
  apply (div_le_iff₀ (mul_pos hN hqp)).mpr
  have hb (s : segmentAnchors G hloc γ n hdiam center x) :
      (∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if h.val center ∈ S then mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (S.card:ℝ)*Real.sqrt c*‖P‖^L := by
    have hh := raw_anchor_finite_collision_bound G hloc a root weight Γ hΓ htr (fun r => (hw r).le)
      hw1 hcov c hc.le hmin γ n hdiam ep (fun _ : PUnit.{1} => center) (fun z : S => z.val)
      P hpos hP L (s.val ep)
    simpa [Subtype.exists] using hh
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hb s)
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hu ⊢
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx] at hu
  apply hu.trans
  have he : 1 ≤ 2*c*segmentReturnMass G hloc a γ ep L (γ ep) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*c)).mp hq
    nlinarith
  have hp : 0 ≤ ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ)*
      (S.card:ℝ)*Real.sqrt c*‖P‖^L := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hp]

end ActualEndpointSeparation
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section EndpointBallBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rooted_label_endpoint_ball_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (m L : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (r : ℕ) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ reachBall G x r then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(((d+1)^r:ℕ):ℝ)*Real.sqrt c*‖P‖^L := by
  have hh := rooted_label_endpoint_hit_bound G hloc a root weight Γ hΓ htr hw hw1 hcov c hc hmin
    γ n hdiam center ep neg P hpos hsym hP hdiag m L x hx (finite_reachBall hloc x r).toFinset
  have hb : ((finite_reachBall hloc x r).toFinset.card : ℝ) ≤ (((d+1)^r:ℕ):ℝ) := by
    exact_mod_cast (by
      simpa only [←Set.ncard_eq_toFinset_card] using reachBall_ncard_le_pow G hloc d hd x r)
  calc
    _ ≤ 2*c*((finite_reachBall hloc x r).toFinset.card:ℝ)*Real.sqrt c*‖P‖^L := by
      simpa only [Set.Finite.mem_toFinset] using hh
    _ ≤ _ := by gcongr

end EndpointBallBound
end Percolation

end OAI
