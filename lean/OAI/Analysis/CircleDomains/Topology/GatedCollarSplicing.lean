import OAI.Analysis.CircleDomains.Modulus.WeightedCollarAvoidance
import OAI.Analysis.CircleDomains.Selection.GateForbiddenSet

namespace OAI

/-! One-ended collar splicing preserves all prescribed hit locations when
the joining levels miss the hit contours. Dust avoidance is retained at
all nonterminal times in the very same constructed path. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_weighted_oneEnded_splicing_preserving_gates
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (havoid : ∀n t, (Γ n).1.val t ∉ S)
    (C K : ℕ → Set Sphere) (hgate : ∀n, GateRules C K (Γ n).1.val)
    (hpgate : ∀i, p ∉ C i)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hlevelAvoid : ∀j z, (D j).function z = (D j).level → π (z : Sphere) ∉ S)
    (hlevelGate : ∀j z, (D j).function z = (D j).level → ∀i, π (z : Sphere) ∉ C i)
    (hnest : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hlevel : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hDF : Disjoint F (closure (D 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η ∧
      GateRules C K ρ.val ∧ ∀t < (⊤ : PathTime), ρ.val t ∉ S := by
  let T := S ∪ gateForbiddenSet C K
  have hΓT (n : ℕ) (t : PathTime) : (Γ n).1.val t ∉ T := by
    rintro (hs | hg)
    · exact havoid n t hs
    · exact (gateRules_iff_avoids C K (Γ n).1.val).mp (hgate n) t hg
  have hlevelT (j : ℕ) (z : ℂ) (hz : (D j).function z = (D j).level) :
      π (z : Sphere) ∉ T := by
    rintro (hs | hg)
    · exact hlevelAvoid j z hz hs
    · exact avoids_gateForbiddenSet_of_avoids_contours C K (hlevelGate j z hz) hg
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, hρT⟩ := exists_weighted_oneEnded_splicing_avoiding_set
    d hU hG hdisj π hπ hclosed hsurj hr he ν N Γ hΓ F hF hstart p hp hend
    g hg m hm T hΓT D hlevelT hnest hshrink hlevel hDF A hA hcost w hw hpos hpoint hη
  refine ⟨ρ, θ, hρ, hρ0, hρ1, hC, ?_, ?_⟩
  · apply (gateRules_iff_avoids C K ρ.val).mpr
    intro t ht
    by_cases htop : t = ⊤
    · rw [htop, hρ1] at ht
      exact avoids_gateForbiddenSet_of_avoids_contours C K hpgate ht
    · exact hρT t (lt_top_iff_ne_top.mpr htop) (Or.inr ht)
  · intro t ht hs
    exact hρT t ht (Or.inl hs)

theorem exists_weighted_twoEnded_splicing_preserving_gates
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (havoid : ∀n t, (Γ n).1.val t ∉ S)
    (C K : ℕ → Set Sphere) (hgate : ∀n, GateRules C K (Γ n).1.val)
    (hpgate : ∀i, p ∉ C i) (hqgate : ∀i, q ∉ C i)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (E : ℕ → WeightedCollar d.physicalDomain π B q (fun z => g (z : Sphere)))
    (havoidD : ∀j z, (D j).function z = (D j).level → π (z : Sphere) ∉ S)
    (havoidE : ∀j z, (E j).function z = (E j).level → π (z : Sphere) ∉ S)
    (hgateD : ∀j z, (D j).function z = (D j).level → ∀i, π (z : Sphere) ∉ C i)
    (hgateE : ∀j z, (E j).function z = (E j).level → ∀i, π (z : Sphere) ∉ C i)
    (hnestD : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hnestE : ∀j, closure (E (j+1)).region ⊆ (E j).region)
    (hshrinkD : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hshrinkE : ∀O ∈ 𝓝 q, ∃k : ℕ, ∀j ≥ k, closure (E j).region ⊆ O)
    (hlevelD : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hlevelE : ∀j, {z | (E (j+1)).function z = (E (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (E j).region)
    (hDE : Disjoint (closure (D 0).region) (closure (E 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η ∧
      GateRules C K ρ.val ∧ ∀t ∈ Ioo (⊥ : PathTime) ⊤, ρ.val t ∉ S := by
  let T := S ∪ gateForbiddenSet C K
  have hΓT (n : ℕ) (t : PathTime) : (Γ n).1.val t ∉ T := by
    rintro (hs | hg)
    · exact havoid n t hs
    · exact (gateRules_iff_avoids C K (Γ n).1.val).mp (hgate n) t hg
  have hDT (j : ℕ) (z : ℂ) (hz : (D j).function z = (D j).level) :
      π (z : Sphere) ∉ T := by
    rintro (hs | hg)
    · exact havoidD j z hz hs
    · exact avoids_gateForbiddenSet_of_avoids_contours C K (hgateD j z hz) hg
  have hET (j : ℕ) (z : ℂ) (hz : (E j).function z = (E j).level) :
      π (z : Sphere) ∉ T := by
    rintro (hs | hg)
    · exact havoidE j z hz hs
    · exact avoids_gateForbiddenSet_of_avoids_contours C K (hgateE j z hz) hg
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, hρT⟩ := exists_weighted_twoEnded_splicing_avoiding_set
    d hU hG hdisj π hπ hclosed hsurj hr he ν N Γ hΓ p q hp hq hstart hend
    g hg m hm T hΓT D E hDT hET hnestD hnestE hshrinkD hshrinkE hlevelD hlevelE hDE
    A hA hcost w hw hpos hpoint hη
  refine ⟨ρ, θ, hρ, hρ0, hρ1, hC, ?_, ?_⟩
  · apply (gateRules_iff_avoids C K ρ.val).mpr
    intro t ht
    by_cases hbot : t = ⊥
    · rw [hbot, hρ0] at ht
      exact avoids_gateForbiddenSet_of_avoids_contours C K hpgate ht
    by_cases htop : t = ⊤
    · rw [htop, hρ1] at ht
      exact avoids_gateForbiddenSet_of_avoids_contours C K hqgate ht
    exact hρT t ⟨bot_lt_iff_ne_bot.mpr hbot, lt_top_iff_ne_top.mpr htop⟩ (Or.inr ht)
  · intro t ht hs
    exact hρT t ht (Or.inl hs)

end CircleDomainRigidity

end

end OAI
