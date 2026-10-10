import OAI.Analysis.StrictMeans.TriangularIndex

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V L : Type*} [AddCommGroup V] [LinearOrder L]

def discreteDivergence (s : V) (f : V → ℤ) (v : V) : ℤ := f (v-s)-f v

lemma finite_support_shift {f : V → ℤ} (hf : HasFiniteSupport f) (s : V) :
    HasFiniteSupport (fun v => f (v-s)) :=
  hf.preimage (Equiv.subRight s).injective.injOn

lemma finite_support_discreteDivergence {f : V → ℤ} (hf : HasFiniteSupport f) (s : V) :
    HasFiniteSupport (discreteDivergence s f) := (finite_support_shift hf s).sub hf

lemma finsum_discreteDivergence {f : V → ℤ} (hf : HasFiniteSupport f) (s : V) :
    ∑ᶠ v, discreteDivergence s f v = 0 := by
  simp only [discreteDivergence]
  rw [finsum_sub_distrib (finite_support_shift hf s) hf]
  have he := finsum_comp_equiv (Equiv.subRight s) (f := f)
  exact sub_eq_zero.mpr he

lemma finite_rank_difference {r t : V → L} (hfin : {v | r v ≠ t v}.Finite) (a b : V) :
    HasFiniteSupport (fun v => rankBit r (v+a) (v+b)-rankBit t (v+a) (v+b)) := by
  apply ((hfin.preimage (Equiv.addRight a).injective.injOn).union
    (hfin.preimage (Equiv.addRight b).injective.injOn)).subset
  intro v hv
  by_contra hh
  have h := not_or.mp hh
  have ha : r (v+a)=t (v+a) := not_not.mp h.1
  have hb : r (v+b)=t (v+b) := not_not.mp h.2
  exact hv (by simp [rankBit,ha,hb])

lemma finite_top_difference {r t : V → L} (hfin : {v | r v ≠ t v}.Finite) (a b c : V) :
    HasFiniteSupport (fun v => topBit r (v+a) (v+b) (v+c)-topBit t (v+a) (v+b) (v+c)) := by
  apply (((hfin.preimage (Equiv.addRight a).injective.injOn).union
    (hfin.preimage (Equiv.addRight b).injective.injOn)).union
    (hfin.preimage (Equiv.addRight c).injective.injOn)).subset
  intro v hv
  by_contra hh
  have hh := not_or.mp hh
  have ha : r (v+a)=t (v+a) := not_not.mp (not_or.mp hh.1).1
  have hb : r (v+b)=t (v+b) := not_not.mp (not_or.mp hh.1).2
  have hc : r (v+c)=t (v+c) := not_not.mp hh.2
  exact hv (by simp [topBit,rankBit,ha,hb,hc])

lemma meshIndex_difference_decomposition {r t : V → L} (hr : Injective r) (ht : Injective t)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    meshIndex r x y v - meshIndex t x y v =
      discreteDivergence x (fun w => edgeFlag r x w-edgeFlag t x w) v +
      discreteDivergence y (fun w => edgeFlag r y w-edgeFlag t y w) v +
      discreteDivergence (x+y) (fun w => edgeFlag r (x+y) w-edgeFlag t (x+y) w) v +
      discreteDivergence x (fun w => lowerTop₁ r x y w-lowerTop₁ t x y w) v +
      discreteDivergence (x+y) (fun w => lowerTop₂ r x y w-lowerTop₂ t x y w) v +
      discreteDivergence y (fun w => upperTop₁ r x y w-upperTop₁ t x y w) v +
      discreteDivergence (x+y) (fun w => upperTop₂ r x y w-upperTop₂ t x y w) v := by
  rw [meshIndex_eq_divergence hr hx hy hd,meshIndex_eq_divergence ht hx hy hd]
  unfold discreteDivergence
  ring

lemma meshIndex_change_finsum_zero {r t : V → L} (hr : Injective r) (ht : Injective t)
    (hfin : {v | r v ≠ t v}.Finite) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) :
    ∑ᶠ v, (meshIndex r x y v-meshIndex t x y v) = 0 := by
  have hE (s : V) : HasFiniteSupport (fun v => edgeFlag r s v-edgeFlag t s v) := by
    simpa only [edgeFlag,add_zero] using finite_rank_difference hfin s 0
  have hA₁ : HasFiniteSupport (fun v => lowerTop₁ r x y v-lowerTop₁ t x y v) := by
    simpa only [lowerTop₁,add_zero,add_assoc] using finite_top_difference hfin x (x+y) 0
  have hA₂ : HasFiniteSupport (fun v => lowerTop₂ r x y v-lowerTop₂ t x y v) := by
    simpa only [lowerTop₂,add_zero,add_assoc] using finite_top_difference hfin (x+y) 0 x
  have hB₁ : HasFiniteSupport (fun v => upperTop₁ r x y v-upperTop₁ t x y v) := by
    simpa only [upperTop₁,add_zero,add_assoc] using finite_top_difference hfin y (x+y) 0
  have hB₂ : HasFiniteSupport (fun v => upperTop₂ r x y v-upperTop₂ t x y v) := by
    simpa only [upperTop₂,add_zero,add_assoc] using finite_top_difference hfin (x+y) 0 y
  have h₁ := finite_support_discreteDivergence (hE x) x
  have h₂ := finite_support_discreteDivergence (hE y) y
  have h₃ := finite_support_discreteDivergence (hE (x+y)) (x+y)
  have h₄ := finite_support_discreteDivergence hA₁ x
  have h₅ := finite_support_discreteDivergence hA₂ (x+y)
  have h₆ := finite_support_discreteDivergence hB₁ y
  have h₇ := finite_support_discreteDivergence hB₂ (x+y)
  simp_rw [meshIndex_difference_decomposition hr ht hx hy hd]
  have he₇ := finsum_add_distrib (((((h₁.add h₂).add h₃).add h₄).add h₅).add h₆) h₇
  have he₆ := finsum_add_distrib ((((h₁.add h₂).add h₃).add h₄).add h₅) h₆
  have he₅ := finsum_add_distrib (((h₁.add h₂).add h₃).add h₄) h₅
  have he₄ := finsum_add_distrib ((h₁.add h₂).add h₃) h₄
  have he₃ := finsum_add_distrib (h₁.add h₂) h₃
  have he₂ := finsum_add_distrib h₁ h₂
  simp only [Pi.add_apply] at he₇ he₆ he₅ he₄ he₃ he₂
  rw [he₇,he₆,he₅,he₄,he₃,he₂]
  simp only [finsum_discreteDivergence (hE x),finsum_discreteDivergence (hE y),
    finsum_discreteDivergence (hE (x+y)),finsum_discreteDivergence hA₁,
    finsum_discreteDivergence hA₂,finsum_discreteDivergence hB₁,
    finsum_discreteDivergence hB₂,add_zero]

end
end StrictInverseFirstPower.Grid

end

end OAI
