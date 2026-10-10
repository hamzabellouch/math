import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.FiniteCoarea
import OAI.GroupTheory.SimpleAmenable.Amenability.UniformShapeMatchings

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SuccessfulLawCovariance
open Classical MeasureTheory Set

theorem successful_law_covariance {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T)
    (t : X → X) (ht : Measurable t) (S : Set X) (hS : MeasurableSet S)
    {ε : ℝ} (hc : ObservableClose μ (μ.map t) ε)
    (f g : X → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) (hg : ∀x,g x∈Icc (0:ℝ) 1)
    (he : ∀x,x∈S → t x∈S → f (t x)=g x) :
    |(∫x,f x ∂μ)-(∫x,g x ∂μ)| ≤ 2*μ.real Sᶜ+2*ε := by
  let ν := μ.map t
  let : IsProbabilityMeasure ν := inferInstance
  let U := T.image t
  have hU : ∀ᵐx ∂ν,x∈U := by
    apply (ae_map_iff ht.aemeasurable U.measurableSet).mpr
    filter_upwards [hT] with x hx
    exact Finset.mem_image_of_mem t hx
  have hic := hc.finiteSupport T U hT hU f hf
  have hmap : (∫x,f x ∂ν)=∫x,f (t x) ∂μ :=
    integral_map ht.aemeasurable (integrable_of_finite_support ν U hU f).aestronglyMeasurable
  rw [hmap] at hic
  let E := Sᶜ ∪ t ⁻¹' Sᶜ
  have hE : MeasurableSet E := hS.compl.union (ht hS.compl)
  have hd := integral_difference_le_failure μ T hT (fun x => f (t x)) g
    (fun x => hf (t x)) hg E hE (by
      intro x hx
      have hx' : x∈S ∧ t x∈S := by simpa [E] using hx
      exact he x hx'.1 hx'.2)
  have hb := hc.event hS.compl
  have hreal : ν.real Sᶜ=μ.real (t ⁻¹' Sᶜ) := map_measureReal_apply ht hS.compl
  have hbound : μ.real E ≤ 2*μ.real Sᶜ+ε := by
    have hu : μ.real E ≤ μ.real Sᶜ+μ.real (t ⁻¹' Sᶜ) :=
      measureReal_union_le (μ:=μ) Sᶜ (t ⁻¹' Sᶜ)
    have ht' := (abs_le.mp hb).1
    change -ε ≤ μ.real Sᶜ-ν.real Sᶜ at ht'
    rw [hreal] at ht'
    linarith
  have htri := abs_sub_le (∫x,f x ∂μ) (∫x,f (t x) ∂μ) (∫x,g x ∂μ)
  linarith

end SuccessfulLawCovariance

section FiniteMixtureWeights
open Classical

noncomputable def finiteUniformWeight {G : Type*} (U : Finset G) (x : G) : ℝ :=
  if x∈U then (1:ℝ)/U.card else 0

theorem finiteUniformWeight_nonneg {G : Type*} (U : Finset G) (x : G) :
    0 ≤ finiteUniformWeight U x := by unfold finiteUniformWeight; split_ifs <;> positivity

theorem finiteUniformWeight_sum {G : Type*} (S U : Finset G) (hUS : U ⊆ S) (f : G → ℝ) :
    (∑x∈S,finiteUniformWeight U x*f x)=(∑x∈U,f x)/U.card := by
  calc
    _ = ∑x∈U,finiteUniformWeight U x*f x := by
      symm
      apply Finset.sum_subset hUS
      intro x hx hxU
      simp [finiteUniformWeight,hxU]
    _ = ∑x∈U,f x/(U.card:ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [finiteUniformWeight,hx,div_eq_mul_inv,mul_comm]
    _ = _ := by rw [Finset.sum_div]

theorem finite_uniform_mixture {X G : Type*} (T : Finset X) (w : X → ℝ) (U : X → Finset G)
    (hw : ∀x∈T,0 ≤ w x) (hmass : (∑x∈T,w x)=1) (hU : ∀x∈T,(U x).Nonempty) :
    ∃ (S : Finset G) (p : G → ℝ), (∀g,0 ≤ p g) ∧ (∀g∉S,p g=0) ∧ (∑g∈S,p g)=1 ∧
      ∀f : G → ℝ,(∑g∈S,p g*f g)=∑x∈T,w x*((∑g∈U x,f g)/(U x).card) := by
  let S := T.biUnion U
  let p := fun g => ∑x∈T,w x*finiteUniformWeight (U x) g
  have hcontains (x : X) (hx : x∈T) : U x ⊆ S := by
    intro g hg
    exact Finset.mem_biUnion.mpr ⟨x,hx,hg⟩
  have htest (f : G → ℝ) : (∑g∈S,p g*f g)=∑x∈T,w x*((∑g∈U x,f g)/(U x).card) := by
    simp only [p,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [mul_assoc]
    rw [←Finset.mul_sum,finiteUniformWeight_sum S (U x) (hcontains x hx)]
  refine ⟨S,p,fun g => Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx)
    (finiteUniformWeight_nonneg (U x) g)),?_,?_,htest⟩
  · intro g hg
    apply Finset.sum_eq_zero
    intro x hx
    have hgU : g∉U x := fun h => hg (hcontains x hx h)
    simp [finiteUniformWeight,hgU]
  · have hh := htest (fun _ => 1)
    simp only [mul_one,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    rw [hh]
    calc
      (∑x∈T,w x*(((U x).card:ℝ)/(U x).card)) = ∑x∈T,w x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hcard : ((U x).card:ℝ)≠0 := by exact_mod_cast (hU x hx).card_pos.ne'
        field_simp
      _ = 1 := hmass

end FiniteMixtureWeights

section FiniteTestReiter
open Classical Set

def FiniteTestReiter (G : Type*) [Group G] : Prop :=
  ∀K : Finset G,∀δ : ℝ,0 < δ → ∃(S : Finset G) (p : G → ℝ),
    (∀x,0 ≤ p x) ∧ (∀x∉S,p x=0) ∧ (∑x∈S,p x)=1 ∧
    ∀k∈K,∀f : G → ℝ,(∀x,f x∈Icc (0:ℝ) 1) →
      |(∑x∈S,p x*f x)-(∑x∈S,p x*f (k*x))| ≤ δ

theorem sum_support_window {G : Type*} (S W : Finset G) (p f : G → ℝ)
    (hS : S ⊆ W) (hp : ∀x∉S,p x=0) :
    (∑x∈W,p x*f x)=∑x∈S,p x*f x := by
  symm
  apply Finset.sum_subset hS
  intro x hx hn
  simp [hp x hn]

theorem sum_translate_window {G : Type*} [Group G] (S W : Finset G) (p f : G → ℝ) (k : G)
    (hS : S.image (fun x => k*x) ⊆ W) (hp : ∀x∉S,p x=0) :
    (∑x∈W,p (k⁻¹*x)*f x)=∑x∈S,p x*f (k*x) := by
  calc
    _ = ∑x∈S.image (fun y => k*y),p (k⁻¹*x)*f x := by
      symm
      apply Finset.sum_subset hS
      intro x hx hn
      have hx' : k⁻¹*x∉S := by
        intro hh
        exact hn (Finset.mem_image.mpr ⟨k⁻¹*x,hh,by group⟩)
      simp [hp _ hx']
    _ = _ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro x hx
        simp
      · intro x hx y hy he
        exact mul_left_cancel he

theorem finite_test_l1_bound {G : Type*} [Group G] (S W : Finset G) (p : G → ℝ) (k : G)
    (hS : S ⊆ W) (hkS : S.image (fun x => k*x) ⊆ W) (hp : ∀x∉S,p x=0)
    (δ : ℝ) (htest : ∀f : G → ℝ,(∀x,f x∈Icc (0:ℝ) 1) →
      |(∑x∈S,p x*f x)-(∑x∈S,p x*f (k*x))| ≤ δ) :
    (∑x∈W,|p (k⁻¹*x)-p x|) ≤ 2*δ := by
  let d := fun x => p (k⁻¹*x)-p x
  have hd (f : G → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) : |∑x∈W,d x*f x| ≤ δ := by
    simp only [d,sub_mul,Finset.sum_sub_distrib]
    rw [sum_translate_window S W p f k hkS hp,sum_support_window S W p f hS hp,abs_sub_comm]
    exact htest f hf
  let fpos := fun x => if 0 ≤ d x then (1:ℝ) else 0
  let fneg := fun x => if 0 ≤ d x then (0:ℝ) else 1
  have hfpos : ∀x,fpos x∈Icc (0:ℝ) 1 := by intro x; dsimp [fpos]; split_ifs <;> norm_num
  have hfneg : ∀x,fneg x∈Icc (0:ℝ) 1 := by intro x; dsimp [fneg]; split_ifs <;> norm_num
  have he : (∑x∈W,|d x|)=(∑x∈W,d x*fpos x)-(∑x∈W,d x*fneg x) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : 0 ≤ d x
    · simp [fpos,fneg,h,abs_of_nonneg h]
    · simp [fpos,fneg,h,abs_of_neg (lt_of_not_ge h)]
  change (∑x∈W,|d x|) ≤ _
  rw [he]
  linarith [(abs_le.mp (hd fpos hfpos)).2,(abs_le.mp (hd fneg hfneg)).1]

theorem finiteSupportReiter_of_finiteTestReiter {G : Type*} [Group G]
    (h : FiniteTestReiter G) : FiniteSupportReiter G := by
  intro K ε hε
  have hc : (0:ℝ)<2*(K.card:ℝ)+1 := by positivity
  let δ := ε/(2*(K.card:ℝ)+1)
  obtain ⟨S,p,hp,hs,hm,ht⟩ := h K δ (div_pos hε hc)
  refine ⟨S,p,hp,hs,hm,?_⟩
  have hbound : weightedVariation K S p ≤ (K.card:ℝ)*(2*δ) := by
    calc
      _ ≤ ∑k∈K,2*δ := by
        apply Finset.sum_le_sum
        intro k hk
        apply finite_test_l1_bound S (translationWindow K S) p k
          (Finset.subset_union_left) _ hs δ (ht k hk)
        intro x hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k,hk,hx⟩)
      _ = _ := by simp
  apply lt_of_le_of_lt hbound
  dsimp [δ]
  rw [←mul_assoc,←mul_div_assoc]
  apply (div_lt_iff₀ hc).mpr
  nlinarith

end FiniteTestReiter

end SimpleAmenable
end
end

end OAI
