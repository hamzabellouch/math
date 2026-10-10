import Mathlib
import OAI.Analysis.PathSelection.ClockAlgebra
import OAI.Analysis.PathSelection.ExpansionAlgebra

namespace OAI

/-! Local sectors, lower sector data and fields of expansion coefficients. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
namespace DegeneratingTrees

lemma sector_eventually_nhds {P : ℂ → Prop} (h : ∀ᶠ z in sectorInfinity,P z) :
    ∀ᶠ z in sectorInfinity,∀ᶠ w in 𝓝 z,P w := by
  obtain ⟨ω,R,hω,hP⟩ := h
  obtain ⟨η,S,hη,hRS,hdisc⟩ := hω.narrow_discs R
  exact ⟨η,S,hη,fun z hz => Filter.mem_of_superset
    (Metric.closedBall_mem_nhds z zero_lt_one) (fun w hw => hP w (hdisc z hz hw))⟩

lemma sector_eventually_analytic_congr {f g : ℂ → ℂ}
    (hf : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ f z) (he : f =ᶠ[sectorInfinity] g) :
    ∀ᶠ z in sectorInfinity,AnalyticAt ℂ g z := by
  filter_upwards [hf,sector_eventually_nhds he] with z hz hez
  exact hz.congr hez

lemma sector_eventually_deriv_congr {f g : ℂ → ℂ} (he : f =ᶠ[sectorInfinity] g) :
    deriv f =ᶠ[sectorInfinity] deriv g := by
  filter_upwards [sector_eventually_nhds he] with z hz
  have hez : f =ᶠ[𝓝 z] g := hz
  exact hez.deriv_eq

namespace Clock
lemma SectorExpansion.congr {f g : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) (he : f =ᶠ[sectorInfinity] g) : SectorExpansion g E b := by
  apply SectorExpansion.of_expSmall hf.bounded_above hf.finite_above
    (sector_eventually_analytic_congr hf.eventually_analytic he)
  intro B
  obtain ⟨a,ha,hO⟩ := hf.expSmall_remainder B
  exact ⟨a,ha,hO.congr' (he.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)⟩
end Clock
end DegeneratingTrees

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

structure LowerSectorData (K : Set (ℂ → ℂ)) : Prop where
  const_mem : ∀ c : ℂ,(fun _ => c) ∈ K
  add_mem : ∀ {f g},f ∈ K → g ∈ K → (fun z => f z+g z) ∈ K
  neg_mem : ∀ {f},f ∈ K → (fun z => -f z) ∈ K
  mul_mem : ∀ {f g},f ∈ K → g ∈ K → (fun z => f z*g z) ∈ K
  inv_mem : ∀ {f},f ∈ K → (fun z => (f z)⁻¹) ∈ K
  analytic : ∀ {f},f ∈ K → ∀ᶠ z in sectorInfinity,AnalyticAt ℂ f z
  slow : ∀ {f},f ∈ K → SectorSlow f
  zero_or_ne : ∀ {f},f ∈ K → (∀ᶠ z in sectorInfinity,f z=0) ∨
    (∀ᶠ z in sectorInfinity,f z≠0)

namespace LowerSectorData
variable {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
include hK

lemma finset_sum_mem {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ S,f i ∈ K) : (fun z => ∑ i ∈ S,f i z) ∈ K := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using hK.const_mem 0
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using hK.add_mem (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma word_mem {E : Set ℝ} {b : ℝ → ℂ → ℂ} (hb : ∀ β ∈ E,b β ∈ K)
    {w : List ℝ} (hw : w ∈ exponentWords E) : wordCoefficient b w ∈ K := by
  induction w with
  | nil => exact hK.const_mem 1
  | cons β w ih =>
    exact hK.mul_mem (hb β (hw β (by simp)))
      (ih (fun γ hγ => hw γ (List.mem_cons_of_mem _ hγ)))

lemma geometric_mem {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ) (hE : ∀ β ∈ E,β≤ -δ)
    (hEl : ∀ B : ℝ,(E ∩ Ici B).Finite) {b : ℝ → ℂ → ℂ} (hb : ∀ β ∈ E,b β ∈ K)
    (β : ℝ) : geometricCoefficient hδ hE hEl b β ∈ K := by
  apply hK.finset_sum_mem
  intro w hw
  exact hK.word_mem hb ((wordFiber_finite hδ hE hEl β).mem_toFinset.mp hw).1

lemma convolution_mem {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F)
    (hEl : ∀ B : ℝ,(E ∩ Ici B).Finite) (hFl : ∀ B : ℝ,(F ∩ Ici B).Finite)
    {b c : ℝ → ℂ → ℂ} (hb : ∀ β ∈ E,b β ∈ K) (hc : ∀ γ ∈ F,c γ ∈ K)
    (δ : ℝ) : exponentConvolution hE hF hEl hFl b c δ ∈ K := by
  apply hK.finset_sum_mem
  intro p hp
  have hh := (exponentFiber_finite hE hF hEl hFl δ).mem_toFinset.mp hp
  exact hK.mul_mem (hb p.1 hh.1) (hc p.2 hh.2.1)
end LowerSectorData

def ExpansionOver (K : Set (ℂ → ℂ)) (f : ℂ → ℂ) : Prop :=
  ∃ E : Set ℝ,∃ b : ℝ → ℂ → ℂ,SectorExpansion f E b ∧ ∀ β ∈ E,b β ∈ K

namespace ExpansionOver
variable {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
include hK

lemma const (c : ℂ) : ExpansionOver K (fun _ => c) :=
  ⟨{0},fun _ _ => c,SectorExpansion.const c,fun _ _ => hK.const_mem c⟩

omit hK in
lemma congr {f g : ℂ → ℂ} (hf : ExpansionOver K f) (he : f =ᶠ[sectorInfinity] g) :
    ExpansionOver K g := by
  obtain ⟨E,b,hf,hb⟩ := hf
  exact ⟨E,b,hf.congr he,hb⟩

lemma neg {f : ℂ → ℂ} (hf : ExpansionOver K f) : ExpansionOver K (fun z => -f z) := by
  obtain ⟨E,b,hf,hb⟩ := hf
  exact ⟨E,fun β z => -b β z,hf.neg,fun β hβ => hK.neg_mem (hb β hβ)⟩

lemma add {f g : ℂ → ℂ} (hf : ExpansionOver K f) (hg : ExpansionOver K g) :
    ExpansionOver K (fun z => f z+g z) := by
  classical
  obtain ⟨E,b,hf,hb⟩ := hf
  obtain ⟨F,c,hg,hc⟩ := hg
  refine ⟨E ∪ F,fun β z => (if β∈E then b β z else 0)+(if β∈F then c β z else 0),hf.add hg,?_⟩
  intro β hβ
  apply hK.add_mem
  · by_cases he : β∈E
    · simpa only [ite_eq_left he] using hb β he
    · simpa only [ite_eq_right he] using hK.const_mem 0
  · by_cases he : β∈F
    · simpa only [ite_eq_left he] using hc β he
    · simpa only [ite_eq_right he] using hK.const_mem 0

lemma mul {f g : ℂ → ℂ} (hf : ExpansionOver K f) (hg : ExpansionOver K g) :
    ExpansionOver K (fun z => f z*g z) := by
  obtain ⟨E,b,hf,hb⟩ := hf
  obtain ⟨F,c,hg,hc⟩ := hg
  exact ⟨exponentSum E F,_,hf.mul hg (fun β hβ => hK.slow (hb β hβ))
    (fun γ hγ => hK.slow (hc γ hγ)),
    fun δ _ => hK.convolution_mem hf.bounded_above hg.bounded_above hf.finite_above hg.finite_above hb hc δ⟩

lemma inverse_of_leading {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) (hb : ∀ β ∈ E,b β ∈ K)
    {β : ℝ} (hβ : β∈E) (hmax : ∀ γ∈E,γ≤β)
    (hbne : ∀ᶠ z in sectorInfinity,b β z≠0) : ExpansionOver K (fun z => (f z)⁻¹) := by
  let q : ℂ → ℂ := fun z => (b β z)⁻¹
  have hq := hK.inv_mem (hb β hβ)
  let r : ℂ → ℂ := fun z => -(Complex.exp (((-β:ℝ):ℂ)*z)*
    (f z-Complex.exp ((β:ℂ)*z)*b β z))*q z
  let D := translatedSupport (-β) (E \ {β})
  let c : ℝ → ℂ → ℂ := fun γ z => -b (γ-(-β)) z*q z
  have hr : SectorExpansion r D c :=
    (((hf.erase hβ (hK.analytic (hb β hβ)) (hK.slow (hb β hβ))).exp_shift (-β)).neg).mul_lower
      (hK.analytic hq) (hK.slow hq)
  have hc : ∀ γ∈D,c γ ∈ K := by
    rintro γ ⟨a,ha,rfl⟩
    dsimp [c]
    simpa only [show -β+a-(-β)=a by ring] using hK.mul_mem (hK.neg_mem (hb a ha.1)) hq
  have hn : ∀ γ∈D,γ<0 := by
    rintro γ ⟨a,ha,rfl⟩
    change -β+a<0
    have hle := hmax a ha.1
    have hne : a≠β := ha.2
    have hlt : a<β := lt_of_le_of_ne hle hne
    linarith
  obtain ⟨δ,hδ,hd⟩ := strict_negative_support_gap hr.finite_above hn
  have hri := hr.geometric_inverse hδ hd (fun γ hγ => hK.slow (hc γ hγ))
  have hfinal := (hri.mul_lower (hK.analytic hq) (hK.slow hq)).exp_shift (-β)
  have hmem : ∀ γ ∈ translatedSupport (-β) (wordSupport D),
      (fun z => geometricCoefficient hδ hd hr.finite_above c (γ-(-β)) z*q z) ∈ K := by
    intro γ _
    exact hK.mul_mem (hK.geometric_mem hδ hd hr.finite_above hc (γ-(-β))) hq
  apply (show ExpansionOver K (fun z => Complex.exp (((-β:ℝ):ℂ)*z)*((1-r z)⁻¹*q z)) from
    ⟨_,_,hfinal,hmem⟩).congr
  filter_upwards [hbne] with z hz
  have hexp : Complex.exp (((-β:ℝ):ℂ)*z)=(Complex.exp ((β:ℂ)*z))⁻¹ := by
    rw [Complex.ofReal_neg,neg_mul,Complex.exp_neg]
  have he := Complex.exp_ne_zero ((β:ℂ)*z)
  dsimp [r,q]
  rw [hexp]
  have hh : 1- -((Complex.exp ((β:ℂ)*z))⁻¹*(f z-Complex.exp ((β:ℂ)*z)*b β z))*(b β z)⁻¹ =
      (Complex.exp ((β:ℂ)*z))⁻¹*f z*(b β z)⁻¹ := by
    field_simp [he,hz]
    ring
  rw [hh,mul_inv_rev,mul_inv_rev,inv_inv,inv_inv]
  field_simp [he,hz]

 

theorem inv {f : ℂ → ℂ} (hf : ExpansionOver K f) : ExpansionOver K (fun z => (f z)⁻¹) := by
  classical
  obtain ⟨E,b,hf,hb⟩ := hf
  have ht := hf.trim_zero (fun β hβ => hK.analytic (hb β hβ))
  rcases (nonzeroRaySupport E b).eq_empty_or_nonempty with he | he
  · rw [he] at ht
    have hz := ht.empty
    obtain ⟨ω,R,hω,ha⟩ := hf.eventually_analytic
    have hzero := sector_zero_of_ray_zero hω ha hz
    apply (const hK 0).congr
    exact hzero.mono (fun _ hz => by simp [hz])
  · obtain ⟨β,hβ,hmax⟩ := exists_greatest_of_finite_above ht.finite_above he
    have hbne : ∀ᶠ z in sectorInfinity,b β z≠0 := by
      rcases hK.zero_or_ne (hb β hβ.1) with hz | hn
      · exact False.elim (hβ.2 (tendsto_real_sectorInfinity.eventually hz))
      · exact hn
    exact inverse_of_leading hK ht (fun γ hγ => hb γ hγ.1) hβ hmax hbne

end ExpansionOver
end DegeneratingTrees.Clock
end

end OAI
