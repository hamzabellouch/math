import Mathlib
import OAI.Analysis.PathSelection.ClockExpansions

namespace OAI

/-! Algebraic operations, shifts and leading terms of clock expansions. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
attribute [local instance] Classical.propDecidable
namespace DegeneratingTrees.Clock

lemma SectorExpansion.const (c : ℂ) : SectorExpansion (fun _ => c) {0} (fun _ _ => c) := by
  classical
  have hfin (B : ℝ) : (({0}:Set ℝ) ∩ Ici B).Finite := (finite_singleton 0).inter_of_left _
  refine ⟨(finite_singleton 0).bddAbove,hfin,?_⟩
  intro B
  obtain ⟨ω,R,hω,hre⟩ := SectorEventually.realpart_pos
  by_cases hB : B ≤ 0
  · have he : (hfin B).toFinset = {0} := by ext x; simp [hB]
    refine ⟨ω,R,1,0,hω,by norm_num,le_rfl,fun _ _ => analyticAt_const,?_⟩
    intro z hz
    rw [he]
    simp
  · have hB : 0 < B := lt_of_not_ge hB
    have he : (hfin B).toFinset = ∅ := by ext x; simp; intro h; subst x; linarith
    refine ⟨ω,R,B/2,‖c‖,hω,by positivity,norm_nonneg _,fun _ _ => analyticAt_const,?_⟩
    intro z hz
    simp only [he,Finset.sum_empty,sub_zero]
    calc
      ‖c‖ = ‖c‖*1 := (mul_one _).symm
      _ ≤ ‖c‖*Real.exp ((B-B/2)*z.re) := mul_le_mul_of_nonneg_left
        (Real.one_le_exp_iff.mpr (by nlinarith [hre z hz])) (norm_nonneg _)

lemma SectorExpansion.neg {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b) : SectorExpansion (fun z => -f z) E (fun β z => -b β z) := by
  classical
  refine ⟨h.bounded_above,h.finite_above,?_⟩
  intro B
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hb⟩ := h.remainders B
  refine ⟨ω,R,ε,C,hω,hε,hC,fun z hz => (hf z hz).neg,?_⟩
  intro z hz
  simpa only [mul_neg,Finset.sum_neg_distrib,neg_sub_neg,norm_sub_rev] using hb z hz

private lemma sum_indicator {E U : Set ℝ} (B : ℝ)
    (hE : (E ∩ Ici B).Finite) (hU : (U ∩ Ici B).Finite) (hsub : E ⊆ U)
    (b : ℝ → ℂ → ℂ) (z : ℂ) :
    (∑ β ∈ hU.toFinset,Complex.exp ((β:ℂ)*z)*(if β ∈ E then b β z else 0)) =
      ∑ β ∈ hE.toFinset,Complex.exp ((β:ℂ)*z)*b β z := by
  classical
  have hs : hE.toFinset ⊆ hU.toFinset := by
    intro β hβ
    exact hU.mem_toFinset.mpr ⟨hsub (hE.mem_toFinset.mp hβ).1,(hE.mem_toFinset.mp hβ).2⟩
  calc
    _ = ∑ β ∈ hE.toFinset,Complex.exp ((β:ℂ)*z)*(if β ∈ E then b β z else 0) := by
      symm
      apply Finset.sum_subset hs
      intro β hβ hn
      have hnot : β ∉ E := by
        intro he
        exact hn (hE.mem_toFinset.mpr ⟨he,(hU.mem_toFinset.mp hβ).2⟩)
      simp only [ite_eq_right hnot,mul_zero]
    _ = _ := Finset.sum_congr rfl (fun β hβ => by rw [ite_eq_left (hE.mem_toFinset.mp hβ).1])

lemma SectorExpansion.add {f g : ℂ → ℂ} {E F : Set ℝ} {b c : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) (hg : SectorExpansion g F c) :
    SectorExpansion (fun z => f z+g z) (E ∪ F)
      (fun β z => (if β ∈ E then b β z else 0)+(if β ∈ F then c β z else 0)) := by
  classical
  have hfin (B : ℝ) : ((E ∪ F) ∩ Ici B).Finite := by
    have h := (hf.finite_above B).union (hg.finite_above B)
    exact h.subset (by intro x hx; rcases hx.1 with h | h; exact Or.inl ⟨h,hx.2⟩; exact Or.inr ⟨h,hx.2⟩)
  refine ⟨hf.bounded_above.union hg.bounded_above,hfin,?_⟩
  intro B
  obtain ⟨ω,R,ε,C,hω,hε,hC,hfa,hfb⟩ := hf.remainders B
  obtain ⟨η,S,δ,D,hη,hδ,hD,hga,hgb⟩ := hg.remainders B
  have h1 : SectorEventually (fun z => z ∈ lossSector ω R) := ⟨ω,R,hω,fun _ h => h⟩
  have h2 : SectorEventually (fun z => z ∈ lossSector η S) := ⟨η,S,hη,fun _ h => h⟩
  obtain ⟨ν,T,hν,hboth⟩ := h1.and (h2.and SectorEventually.realpart_pos)
  refine ⟨ν,T,min ε δ,C+D,hν,lt_min hε hδ,add_nonneg hC hD,?_,?_⟩
  · intro z hz
    exact (hfa z (hboth z hz).1).add (hga z (hboth z hz).2.1)
  · intro z hz
    have hsum : (∑ β ∈ (hfin B).toFinset, Complex.exp ((β:ℂ)*z)*
        ((if β ∈ E then b β z else 0)+(if β ∈ F then c β z else 0))) =
        (∑ β ∈ (hf.finite_above B).toFinset,Complex.exp ((β:ℂ)*z)*b β z)+
        (∑ β ∈ (hg.finite_above B).toFinset,Complex.exp ((β:ℂ)*z)*c β z) := by
      simp only [mul_add,Finset.sum_add_distrib]
      rw [sum_indicator B (hf.finite_above B) (hfin B) subset_union_left,
        sum_indicator B (hg.finite_above B) (hfin B) subset_union_right]
    rw [hsum]
    have he : B-ε ≤ B-min ε δ := by linarith [min_le_left ε δ]
    have hd : B-δ ≤ B-min ε δ := by linarith [min_le_right ε δ]
    have he' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right he (hboth z hz).2.2.le)
    have hd' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (hboth z hz).2.2.le)
    have hb1 := (hfb z (hboth z hz).1).trans (mul_le_mul_of_nonneg_left he' hC)
    have hb2 := (hgb z (hboth z hz).2.1).trans (mul_le_mul_of_nonneg_left hd' hD)
    calc
      ‖f z+g z-((∑ β ∈ (hf.finite_above B).toFinset,Complex.exp ((β:ℂ)*z)*b β z)+
          (∑ β ∈ (hg.finite_above B).toFinset,Complex.exp ((β:ℂ)*z)*c β z))‖ =
          ‖(f z-(∑ β ∈ (hf.finite_above B).toFinset,Complex.exp ((β:ℂ)*z)*b β z))+
          (g z-(∑ β ∈ (hg.finite_above B).toFinset,Complex.exp ((β:ℂ)*z)*c β z))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (by nlinarith)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma ExpSmall.mul_slow {B : ℝ} {f g : ℂ → ℂ} (hf : ExpSmall B f) (hg : SectorSlow g) :
    ExpSmall B (fun z => f z*g z) := by
  obtain ⟨a,ha,hf⟩ := hf
  exact ⟨a+(B-a)/2,by linarith,hf.mul (hg ((B-a)/2) (by linarith))⟩

lemma SectorExpansion.mul_lower {f g : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) (hg : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ g z)
    (hgs : SectorSlow g) : SectorExpansion (fun z => f z*g z) E (fun β z => b β z*g z) := by
  apply SectorExpansion.of_expSmall hf.bounded_above hf.finite_above
  · filter_upwards [hf.eventually_analytic,hg] with z hzf hzg
    exact hzf.mul hzg
  · intro B
    convert (hf.expSmall_remainder B).mul_slow hgs using 1
    funext z
    rw [sub_mul,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro β hβ
    ring

def translatedSupport (a : ℝ) (E : Set ℝ) : Set ℝ := (fun β => a+β) '' E

lemma translatedSupport_bddAbove (a : ℝ) {E : Set ℝ} (hE : BddAbove E) :
    BddAbove (translatedSupport a E) := by
  obtain ⟨A,hA⟩ := hE
  refine ⟨a+A,?_⟩
  rintro _ ⟨β,hβ,rfl⟩
  change a+β ≤ a+A
  linarith [hA hβ]

lemma translatedSupport_finite (a : ℝ) {E : Set ℝ}
    (hE : ∀ B : ℝ,(E ∩ Ici B).Finite) (B : ℝ) :
    (translatedSupport a E ∩ Ici B).Finite := by
  apply ((hE (B-a)).image (fun β => a+β)).subset
  rintro _ ⟨⟨β,hβ,rfl⟩,hB⟩
  exact ⟨β,⟨hβ,by change B-a≤β; change B≤a+β at hB; linarith⟩,rfl⟩

lemma translated_truncation (a : ℝ) {E : Set ℝ}
    (hE : ∀ B : ℝ,(E ∩ Ici B).Finite) (b : ℝ → ℂ → ℂ) (B : ℝ) (z : ℂ) :
    (∑ β ∈ (translatedSupport_finite a hE B).toFinset,Complex.exp ((β:ℂ)*z)*b (β-a) z) =
      Complex.exp ((a:ℂ)*z)*(∑ β ∈ (hE (B-a)).toFinset,Complex.exp ((β:ℂ)*z)*b β z) := by
  classical
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun β _ => a+β)
  · intro β hβ
    have hh := (hE (B-a)).mem_toFinset.mp hβ
    refine (translatedSupport_finite a hE B).mem_toFinset.mpr ⟨⟨β,hh.1,rfl⟩,?_⟩
    change B≤a+β
    have : B-a≤β := hh.2
    linarith
  · intro β hβ γ hγ he
    exact add_left_cancel he
  · intro γ hγ
    obtain ⟨⟨β,hβ,rfl⟩,hB⟩ := (translatedSupport_finite a hE B).mem_toFinset.mp hγ
    refine ⟨β,(hE (B-a)).mem_toFinset.mpr ⟨hβ,?_⟩,rfl⟩
    change B-a≤β
    change B≤a+β at hB
    linarith
  · intro β hβ
    simp only [add_sub_cancel_left,Complex.ofReal_add,add_mul,Complex.exp_add]
    ring

lemma SectorExpansion.exp_shift {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) (a : ℝ) :
    SectorExpansion (fun z => Complex.exp ((a:ℂ)*z)*f z) (translatedSupport a E)
      (fun β => b (β-a)) := by
  apply SectorExpansion.of_expSmall (translatedSupport_bddAbove a hf.bounded_above)
    (translatedSupport_finite a hf.finite_above)
  · filter_upwards [hf.eventually_analytic] with z hz
    exact ((analyticAt_const.mul analyticAt_id).cexp).mul hz
  · intro B
    have hh := (hf.expSmall_remainder (B-a)).mul (ExpBound.cexp a)
    simp only [sub_add_cancel] at hh
    convert hh using 1
    funext z
    rw [translated_truncation a hf.finite_above b B z]
    ring

lemma SectorExpansion.single (a : ℝ) {b : ℂ → ℂ}
    (hb : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ b z) (hs : SectorSlow b) :
    SectorExpansion (fun z => Complex.exp ((a:ℂ)*z)*b z) {a} (fun _ => b) := by
  classical
  apply SectorExpansion.of_expSmall bddAbove_singleton (fun _ => (finite_singleton a).inter_of_left _)
  · filter_upwards [hb] with z hz
    exact ((analyticAt_const.mul analyticAt_id).cexp).mul hz
  · intro B
    by_cases hB : B≤a
    · have he : ((finite_singleton a).inter_of_left (Ici B)).toFinset={a} := by
        ext β
        simp only [Set.Finite.mem_toFinset,mem_inter_iff,mem_singleton_iff,mem_Ici,Finset.mem_singleton]
        exact ⟨And.left,fun h => ⟨h,h ▸ hB⟩⟩
      simp only [he,Finset.sum_singleton,sub_self]
      exact ExpSmall.zero B
    · have he : ((finite_singleton a).inter_of_left (Ici B)).toFinset=∅ := by
        ext β
        simp only [Set.Finite.mem_toFinset,mem_inter_iff,mem_singleton_iff,mem_Ici,Finset.notMem_empty,iff_false]
        rintro ⟨rfl,hh⟩
        exact hB hh
      simpa only [he,Finset.sum_empty,sub_zero] using hs.expSmall (lt_of_not_ge hB)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma SectorExpansion.erase {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) {β : ℝ} (hβ : β ∈ E)
    (hba : ∀ᶠ z in sectorInfinity, AnalyticAt ℂ (b β) z) (hbs : SectorSlow (b β)) :
    SectorExpansion (fun z => f z-Complex.exp ((β:ℂ)*z)*b β z) (E \ {β}) b := by
  classical
  have hfin (B : ℝ) : ((E \ {β}) ∩ Ici B).Finite :=
    (hf.finite_above B).subset (fun _ hx => ⟨hx.1.1,hx.2⟩)
  apply SectorExpansion.of_expSmall (hf.bounded_above.mono (sdiff_subset)) hfin
  · filter_upwards [hf.eventually_analytic,hba] with z hzf hzb
    exact hzf.sub (((analyticAt_const.mul analyticAt_id).cexp).mul hzb)
  · intro B
    have hs : (hfin B).toFinset = (hf.finite_above B).toFinset.erase β := by
      ext γ
      simp only [Set.Finite.mem_toFinset,Finset.mem_erase,mem_inter_iff,Set.mem_sdiff,
        mem_singleton_iff]
      tauto
    rw [hs]
    by_cases hB : B≤β
    · have hm : β ∈ (hf.finite_above B).toFinset :=
        (hf.finite_above B).mem_toFinset.mpr ⟨hβ,hB⟩
      convert hf.expSmall_remainder B using 1
      funext z
      have he := Finset.sum_erase_add (s := (hf.finite_above B).toFinset)
        (fun γ => Complex.exp ((γ:ℂ)*z)*b γ z) hm
      rw [←he]
      ring
    · have hm : β ∉ (hf.finite_above B).toFinset := by
        intro hh
        exact hB ((hf.finite_above B).mem_toFinset.mp hh).2
      rw [Finset.erase_eq_of_notMem hm]
      convert (hf.expSmall_remainder B).sub (hbs.expSmall (lt_of_not_ge hB)) using 1
      funext z
      ring

lemma strict_negative_support_gap {E : Set ℝ}
    (hEl : ∀ B : ℝ,(E ∩ Ici B).Finite) (hE : ∀ β ∈ E,β<0) :
    ∃ δ : ℝ,0<δ ∧ ∀ β ∈ E,β≤ -δ := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1,zero_lt_one,by simp⟩
  · obtain ⟨β,hβ,hmax⟩ := exists_greatest_of_finite_above hEl hne
    exact ⟨-β,neg_pos.mpr (hE β hβ),by simpa only [neg_neg] using hmax⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
open scoped BigOperators
namespace DegeneratingTrees.Clock

def nonzeroRaySupport (E : Set ℝ) (b : ℝ → ℂ → ℂ) : Set ℝ :=
  {β | β ∈ E ∧ ¬ (∀ᶠ x : ℝ in atTop, b β (x:ℂ)=0)}

lemma SectorExpansion.trim_zero {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b)
    (ha : ∀ β ∈ E, SectorEventually (fun z => AnalyticAt ℂ (b β) z)) :
    SectorExpansion f (nonzeroRaySupport E b) b := by
  classical
  have hsub : nonzeroRaySupport E b ⊆ E := fun _ hx => hx.1
  have hfin (B : ℝ) : (nonzeroRaySupport E b ∩ Ici B).Finite :=
    (h.finite_above B).subset (fun _ hx => ⟨hx.1.1,hx.2⟩)
  refine ⟨h.bounded_above.mono hsub,hfin,?_⟩
  intro B
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hrem⟩ := h.remainders B
  have hbase : SectorEventually (fun _ => True) := ⟨ω,R,hω,fun _ _ => True.intro⟩
  have hz : SectorEventually (fun z => ∀ β ∈ (h.finite_above B).toFinset,
      β ∉ nonzeroRaySupport E b → b β z=0) := by
    apply SectorEventually.finset_forall _ hbase
    intro β hβ
    have hβE := ((h.finite_above B).mem_toFinset.mp hβ).1
    by_cases hzero : ∀ᶠ x : ℝ in atTop, b β (x:ℂ)=0
    · obtain ⟨η,S,hη,hba⟩ := ha β hβE
      exact (sector_zero_of_ray_zero hη hba hzero).mono (by tauto)
    · exact hbase.mono (fun z _ hn => (hn ⟨hβE,hzero⟩).elim)
  obtain ⟨η,S,hη,hboth⟩ := hz.and (show SectorEventually (fun z => z ∈ lossSector ω R)
    from ⟨ω,R,hω,fun _ hz => hz⟩)
  refine ⟨η,S,ε,C,hη,hε,hC,fun z hz => hf z (hboth z hz).2,?_⟩
  intro z hz
  have hs : (hfin B).toFinset ⊆ (h.finite_above B).toFinset := by
    intro β hβ
    have hh := (hfin B).mem_toFinset.mp hβ
    exact (h.finite_above B).mem_toFinset.mpr ⟨hh.1.1,hh.2⟩
  have he : (∑ β ∈ (hfin B).toFinset, Complex.exp ((β:ℂ)*z)*b β z) =
      ∑ β ∈ (h.finite_above B).toFinset, Complex.exp ((β:ℂ)*z)*b β z := by
    apply Finset.sum_subset hs
    intro β hβ hn
    have hn' : β ∉ nonzeroRaySupport E b := by
      intro hh
      apply hn
      exact (hfin B).mem_toFinset.mpr ⟨hh,((h.finite_above B).mem_toFinset.mp hβ).2⟩
    rw [(hboth z hz).1 β hβ hn',mul_zero]
  rw [he]
  exact hrem z (hboth z hz).2

 

theorem SectorExpansion.leading_or_zero_general {f : ℂ → ℂ} {E : Set ℝ}
    {b : ℝ → ℂ → ℂ} (h : SectorExpansion f E b)
    (ha : ∀ β ∈ E, SectorEventually (fun z => AnalyticAt ℂ (b β) z))
    (hc : ∀ β ∈ E, (∀ᶠ x : ℝ in atTop, b β (x:ℂ)=0) ∨
      ((∀ᶠ x : ℝ in atTop, b β (x:ℂ) ≠ 0) ∧
      Subexponential atTop id (fun x : ℝ => (b β (x:ℂ))⁻¹))) :
    (fun x : ℝ => f (x:ℂ)) =ᶠ[atTop] 0 ∨
    ∃ β ∈ E, (∀ᶠ x : ℝ in atTop, b β (x:ℂ) ≠ 0) ∧
      Tendsto (fun x : ℝ => (Real.exp (-β*x):ℂ)*(b β (x:ℂ))⁻¹*f (x:ℂ))
        atTop (𝓝 1) := by
  have h' := h.trim_zero ha
  have hb : ∀ β ∈ nonzeroRaySupport E b, (∀ᶠ x : ℝ in atTop, b β (x:ℂ) ≠ 0) ∧
      Subexponential atTop id (fun x : ℝ => (b β (x:ℂ))⁻¹) := by
    intro β hβ
    exact (hc β hβ.1).resolve_left hβ.2
  rcases h'.leading_or_zero hb with hz | ⟨β,hβ,hgreat,ht⟩
  · exact Or.inl hz
  · exact Or.inr ⟨β,hβ.1,(hb β hβ).1,ht⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma SectorExpansion.leading_error {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) {β : ℝ} (hβ : β ∈ E) (hgreat : ∀ γ ∈ E,γ≤β) :
    ExpSmall β (fun z => f z-Complex.exp ((β:ℂ)*z)*b β z) := by
  classical
  have hs : (hf.finite_above β).toFinset={β} := by
    ext γ
    simp only [Set.Finite.mem_toFinset,mem_inter_iff,mem_Ici,Finset.mem_singleton]
    exact ⟨fun h => le_antisymm (hgreat γ h.1) h.2,fun h => by subst γ; exact ⟨hβ,le_rfl⟩⟩
  simpa only [hs,Finset.sum_singleton] using hf.expSmall_remainder β

lemma ExpSmall.tendsto_zero {f : ℂ → ℂ} (hf : ExpSmall 0 f) :
    Tendsto f sectorInfinity (𝓝 0) := by
  obtain ⟨a,ha,hf⟩ := hf
  exact hf.trans_tendsto (Real.tendsto_exp_atBot.comp
    (tendsto_re_sectorInfinity.const_mul_atTop_of_neg ha))

lemma SectorExpansion.uniform_leading {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) {β : ℝ} (hβ : β ∈ E) (hgreat : ∀ γ ∈ E,γ≤β)
    (hb : ∀ᶠ z in sectorInfinity,b β z≠0) (hs : SectorSlow (fun z => (b β z)⁻¹)) :
    ExpSmall 0 (fun z => Complex.exp (((-β:ℝ):ℂ) * z)*(b β z)⁻¹*f z-1) := by
  have he := ((hf.leading_error hβ hgreat).mul (ExpBound.cexp (-β))).mul_slow hs
  simp only [add_neg_cancel] at he
  obtain ⟨exponent,hexponent,hbound⟩ := he
  refine ⟨exponent,hexponent,hbound.congr' ?_ (EventuallyEq.refl _ _)⟩
  filter_upwards [hb] with z hz
  have hexp : Complex.exp (((-β:ℝ):ℂ) * z)*Complex.exp ((β:ℂ)*z)=1 := by
    rw [←Complex.exp_add]
    simp
  have hn := Complex.exp_ne_zero ((β:ℂ)*z)
  have hei : Complex.exp (((-β:ℝ):ℂ) * z)=(Complex.exp ((β:ℂ)*z))⁻¹ := by
    apply (mul_right_cancel₀ hn)
    rw [hexp,inv_mul_cancel₀ hn]
  rw [hei]
  field_simp

lemma SectorExpansion.uniform_leading_tendsto {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) {β : ℝ} (hβ : β ∈ E) (hgreat : ∀ γ ∈ E,γ≤β)
    (hb : ∀ᶠ z in sectorInfinity,b β z≠0) (hs : SectorSlow (fun z => (b β z)⁻¹)) :
    Tendsto (fun z => Complex.exp (((-β:ℝ):ℂ) * z)*(b β z)⁻¹*f z) sectorInfinity (𝓝 1) := by
  simpa only [sub_add_cancel,zero_add] using
    (hf.uniform_leading hβ hgreat hb hs).tendsto_zero.add_const 1

lemma SectorExpansion.eventually_ne_of_leading {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) {β : ℝ} (hβ : β ∈ E) (hgreat : ∀ γ ∈ E,γ≤β)
    (hb : ∀ᶠ z in sectorInfinity,b β z≠0) (hs : SectorSlow (fun z => (b β z)⁻¹)) :
    ∀ᶠ z in sectorInfinity,f z≠0 := by
  have ht := hf.uniform_leading_tendsto hβ hgreat hb hs
  filter_upwards [ht.eventually_ne (by norm_num : (1:ℂ)≠0)] with z hz
  exact fun hfz => hz (by rw [hfz,mul_zero])

end DegeneratingTrees.Clock
end

end OAI
