import Mathlib
import OAI.Analysis.PathSelection.ExponentSupports
import OAI.Analysis.PathSelection.SectorLimits

namespace OAI

/-! Clock expansions, uniform bounds and convolution. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
open scoped BigOperators
namespace DegeneratingTrees.Clock

 

structure SectorExpansion (f : ℂ → ℂ) (E : Set ℝ) (b : ℝ → ℂ → ℂ) : Prop where
  bounded_above : BddAbove E
  finite_above : ∀ B : ℝ, (E ∩ Ici B).Finite
  remainders : ∀ B : ℝ, ∃ (ω : ℝ → ℝ) (R ε C : ℝ),
    AdmissibleAngularLoss ω ∧ 0 < ε ∧ 0 ≤ C ∧
    AnalyticOnNhd ℂ f (lossSector ω R) ∧
    ∀ z ∈ lossSector ω R,
      ‖f z - ∑ β ∈ (finite_above B).toFinset, Complex.exp ((β:ℂ)*z)*b β z‖ ≤
        C*Real.exp ((B-ε)*z.re)

lemma central_re_lower {z : ℂ} (hz : |z.arg| ≤ Real.pi/4) : ‖z‖/2 ≤ z.re := by
  have hc : (1/2:ℝ) ≤ Real.cos z.arg := by
    rw [←Real.cos_abs]
    calc (1/2:ℝ) = Real.cos (Real.pi/3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |z.arg| := Real.cos_le_cos_of_nonneg_of_le_pi
        (abs_nonneg _) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg z)
  rw [Complex.norm_mul_cos_arg] at hm
  linarith

lemma AdmissibleAngularLoss.central_tail {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) (R : ℝ) :
    ∃ T : ℝ, ∀ z : ℂ, T < ‖z‖ → |z.arg| ≤ Real.pi/4 → z ∈ lossSector ω R := by
  obtain ⟨a,t,S,hS,ha,has,ht,hsmall,hbound⟩ := angularLoss_kernel_data hω
  refine ⟨max S R,fun z hz hang => ⟨(le_max_right _ _).trans_lt hz,?_⟩⟩
  have hSn : S ≤ ‖z‖ := ((le_max_left _ _).trans_lt hz).le
  have hbn := (hbound _ hSn).2.1
  have hp := Real.pi_gt_three
  linarith

 

lemma SectorExpansion.empty {f : ℂ → ℂ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f ∅ b) : (fun x : ℝ => f (x:ℂ)) =ᶠ[atTop] 0 := by
  have hsum (B : ℝ) (z : ℂ) :
      (∑ β ∈ (h.finite_above B).toFinset, Complex.exp ((β:ℂ)*z)*b β z) = 0 := by
    apply Finset.sum_eq_zero
    intro β hβ
    exact ((h.finite_above B).mem_toFinset.mp hβ).1.elim
  have hcentral : CentralSuperexponential f := by
    intro B hB
    obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hbound⟩ := h.remainders (-2*B)
    obtain ⟨T,hT⟩ := AdmissibleAngularLoss.central_tail hω R
    refine ⟨C,max T 0,hC,?_⟩
    intro z hz hang
    have hzT : T < ‖z‖ := (le_max_left _ _).trans_lt hz
    have hn : 0 < ‖z‖ := (le_max_right _ _).trans_lt hz
    have hb := hbound z (hT z hzT hang)
    simp only [hsum,sub_zero] at hb
    have hr := central_re_lower hang
    refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
    nlinarith
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hbound⟩ := h.remainders 0
  obtain ⟨a,t,S,hS,ha,has,ht,hsmall,hloss⟩ := angularLoss_kernel_data hω
  have hsub : lossSector ω (max R S) ⊆ lossSector ω R :=
    fun z hz => ⟨(le_max_left _ _).trans_lt hz.1,hz.2⟩
  have hbounded : ∃ M : ℝ, ∀ z ∈ lossSector ω (max R S), ‖f z‖ ≤ M := by
    refine ⟨C,?_⟩
    intro z hz
    have hb := hbound z (hsub hz)
    simp only [hsum,sub_zero,zero_sub] at hb
    have hp := (hloss _ (((le_max_right _ _).trans_lt hz.1).le)).1
    have hre : 0 ≤ z.re := Complex.abs_arg_le_pi_div_two_iff.mp (by linarith [hz.2])
    calc ‖f z‖ ≤ C*Real.exp (-ε*z.re) := hb
      _ ≤ C*1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith)) hC
      _ = C := mul_one _
  obtain ⟨R',hRR',hf0⟩ := sector_uniqueness ω (max R S) f hω (hf.mono hsub) hbounded hcentral
  filter_upwards [hω.real_discs R'] with x hx
  exact hf0 (hx.2 (mem_closedBall_self (by linarith [hx.1])))

lemma exists_greatest_of_finite_above {E : Set ℝ}
    (hE : ∀ B : ℝ, (E ∩ Ici B).Finite) (hne : E.Nonempty) :
    ∃ β ∈ E, ∀ γ ∈ E, γ ≤ β := by
  classical
  obtain ⟨a,ha⟩ := hne
  let S := (hE a).toFinset
  have haS : a ∈ S := (hE a).mem_toFinset.mpr ⟨ha,show a ≤ a from le_rfl⟩
  let β := S.max' ⟨a,haS⟩
  have hβS : β ∈ S := Finset.max'_mem _ _
  have haβ : a ≤ β := Finset.le_max' _ _ haS
  refine ⟨β,((hE a).mem_toFinset.mp hβS).1,?_⟩
  intro γ hγ
  by_cases haγ : a ≤ γ
  · exact Finset.le_max' _ _ ((hE a).mem_toFinset.mpr ⟨hγ,haγ⟩)
  · exact (le_of_not_ge haγ).trans haβ

 

theorem SectorExpansion.leading {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b) (hne : E.Nonempty)
    (hcoeff : ∀ β ∈ E, (∀ᶠ x : ℝ in atTop, b β (x:ℂ) ≠ 0) ∧
      Subexponential atTop id (fun x : ℝ => (b β (x:ℂ))⁻¹)) :
    ∃ β ∈ E, (∀ γ ∈ E, γ ≤ β) ∧
      Tendsto (fun x : ℝ => (Real.exp (-β*x):ℂ)*(b β (x:ℂ))⁻¹*f (x:ℂ))
        atTop (𝓝 1) := by
  classical
  obtain ⟨β,hβ,hgreat⟩ := exists_greatest_of_finite_above h.finite_above hne
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hrem⟩ := h.remainders β
  have hsingle : (h.finite_above β).toFinset = {β} := by
    ext γ
    simp only [Set.Finite.mem_toFinset,Set.mem_inter_iff,Set.mem_Ici,Finset.mem_singleton]
    constructor
    · intro hγ; exact le_antisymm (hgreat γ hγ.1) hγ.2
    · rintro rfl; exact ⟨hβ,le_rfl⟩
  have herr : ∀ᶠ x : ℝ in atTop,
      ‖f (x:ℂ)-(Real.exp (-(-β)*x):ℂ) • b β (x:ℂ)‖ ≤ C*Real.exp (-(-β+ε)*x) := by
    filter_upwards [hω.real_discs R] with x hx
    have hp := hrem (x:ℂ) (hx.2 (mem_closedBall_self (by linarith [hx.1])))
    simp only [hsingle,Finset.sum_singleton,←Complex.ofReal_mul,←Complex.ofReal_exp,
      Complex.ofReal_re] at hp
    convert hp using 1 <;> try simp only [neg_neg,smul_eq_mul]
    congr 2; ring
  have hb : Tendsto (fun x : ℝ => (b β (x:ℂ))⁻¹ • b β (x:ℂ)) atTop (𝓝 (1:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(hcoeff β hβ).1] with x hx
    simp [smul_eq_mul,hx]
  have ht := grouped_leading_normalization (X := id) (d := -β)
    tendsto_id (hcoeff β hβ).2 hε hC herr hb
  exact ⟨β,hβ,hgreat,by simpa only [id_eq,smul_eq_mul] using ht⟩

 

theorem SectorExpansion.leading_or_zero {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b)
    (hcoeff : ∀ β ∈ E, (∀ᶠ x : ℝ in atTop, b β (x:ℂ) ≠ 0) ∧
      Subexponential atTop id (fun x : ℝ => (b β (x:ℂ))⁻¹)) :
    (fun x : ℝ => f (x:ℂ)) =ᶠ[atTop] 0 ∨
    ∃ β ∈ E, (∀ γ ∈ E, γ ≤ β) ∧
      Tendsto (fun x : ℝ => (Real.exp (-β*x):ℂ)*(b β (x:ℂ))⁻¹*f (x:ℂ))
        atTop (𝓝 1) := by
  rcases E.eq_empty_or_nonempty with he | he
  · subst E; exact Or.inl h.empty
  · exact Or.inr (h.leading he hcoeff)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ExpBound.zero (a : ℝ) : ExpBound a (fun _ => 0) := Asymptotics.isBigO_zero _ _
lemma ExpBound.neg {a : ℝ} {f : ℂ → ℂ} (hf : ExpBound a f) :
    ExpBound a (fun z => -f z) := Asymptotics.IsBigO.neg_left hf
lemma ExpBound.sub {a : ℝ} {f g : ℂ → ℂ} (hf : ExpBound a f) (hg : ExpBound a g) :
    ExpBound a (fun z => f z-g z) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma ExpBound.sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} {a : ℝ}
    (h : ∀ i ∈ S, ExpBound a (f i)) : ExpBound a (fun z => ∑ i ∈ S,f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ExpBound.zero a
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h _ (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma ExpSmall.zero (B : ℝ) : ExpSmall B (fun _ => 0) := ⟨B-1,by linarith,ExpBound.zero _⟩
lemma ExpSmall.neg {B : ℝ} {f : ℂ → ℂ} (hf : ExpSmall B f) :
    ExpSmall B (fun z => -f z) := by
  obtain ⟨a,ha,hf⟩ := hf
  exact ⟨a,ha,hf.neg⟩
lemma ExpSmall.sub {B : ℝ} {f g : ℂ → ℂ} (hf : ExpSmall B f) (hg : ExpSmall B g) :
    ExpSmall B (fun z => f z-g z) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma ExpSmall.sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} {B : ℝ}
    (h : ∀ i ∈ S, ExpSmall B (f i)) : ExpSmall B (fun z => ∑ i ∈ S,f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ExpSmall.zero B
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h _ (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma ExpBound.cexp (β : ℝ) : ExpBound β (fun z => Complex.exp ((β:ℂ)*z)) := by
  apply Asymptotics.IsBigO.of_bound 1
  exact Eventually.of_forall (fun z => by simp [Complex.norm_exp])

lemma ExpBound.expTerm {a : ℝ} {b : ℂ → ℂ} (hb : ExpBound a b) (β : ℝ) :
    ExpBound (β+a) (fun z => Complex.exp ((β:ℂ)*z)*b z) := (ExpBound.cexp β).mul hb

lemma SectorSlow.mul {f g : ℂ → ℂ} (hf : SectorSlow f) (hg : SectorSlow g) :
    SectorSlow (fun z => f z*g z) := by
  intro ε hε
  have h := (hf (ε/2) (by linarith)).mul (hg (ε/2) (by linarith))
  simpa only [add_halves] using h

lemma SectorSlow.expSmall {b : ℂ → ℂ} (hb : SectorSlow b) {β B : ℝ} (hβ : β < B) :
    ExpSmall B (fun z => Complex.exp ((β:ℂ)*z)*b z) := by
  refine ⟨β+(B-β)/2,by linarith,(hb ((B-β)/2) (by linarith)).expTerm β⟩

lemma SectorExpansion.eventually_analytic {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b) : ∀ᶠ z in sectorInfinity, AnalyticAt ℂ f z := by
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hb⟩ := h.remainders 0
  exact ⟨ω,R,hω,hf⟩

lemma SectorExpansion.expSmall_remainder {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b) (B : ℝ) :
    ExpSmall B (fun z => f z-∑ β ∈ (h.finite_above B).toFinset,Complex.exp ((β:ℂ)*z)*b β z) := by
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hb⟩ := h.remainders B
  refine ⟨B-ε,by linarith,Asymptotics.IsBigO.of_bound C ?_⟩
  exact ⟨ω,R,hω,fun z hz => by simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hb z hz⟩

lemma SectorExpansion.of_expSmall {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hE : BddAbove E) (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite)
    (hf : ∀ᶠ z in sectorInfinity, AnalyticAt ℂ f z)
    (hb : ∀ B : ℝ, ExpSmall B
      (fun z => f z-∑ β ∈ (hEl B).toFinset,Complex.exp ((β:ℂ)*z)*b β z)) :
    SectorExpansion f E b := by
  refine ⟨hE,hEl,?_⟩
  intro B
  obtain ⟨a,ha,hO⟩ := hb B
  obtain ⟨C,hC,hbound⟩ := hO.exists_pos
  obtain ⟨ω,R,hω,hboth⟩ := eventually_sectorInfinity.mp (hf.and hbound.bound)
  refine ⟨ω,R,B-a,C,hω,by linarith,hC.le,fun z hz => (hboth z hz).1,?_⟩
  intro z hz
  simpa only [sub_sub_cancel,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using (hboth z hz).2

lemma SectorExpansion.expBound {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b) {A : ℝ} (hA : ∀ β ∈ E, β ≤ A) : ExpBound (A+1) f := by
  have he : (h.finite_above (A+1)).toFinset = ∅ := by
    classical
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro β hβ
    have hh := (h.finite_above (A+1)).mem_toFinset.mp hβ
    have := hA β hh.1
    have : A+1≤β := hh.2
    linarith
  obtain ⟨a,ha,hO⟩ := h.expSmall_remainder (A+1)
  simp only [he,Finset.sum_empty,sub_zero] at hO
  exact hO.mono ha.le

lemma truncation_expBound {E : Set ℝ} {b : ℝ → ℂ → ℂ} {A : ℝ}
    (hA : ∀ β ∈ E, β ≤ A) (hb : ∀ β ∈ E, SectorSlow (b β))
    (B : ℝ) (hEl : (E ∩ Ici B).Finite) :
    ExpBound (A+1) (fun z => ∑ β ∈ hEl.toFinset,Complex.exp ((β:ℂ)*z)*b β z) := by
  apply ExpBound.sum
  intro β hβ
  have he := (hEl.mem_toFinset.mp hβ).1
  exact ((hb β he 1 zero_lt_one).expTerm β).mono (by linarith [hA β he])

end DegeneratingTrees.Clock

 

 

 

open Set Complex
namespace DegeneratingTrees.Clock

variable {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F)
  (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (hFl : ∀ B : ℝ, (F ∩ Ici B).Finite)

def exponentConvolution (b c : ℝ → ℂ → ℂ) (δ : ℝ) (z : ℂ) : ℂ :=
  ∑ p ∈ (exponentFiber_finite hE hF hEl hFl δ).toFinset,b p.1 z*c p.2 z

lemma convolution_truncation (b c : ℝ → ℂ → ℂ) (B : ℝ) (z : ℂ) :
    (∑ δ ∈ (exponentSum_finite hE hF hEl hFl B).toFinset,
      Complex.exp ((δ:ℂ)*z)*exponentConvolution hE hF hEl hFl b c δ z) =
    ∑ p ∈ (exponentPairs_finite hE hF hEl hFl B).toFinset,
      Complex.exp (((p.1+p.2:ℝ):ℂ)*z)*(b p.1 z*c p.2 z) := by
  classical
  let S := (exponentSum_finite hE hF hEl hFl B).toFinset
  let T := (exponentPairs_finite hE hF hEl hFl B).toFinset
  have hmaps : ∀ p ∈ T, p.1+p.2 ∈ S := by
    intro p hp
    have hh := (exponentPairs_finite hE hF hEl hFl B).mem_toFinset.mp hp
    exact (exponentSum_finite hE hF hEl hFl B).mem_toFinset.mpr
      ⟨⟨p,⟨hh.1,hh.2.1⟩,rfl⟩,hh.2.2⟩
  calc
    _ = ∑ δ ∈ S,∑ p ∈ T with p.1+p.2=δ,
        Complex.exp (((p.1+p.2:ℝ):ℂ)*z)*(b p.1 z*c p.2 z) := by
      apply Finset.sum_congr rfl
      intro δ hδ
      have hB := ((exponentSum_finite hE hF hEl hFl B).mem_toFinset.mp hδ).2
      have he : (exponentFiber_finite hE hF hEl hFl δ).toFinset =
          T.filter (fun p => p.1+p.2=δ) := by
        ext p
        simp only [Set.Finite.mem_toFinset,Finset.mem_filter,T,exponentFiber,
          exponentPairs,mem_ofPred_eq]
        constructor
        · intro hp
          exact ⟨⟨hp.1,hp.2.1,by simpa only [hp.2.2,Set.mem_Ici] using hB⟩,hp.2.2⟩
        · intro hp
          exact ⟨hp.1.1,hp.1.2.1,hp.2⟩
      rw [exponentConvolution,he,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])
    _ = _ := Finset.sum_fiberwise_of_maps_to hmaps _

lemma product_truncation_rectangle (b c : ℝ → ℂ → ℂ) (U V : ℝ) (z : ℂ) :
    (∑ β ∈ (hEl U).toFinset,Complex.exp ((β:ℂ)*z)*b β z) *
      (∑ γ ∈ (hFl V).toFinset,Complex.exp ((γ:ℂ)*z)*c γ z) =
    ∑ p ∈ (hEl U).toFinset ×ˢ (hFl V).toFinset,
      Complex.exp (((p.1+p.2:ℝ):ℂ)*z)*(b p.1 z*c p.2 z) := by
  classical
  rw [Finset.sum_product,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  simp only [Complex.ofReal_add,add_mul,Complex.exp_add]
  ring

lemma rectangle_high {A C B U V : ℝ}
    (hA : ∀ β ∈ E, β ≤ A) (hC : ∀ γ ∈ F, γ ≤ C)
    (hU : U ≤ B-C) (hV : V ≤ B-A) :
    ((hEl U).toFinset ×ˢ (hFl V).toFinset).filter (fun p => B ≤ p.1+p.2) =
      (exponentPairs_finite hE hF hEl hFl B).toFinset := by
  classical
  ext p
  simp only [Finset.mem_filter,Finset.mem_product,Set.Finite.mem_toFinset]
  constructor
  · intro hp
    exact ⟨hp.1.1.1,hp.1.2.1,hp.2⟩
  · intro hp
    exact ⟨exponentPairs_subset_rectangle hA hC hU hV hp,hp.2.2⟩

lemma rectangle_split {A C B U V : ℝ}
    (hA : ∀ β ∈ E, β ≤ A) (hC : ∀ γ ∈ F, γ ≤ C)
    (hU : U ≤ B-C) (hV : V ≤ B-A) (b c : ℝ → ℂ → ℂ) (z : ℂ) :
    (∑ β ∈ (hEl U).toFinset,Complex.exp ((β:ℂ)*z)*b β z) *
      (∑ γ ∈ (hFl V).toFinset,Complex.exp ((γ:ℂ)*z)*c γ z) =
    (∑ δ ∈ (exponentSum_finite hE hF hEl hFl B).toFinset,
      Complex.exp ((δ:ℂ)*z)*exponentConvolution hE hF hEl hFl b c δ z) +
    ∑ p ∈ ((hEl U).toFinset ×ˢ (hFl V).toFinset).filter (fun p => p.1+p.2 < B),
      Complex.exp (((p.1+p.2:ℝ):ℂ)*z)*(b p.1 z*c p.2 z) := by
  classical
  rw [product_truncation_rectangle hEl hFl,convolution_truncation hE hF hEl hFl]
  rw [←rectangle_high hE hF hEl hFl hA hC hU hV]
  symm
  simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
    ((hEl U).toFinset ×ˢ (hFl V).toFinset) (fun p => B ≤ p.1+p.2)
    (fun p => Complex.exp (((p.1+p.2:ℝ):ℂ)*z)*(b p.1 z*c p.2 z))

end DegeneratingTrees.Clock
end

end OAI
