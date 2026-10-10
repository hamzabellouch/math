import Mathlib
import OAI.Probability.SKValue.Evolution.GridProfile
import OAI.Probability.SKValue.Coercivity.FiniteCoercivity

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma profileTime_append (l r:HeatProfile) : profileTime (l++r)=profileTime l+profileTime r := by
  induction l with
  | nil => simp [profileTime]
  | cons p l ih => simp only [List.cons_append,profileTime,ih,add_assoc]
lemma profileValue_append_zero (A:ℝ → ℝ) (l r:HeatProfile) :
    profileValue A (l++r) 0=profileValue (profileValue A r 0) l 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,profileValue_zero_cons,ih]
lemma profileValue_append_before (A:ℝ → ℝ) (l r:HeatProfile) {t:ℝ}
    (ht:t∈Icc (0:ℝ) (profileTime l)) :
    profileValue A (l++r) t=profileValue (profileValue A r 0) l t := by
  induction l generalizing t with
  | nil => have ht0:t=0 := le_antisymm ht.2 ht.1; subst t; rfl
  | cons p l ih =>
    change patchTime (p.1:ℝ) _ _ t=patchTime (p.1:ℝ) _ _ t
    by_cases hp:t≤(p.1:ℝ)
    · rw [patchTime_left _ _ hp,patchTime_left _ _ hp]
      congr 1
      exact profileValue_append_zero A l r
    · rw [patchTime_right _ _ (lt_of_not_ge hp),patchTime_right _ _ (lt_of_not_ge hp)]
      apply ih
      constructor
      · exact (sub_pos.mpr (lt_of_not_ge hp)).le
      · have htu:t≤(p.1:ℝ)+profileTime l := ht.2
        linarith
lemma profileCoeff_append_before (l r:HeatProfile) {t:ℝ}
    (ht:t∈Ioc (0:ℝ) (profileTime l)) : profileCoeff (l++r) t=profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change patchTime (p.1:ℝ) _ _ t=patchTime (p.1:ℝ) _ _ t
    by_cases hp:t≤(p.1:ℝ)
    · rw [patchTime_left _ _ hp,patchTime_left _ _ hp]
    · rw [patchTime_right _ _ (lt_of_not_ge hp),patchTime_right _ _ (lt_of_not_ge hp)]
      apply ih
      constructor
      · exact sub_pos.mpr (lt_of_not_ge hp)
      · have htu:t≤(p.1:ℝ)+profileTime l := ht.2
        linarith

lemma BackwardShape.diffusion_prefix_coercivity {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hBrown:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {A:ℝ → ℝ} {M C:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape M A) (hM:0<M) (hC:0<C) (hCM:C≤M)
    {p:ℝ≥0 × ℝ≥0} {l r:HeatProfile}
    (hp:0<(p.2:ℝ)) (ht:0<(p.1:ℝ))
    (hl:((p::l)++r).Pairwise (fun p q ↦ p.2≤q.2))
    (hleft:∀ q∈p::l,(q.2:ℝ)≤C) (hright:∀ q∈r,C≤(q.2:ℝ))
    (hup:∀ q∈r,(q.2:ℝ)≤M)
    (hT1:profileTime ((p::l)++r)≤1)
    (hXM:∀ t∈Icc (0:ℝ) (profileTime ((p::l)++r)),AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) (profileTime ((p::l)++r))) ∧
      IntervalIntegrable (fun s ↦ profileCoeff ((p::l)++r) s*deriv (profileValue A ((p::l)++r) s) (X s ω)) volume 0 (profileTime ((p::l)++r)) ∧
      (∀ t∈Icc (0:ℝ) (profileTime ((p::l)++r)),X t ω=B t.toNNReal ω+
        ∫ s in (0:ℝ)..t,profileCoeff ((p::l)++r) s*deriv (profileValue A ((p::l)++r) s) (X s ω)) ∧ X 0 ω=0) :
    let V:=profileValue A ((p::l)++r) (profileTime (p::l))
    (1/1000:ℝ)*(∫ ω,(spatialJet C V 1 (X (profileTime (p::l)) ω))^4 ∂μ)≤
      ∫ ω,((spatialJet C V 3 (X (profileTime (p::l)) ω))^2-
        12*spatialJet C V 1 (X (profileTime (p::l)) ω)*(spatialJet C V 2 (X (profileTime (p::l)) ω))^2+
        6*(spatialJet C V 1 (X (profileTime (p::l)) ω))^4) ∂μ := by
  dsimp only
  rw [profileValue_append_before A (p::l) r ⟨profileTime_nonneg _,le_rfl⟩,profileValue_terminal]
  have hll:(p::l).Pairwise (fun p q ↦ p.2≤q.2) := (List.pairwise_append.mp hl).1
  have hrr:r.Pairwise (fun p q ↦ p.2≤q.2) := (List.pairwise_append.mp hl).2.1
  have hBs:SmoothTerminal (profileValue A r 0) := (hA.profile_evolution r).slices 0 ⟨le_rfl,profileTime_nonneg r⟩
  have hBb:=hB.profile hA hM hC hCM hrr hright hup 0
  have hsub:profileTime (p::l)≤profileTime ((p::l)++r) := by
    rw [profileTime_append]; exact le_add_of_nonneg_right (profileTime_nonneg r)
  have heq (ω:Ω) (s:ℝ) (hs:s∈Ioc (0:ℝ) (profileTime (p::l))) :
      profileCoeff ((p::l)++r) s*deriv (profileValue A ((p::l)++r) s) (X s ω)=
      profileCoeff (p::l) s*deriv (profileValue (profileValue A r 0) (p::l) s) (X s ω) := by
    rw [profileCoeff_append_before (p::l) r hs,profileValue_append_before A (p::l) r ⟨hs.1.le,hs.2⟩]
  apply hBb.diffusion_coercivity hBrown hBs hp ht hll hleft (hsub.trans hT1)
    (fun t ht ↦ hXM t ⟨ht.1,ht.2.trans hsub⟩)
  filter_upwards [hpaths] with ω hω
  refine ⟨hω.1.mono (Icc_subset_Icc le_rfl hsub),?_,?_,hω.2.2.2⟩
  · have hi:=hω.2.1.mono_set (show uIcc (0:ℝ) (profileTime (p::l)) ⊆ uIcc (0:ℝ) (profileTime ((p::l)++r)) by
      rw [uIcc_of_le (profileTime_nonneg _),uIcc_of_le (profileTime_nonneg _)]; exact Icc_subset_Icc le_rfl hsub)
    apply hi.congr_ae
    rw [uIoc_of_le (profileTime_nonneg _)]
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun s hs ↦ heq ω s hs)
  · intro t ht
    rw [hω.2.2.1 t ⟨ht.1,ht.2.trans hsub⟩]
    congr 1
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le ht.1]
    exact Eventually.of_forall (fun s hs ↦ heq ω s ⟨hs.1,hs.2.trans ht.2⟩)
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma profileCoeff_append_after (l r:HeatProfile) {s:ℝ} (hs:profileTime l<s) :
    profileCoeff (l++r) s=profileCoeff r (s-profileTime l) := by
  induction l generalizing s with
  | nil => simp only [List.nil_append,profileTime,sub_zero]
  | cons p l ih =>
    have hp:(p.1:ℝ)<s := (le_add_of_nonneg_right (profileTime_nonneg l)).trans_lt hs
    change patchTime (p.1:ℝ) _ _ s=_
    rw [patchTime_right _ _ hp]
    have he:profileTime l<s-(p.1:ℝ) := by change (p.1:ℝ)+profileTime l<s at hs;linarith
    change profileCoeff (l++r) (s-(p.1:ℝ))=profileCoeff r (s-profileTime (p::l))
    rw [ih he]
    congr 1
    change s-(p.1:ℝ)-profileTime l=s-((p.1:ℝ)+profileTime l)
    ring

noncomputable def splitLength (a b:ℝ) (hab:a≤b) (n:ℕ) : ℝ≥0 :=
  ⟨(b-a)/(n+1:ℝ),div_nonneg (sub_nonneg.mpr hab) (by positivity)⟩
noncomputable def OrderParameter.splitSegment (γ:OrderParameter) (a b:ℝ)
    (hab:a≤b) (n:ℕ) : HeatProfile :=
  gridProfile (splitLength a b hab n)
    (fun i ↦ (γ.coeff (a+(i:ℝ)*(splitLength a b hab n))).toNNReal+gridDelta n) 0 (n+1)
lemma splitLength_mul (a b:ℝ) (hab:a≤b) (n:ℕ) :
    ((n+1:ℕ):ℝ)*(splitLength a b hab n)=b-a := by
  change ((n+1:ℕ):ℝ)*((b-a)/(n+1:ℝ))=b-a
  rw [Nat.cast_add,Nat.cast_one]
  field_simp
lemma OrderParameter.splitSegment_time (γ:OrderParameter) (a b:ℝ) (hab:a≤b) (n:ℕ) :
    profileTime (γ.splitSegment a b hab n)=b-a := by
  rw [OrderParameter.splitSegment,gridProfile_time,splitLength_mul]
lemma split_sample_mem {a b:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1) {n i:ℕ} (hi:i<n+1) :
    a+(i:ℝ)*(splitLength a b hab.le n)∈Ico (0:ℝ) 1 := by
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast hi
  have ht:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at ht
  exact ⟨add_nonneg ha (mul_nonneg (Nat.cast_nonneg _) hd.le),by linarith⟩
lemma OrderParameter.splitSegment_mono (γ:OrderParameter) {a b:ℝ}
    (ha:0≤a) (hab:a<b) (hb:b≤1) (n:ℕ) :
    (γ.splitSegment a b hab.le n).Pairwise (fun p q ↦ p.2≤q.2) := by
  apply gridProfile_pairwise
  intro i k _ hik hk
  apply add_le_add _ le_rfl
  apply Real.toNNReal_mono
  exact γ.monotone (split_sample_mem ha hab hb (by omega))
    (split_sample_mem ha hab hb (by omega))
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hik.le) (splitLength a b hab.le n).coe_nonneg))
lemma OrderParameter.splitSegment_sample (γ:OrderParameter) {a b s:ℝ}
    (ha:0≤a) (hab:a<b) (hb:b≤1) (n:ℕ) (hs:s∈Icc (0:ℝ) (b-a)) :
    ∃ r∈Ico (0:ℝ) 1, a≤r ∧ r<b ∧
      profileCoeff (γ.splitSegment a b hab.le n) s=γ.coeff r+(gridDelta n:ℝ) ∧
      r≤a+s ∧ a+s-r≤(splitLength a b hab.le n:ℝ) := by
  obtain ⟨i,hi,hin,hc,hlo,hhi⟩:=gridProfile_sample (d:=splitLength a b hab.le n)
    (f:=fun i ↦ (γ.coeff (a+(i:ℝ)*(splitLength a b hab.le n))).toNNReal+gridDelta n)
    (j:=0) (Nat.succ_pos n) (by simpa only [splitLength_mul] using hs)
  have hr:=split_sample_mem ha hab hb (show i<n+1 by omega)
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast (show i<n+1 by omega)
  have ht:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at ht
  refine ⟨a+(i:ℝ)*(splitLength a b hab.le n),hr,le_add_of_nonneg_right (by positivity),by linarith,?_,?_,?_⟩
  · simpa only [OrderParameter.splitSegment,NNReal.coe_add,Real.coe_toNNReal _ (γ.nonneg _ hr)] using hc
  · simp only [Nat.cast_zero,zero_mul,zero_add] at hlo;linarith
  · simp only [Nat.cast_zero,zero_mul,zero_add] at hhi;linarith

noncomputable def OrderParameter.splitGrid (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : HeatProfile :=
  γ.splitSegment 0 t t.property.1.le n++γ.splitSegment t 1 t.property.2.le n
lemma OrderParameter.splitGrid_time (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    profileTime (γ.splitGrid t n)=1 := by
  rw [OrderParameter.splitGrid,profileTime_append,γ.splitSegment_time,γ.splitSegment_time]
  ring
lemma OrderParameter.splitGrid_mono (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    (γ.splitGrid t n).Pairwise (fun p q ↦ p.2≤q.2) := by
  rw [OrderParameter.splitGrid,List.pairwise_append]
  refine ⟨γ.splitSegment_mono le_rfl t.property.1 t.property.2.le n,
    γ.splitSegment_mono t.property.1.le t.property.2 le_rfl n,?_⟩
  intro p hp q hq
  obtain ⟨i,_,hi,rfl⟩:=gridProfile_mem hp
  obtain ⟨j,_,hj,rfl⟩:=gridProfile_mem hq
  apply add_le_add _ le_rfl
  apply Real.toNNReal_mono
  have hir:=split_sample_mem (a:=0) le_rfl t.property.1 t.property.2.le (show i<n+1 by omega)
  have hjr:=split_sample_mem t.property.1.le t.property.2 le_rfl (show j<n+1 by omega)
  apply γ.monotone hir hjr
  have hi':(i:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show i≤n+1 by omega)
  have hle:=mul_le_mul_of_nonneg_right hi' (splitLength 0 t t.property.1.le n).coe_nonneg
  rw [splitLength_mul] at hle
  have hj0:0≤(j:ℝ)*(splitLength t 1 t.property.2.le n) := by positivity
  linarith
lemma OrderParameter.splitGrid_sample (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    ∃ r∈Ico (0:ℝ) 1,profileCoeff (γ.splitGrid t n) s=γ.coeff r+(gridDelta n:ℝ) ∧
      r ≤ s ∧ s-r ≤ (gridDelta n:ℝ) := by
  have hd:0<(n+1:ℝ) := by positivity
  by_cases hst:s≤t
  · have he:profileCoeff (γ.splitGrid t n) s=profileCoeff (γ.splitSegment 0 t t.property.1.le n) s := by
      rcases hs.1.eq_or_lt with rfl | hs0
      · change patchTime _ _ _ 0=patchTime _ _ _ 0
        rw [patchTime_left _ _ (splitLength 0 t t.property.1.le n).coe_nonneg,
          patchTime_left _ _ (splitLength 0 t t.property.1.le n).coe_nonneg]
      · exact profileCoeff_append_before _ _ ⟨hs0,by simpa only [γ.splitSegment_time,sub_zero] using hst⟩
    obtain ⟨r,hr,_,_,hc,hrs,hclose⟩:=γ.splitSegment_sample le_rfl t.property.1 t.property.2.le n
      (show s∈Icc (0:ℝ) ((t:ℝ)-0) by exact ⟨hs.1,by simpa only [sub_zero] using hst⟩)
    refine ⟨r,hr,he.trans hc,by simpa only [zero_add] using hrs,?_⟩
    have hlen:(splitLength 0 t t.property.1.le n:ℝ)≤gridDelta n :=
      div_le_div_of_nonneg_right (by simpa only [sub_zero] using t.property.2.le) hd.le
    simpa only [zero_add] using hclose.trans hlen
  · have ht:(t:ℝ)<s := lt_of_not_ge hst
    have he:profileCoeff (γ.splitGrid t n) s=profileCoeff (γ.splitSegment t 1 t.property.2.le n) (s-t) := by
      rw [OrderParameter.splitGrid,profileCoeff_append_after _ _ (by rw [γ.splitSegment_time,sub_zero];exact ht),γ.splitSegment_time,sub_zero]
    obtain ⟨r,hr,_,_,hc,hrs,hclose⟩:=γ.splitSegment_sample t.property.1.le t.property.2 le_rfl n
      (show s-(t:ℝ)∈Icc (0:ℝ) (1-t) by constructor <;> linarith [hs.2])
    refine ⟨r,hr,he.trans hc,?_,?_⟩
    · linarith
    · have hlen:(splitLength t 1 t.property.2.le n:ℝ)≤gridDelta n :=
        div_le_div_of_nonneg_right (by linarith [t.property.1]) hd.le
      linarith
end SKValue

end

end OAI
