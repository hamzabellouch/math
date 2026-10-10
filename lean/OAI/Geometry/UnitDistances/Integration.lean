import OAI.Geometry.UnitDistances.Scores

namespace OAI

namespace PlanarUnitDistances.TailWindows
open Finset Set FiniteLaw
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E]

def tail (μ : Law E) (x : E → ℝ) (s : ℝ) : ℝ := event μ (fun e => s<x e)
lemma tail_antitone (μ : Law E) (x : E → ℝ) : Antitone (tail μ x) := by
  intro s t hst
  exact event_mono μ (fun e he => lt_of_le_of_lt hst he)
lemma below_all (μ : Law E) (x : E → ℝ) (s : ℝ) (h : ∀e,s<x e) : tail μ x s=1 := by
  unfold tail event
  simp only [ite_eq_left (h _)]
  exact avg_const μ 1
lemma above_all (μ : Law E) (x : E → ℝ) (s : ℝ) (h : ∀e,x e ≤ s) : tail μ x s=0 := by
  unfold tail event
  simp only [ite_eq_right (not_lt.mpr (h _))]
  exact avg_const μ 0

lemma step (μ : Law E) (x : E → ℝ) (s : ℝ) (hs : tail μ x s<1) :
    ∃e,x e ≤ s ∧ tail μ x (x e)=tail μ x s := by
  let F := univ.filter (fun e => x e ≤ s)
  have hF : F.Nonempty := by
    by_contra h
    have hh : ∀e,s<x e := by
      intro e
      by_contra he
      exact h ⟨e,mem_filter.mpr ⟨mem_univ _,le_of_not_gt he⟩⟩
    linarith [below_all μ x s hh]
  obtain ⟨e,he,hem⟩ := F.exists_max_image x hF
  have hes := (mem_filter.mp he).2
  refine ⟨e,hes,?_⟩
  apply avg_congr
  intro f
  have hh : x e<x f ↔ s<x f := by
    constructor
    · intro h
      by_contra ht
      exact (not_lt_of_ge (hem f (mem_filter.mpr ⟨mem_univ _,le_of_not_gt ht⟩))) h
    · exact fun h => lt_of_le_of_lt hes h
  simp only [hh]

lemma nonempty_type (μ : Law E) : Nonempty E := by
  by_contra h
  have : IsEmpty E := not_nonempty_iff.mp h
  have ht := μ.total
  simp at ht

lemma least_threshold (μ : Law E) (x : E → ℝ) (P : ℝ → Prop)
    (hmono : ∀a b,b ≤ a → P a → P b) (hsmall : ∀a,P a → a<1)
    (hzero : P 0) : ∃l,∀s,P (tail μ x s) ↔ l ≤ s := by
  let F := univ.filter (fun e => P (tail μ x (x e)))
  have hF : F.Nonempty := by
    let _ : Nonempty E := nonempty_type μ
    obtain ⟨e,_,he⟩ := univ.exists_max_image x univ_nonempty
    have hz : tail μ x (x e)=0 := above_all μ x _ (fun f => he f (mem_univ _))
    exact ⟨e,mem_filter.mpr ⟨mem_univ _,by rw [hz]; exact hzero⟩⟩
  obtain ⟨e,he,hem⟩ := F.exists_min_image x hF
  refine ⟨x e,fun s => ⟨?_,?_⟩⟩
  · intro hs
    obtain ⟨f,hf,hv⟩ := step μ x s (hsmall _ hs)
    exact (hem f (mem_filter.mpr ⟨mem_univ _,by rw [hv]; exact hs⟩)).trans hf
  · intro hs
    exact hmono _ _ (tail_antitone μ x hs) (mem_filter.mp he).2

theorem window (μ : Law E) (x : E → ℝ) {L U : ℝ}
    (hL : 0<L) (hLU : L ≤ U) (hU : U<1) :
    ∃l r,l ≤ r ∧ ∀s,(L ≤ tail μ x s ∧ tail μ x s ≤ U) ↔ s∈Set.Ico l r := by
  obtain ⟨l,hl⟩ := least_threshold μ x (fun a => a ≤ U)
    (fun a b hab ha => hab.trans ha) (fun a ha => ha.trans_lt hU) (hL.le.trans hLU)
  obtain ⟨r,hr⟩ := least_threshold μ x (fun a => a<L)
    (fun a b hab ha => hab.trans_lt ha) (fun a ha => (ha.trans_le hLU).trans hU) hL
  have hlr : l ≤ r := (hl r).mp (((hr r).mpr le_rfl).le.trans hLU)
  refine ⟨l,r,hlr,fun s => ?_⟩
  have he : L ≤ tail μ x s ↔ s<r := by
    rw [← not_lt,hr,not_le]
  simp only [he,hl,Set.mem_Ico,and_comm]

end
end PlanarUnitDistances.TailWindows

namespace PlanarUnitDistances.StarWindow
open MeasureTheory Set Real FiniteLaw TailWindows PlaceScore
open scoped Classical
noncomputable section
variable {E F : Type*} [Fintype E] [Fintype F]

lemma common_window (μ : Law E) (x : E → ℝ) {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2) :
    ∃l r,l ≤ r ∧ ∀s,common ε (tail μ x s) ↔ s∈Ico l r :=
  window μ x hε (by linarith) (by linarith)

lemma central_window (μ : Law E) (x : E → ℝ) :
    ∃l r,l ≤ r ∧ ∀s,|tail μ x s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r := by
  obtain ⟨l,r,hlr,h⟩ := window μ x (L:=(1/2-1/100:ℝ)) (U:=(1/2+1/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨l,r,hlr,fun s => ?_⟩
  rw [←h s,abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem exists_joint_window (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2) :
    ∃l r,∀s,common ε (tail μ x s) ∧ |tail ν y s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r := by
  obtain ⟨a,b,_,hg⟩ := common_window μ x hε hε'
  obtain ⟨c,d,_,hr⟩ := central_window ν y
  refine ⟨max a c,min b d,fun s => ?_⟩
  rw [hg,hr]
  simp only [mem_Ico,max_le_iff,lt_min_iff]
  tauto

lemma tail_eq (μ : Law E) (x : E → ℝ) (s : ℝ) : tail μ x s=BudgetIntervals.tail μ.val x s := rfl

theorem mean_excess (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ}
    (hJ : ∀s,common ε (tail μ x s) ∧ |tail ν y s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r) :
    avg (pair ν ν) (fun ef => (1/20000:ℝ)*max 0 (r-l)*
      (if l < min (y ef.1) (y ef.2) ∧ min (y ef.1) (y ef.2)<r ∧
          l < max (y ef.1) (y ef.2) ∧ max (y ef.1) (y ef.2)<r then 1 else 0)) ≤
      4*(1/100:ℝ)^2*(1/20000:ℝ)*max 0 (r-l) := by
  have hc : ∀s∈Ioo l r,|BudgetIntervals.tail ν.val y s-1/2| ≤ (1/100:ℝ) := by
    intro s hs
    exact ((hJ s).mpr ⟨hs.1.le,hs.2⟩).2
  rw [pair_avg]
  unfold avg
  have he := BudgetIntervals.pair_interior_mass ν.val y l r
  have hh : (∑e,ν.val e*∑f,ν.val f*((1/20000:ℝ)*max 0 (r-l)*
      (if l < min (y e) (y f) ∧ min (y e) (y f)<r ∧
          l < max (y e) (y f) ∧ max (y e) (y f)<r then 1 else 0))) =
      ((1/20000:ℝ)*max 0 (r-l))*(BudgetIntervals.interiorMass ν.val y l r)^2 := by
    rw [←he]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [hh]
  have hm := BudgetIntervals.interior_mass_le ν.nonneg y (by norm_num : (0:ℝ) ≤ 1/100) hc
  have hn := BudgetIntervals.interiorMass_nonneg ν.val ν.nonneg y l r
  have hs : (BudgetIntervals.interiorMass ν.val y l r)^2 ≤ (2*(1/100:ℝ))^2 :=
    (sq_le_sq₀ hn (by norm_num)).mpr hm
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1/20000:ℝ)*max 0 (r-l) by positivity)
  nlinarith only [h]
end
end PlanarUnitDistances.StarWindow

namespace PlanarUnitDistances.WindowVariation
open MeasureTheory Set Real FiniteLaw TailWindows PlaceScore StarWindow
open scoped Classical
noncomputable section
variable {E F : Type*} [Fintype E] [Fintype F]

def variation (ε : ℝ) (g ρ : ℝ → ℝ) (s : ℝ) : ℝ :=
  if common ε (g s) then 2*ρ s*(1-ρ s) else 0

lemma variation_nonneg {ε : ℝ} {g ρ : ℝ → ℝ} (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1) (s : ℝ) :
    0 ≤ variation ε g ρ s := by
  unfold variation
  split_ifs
  · exact mul_nonneg (mul_nonneg (by norm_num) (hρ s).1) (sub_nonneg.mpr (hρ s).2)
  · exact le_rfl

lemma central_lower {ε l r : ℝ} {g ρ : ℝ → ℝ}
    (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r) (s : ℝ) :
    (2*((1/4:ℝ)-(1/100:ℝ)^2))*ind (Icc l r) s ≤ variation ε g ρ s ∨ s=r := by
  by_cases he : s=r
  · exact Or.inr he
  left
  by_cases hs : s∈Icc l r
  · have hc := (hJ s).mpr ⟨hs.1,lt_of_le_of_ne hs.2 he⟩
    rw [ind,Set.indicator_of_mem hs,variation,ite_eq_left hc.1,mul_one]
    have hr := abs_le.mp hc.2
    nlinarith [sq_nonneg (ρ s-1/2),mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hr.1)]
  · rw [ind,Set.indicator_of_notMem hs,mul_zero]
    exact variation_nonneg hρ s

lemma window_le_variation {ε l r : ℝ} {g ρ : ℝ → ℝ}
    (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r)
    (hi : Integrable (variation ε g ρ)) :
    2*((1/4:ℝ)-(1/100:ℝ)^2)*max 0 (r-l) ≤ ∫s,variation ε g ρ s := by
  have hp : ∀ᵐ s : ℝ, (2*((1/4:ℝ)-(1/100:ℝ)^2))*ind (Icc l r) s ≤ variation ε g ρ s := by
    have hne : ∀ᵐ s : ℝ, s≠r := by rw [ae_iff]; simp
    filter_upwards [hne] with s hs
    exact (central_lower hρ hJ s).resolve_right hs
  have h := integral_mono_ae ((ind_Icc_integrable l r).const_mul _) hi hp
  rw [integral_const_mul,ind_Icc_integral] at h
  exact h

lemma excess_le_variation {ε l r : ℝ} {g ρ : ℝ → ℝ}
    (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r)
    (hi : Integrable (variation ε g ρ)) :
    4*(1/100:ℝ)^2*(1/20000:ℝ)*max 0 (r-l) ≤
      (1/20000000:ℝ)*(∫s,variation ε g ρ s) := by
  have h := window_le_variation hρ hJ hi
  have hn : 0 ≤ max 0 (r-l) := le_max_left _ _
  nlinarith only [h,hn]
end
end PlanarUnitDistances.WindowVariation

namespace PlanarUnitDistances.FiniteLawIntegral
open MeasureTheory Finset FiniteLaw
open scoped Classical
noncomputable section
variable {X Ω : Type*} [Fintype X] [MeasurableSpace Ω]

lemma measurable_avg (μ : Law X) (f : X → Ω → ℝ) (hf : ∀x,Measurable (f x)) :
    Measurable (fun a => avg μ (fun x => f x a)) := by
  exact Finset.measurable_sum _ (fun x _ => (hf x).const_mul _)

lemma integrable_avg (μ : Law X) {ν : Measure Ω} (f : X → Ω → ℝ)
    (hf : ∀x,Integrable (f x) ν) : Integrable (fun a => avg μ (fun x => f x a)) ν := by
  exact integrable_finsetSum _ (fun x _ => (hf x).const_mul _)

lemma integral_avg (μ : Law X) {ν : Measure Ω} (f : X → Ω → ℝ)
    (hf : ∀x,Integrable (f x) ν) :
    (∫a,avg μ (fun x => f x a) ∂ν)=avg μ (fun x => ∫a,f x a ∂ν) := by
  unfold avg
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul _)]
  simp only [integral_const_mul]

lemma avg_sum {I : Type*} [Fintype I] (μ : Law X) (f : I → X → ℝ) :
    avg μ (fun x => ∑i,f i x)=∑i,avg μ (f i) := by
  simp only [avg,Finset.mul_sum]
  exact Finset.sum_comm

lemma avg_div (μ : Law X) (f : X → ℝ) (c : ℝ) :
    avg μ (fun x => f x/c)=avg μ f/c := by
  simp only [avg,mul_div_assoc,Finset.sum_div]

lemma avg_mono_support (μ : Law X) {f g : X → ℝ}
    (h : ∀x,0<μ.val x → f x ≤ g x) : avg μ f ≤ avg μ g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : μ.val x=0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))) (μ.nonneg x)

lemma avg_indicator_mul (μ : Law X) (P : X → Prop) (c : ℝ) :
    avg μ (fun x => if P x then c else 0)=c*event μ P := by
  unfold event
  rw [←avg_smul]
  apply avg_congr
  intro x
  split_ifs <;> ring
end
end PlanarUnitDistances.FiniteLawIntegral

namespace PlanarUnitDistances.ExpectedBudget
open MeasureTheory Set Finset Real FiniteLaw FiniteLawIntegral PlaceLevels BudgetPlaces
  LevelGeometry GlobalPairBudget PlaceScore TailWindows StarWindow WindowVariation
open scoped Classical
noncomputable section
variable {K E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype E] [Fintype F]

def pairScore (S : Finset K) (d : F → K) (f : F → F → Place K S → ℝ → ℝ) (a : F×F) : ℝ :=
  (∑v : Place K S,((∫s,f a.1 a.2 v s)-|threshold (av K v) (d a.1)-threshold (av K v) (d a.2)|)) /
    (Module.finrank ℚ K:ℝ)

def excess (S : Finset K) (d : F → K) (l r : Place K S → ℝ) (v : Place K S) (a : F×F) : ℝ :=
  (1/20000:ℝ)*max 0 (r v-l v)*
    (if l v < min (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2)) ∧
        min (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2))<r v ∧
        l v < max (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2)) ∧
        max (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2))<r v then 1 else 0)

omit [IsGalois ℚ K] [Fintype F] in
lemma excess_nonneg (S : Finset K) (d : F → K) (l r : Place K S → ℝ) (v : Place K S) (a : F×F) :
    0 ≤ excess S d l r v a := by unfold excess; split_ifs <;> positivity

theorem star_upper (μ : Law E) (ν : Law F) (S : Finset K) (d : F → K)
    (c : Place K S → E → ℝ) (hd : ∀e,0<ν.val e → d e≠0)
    (hinj : ∀e f,0<ν.val e → 0<ν.val f → e≠f → d e≠d f)
    (hmem : ∀e f,0<ν.val e → 0<ν.val f → e≠f → differenceProduct (d e) (d f)∈S)
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (f : F → F → Place K S → ℝ → ℝ)
    (hf : ∀e e' v,Integrable (f e e' v))
    (hcap : ∀e e',0<ν.val e → 0<ν.val e' → e≠e' → ∀v s,f e e' v s ≤ PlaceScore.cap ε (tail μ (c v))
      (tail ν (fun e => threshold (av K v) (d e)))
      (min (threshold (av K v) (d e)) (threshold (av K v) (d e')))
      (max (threshold (av K v) (d e)) (threshold (av K v) (d e')))
      (alpha (av K v) (d e) (d e')+allowance v) s)
    (hv : ∀v,Integrable (variation ε (tail μ (c v)) (tail ν (fun e => threshold (av K v) (d e)))))
    {W : ℝ} (hdiag : ∀e,pairScore S d f (e,e) ≤ W) :
    avg (pair ν ν) (pairScore S d f) ≤ 2*log 2+
      (1/20000000:ℝ)*((∑v : Place K S,∫s,variation ε (tail μ (c v))
        (tail ν (fun e => threshold (av K v) (d e))) s)/(Module.finrank ℚ K:ℝ))+
      W*event (pair ν ν) (fun ef => ef.1=ef.2) := by
  choose l r hJ using fun v : Place K S => exists_joint_window μ ν (c v)
    (fun e => threshold (av K v) (d e)) hε hε'
  let ex (a : F×F) : ℝ := (∑v : Place K S,excess S d l r v a)/(Module.finrank ℚ K:ℝ)
  have hex (a : F×F) : 0 ≤ ex a := div_nonneg (sum_nonneg (fun v _ => excess_nonneg S d l r v a))
    (Nat.cast_nonneg _)
  have hc (a : F×F) (hpos : 0<(pair ν ν).val a) : pairScore S d f a ≤ 2*log 2+ex a+(if a.1=a.2 then W else 0) := by
    have hpa : 0<ν.val a.1 := (mul_pos_iff.mp hpos).elim And.left (fun h => False.elim (not_lt.mpr (ν.nonneg a.1) h.1))
    have hpb : 0<ν.val a.2 := (mul_pos_iff.mp hpos).elim And.right (fun h => False.elim (not_lt.mpr (ν.nonneg a.2) h.2))
    by_cases ha : a.1=a.2
    · rw [ite_eq_left ha]
      have hh : pairScore S d f a ≤ W := by
        rcases a with ⟨a,b⟩
        change a=b at ha
        subst b
        exact hdiag a
      have hl : 0 ≤ log (2:ℝ) := Real.log_nonneg (by norm_num)
      linarith [hex a]
    · rw [ite_eq_right ha,add_zero]
      exact weighted_pair S (hd a.1 hpa) (hd a.2 hpb) (hinj _ _ hpa hpb ha) (hmem _ _ hpa hpb ha) hε'
        (fun v => tail μ (c v)) (fun v => tail ν (fun e => threshold (av K v) (d e)))
        (f a.1 a.2) l r (fun v => tail_antitone μ (c v)) hJ (hf _ _) (hcap _ _ hpa hpb ha)
  have hmean := avg_mono_support (pair ν ν) hc
  rw [avg_add,avg_add,avg_const,avg_indicator_mul] at hmean
  have hm (v : Place K S) : avg (pair ν ν) (excess S d l r v) ≤
      (1/20000000:ℝ)*(∫s,variation ε (tail μ (c v))
        (tail ν (fun e => threshold (av K v) (d e))) s) := by
    refine (mean_excess μ ν (c v) (fun e => threshold (av K v) (d e)) (hJ v)).trans ?_
    apply excess_le_variation _ (hJ v) (hv v)
    intro s
    exact ⟨event_nonneg _ _,event_le_one _ _⟩
  have hexmean : avg (pair ν ν) ex ≤
      (1/20000000:ℝ)*((∑v : Place K S,∫s,variation ε (tail μ (c v))
        (tail ν (fun e => threshold (av K v) (d e))) s)/(Module.finrank ℚ K:ℝ)) := by
    dsimp only [ex]
    rw [avg_div,FiniteLawIntegral.avg_sum]
    have hh := div_le_div_of_nonneg_right (sum_le_sum (s:=univ) (fun v _ => hm v))
      (Nat.cast_nonneg (Module.finrank ℚ K))
    simpa only [←Finset.mul_sum,mul_div_assoc] using hh
  linarith
end
end PlanarUnitDistances.ExpectedBudget

namespace PlanarUnitDistances.SlotIntegration
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E] [Fintype F]

def truncatedPositive (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (v : Place K S) (s : ℝ) : ℝ :=
  (Icc (-radius K S v) (radius K S v)).indicator
    (fun s => positive ε μ ν edge y x good label e f (snapshot S z w src tgt u (v,s))) s

lemma positive_integrable (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (v : Place K S) : Integrable (truncatedPositive S z w src tgt u ε μ ν edge y x good label e f v) := by
  exact (integrable_piece S z w src tgt u (positive ε μ ν edge y x good label e f) v _ _).integrable_indicator measurableSet_Icc

lemma piece_score (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (hm : ∀j,z (src (edge j))-z (tgt (edge j))∈S) (e f : F) (v : Place K S) :
    (∫s in Icc (-radius K S v) (radius K S v),
      score ε μ ν edge y x good label e f (snapshot S z w src tgt u (v,s)))=
    (∫s,truncatedPositive S z w src tgt u ε μ ν edge y x good label e f v s)-
      |threshold (av K v) (z (src (edge e))-z (tgt (edge e)))-
       threshold (av K v) (z (src (edge f))-z (tgt (edge f)))| := by
  have hp := integrable_piece S z w src tgt u (positive ε μ ν edge y x good label e f) v (-radius K S v) (radius K S v)
  have hn := integrable_piece S z w src tgt u
    (fun a : Data V E => RareScore.ind (a.1 (edge e)≠a.1 (edge f))) v (-radius K S v) (radius K S v)
  unfold score truncatedPositive
  rw [integral_sub hp hn,integral_indicator measurableSet_Icc]
  congr 1
  exact negative_integral (threshold_in_range K (hm e) v).1 (threshold_in_range K (hm e) v).2
    (threshold_in_range K (hm f) v).1 (threshold_in_range K (hm f) v).2

lemma score_eq_pairScore (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (hm : ∀j,z (src (edge j))-z (tgt (edge j))∈S) (e f : F) :
    (∫a,score ε μ ν edge y x good label e f (snapshot S z w src tgt u a) ∂LevelScale.measure S)=
      ExpectedBudget.pairScore S (fun j => z (src (edge j))-z (tgt (edge j)))
        (truncatedPositive S z w src tgt u ε μ ν edge y x good label) (e,f) := by
  have hb (a : Place K S×ℝ) : |score ε μ ν edge y x good label e f (snapshot S z w src tgt u a)| ≤ 2 := by
    have h := LevelScores.score_bounds ε (frequency μ (snapshot S z w src tgt u a))
      (event ν (fun j => (snapshot S z w src tgt u a).1 (edge j)=true))
      (good (snapshot S z w src tgt u a)) (label (snapshot S z w src tgt u a))
      ((snapshot S z w src tgt u a).2 x) ((snapshot S z w src tgt u a).2 (y e))
      ((snapshot S z w src tgt u a).2 (y f)) ((snapshot S z w src tgt u a).1 (edge e))
      ((snapshot S z w src tgt u a).1 (edge f))
    apply abs_le.mpr
    change -1 ≤ score ε μ ν edge y x good label e f (snapshot S z w src tgt u a) ∧
      score ε μ ν edge y x good label e f (snapshot S z w src tgt u a) ≤ 2 at h
    constructor <;> linarith
  rw [LevelScale.measure,FiniteLevels.integral_eq _ _ _ _
    (measurable_score S z w src tgt u ε μ ν edge y x good label e f) 2 hb]
  simp_rw [piece_score S z w src tgt u ε μ ν edge y x good label hm e f]
  simp only [ExpectedBudget.pairScore,LevelScale.weight,div_eq_mul_inv,mul_comm]
  rfl
end
end PlanarUnitDistances.SlotIntegration

namespace PlanarUnitDistances.TailVariation
open MeasureTheory Set Finset Real FiniteLaw TailWindows PlaceScore WindowVariation
open scoped Classical
noncomputable section
variable {E F : Type*} [Fintype E] [Fintype F]

lemma tail_measurable (μ : Law E) (x : E → ℝ) : Measurable (tail μ x) := by
  unfold tail event avg
  exact Finset.measurable_sum _ (fun e _ => (Measurable.ite measurableSet_Iio measurable_const measurable_const).const_mul (μ.val e))
lemma variation_measurable (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ) (ε : ℝ) :
    Measurable (variation ε (tail μ x) (tail ν y)) := by
  apply Measurable.ite _ ((measurable_const.mul (tail_measurable ν y)).mul
    (measurable_const.sub (tail_measurable ν y))) measurable_const
  exact (measurableSet_le measurable_const (tail_measurable μ x)).inter
    (measurableSet_le (tail_measurable μ x) measurable_const)
lemma variation_bounds (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ) (ε s : ℝ) :
    0 ≤ variation ε (tail μ x) (tail ν y) s ∧ variation ε (tail μ x) (tail ν y) s ≤ 1/2 := by
  constructor
  · exact variation_nonneg (fun t => ⟨event_nonneg ν _,event_le_one ν _⟩) s
  · unfold variation
    split_ifs <;> nlinarith [sq_nonneg (tail ν y s-1/2)]
lemma variation_off (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ} (hε : 0<ε) (hl : ∀e,l ≤ x e) (hr : ∀e,x e ≤ r) {s : ℝ} (hs : s∉Icc l r) :
    variation ε (tail μ x) (tail ν y) s=0 := by
  have hc : ¬common ε (tail μ x s) := by
    by_cases hsl : s<l
    · rw [below_all μ x s (fun e => hsl.trans_le (hl e))]
      unfold common
      intro h
      linarith [h.2]
    · have hrs : r<s := by simp only [Set.mem_Icc,not_and_or,not_le] at hs; exact hs.resolve_left hsl
      rw [above_all μ x s (fun e => (hr e).trans hrs.le)]
      exact fun h => not_le.mpr hε h.1
  simp [variation,hc]
lemma variation_integrable (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ} (hε : 0<ε) (hl : ∀e,l ≤ x e) (hr : ∀e,x e ≤ r) :
    Integrable (variation ε (tail μ x) (tail ν y)) := by
  have hi : IntegrableOn (variation ε (tail μ x) (tail ν y)) (Icc l r) := by
    apply Integrable.mono' (integrable_const (1/2:ℝ)) (variation_measurable μ ν x y ε).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (variation_bounds μ ν x y ε s).1]
      exact (variation_bounds μ ν x y ε s).2
  have he : (Icc l r).indicator (variation ε (tail μ x) (tail ν y))=variation ε (tail μ x) (tail ν y) := by
    ext s
    by_cases hs : s∈Icc l r
    · exact Set.indicator_of_mem hs _
    · rw [Set.indicator_of_notMem hs,variation_off μ ν x y hε hl hr hs]
  rw [←he]
  exact hi.integrable_indicator measurableSet_Icc
lemma variation_integral (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ} (hε : 0<ε) (hl : ∀e,l ≤ x e) (hr : ∀e,x e ≤ r) :
    (∫s in Icc l r,variation ε (tail μ x) (tail ν y) s)=
      ∫s,variation ε (tail μ x) (tail ν y) s := by
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    by_cases hs : s∈Icc l r
    · exact Set.indicator_of_mem hs _
    · rw [Set.indicator_of_notMem hs,variation_off μ ν x y hε hl hr hs]
end
end PlanarUnitDistances.TailVariation

namespace PlanarUnitDistances.ActualBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots SlotIntegration TailWindows
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype V] [Fintype E] [Fintype F]

omit [IsGalois ℚ K] [Fintype V] in
lemma snapshot_frequency (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E) (v : Place K S) (s : ℝ) :
    frequency μ (snapshot S z w src tgt u (v,s))=
      tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))) s := by
  simp only [frequency,snapshot,LevelStates.bit,TailWindows.tail,threshold,decide_eq_true_eq]
omit [IsGalois ℚ K] [Fintype V] [Fintype E] in
lemma snapshot_conditional (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (ν : Law F) (edge : F → E) (v : Place K S) (s : ℝ) :
    event ν (fun j => (snapshot S z w src tgt u (v,s)).1 (edge j)=true)=
      tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j)))) s := by
  simp only [snapshot,LevelStates.bit,TailWindows.tail,threshold,decide_eq_true_eq]

theorem star_upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (μ : Law E) (ν : Law F) (edge : F → E) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hsrc : ∀j,0<ν.val j → src (edge j)=x)
    (hu : ∀j,0<ν.val j → (z (src (edge j))-z (tgt (edge j)))*(w (src (edge j))-w (tgt (edge j)))=1)
    (hinj : ∀e f,0<ν.val e → 0<ν.val f → e≠f → z (tgt (edge e))≠z (tgt (edge f)))
    (hm : ∀e,z (src e)-z (tgt e)∈S)
    (hΔ : ∀e f,0<ν.val e → 0<ν.val f → e≠f →
      differenceProduct (z (src (edge e))-z (tgt (edge e))) (z (src (edge f))-z (tgt (edge f)))∈S) :
    avg (pair ν ν) (fun ef => ∫a,score ε μ ν edge (tgt ∘ edge) x good label ef.1 ef.2
      (snapshot S z w src tgt u a) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*((∑v : Place K S,∫s,WindowVariation.variation ε
      (tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
      (tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j))))) s)/(Module.finrank ℚ K:ℝ))+
    (2*(∫a,active ε μ good label x (snapshot S z w src tgt u a) ∂LevelScale.measure S))*
      event (pair ν ν) (fun ef => ef.1=ef.2) := by
  let d : F → K := fun j => z (src (edge j))-z (tgt (edge j))
  let f := truncatedPositive S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label
  have hpair (e f' : F) := score_eq_pairScore S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label
    (fun j => hm (edge j)) e f'
  simp_rw [hpair]
  apply ExpectedBudget.star_upper μ ν S d
    (fun v e => threshold (av K v) (z (src e)-z (tgt e)))
    (fun j hj => left_ne_zero_of_mul_eq_one (hu j hj))
    (fun e f he hf hef => by
      dsimp [d]
      rw [hsrc e he,hsrc f hf]
      exact fun h => hinj e f he hf hef (sub_right_injective h))
    hΔ hε hε' f
    (fun e f v => positive_integrable S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label e f v)
  · intro e f' he hf hef v s
    dsimp only [f,truncatedPositive]
    by_cases hs : s∈Icc (-radius K S v) (radius K S v)
    · rw [Set.indicator_of_mem hs]
      unfold positive
      rw [snapshot_frequency,snapshot_conditional]
      have hue := hu e he
      have huf := hu f' hf
      rw [hsrc e he] at hue
      rw [hsrc f' hf] at huf
      have hh := LevelSlotGeometry.positive_le_cap S z w u v s ε
        (tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
        (tail ν (fun j => threshold (av K v) (d j))) hε'
        (good (snapshot S z w src tgt u (v,s))) (label (snapshot S z w src tgt u (v,s)))
        x (tgt (edge e)) (tgt (edge f')) hue huf (hinj e f' he hf hef)
      convert hh using 1 <;> simp only [snapshot,d,Function.comp_apply,LevelStates.bit,threshold,hsrc e he,hsrc f' hf]
      congr 1
    · rw [Set.indicator_of_notMem hs]
      unfold PlaceScore.cap
      exact add_nonneg (mul_nonneg (PlaceScore.reward_bounds _ _ _ true).1 (PlaceScore.ind_nonneg _ _))
        (mul_nonneg (PlaceScore.reward_bounds _ _ _ false).1 (PlaceScore.ind_nonneg _ _))
  · intro v
    exact TailVariation.variation_integrable μ ν _ _ hε
      (fun e => (threshold_in_range K (hm e) v).1) (fun e => (threshold_in_range K (hm e) v).2)
  · intro e
    rw [←hpair]
    exact integrated_diagonal S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label e
end
end PlanarUnitDistances.ActualBudget

namespace PlanarUnitDistances.ActualBudgetIntegral
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudget FiniteLawIntegral
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype E] [Fintype F]

def commonVariation (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (a : Data V E) : ℝ :=
  if PlaceScore.common ε (frequency μ a) then StarScore.variation ν (fun j => a.1 (edge j)) else 0

omit [IsGalois ℚ K] in
lemma variation_integral (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    {ε : ℝ} (hε : 0<ε) (μ : Law E) (ν : Law F) (edge : F → E)
    (hm : ∀e,z (src e)-z (tgt e)∈S) :
    (∫a,commonVariation ε μ ν edge (snapshot S z w src tgt u a) ∂LevelScale.measure S)=
      (∑v : Place K S,∫s,WindowVariation.variation ε
        (TailWindows.tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
        (TailWindows.tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j))))) s)/
        (Module.finrank ℚ K:ℝ) := by
  have hB (a : Data V E) : |commonVariation ε μ ν edge a| ≤ 1/2 := by
    unfold commonVariation
    split_ifs
    · rw [abs_of_nonneg (StarScore.variation_nonneg _ _)]
      exact StarScore.variation_le_half _ _
    · norm_num
  rw [LevelScale.measure,FiniteLevels.integral_eq (LevelScale.weight K) _ _ _
    (measurable_value S z w src tgt u _) (1/2) (fun a => hB _)]
  have he (v : Place K S) (s : ℝ) :
      commonVariation ε μ ν edge (snapshot S z w src tgt u (v,s))=
      WindowVariation.variation ε
        (TailWindows.tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
        (TailWindows.tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j))))) s := by
    simp only [commonVariation,WindowVariation.variation,StarScore.variation,StarScore.frequency,
      snapshot_frequency,snapshot_conditional]
  simp_rw [he]
  change (Module.finrank ℚ K:ℝ)⁻¹*_=_
  rw [div_eq_inv_mul]
  congr 1
  apply sum_congr rfl
  intro v _
  exact TailVariation.variation_integral μ ν _ _ hε
    (fun e => (threshold_in_range K (hm e) v).1) (fun e => (threshold_in_range K (hm e) v).2)

theorem upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (μ : Law E) (ν : Law F) (edge : F → E) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hsrc : ∀j,0<ν.val j → src (edge j)=x)
    (hu : ∀j,0<ν.val j → (z (src (edge j))-z (tgt (edge j)))*(w (src (edge j))-w (tgt (edge j)))=1)
    (hinj : ∀e f,0<ν.val e → 0<ν.val f → e≠f → z (tgt (edge e))≠z (tgt (edge f)))
    (hm : ∀e,z (src e)-z (tgt e)∈S)
    (hΔ : ∀e f,0<ν.val e → 0<ν.val f → e≠f →
      differenceProduct (z (src (edge e))-z (tgt (edge e))) (z (src (edge f))-z (tgt (edge f)))∈S) :
    (∫a,avg (pair ν ν) (fun ef => score ε μ ν edge (tgt ∘ edge) x good label ef.1 ef.2
      (snapshot S z w src tgt u a)) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*(∫a,commonVariation ε μ ν edge (snapshot S z w src tgt u a) ∂LevelScale.measure S)+
    (2*(∫a,active ε μ good label x (snapshot S z w src tgt u a) ∂LevelScale.measure S))*
      event (pair ν ν) (fun ef => ef.1=ef.2) := by
  rw [integral_avg (pair ν ν) _ (fun ef => score_integrable S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label ef.1 ef.2),
    variation_integral S z w src tgt u hε μ ν edge hm]
  exact star_upper S z w src tgt u μ ν edge x good label hε hε' hsrc hu hinj hm hΔ
end
end PlanarUnitDistances.ActualBudgetIntegral

namespace PlanarUnitDistances.ActualFamilyBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral
open scoped Classical
noncomputable section
variable {K V E F B : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype E] [Fintype F] [Fintype B]

theorem upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (μ : Law E) (β : Law B) (ν : B → Law F) (edge : B → F → E) (x : B → V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hsrc : ∀b,0<β.val b → ∀j,0<(ν b).val j → src (edge b j)=x b)
    (hu : ∀b,0<β.val b → ∀j,0<(ν b).val j →
      (z (src (edge b j))-z (tgt (edge b j)))*(w (src (edge b j))-w (tgt (edge b j)))=1)
    (hinj : ∀b,0<β.val b → ∀e f,0<(ν b).val e → 0<(ν b).val f → e≠f →
      z (tgt (edge b e))≠z (tgt (edge b f)))
    (hm : ∀e,z (src e)-z (tgt e)∈S)
    (hΔ : ∀b,0<β.val b → ∀e f,0<(ν b).val e → 0<(ν b).val f → e≠f →
      differenceProduct (z (src (edge b e))-z (tgt (edge b e)))
        (z (src (edge b f))-z (tgt (edge b f)))∈S) :
    (∫a,avg β (fun b => avg (pair (ν b) (ν b)) (fun ef =>
      score ε μ (ν b) (edge b) (tgt ∘ edge b) (x b) good label ef.1 ef.2
        (snapshot S z w src tgt u a))) ∂LevelScale.measure S) ≤
      2*log 2+(1/20000000:ℝ)*(∫a,avg β (fun b =>
        commonVariation ε μ (ν b) (edge b) (snapshot S z w src tgt u a)) ∂LevelScale.measure S)+
      2*avg β (fun b => (∫a,active ε μ good label (x b) (snapshot S z w src tgt u a) ∂LevelScale.measure S)*
        event (pair (ν b) (ν b)) (fun ef => ef.1=ef.2)) := by
  rw [integral_avg β (fun b a => avg (pair (ν b) (ν b)) (fun ef =>
      score ε μ (ν b) (edge b) (tgt ∘ edge b) (x b) good label ef.1 ef.2
        (snapshot S z w src tgt u a))) (fun b => integrable_value S z w src tgt u (fun a => avg (pair (ν b) (ν b)) (fun ef =>
      score ε μ (ν b) (edge b) (tgt ∘ edge b) (x b) good label ef.1 ef.2 a))),
    integral_avg β (fun b a => commonVariation ε μ (ν b) (edge b) (snapshot S z w src tgt u a))
      (fun b => integrable_value S z w src tgt u (commonVariation ε μ (ν b) (edge b)))]
  have hh := avg_mono_support β (fun b hb => ActualBudgetIntegral.upper S z w src tgt u μ (ν b)
    (edge b) (x b) good label hε hε' (hsrc b hb) (hu b hb) (hinj b hb) hm (hΔ b hb))
  simp only [avg_add,avg_const,avg_smul] at hh
  convert hh using 1
  congr 1
  rw [←avg_smul]
  apply avg_congr
  intro b
  ring
end
end PlanarUnitDistances.ActualFamilyBudget

namespace PlanarUnitDistances.ActualRowBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral FiniteStarCoupling RareRows
open scoped Classical
noncomputable section
variable {K V P Q : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q]

theorem raw (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y))
    (hm : ∀p q,z (x p)-z (y q)∈S)
    (hΔ : ∀p q r,q≠r → differenceProduct (z (x p)-z (y q)) (z (x p)-z (y r))∈S) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreP ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VP σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*avg (left σ) (fun p => (∫a,active ε μ good label (x p) (s a) ∂LevelScale.measure S)*
      event (pair (row σ p) (row σ p)) (fun qq => qq.1=qq.2)) := by
  dsimp only
  let src : P×Q → V := fun pq => x pq.1
  let tgt : P×Q → V := fun pq => y pq.2
  let s := snapshot S z w src tgt u
  have hb := ActualFamilyBudget.upper S z w src tgt u μ (left σ) (row σ)
    (fun p q => (p,q)) x good label hε hε'
    (fun _ _ _ _ => rfl)
    (fun p hp q hq => hu p q (by rw [←row_weight σ p q]; exact mul_pos hp hq))
    (fun _ _ _ _ _ _ hqr => hy.ne hqr)
    (fun pq => hm pq.1 pq.2)
    (fun p _ q r _ _ hqr => hΔ p q r hqr)
  have hv (a : Data V (P×Q)) : avg (left σ) (fun p => commonVariation ε μ (row σ p) (fun q => (p,q)) a)=
      (if PlaceScore.common ε (ActualSlots.frequency μ a) then VP σ (fun p q => a.1 (p,q)) else 0) := by
    by_cases hc : PlaceScore.common ε (ActualSlots.frequency μ a)
    · simp only [commonVariation,hc,ite_true,VP]
    · simp only [commonVariation,hc,ite_false,avg_const]
  simp_rw [hv] at hb
  exact hb

theorem compressed_upper (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y))
    (hm : ∀p q,z (x p)-z (y q)∈S)
    (hΔ : ∀p q r,q≠r → differenceProduct (z (x p)-z (y q)) (z (x p)-z (y r))∈S)
    (hd : ∀p q,σ.val (p,q) ≤ d*(left σ).val p) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreP ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VP σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*d*avg (left σ) (fun p => ∫a,active ε μ good label (x p) (s a) ∂LevelScale.measure S) := by
  dsimp only
  have hb := raw S z w x y u μ σ good label hε hε' hu hy hm hΔ
  have hc := TemplateCollision.row_weighted σ
    (fun p => ∫a,active ε μ good label (x p)
      (snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u a) ∂LevelScale.measure S)
    (fun p => integral_nonneg (fun a => add_nonneg (RareScore.ind_nonneg _) (RareScore.ind_nonneg _))) hd
  dsimp only at hb
  linarith
end
end PlanarUnitDistances.ActualRowBudget

end OAI
