import Mathlib
import OAI.Combinatorics.KServer.AllocationCausality
import OAI.Combinatorics.KServer.JointExperiment

namespace OAI

/-! Exact structural identifications of the scheduled integral family and
bounds on the actual slack coefficients. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduleShape
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma eta_bound {δ ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hct : 0≤ct) (hctu : ct*20002≤1) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J) :
    ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/(1+Real.log (k+1))∈Set.Icc 0 1 := by
  have hel : 0<1+Real.log (k+1) := by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  constructor
  · exact div_nonneg (mul_nonneg hct (weight_nonneg δ _ _ (vector_nonneg cutoff δ P ω) t i)) hel.le
  · apply (div_le_iff₀ hel).mpr
    have h:=weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
      (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i
    have hmul:=mul_le_mul_of_nonneg_left h hct
    have hmul2:=mul_le_mul_of_nonneg_right hctu hel.le
    nlinarith

omit [Fintype R] in
lemma regular_data {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool) (t:ℕ)
    (hA:(activeSet (x t)).Nonempty)
    (hn:EpochSchedule.dominant (EpochSchedule.run x key t)=none)
    (hh:∀ i,1≤weight δ x key t i) :
    data hδ hδu C ell ct x key hx flags t=
      regular (activeSet (x t)) (flags t) (weight δ x key t) (fun i=>ct*weight δ x key t i/ell) hh := by
  unfold data
  dsimp only
  rw [ite_eq_left hA]
  split <;> simp_all

omit [Fintype R] in
lemma marked_data {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool) (t:ℕ) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (hu:0<sideRatio δ x key t) (hu1:sideRatio δ x key t≤1)
    (hh:∀ i≠o,1≤weight δ x key t i) :
    data hδ hδu C ell ct x key hx flags t=
      marked (activeSet (x t)) (flags t) o (weight δ x key t) (fun i=>ct*weight δ x key t i/ell)
        (sideRatio δ x key t) hu hu1 hh := by
  have hA:(activeSet (x t)).Nonempty:=⟨o,marked_active x key hx t ho⟩
  unfold data
  dsimp only
  rw [ite_eq_left hA]
  split <;> simp_all

end KServer.ScheduleShape

end


/- Deterministic scheduled-simplex payments use raw ranks before parameter edits. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledPayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation ScheduleShape
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma ordinary_regular {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hct : 0<ct) (hctu : ct*20002≤1) (hgap:700<C*ct) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1))
    (hA:(activeSet (vector cutoff δ P ω t)).Nonempty)
    (hB:(activeSet (vector cutoff δ P ω (t+1))).Nonempty)
    (hn:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=none) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (6*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  let h:=weight δ x ky t
  let h':=weight δ x ky (t+1)
  let f:=StarSimplex.flags P ω t
  let g:=StarSimplex.flags P ω (t+1)
  let A:=activeSet (x t)
  let B:=activeSet (x (t+1))
  have hel:0<ell := by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  change EpochSchedule.dominant (EpochSchedule.run x ky t)=none at hn
  have hn':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=none :=
    (ScheduleEdits.ordinary_mark x ky t he).trans hn
  have hh:∀ i,1≤h i := fun i=>weight_regular_one δ x ky t i (by simp [hn])
  have hh':∀ i,1≤h' i := fun i=>weight_regular_one δ x ky (t+1) i (by simp [hn'])
  have heta:∀ i,ct*h i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs t ω
  have heta':∀ i,ct*h' i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs (t+1) ω
  have ht:=regular_exp_sum δ x ky (vector_nonneg cutoff δ P ω) t
    (ScheduledSimplex.nonempty_mass x ky (vector_nonneg cutoff δ P ω) t hA) hn
  have hgp:2*(25+32*(2:ℝ))*(1+1)<C*ct := by linarith
  have hold:(d t ω).data=regular A f h (fun i=>ct*h i/ell) hh :=
    regular_data hδ hδu C ell ct x ky (vector_nonneg cutoff δ P ω) (StarSimplex.flags P ω) t hA hn hh
  have hnew:(d (t+1) ω).data=regular B g h' (fun i=>ct*h' i/ell) hh' :=
    regular_data hδ hδu C ell ct x ky (vector_nonneg cutoff δ P ω) (StarSimplex.flags P ω) (t+1) hB hn' hh'
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1 := fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉A,∀ r,f i r=false := fun i hi r=>flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉B,∀ r,g i r=false := fun i hi r=>flags_supported hδ hδu P (t+1) ω i hi r
  have ha:a t ω∈ChangingDomains.simplex A := StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':a (t+1) ω∈ChangingDomains.simplex B := StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hstep:a (t+1) ω=regularStep C ell ct A B g h h' hh hh' (d (t+1) ω).ranks (a t ω) :=
    CausalSimplex.regular_successor d t ω hA hB f g h h' hh hh' hC hel hct
      (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) ht hgp (fun ir=>(hp ir).1) hold hnew he
  have hpay:=regular_step_payment hA hB f g h h' hh hh' hC hel hct heta heta'
    (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) ht hgp (d (t+1) ω).ranks hp hf hg (a t ω) ha
  dsimp only at hpay
  rw [←hstep] at hpay
  have hv0: (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)=
      potential C ell (regular A f h (fun i=>ct*h i/ell) hh)
        (core (regular A f h (fun i=>ct*h i/ell) hh) (d (t+1) ω).ranks) (a t ω) := by
    rw [hold]
    exact value_eq C ell _ _ _ ha
  have hv1: (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)=
      potential C ell (regular B g h' (fun i=>ct*h' i/ell) hh')
        (core (regular B g h' (fun i=>ct*h' i/ell) hh') (d (t+1) ω).ranks) (a (t+1) ω) := by
    rw [hnew]
    exact value_eq C ell _ _ _ ha'
  have hc:=ScheduleEdits.regular_charge hδ hδu P key t ω he (d (t+1) ω).ranks hp univ
    (fun i _=>by rw [hn]; simp)
  change (∑ i,if h i=h' i then 0 else preparedInput A B g (d (t+1) ω).ranks i)≤
    40*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) at hc
  have hcn:0≤8*C*ell := by positivity
  have hc':=mul_le_mul_of_nonneg_left hc hcn
  rw [hv0,hv1]
  change (∑ i,core (d (t+1) ω).data (d (t+1) ω).ranks i)*_≤_
  rw [hnew]
  nlinarith


lemma ordinary_marked {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hct : 0<ct) (hctu : ct*20002≤1) (hgap:700<C*ct) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=some o)
    (hu:0<sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) t)
    (hu':0<sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let ell:=1+Real.log (k+1)
    let x:=vector cutoff δ P ω
    let ky:=fun s=>key s ω
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i∈univ.erase o,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
      2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t := by
  intro ell x ky d a
  let h:=weight δ x ky t
  let h':=weight δ x ky (t+1)
  let u:=sideRatio δ x ky t
  let u':=sideRatio δ x ky (t+1)
  let f:=StarSimplex.flags P ω t
  let g:=StarSimplex.flags P ω (t+1)
  let A:=activeSet (x t)
  let B:=activeSet (x (t+1))
  have hxn:=vector_nonneg cutoff δ P ω
  have hel:0<ell := by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  change EpochSchedule.dominant (EpochSchedule.run x ky t)=some o at ho
  have ho':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=some o :=
    (ScheduleEdits.ordinary_mark x ky t he).trans ho
  have hA:o∈A:=marked_active x ky hxn t ho
  have hB:B.Nonempty:=⟨o,marked_active x ky hxn (t+1) ho'⟩
  have hh:∀ i≠o,1≤h i := fun i hi=>weight_regular_one δ x ky t i (by rw [ho]; simpa [eq_comm] using hi)
  have hh':∀ i≠o,1≤h' i := fun i hi=>weight_regular_one δ x ky (t+1) i (by rw [ho']; simpa [eq_comm] using hi)
  have heta:∀ i,ct*h i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs t ω
  have heta':∀ i,ct*h' i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs (t+1) ω
  have hu1:u≤1:= (side_ratio_upper hδ hδu x ky hxn t ho).trans (by norm_num)
  have hu1':u'≤1:= (side_ratio_upper hδ hδu x ky hxn (t+1) ho').trans (by norm_num)
  have how:h o=u:=marked_weight δ x ky t o ho
  have how':h' o=u':=marked_weight δ x ky (t+1) o ho'
  have hside:∀ i∈A,i≠o→(1/2:ℝ)*(1+Real.log (1/u))≤h i :=
    fun i hi hio=>weight_side_lower hδ hδu x ky hxn t ho hi hio hu
  have ht:=side_exp_sum hδ hδu x ky hxn t ho
  have hgp:2*((25*(1/2:ℝ)+2+32*2)/(1/2))*(1+1)<C*ct := by linarith
  have hold:(d t ω).data=marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh :=
    marked_data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t o ho hu hu1 hh
  have hnew:(d (t+1) ω).data=marked B g o h' (fun i=>ct*h' i/ell) u' hu' hu1' hh' :=
    marked_data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1) o ho' hu' hu1' hh'
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1 := fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉A,∀ r,f i r=false := fun i hi r=>flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉B,∀ r,g i r=false := fun i hi r=>flags_supported hδ hδu P (t+1) ω i hi r
  have ha:a t ω∈ChangingDomains.simplex A := StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':a (t+1) ω∈ChangingDomains.simplex B := StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hstep:a (t+1) ω=markedStep C ell ct A B g o h h' u u' hu hu1 hu' hu1' hh hh' (d (t+1) ω).ranks (a t ω) :=
    CausalSimplex.marked_successor d t ω hA hB f g h h' hu hu1 hu' hu1' how hh hh' hC hel hct
      (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
      (by norm_num) hside ht hgp (fun ir=>(hp ir).1) hold hnew he
  have hcte:ct≤ell:=by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  have hote:ct*u/ell≤u:= (div_le_iff₀ hel).mpr (by nlinarith)
  have hote':ct*u'/ell≤u':= (div_le_iff₀ hel).mpr (by nlinarith)
  have hpay:=marked_step_payment hA hB f g h h' hu hu1 hu' hu1' how how' hh hh' hC hel hct heta heta'
    hote hote' (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
    (by norm_num) hside ht hgp (d (t+1) ω).ranks hp hf hg (a t ω) ha
  dsimp only at hpay
  rw [←hstep] at hpay
  have hv0: (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)=
      potential C ell (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh)
        (core (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh) (d (t+1) ω).ranks) (a t ω) := by
    rw [hold]
    exact value_eq C ell _ _ _ ha
  have hv1: (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)=
      potential C ell (marked B g o h' (fun i=>ct*h' i/ell) u' hu' hu1' hh')
        (core (marked B g o h' (fun i=>ct*h' i/ell) u' hu' hu1' hh') (d (t+1) ω).ranks) (a (t+1) ω) := by
    rw [hnew]
    exact value_eq C ell _ _ _ ha'
  have hc:=ScheduleEdits.regular_charge hδ hδu P key t ω he (d (t+1) ω).ranks hp (univ.erase o)
    (fun i hi=>by rw [ho]; simpa [eq_comm] using (mem_erase.mp hi).1)
  have huq:=ScheduleEdits.side_ratio_charge hδ hδu x ky hxn t he o ho
    (preparedInput A B g (d (t+1) ω).ranks)
    (ScheduleEdits.prepared_input_bound hδ hδu P A (t+1) ω (d (t+1) ω).ranks hp)
  have hc':=mul_le_mul_of_nonneg_left hc (by positivity : 0≤8*C*ell)
  have huq':=mul_le_mul_of_nonneg_left huq (by positivity : 0≤24*C*ell)
  rw [hv0,hv1]
  change (∑ i,core (d (t+1) ω).data (d (t+1) ω).ranks i)*_≤_
  rw [hnew]
  nlinarith

end KServer.ScheduledPayment

end


/-! Actual singleton/side-free transitions: their cost is paid by changed
flags, not by a fresh charge to the persistent dominant mass. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SingletonPayment
attribute [local instance] Classical.propDecidable
open SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

def point (o:J) : J→ℝ := fun i=>if i=o then 1 else 0

lemma point_mem (o:J) {A:Finset J} (ho:o∈A) : point o∈ChangingDomains.simplex A := by
  refine ⟨fun i=>by unfold point; split_ifs <;> norm_num,?_,?_⟩
  · simp [point,ite_eq_left (show A.Nonempty from ⟨o,ho⟩)]
  · intro i hi
    have hn:i≠o:=fun he=>hi (he ▸ ho)
    simp [point,hn]

lemma singleton_eq {o:J} {a:J→ℝ} (ha:a∈ChangingDomains.simplex {o}) : a=point o := by
  have hz:∀ i,i≠o→a i=0:=fun i hi=>ha.2.2 i (by simpa using hi)
  have hs:(∑ i,a i)=a o := sum_eq_single o (fun i _ hi=>hz i hi) (by simp)
  have ho:a o=1:=by simpa only [hs,singleton_nonempty,ite_true] using ha.2.1
  funext i
  by_cases hi:i=o
  · subst i; simp [point,ho]
  · simp [point,hi,hz i hi]

lemma zero_value (C ell:ℝ) (d:Data J R) (p:J×R→ℝ) (a:J→ℝ)
    (hz:d.zeroPotential=true) : (family C ell).value d p a=0 := by
  simp [AdaptiveMinimization.Family.value,family,coefficient,hz]

lemma base_value (C ell:ℝ) (d:Data J R) (p:J×R→ℝ) :
    (family C ell).value d p d.base=0 := by
  simp [AdaptiveMinimization.Family.value,family,coefficient,K,Z]

lemma core_value_bound (C ell:ℝ) (d:Data J R) (p:J×R→ℝ) (a:J→ℝ) {L:ℝ}
    (hc:∀ ir,|coefficient C ell d a ir|≤L) (hp:∀ ir,0≤p ir) :
    |(family C ell).value d p a|≤L*(∑ i,core d p i) := by
  change |0+∑ ir,coefficient C ell d a ir*p ir|≤_
  rw [zero_add]
  calc _≤∑ ir,|coefficient C ell d a ir*p ir|:=abs_sum_le_sum_abs _ _
       _≤∑ ir:J×R,L*(if d.flags ir.1 ir.2 then p ir else 0) := by
        apply sum_le_sum
        intro ir _
        by_cases hf:d.flags ir.1 ir.2=true
        · simp only [hf,ite_true,abs_mul,abs_of_nonneg (hp ir)]
          exact mul_le_mul_of_nonneg_right (hc ir) (hp ir)
        · have hz:coefficient C ell d a ir=0:=by simp [coefficient,hf]
          simp [hz,hf]
       _= _ := by rw [←mul_sum,Fintype.sum_prod_type]; rfl

lemma candidate_singleton (C ell:ℝ) (old new:Data J R) (o:J)
    (hA:old.active={o}) (p:J×R→ℝ) (a:J→ℝ) :
    CausalSimplex.candidate C ell old new p a=
      ChangingDomains.transposeSimplex new.active (∑ i,core (CausalSimplex.prepared old new) p i) (point o) := by
  have hm := (family C ell).update_mem (CausalSimplex.prepared old new) p
    (∑ i,core (CausalSimplex.prepared old new) p i) a
  change CausalSimplex.prepare C ell old new p a∈ChangingDomains.simplex old.active at hm
  rw [hA] at hm
  exact congrArg (ChangingDomains.transposeSimplex new.active _) (singleton_eq hm)

lemma old_singleton {C ell L:ℝ} (hL:0≤L) (old new:CausalSimplex.Input J R)
    (o:J) (hA:old.data.active={o}) (ho:o∈new.data.active)
    (he:old.epoch=new.epoch) (hz:old.data.zeroPotential=true)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (hf:∀ i∉old.data.active,∀ r,old.data.flags i r=false)
    (hg:∀ i∉new.data.active,∀ r,new.data.flags i r=false)
    (hbase:(family C ell).value new.data p (point o)=0)
    (hcoeff:∀ a,a∈ChangingDomains.simplex new.data.active→∀ ir,|coefficient C ell new.data a ir|≤L)
    (a:J→ℝ) (ha:a∈ChangingDomains.simplex old.data.active) :
    let S:=∑ i,core new.data p i
    let b:=CausalSimplex.move C ell old new p a
    let c:=(family C ell).update new.data p S b
    S*ChangingDomains.variation c a≤
      (family C ell).value old.data p a-(family C ell).value new.data p c+
      (L+2)*ChangingDomains.changedFlags old.data.flags new.data.flags := by
  intro S b c
  have hae:a=point o:=singleton_eq (hA ▸ ha)
  have hB:new.data.active.Nonempty:=⟨o,ho⟩
  let T:=∑ i,core (CausalSimplex.prepared old.data new.data) p i
  have hcand:=candidate_singleton C ell old.data new.data o hA p a
  have hcm:CausalSimplex.candidate C ell old.data new.data p a∈ChangingDomains.simplex new.data.active := by
    rw [hcand]
    unfold ChangingDomains.transposeSimplex
    split_ifs
    · exact ChangingDomains.canonical_mem _
    · exact point_mem o ho
  have hb:b=ChangingDomains.transposeSimplex new.data.active T (point o) := by
    change CausalSimplex.move C ell old new p a=_
    rw [CausalSimplex.move,ite_eq_left he,ite_eq_left hcm,hcand]
  have hbm:b∈ChangingDomains.simplex new.data.active:=CausalSimplex.move_mem C ell old new p a
  have hSn:0≤S:=sum_nonneg fun i _=>ChangingDomains.core_nonneg (fun i r=>(hp (i,r)).1) i
  have hpay: S*ChangingDomains.variation c b≤
      (family C ell).value new.data p b-(family C ell).value new.data p c :=
    (family C ell).update_payment new.data p S hbm
  have hvold:=zero_value C ell old.data p a hz
  rw [hvold]
  by_cases ht:T=0
  · have herr:= (ChangingDomains.synthetic_errors (fun i r=>hp (i,r)) hf hg).2
    have hdiff:=le_of_abs_le ((total_variation_bound (core new.data p)
      (core (CausalSimplex.prepared old.data new.data) p)).trans herr)
    change S-T≤ChangingDomains.changedFlags old.data.flags new.data.flags at hdiff
    rw [ht,sub_zero] at hdiff
    have hv: (family C ell).value new.data p b≤L*S :=
      (le_abs_self _).trans (core_value_bound C ell new.data p b (hcoeff b hbm) (fun ir=>(hp ir).1))
    have htri:=mul_le_mul_of_nonneg_left (ChangingDomains.variation_triangle c b a) hSn
    have hvar:=mul_le_mul_of_nonneg_left (ChangingDomains.simplex_variation hbm ha) hSn
    have hmul:=mul_le_mul_of_nonneg_left hdiff (show 0≤L+2 by linarith)
    nlinarith
  · have hba:b=a:=by rw [hb,ChangingDomains.transposeSimplex,ite_eq_right ht,hae]
    rw [hba] at hpay
    rw [hae,hbase] at hpay
    rw [hae]
    have hfn:0≤ChangingDomains.changedFlags old.data.flags new.data.flags := by
      apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro r _
      split_ifs <;> norm_num
    nlinarith [mul_nonneg (show 0≤L+2 by linarith) hfn]

end KServer.SingletonPayment

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SingletonPayment
attribute [local instance] Classical.propDecidable
open SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

omit [Fintype R] in
lemma marked_point_potential (A : Finset J) (f : J→R→Bool) (o:J) (h eta:J→ℝ)
    {u:ℝ} (hu:0<u) (hu1:u≤1) (hh:∀ i≠o,1≤h i) (C ell:ℝ) (v:J→ℝ) :
    potential C ell (marked A f o h eta u hu hu1 hh) v (point o)=0 := by
  simp [potential,marked,SimplexAnalytic.primitive,point]

lemma new_singleton {A:Finset J} {o:J} (hoA:o∈A)
    (f g:J→R→Bool) (h:J→ℝ) {u:ℝ} (hu:0<u) (hu1:u≤1)
    (ho:h o=u) (hh:∀ i≠o,1≤h i)
    {C ell ct ηmax Cexp c:ℝ} (hC:0<C) (hl:0<ell) (hc:0<ct)
    (he:∀ i,ct*h i/ell∈Set.Icc 0 1)
    (hmax:∀ i∈A,ct*h i/ell≤ηmax) (hCexp:0≤Cexp)
    (hsideC:0<c) (hsideC1:c≤1)
    (hside:∀ i∈A,i≠o→c*(1+Real.log (1/u))≤h i)
    (htail:∑ i∈A.erase o,Real.exp (-h i)≤Cexp*u)
    (hgap:2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (hf:∀ i∉A,∀ r,f i r=false) (hg:∀ i∉({o}:Finset J),∀ r,g i r=false)
    (a:J→ℝ) (ha:a∈ChangingDomains.simplex A) :
    let d0:=marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh
    (∑ i,ChangingDomains.core g (fun i r=>p (i,r)) i)*ChangingDomains.variation (point o) a≤
      potential C ell d0 (core d0 p) a+(13*C*ell+4)*ChangingDomains.changedFlags f g := by
  intro d0
  let B:=({o}:Finset J)
  let v:=preparedInput A B g p
  let d1:=marked A (preparedFlags A B g) o h (fun i=>ct*h i/ell) u hu hu1 hh
  let a1:=markedPrepare C ell ct A B g o h u hu hu1 hh p a
  let a2:=markedTransport C ell ct A B g o h u hu hu1 hh p a
  let S:=∑ i,v i
  let T:=∑ i,ChangingDomains.core g (fun i r=>p (i,r)) i
  have hv:∀ i,0≤v i:=fun i=>ChangingDomains.core_nonneg (fun i r=>(hp (i,r)).1) i
  have hSn:0≤S:=sum_nonneg fun i _=>hv i
  have hB:B.Nonempty:=singleton_nonempty o
  have ha1:a1∈ChangingDomains.simplex A := (family C ell).update_mem d1 p S a
  have ha2:a2∈ChangingDomains.simplex B:=marked_transport_mem hoA hB g h hu hu1 ho hh
    hC hl hc hmax hCexp hsideC hsideC1 hside htail hgap p (fun ir=>(hp ir).1) a ha
  have hae:a2=point o:=singleton_eq ha2
  have ht:potential C ell d0 v a2=potential C ell d0 v a1 :=
    marked_transpose_value A B f o h (fun i=>ct*h i/ell) hu hu1 hh C ell v a1 hv
  have hz:potential C ell d0 v a2=0 := by
    rw [hae]
    exact marked_point_potential A f o h (fun i=>ct*h i/ell) hu hu1 hh C ell v
  have hpay:S*ChangingDomains.variation a1 a≤potential C ell d0 v a := by
    have hp1:=literal_update_payment C ell d1 p S ha
    change S*ChangingDomains.variation a1 a≤potential C ell d0 v a-potential C ell d0 v a1 at hp1
    rw [←ht,hz,sub_zero] at hp1
    exact hp1
  have herr:=ChangingDomains.synthetic_errors (fun i r=>hp (i,r)) hf hg
  have hi:=marked_input_bound A ⟨o,hoA⟩ f o h (fun i=>ct*h i/ell) hu hu1 hh he hC.le hl.le
    (B:=core d0 p) (B':=v) ha
  have hdelta:=mul_le_mul_of_nonneg_left herr.1 (by positivity : 0≤13*C*ell)
  have hzero:S*ChangingDomains.variation a2 a1=0:=ChangingDomains.transposeSimplex_payment B S a1
  have hST:S≤T:=sub_nonneg.mp (ChangingDomains.synthetic_total (A:=A) (B:=B) (g:=g) (fun i r=>(hp (i,r)).1))
  have hdiff:T-S≤ChangingDomains.changedFlags f g :=
    (le_abs_self _).trans ((total_variation_bound (ChangingDomains.core g (fun i r=>p (i,r))) v).trans herr.2)
  have hm:=ChangingDomains.prepared_weight_comparison ha ha1 ha2 hSn hST hzero (a₃:=a2)
  rw [ChangingDomains.variation_self,mul_zero,add_zero,hae] at hm
  have hlow:=neg_le_of_abs_le hi
  change -(13*C*ell*ChangingDomains.variation (core d0 p) v)≤
    potential C ell d0 (core d0 p) a-potential C ell d0 v a at hlow
  change 13*C*ell*ChangingDomains.variation (core d0 p) v≤
    13*C*ell*ChangingDomains.changedFlags f g at hdelta
  change T*ChangingDomains.variation (point o) a≤_
  nlinarith

end KServer.SingletonPayment

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledPayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation ScheduleShape SingletonPayment
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

omit [Fintype Ω] [Fintype R] in
lemma marked_zero_flag {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool)
    (t:ℕ) (o:J) (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (hu:sideRatio δ x key t=0) :
    (data hδ hδu C ell ct x key hx flags t).zeroPotential=true := by
  have hA:(activeSet (x t)).Nonempty:=⟨o,marked_active x key hx t ho⟩
  unfold data
  dsimp only
  rw [ite_eq_left hA]
  split <;> simp_all [zeroData]

omit [Fintype Ω] in
lemma marked_point_value {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool)
    (t:ℕ) (o:J) (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (p:J×R→ℝ) :
    (family C ell).value (data hδ hδu C ell ct x key hx flags t) p (point o)=0 := by
  by_cases hu:0<sideRatio δ x key t
  · have hu1:sideRatio δ x key t≤1:=(side_ratio_upper hδ hδu x key hx t ho).trans (by norm_num)
    have hh:∀ i≠o,1≤weight δ x key t i:=fun i hi=>weight_regular_one δ x key t i (by rw [ho]; simpa [eq_comm] using hi)
    rw [marked_data hδ hδu C ell ct x key hx flags t o ho hu hu1 hh]
    exact base_value C ell _ p
  · have hz:sideRatio δ x key t=0:=le_antisymm (le_of_not_gt hu) (side_ratio_nonneg δ x key hx t)
    exact zero_value C ell _ p _ (marked_zero_flag hδ hδu C ell ct x key hx flags t o ho hz)

lemma ordinary_old_zero {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0≤C) (hct:0≤ct) (hctu:ct*20002≤1) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=some o)
    (hu:sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) t=0) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (13*C*ell+2)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  have hxn:=vector_nonneg cutoff δ P ω
  have hel:0≤ell:=by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  have ho':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=some o:=
    (ScheduleEdits.ordinary_mark x ky t he).trans ho
  have hA:(d t ω).data.active={o}:=(data_active hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t).trans
    (marked_zero_singleton hδ x ky hxn t ho hu)
  have hoB:o∈(d (t+1) ω).data.active:=by
    change o∈(data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)).active
    rw [data_active]
    exact marked_active x ky hxn (t+1) ho'
  have hz:(d t ω).data.zeroPotential=true:=marked_zero_flag hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t o ho hu
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉(d t ω).data.active,∀ r,(d t ω).data.flags i r=false:=by
    change ∀ i∉(data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t).active,∀ r,_=false
    simp only [data_active]
    intro i hi r
    change (data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) _).flags i r=false
    rw [data_flags]
    exact flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉(d (t+1) ω).data.active,∀ r,(d (t+1) ω).data.flags i r=false:=by
    change ∀ i∉(data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)).active,∀ r,_=false
    simp only [data_active]
    intro i hi r
    change (data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) _).flags i r=false
    rw [data_flags]
    exact flags_supported hδ hδu P (t+1) ω i hi r
  have hcoeff:∀ b,b∈ChangingDomains.simplex (d (t+1) ω).data.active→∀ ir,|coefficient C ell (d (t+1) ω).data b ir|≤13*C*ell := by
    intro b hb
    have hm:(d (t+1) ω).data.active=activeSet (x (t+1)):=data_active hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)
    exact ScheduledSlope.actual_bound hδ hδu hC hct hctu hk P key hs (t+1) ω b (hm ▸ hb)
  have hb: (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (point o)=0 :=
    marked_point_value hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1) o ho' _
  have ha:a t ω∈ChangingDomains.simplex (d t ω).data.active:=CausalSimplex.run_mem C ell d t ω
  have hpay:=old_singleton (by positivity : 0≤13*C*ell) (d t ω) (d (t+1) ω) o hA hoB he hz _ hp hf hg hb hcoeff _ ha
  have hsuc:a (t+1) ω=(family C ell).update (d (t+1) ω).data (d (t+1) ω).ranks
      (CausalSimplex.mass (d (t+1) ω))
      (CausalSimplex.move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (a t ω)) :=
    CausalSimplex.run_successor C ell d t ω
  rw [hsuc]
  have hf0:(d t ω).data.flags=StarSimplex.flags P ω t:=data_flags hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t
  have hf1:(d (t+1) ω).data.flags=StarSimplex.flags P ω (t+1):=data_flags hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)
  simpa only [CausalSimplex.mass,hf0,hf1] using hpay


lemma ordinary_new_zero {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0<ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=some o)
    (hu:0<sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) t)
    (hu':sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) (t+1)=0) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (13*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  let h:=weight δ x ky t
  let u:=sideRatio δ x ky t
  let f:=StarSimplex.flags P ω t
  let g:=StarSimplex.flags P ω (t+1)
  let A:=activeSet (x t)
  have hxn:=vector_nonneg cutoff δ P ω
  have hel:0<ell:=by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  change EpochSchedule.dominant (EpochSchedule.run x ky t)=some o at ho
  have ho':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=some o:=
    (ScheduleEdits.ordinary_mark x ky t he).trans ho
  have hA:o∈A:=marked_active x ky hxn t ho
  have hB:activeSet (x (t+1))={o}:=marked_zero_singleton hδ x ky hxn (t+1) ho' hu'
  have hh:∀ i≠o,1≤h i:=fun i hi=>weight_regular_one δ x ky t i (by rw [ho]; simpa [eq_comm] using hi)
  have heta:∀ i,ct*h i/ell∈Set.Icc 0 1:=eta_bound hδ hδu hct.le hctu hk P key hs t ω
  have hu1:u≤1:=(side_ratio_upper hδ hδu x ky hxn t ho).trans (by norm_num)
  have how:h o=u:=marked_weight δ x ky t o ho
  have hside:∀ i∈A,i≠o→(1/2:ℝ)*(1+Real.log (1/u))≤h i:=
    fun i hi hio=>weight_side_lower hδ hδu x ky hxn t ho hi hio hu
  have ht:=side_exp_sum hδ hδu x ky hxn t ho
  have hgp:2*((25*(1/2:ℝ)+2+32*2)/(1/2))*(1+1)<C*ct:=by linarith
  have hold:(d t ω).data=marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh :=
    marked_data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t o ho hu hu1 hh
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉A,∀ r,f i r=false:=fun i hi r=>flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉({o}:Finset J),∀ r,g i r=false:=by
    rw [←hB]
    exact fun i hi r=>flags_supported hδ hδu P (t+1) ω i hi r
  have ha:a t ω∈ChangingDomains.simplex A:=StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':a (t+1) ω∈ChangingDomains.simplex {o}:=by
    rw [←hB]
    exact StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hae:a (t+1) ω=point o:=singleton_eq ha'
  have hpay:=new_singleton hA f g h hu hu1 how hh hC hel hct heta
    (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
    (by norm_num) hside ht hgp (d (t+1) ω).ranks hp hf hg (a t ω) ha
  dsimp only at hpay
  have hv0:(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)=
      potential C ell (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh)
        (core (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh) (d (t+1) ω).ranks) (a t ω) := by
    rw [hold]
    exact value_eq C ell _ _ _ ha
  have hv1:(family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)=0:=
    zero_value C ell _ _ _ (marked_zero_flag hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1) o ho' hu')
  have hm:CausalSimplex.mass (d (t+1) ω)=∑ i,ChangingDomains.core g (fun i r=>(d (t+1) ω).ranks (i,r)) i := by
    have hgf:(d (t+1) ω).data.flags=g:=data_flags hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)
    simp only [CausalSimplex.mass,core,hgf,ChangingDomains.core]
  rw [hv0,hv1,sub_zero,hae,hm]
  exact hpay

end KServer.ScheduledPayment

end


/-! The complete ordinary/wholesale simplex payment for the literal schedule.
All charges below are computed by the actual switches, never supplied by a
finite-law hypothesis. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledPayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation ScheduleShape SingletonPayment
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

omit [Fintype Ω] [DecidableEq J] [Fintype R] in
lemma empty_total (x:J→ℝ) (hx:∀ i,0≤x i) (hA:¬(activeSet x).Nonempty) : EpochSchedule.total x=0 := by
  apply sum_eq_zero
  intro i _
  apply le_antisymm _ (hx i)
  by_contra hn
  exact hA ⟨i,(mem_activeSet x i).mpr (lt_of_not_ge hn)⟩

omit [Fintype Ω] [DecidableEq J] [Fintype R] in
lemma positive_active (x:J→ℝ) (hx:∀ i,0≤x i) (hp:0<EpochSchedule.total x) : (activeSet x).Nonempty := by
  by_contra hn
  rw [empty_total x hx hn] at hp
  exact (lt_irrefl _ hp)

omit [Fintype Ω] [DecidableEq J] [Fintype R] in
lemma ordinary_nonempty (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (t:ℕ)
    (he:epoch x key t=epoch x key (t+1)) :
    (activeSet (x t)).Nonempty ↔ (activeSet (x (t+1))).Nonempty := by
  have hm:=ScheduleEdits.ordinary_mass x key t he
  constructor
  · intro ha
    have h:=ScheduledSimplex.nonempty_mass x key hx t ha
    have hb:=(mass_accuracy x key hx (t+1)).1
    rw [hm] at hb
    exact positive_active _ (hx (t+1)) (by linarith)
  · intro hb
    have h:=ScheduledSimplex.nonempty_mass x key hx (t+1) hb
    rw [hm] at h
    have ha:=(mass_accuracy x key hx t).1
    exact positive_active _ (hx t) (by linarith)

omit [Fintype Ω] [DecidableEq J] in
lemma flags_nonneg (f g:J→R→Bool) : 0≤ChangingDomains.changedFlags f g := by
  apply sum_nonneg
  intro i _
  apply sum_nonneg
  intro r _
  split_ifs <;> norm_num

omit [Fintype Ω] [Fintype R] [DecidableEq J] in
lemma side_charge_nonneg (δ:ℝ) (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (t:ℕ) :
    0≤CoarseSide.charge δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key) t := by
  unfold CoarseSide.charge
  split_ifs
  · exact add_nonneg (CoarseSide.side_nonneg (hx t) _) (CoarseSide.side_nonneg (hx (t+1)) _)
  · rfl

def expense (C ell δ:ℝ) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) : ℝ :=
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  (26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
  320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
  2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t+
  (520*C*ell+80)*EpochSchedule.wholesale (x t) (x (t+1)) (ky t) (ky (t+1)) (EpochSchedule.run x ky t)

omit [DecidableEq J] in
lemma expense_nonneg {C ell:ℝ} (hC:0≤C) (hel:0≤ell) (δ:ℝ) (P:J→R→FilteredRanks w)
    (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) : 0≤expense C ell δ P key t ω := by
  have hf:=flags_nonneg (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
  have hc:0≤∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
    sum_nonneg fun i _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1))
  have hu:=side_charge_nonneg δ (vector cutoff δ P ω) (fun s=>key s ω) (vector_nonneg cutoff δ P ω) t
  have hw:0≤EpochSchedule.wholesale (vector cutoff δ P ω t) (vector cutoff δ P ω (t+1)) (key t ω) (key (t+1) ω)
      (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t) := by
    unfold EpochSchedule.wholesale
    split_ifs
    · exact add_nonneg (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t))
        (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω (t+1)))
    · rfl
  unfold expense
  positivity

lemma mass_bound {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ) (P:J→R→FilteredRanks w)
    (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    CausalSimplex.mass (StarSimplex.input hδ hδu C ell ct P key t ω)≤40*EpochSchedule.total (vector cutoff δ P ω t) := by
  simp only [CausalSimplex.mass,core,StarSimplex.input,data_flags,StarSimplex.flags]
  change (∑ i,∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0)≤40*(∑ i,vector cutoff δ P ω t i)
  rw [mul_sum]
  exact sum_le_sum fun i _=>ScheduleEdits.raw_core_bound hδ hδu (P i) t ω
    (fun r=>(P i r).p t ω) (fun r=>(P i r).range t ω)

lemma wholesale_payment {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0≤C) (hct:0≤ct) (hctu:ct*20002≤1) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t≠
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+expense C ell δ P key t ω := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  have hel:0≤ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  have ha:=StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':=StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hm:=mass_bound hδ hδu C ell ct P key (t+1) ω
  have hmove: CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤80*EpochSchedule.total (x (t+1)) := by
    have hn:0≤CausalSimplex.mass (d (t+1) ω):=by
      apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro r _
      split_ifs
      · exact ((P i r).range (t+1) ω).1
      · rfl
    have hh:=mul_le_mul_of_nonneg_left (ChangingDomains.simplex_variation ha' ha) hn
    nlinarith
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have h₀:=neg_le_of_abs_le (ScheduledEndpoint.actual_bound hδ hδu hC hct hctu hk P key hs t ω _ hp _ ha)
  have h₁:=le_of_abs_le (ScheduledEndpoint.actual_bound hδ hδu hC hct hctu hk P key hs (t+1) ω _ hp _ ha')
  have hn:CoarseSide.epochReset x ky t:=Classical.not_not.mp (fun hh=>he ((epoch_same_iff x ky t).mpr hh))
  have wh:EpochSchedule.wholesale (x t) (x (t+1)) (ky t) (ky (t+1)) (EpochSchedule.run x ky t)=
      EpochSchedule.total (x t)+EpochSchedule.total (x (t+1)):=ite_eq_left hn
  have hcharges:0≤(26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
      2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t := by
    have hf:=flags_nonneg (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
    have hc:0≤∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
      sum_nonneg fun i _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1))
    have hu:=side_charge_nonneg δ x ky (vector_nonneg cutoff δ P ω) t
    positivity
  unfold expense
  change _≤_+(_+(_)*EpochSchedule.wholesale (x t) (x (t+1)) (ky t) (ky (t+1)) (EpochSchedule.run x ky t))
  rw [wh]
  have hx0:0≤EpochSchedule.total (x t):=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t)
  nlinarith

omit [DecidableEq J] in
lemma expense_lower {C ell:ℝ} (hC:0≤C) (hel:0≤ell) (δ:ℝ) (P:J→R→FilteredRanks w)
    (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    (26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
      2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput (vector cutoff δ P ω) (fun s=>key s ω))
        (CoarseSide.epochReset (vector cutoff δ P ω) (fun s=>key s ω)) t ≤ expense C ell δ P key t ω := by
  have hw:0≤EpochSchedule.wholesale (vector cutoff δ P ω t) (vector cutoff δ P ω (t+1)) (key t ω) (key (t+1) ω)
      (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t) := by
    unfold EpochSchedule.wholesale
    split_ifs
    · exact add_nonneg (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t))
        (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω (t+1)))
    · rfl
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) hw)

lemma payment {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0<ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+expense C ell δ P key t ω := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  have hx:=vector_nonneg cutoff δ P ω
  have hel:0≤ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  by_cases he:epoch x ky t=epoch x ky (t+1)
  · have hf:=flags_nonneg (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
    have hc:0≤∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
      sum_nonneg fun i _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1))
    have hu:=side_charge_nonneg δ x ky hx t
    have hl:=expense_lower hC.le hel δ P key t ω
    have hcn:0≤C*ell:=mul_nonneg hC.le hel
    by_cases hA:(activeSet (x t)).Nonempty
    · have hB:=(ordinary_nonempty x ky hx t he).mp hA
      cases ho:EpochSchedule.dominant (EpochSchedule.run x ky t) with
      | none =>
        have hp:=ordinary_regular hδ hδu hC hct hctu hgap hk P key hs t ω he hA hB ho
        change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
          (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_+_ at hp
        change _+_+2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t≤_ at hl
        nlinarith [mul_nonneg hcn hf,mul_nonneg hcn hu]
      | some o =>
        by_cases hu0:sideRatio δ x ky t=0
        · have hp:=ordinary_old_zero hδ hδu hC.le hct.le hctu hk P key hs t ω he o ho hu0
          change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
            (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
          change _+_+2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t≤_ at hl
          nlinarith [mul_nonneg hcn hf,mul_nonneg hcn hc,mul_nonneg hcn hu]
        · have hup:0<sideRatio δ x ky t:=lt_of_le_of_ne (side_ratio_nonneg δ x ky hx t) (Ne.symm hu0)
          by_cases hu1:sideRatio δ x ky (t+1)=0
          · have hp:=ordinary_new_zero hδ hδu hC hct hctu hgap hk P key hs t ω he o ho hup hu1
            change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
              (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
            change _+_+2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t≤_ at hl
            nlinarith [mul_nonneg hcn hf,mul_nonneg hcn hc,mul_nonneg hcn hu]
          · have hup':0<sideRatio δ x ky (t+1):=lt_of_le_of_ne (side_ratio_nonneg δ x ky hx (t+1)) (Ne.symm hu1)
            have hp:=ordinary_marked hδ hδu hC hct hctu hgap hk P key hs t ω he o ho hup hup'
            have hs' : (∑ i∈univ.erase o,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))≤
                ∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
              sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1)))
            have hmul:=mul_le_mul_of_nonneg_left hs' (show 0≤320*C*ell by positivity)
            change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
              (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_+_+_ at hp
            linarith
    · have hB:¬(activeSet (x (t+1))).Nonempty:=fun hh=>hA ((ordinary_nonempty x ky hx t he).mpr hh)
      have hz (s:ℕ) (hn:¬(activeSet (x s)).Nonempty) : (d s ω).data.zeroPotential=true := by
        change (data hδ hδu C ell ct x ky hx (StarSimplex.flags P ω) s).zeroPotential=true
        unfold data
        dsimp only
        rw [ite_eq_right hn]
        rfl
      have hm:CausalSimplex.mass (d (t+1) ω)=0 := by
        have hm:=mass_bound hδ hδu C ell ct P key (t+1) ω
        rw [empty_total _ (hx (t+1)) hB,mul_zero] at hm
        apply le_antisymm hm
        apply sum_nonneg
        intro i _
        exact ChangingDomains.core_nonneg (fun i r=>((P i r).range (t+1) ω).1) _
      rw [hm,zero_mul,zero_value C ell _ _ _ (hz t hA),zero_value C ell _ _ _ (hz (t+1) hB),sub_self,zero_add]
      exact expense_nonneg hC.le hel δ P key t ω
  · exact wholesale_payment hδ hδu hC.le hct.le hctu hk P key hs t ω he

end KServer.ScheduledPayment

end


/-! Literal coarse schedule bills and their finite-experiment budgets. The
right sides use drift after conditioning, never raw posterior variation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def drift (P:R→ FilteredRanks w) (N:ℕ):ℝ:=
  ∑ t∈range N,avg w (fun ω=>∑ r,|(P r).p (t+1) ω-(P r).before (t+1) ω|)
def inventory (P:R→ FilteredRanks w) (N:ℕ):ℝ:=drift P N+Fintype.card R
def flat (P:J→ R→ FilteredRanks w):J×R→ FilteredRanks w:=fun ir=> P ir.1 ir.2

def flags (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
def active (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  ∑ i,CoarseSchedule.charge (CoarseProcess.active cutoff ds (P i) ω t)
    (CoarseProcess.active cutoff ds (P i) ω (t+1))
def parentCharge (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  CoarseProcess.relativeCharge dp (clipped cutoff dp Q) t ω
def wholesale (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  EpochSchedule.wholesale (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
    (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t)
def sideRefresh (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  CoarseSide.charge ds (CoarseSide.sideInput (vector cutoff ds P ω) (fun s=> key Q s ω))
    (CoarseSide.epochReset (vector cutoff ds P ω) (fun s=> key Q s ω)) t

def activeConstant:ℝ:=CoarseSchedule.factor ds*(5*(4/3:ℝ)^2/ds+1)
def parentConstant:ℝ:=CoarseSchedule.factor dp*(5*(4/3:ℝ)^2/dp)
def flagConstant:ℝ:=(CoreFlags.tolerance^2)⁻¹

lemma constants_nonneg:0≤ activeConstant ∧ 0≤ parentConstant ∧ 0≤ flagConstant:=by
  norm_num [activeConstant,parentConstant,flagConstant,CoarseSchedule.factor,ds,dp,lb,cb,CoreFlags.tolerance]
lemma inventory_nonneg (hw:∀ ω,0≤ w ω) (P:R→ FilteredRanks w) (N:ℕ):0≤ inventory P N:=by
  apply add_nonneg _ (Nat.cast_nonneg _)
  unfold drift
  exact sum_nonneg fun t _=>sum_nonneg fun ω _=>mul_nonneg (hw ω)
    (sum_nonneg fun r _=>abs_nonneg _)
lemma flags_nonneg (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ flags P t ω:=
  ScheduledPayment.flags_nonneg _ _
lemma active_nonneg (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ active P t ω:=by
  apply sum_nonneg
  intro i _
  exact CoarseProcess.charge_nonneg (active_valid cutoff ds (P i) ω t) (active_valid cutoff ds (P i) ω (t+1))
lemma parent_nonneg (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ parentCharge Q t ω:=by
  unfold parentCharge relativeCharge
  split_ifs
  · rfl
  · exact add_nonneg (CoarseEpoch.parent_nonneg (by norm_num [cutoff]) dp Q t ω)
      (CoarseEpoch.parent_nonneg (by norm_num [cutoff]) dp Q (t+1) ω)
lemma wholesale_nonneg (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ wholesale P Q t ω:=by
  unfold wholesale EpochSchedule.wholesale
  split_ifs
  · exact add_nonneg (EpochSchedule.total_nonneg (vector_nonneg cutoff ds P ω t))
      (EpochSchedule.total_nonneg (vector_nonneg cutoff ds P ω (t+1)))
  · rfl
lemma sideRefresh_nonneg (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ sideRefresh P Q t ω:=
  ScheduledPayment.side_charge_nonneg ds _ _ (vector_nonneg cutoff ds P ω) t

lemma flags_eq (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    flags P t ω=∑ ir:J×R,CoreFlags.change (P ir.1 ir.2) t ω:=by
  unfold flags ChangingDomains.changedFlags
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro r _
  unfold StarSimplex.flags CoreFlags.change
  by_cases he:CoreFlags.flag (P i r) t ω=CoreFlags.flag (P i r) (t+1) ω
  · simp only [he,ite_true]
  · simp only [he,Ne.symm he,ite_false]

lemma flags_budget (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (N:ℕ):
    (∑ t∈range N,avg w (flags P t))≤ flagConstant*inventory (flat P) N:=by
  have h:=CoreFlags.core_change_budget hw hw1 (flat P) N
  change (∑ t∈range N,avg w (fun ω=>∑ ir:J×R,CoreFlags.change (P ir.1 ir.2) t ω))≤_ at h
  simpa only [←flags_eq,flagConstant,inventory,drift] using h

lemma inventory_flat (P:J→ R→ FilteredRanks w) (N:ℕ):
    inventory (flat P) N=∑ i,inventory (P i) N:=by
  simp only [inventory,drift,flat,Fintype.sum_prod_type,avg_sum,sum_add_distrib,sum_const,nsmul_eq_mul,
    Fintype.card_prod,Nat.cast_mul,card_univ]
  rw [sum_comm]

lemma active_budget (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (N:ℕ):
    (∑ t∈range N,avg w (active P t))≤ activeConstant*inventory (flat P) N:=by
  have hb (i:J): (∑ t∈range N,avg w (fun ω=> CoarseSchedule.charge
      (CoarseProcess.active cutoff ds (P i) ω t) (CoarseProcess.active cutoff ds (P i) ω (t+1))))≤
      activeConstant*inventory (P i) N:=by
    have h:=CoarseProcess.active_budget (by norm_num [cutoff] : 0< cutoff)
      (by norm_num [ds] : 0< ds) (by norm_num [ds] : ds≤1/1000) hw hw1 (P i) N
    have hd:0≤ drift (P i) N:=by
      unfold drift avg
      exact sum_nonneg fun t _=>sum_nonneg fun ω _=>mul_nonneg (hw ω)
        (sum_nonneg fun r _=>abs_nonneg _)
    have hf:0≤ CoarseSchedule.factor ds:=by norm_num [CoarseSchedule.factor,ds]
    rw [sum_comm] at h
    simp only [←avg_sum] at h
    change _≤ CoarseSchedule.factor ds*(5*(4/3:ℝ)^2/ds)*drift (P i) N+
      activeConstant*Fintype.card R at h
    dsimp only [activeConstant,inventory] at ⊢
    dsimp only [activeConstant] at h
    nlinarith [mul_nonneg hf hd]
  change (∑ t∈range N,avg w (fun ω=>∑ i,CoarseSchedule.charge
    (CoarseProcess.active cutoff ds (P i) ω t) (CoarseProcess.active cutoff ds (P i) ω (t+1))))≤_
  simp only [avg_sum]
  rw [sum_comm,inventory_flat,mul_sum]
  exact sum_le_sum fun i _=> hb i

lemma parent_budget (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (Q:R→ FilteredRanks w) (N:ℕ):
    (∑ t∈range N,avg w (parentCharge Q t))≤ parentConstant*inventory Q N:=by
  have h:=CoarseEpoch.parent_budget (by norm_num [cutoff] : 0≤ cutoff)
    (by norm_num [dp,lb,cb] : 0< dp) (by norm_num [dp,lb,cb] : dp≤1/3) hw hw1 Q N
  rw [sum_comm] at h
  change (∑ t∈range N,avg w (CoarseProcess.relativeCharge dp (clipped cutoff dp Q) t))≤_
  simpa only [←avg_sum,parentConstant,inventory,drift] using h

lemma wholesale_budget (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ) (ω:Ω):
    (∑ t∈range N,wholesale P Q t ω)≤203*(∑ t∈range N,active P t ω)+
      2*(∑ t∈range N,parentCharge Q t ω):=by
  exact CoarseEpoch.wholesale_budget (by norm_num [cutoff]) (by norm_num [ds]) (by norm_num [ds])
    (by norm_num [dp,lb,cb]) (by norm_num [dp,lb,cb]) P Q hs id ω N

lemma sideRefresh_budget (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ) (ω:Ω):
    (∑ t∈range N,sideRefresh P Q t ω)≤ CoarseSide.C ds*(∑ t∈range N,active P t ω):=by
  exact (CoarseSide.side_budget (by norm_num [ds] : 0< ds) (vector cutoff ds P ω)
    (fun s=> key Q s ω) (vector_nonneg cutoff ds P ω) N).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun t _=> vector_variation cutoff ds P ω t)
      (CoarseSide.C_nonneg (by norm_num [ds])))
end KServer.ActualCharges

end


/-! Uniform coarse accounting for the actual local star. The only variable
right-hand side is the sum of true drift and one fixed rank inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def total (w:Ω→ℝ) (N:ℕ) (f:ℕ→Ω→ℝ):ℝ:=∑ t∈range N,avg w (f t)
def stock (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):ℝ:=
  inventory (flat P) N+inventory Q N

def wholesaleConstant:ℝ:=203*activeConstant+2*parentConstant
def scaleConstant:ℝ:=80/ds+flagConstant+41*wholesaleConstant
def sideRefreshConstant:ℝ:=CoarseSide.C ds*activeConstant

lemma total_mono (hw:∀ ω,0≤ w ω) {N:ℕ} {f g:ℕ→Ω→ℝ} (h:∀ t ω,f t ω≤ g t ω):
    total w N f≤ total w N g:=sum_le_sum fun t _=> avg_mono hw (h t)
lemma total_nonneg (hw:∀ ω,0≤ w ω) {N:ℕ} {f:ℕ→Ω→ℝ} (h:∀ t ω,0≤ f t ω):
    0≤ total w N f:=sum_nonneg fun t _=> sum_nonneg fun ω _=> mul_nonneg (hw ω) (h t ω)
lemma total_add (N:ℕ) (f g:ℕ→Ω→ℝ):
    total w N (fun t ω=> f t ω+g t ω)=total w N f+total w N g:=by
  simp only [total,avg_add,sum_add_distrib]
lemma total_mul (N:ℕ) (c:ℝ) (f:ℕ→Ω→ℝ):
    total w N (fun t ω=> c*f t ω)=c*total w N f:=by
  simp only [total,avg_mul,←mul_sum]
lemma stock_nonneg (hw:∀ ω,0≤ w ω) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    0≤ stock P Q N:=add_nonneg (inventory_nonneg hw _ _) (inventory_nonneg hw _ _)
lemma inventory_child_le (hw:∀ ω,0≤ w ω) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    inventory (flat P) N≤ stock P Q N:=le_add_of_nonneg_right (inventory_nonneg hw _ _)
lemma inventory_parent_le (hw:∀ ω,0≤ w ω) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    inventory Q N≤ stock P Q N:=le_add_of_nonneg_left (inventory_nonneg hw _ _)
lemma more_constants_nonneg:0≤ wholesaleConstant ∧ 0≤ scaleConstant ∧ 0≤ sideRefreshConstant:=by
  rcases constants_nonneg with ⟨ha,hp,hf⟩
  have hc:=CoarseSide.C_nonneg (by norm_num [ds]:0< ds)
  have hd:0≤80/ds:=by norm_num [ds]
  dsimp only [wholesaleConstant,scaleConstant,sideRefreshConstant]
  constructor
  · positivity
  constructor <;> positivity

lemma flags_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (flags P)≤ flagConstant*stock P Q N:=
  (flags_budget hw hw1 P N).trans (mul_le_mul_of_nonneg_left (inventory_child_le hw P Q N) constants_nonneg.2.2)
lemma active_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (ActualCharges.active P)≤ activeConstant*stock P Q N:=
  (active_budget hw hw1 P N).trans (mul_le_mul_of_nonneg_left (inventory_child_le hw P Q N) constants_nonneg.1)
lemma parent_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (parentCharge Q)≤ parentConstant*stock P Q N:=
  (parent_budget hw hw1 Q N).trans (mul_le_mul_of_nonneg_left (inventory_parent_le hw P Q N) constants_nonneg.2.1)
lemma wholesale_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (wholesale P Q)≤ wholesaleConstant*stock P Q N:=by
  have h:=avg_mono hw (wholesale_budget P Q hs N)
  simp only [avg_add,avg_mul,←CoarseProcess.avg_range] at h
  change total w N (wholesale P Q)≤203*total w N (ActualCharges.active P)+2*total w N (parentCharge Q) at h
  have ha:=active_bound hw hw1 P Q N
  have hp:=parent_bound hw hw1 P Q N
  dsimp only [wholesaleConstant]
  nlinarith
lemma sideRefresh_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (sideRefresh P Q)≤ sideRefreshConstant*stock P Q N:=by
  have h:=avg_mono hw (sideRefresh_budget P Q N)
  simp only [avg_mul,←CoarseProcess.avg_range] at h
  change total w N (sideRefresh P Q)≤ CoarseSide.C ds*total w N (ActualCharges.active P) at h
  exact h.trans (by simpa only [sideRefreshConstant,mul_assoc] using
    mul_le_mul_of_nonneg_left (active_bound hw hw1 P Q N) (CoarseSide.C_nonneg (by norm_num [ds])))

lemma scale_eq (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    ActualOutput.D P Q t ω=CoarseScale.scale ds P t ω
      (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t):=by
  unfold ActualOutput.D StarSide.scale StarSide.mark CoarseScale.scale
  cases EpochSchedule.dominant (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t) <;> rfl

lemma scale_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (fun t ω=>|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|)≤ scaleConstant*stock P Q N:=by
  have hc:=CoarseScale.scale_budget (by norm_num [cutoff]:0< cutoff) (by norm_num [ds]:0< ds)
    (by norm_num [ds]:ds≤1/1000) hw hw1 P (fun ω t=> key Q t ω) N
  have hd:(∑ i,∑ r,∑ t∈range N,avg w (fun ω=>|(P i r).p (t+1) ω-(P i r).before (t+1) ω|))=drift (flat P) N:=by
    simp only [drift,flat,Fintype.sum_prod_type,avg_sum]
    symm
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    exact sum_comm
  simp only [hd,←scale_eq] at hc
  have hi:drift (flat P) N+(Fintype.card J:ℝ)*(Fintype.card R:ℝ)=inventory (flat P) N:=by
    simp only [inventory,Fintype.card_prod,Nat.cast_mul]
  rw [hi] at hc
  change total w N (fun t ω=>|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|)≤
    (80/ds+flagConstant)*inventory (flat P) N+41*total w N (wholesale P Q) at hc
  have hwc:=wholesale_bound hw hw1 P Q hs N
  have hci:=inventory_child_le hw P Q N
  have hcc:0≤80/ds+flagConstant:=by have h:=constants_nonneg.2.2; norm_num [ds]; positivity
  have hb:=mul_le_mul_of_nonneg_left hci hcc
  dsimp only [scaleConstant]
  nlinarith
end KServer.ActualCharges

end


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SidePayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide
open SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w:Ω→ℝ}

lemma pre_actual {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0<cw) (hel:1≤ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (hb:0≤b t ω)
    (hM:∀ i,b t ω+cw*logs δ P key t ω i/ell≤5) (hbe:b t ω=b (t+1) ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let hp:0<ell:=lt_of_lt_of_le zero_lt_one hel
    let d:=input hcw hp δ P key b
    let a:=proportion hcw hp δ P key b t ω
    |(family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks a-
      (family 40).value (d t ω).data (d (t+1) ω).ranks a|≤
      SideEdits.L cw ell*|scale δ P key (t+1) ω-scale δ P key t ω|+
      SideEdits.Q cw ell*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  intro hp d a
  have hh:=SideEdits.pre_edit hcw hel (sides δ P key t ω) (sides δ P key (t+1) ω)
    (sideFlags δ P key t ω) (sideFlags δ P key (t+1) ω)
    (logs δ P key t ω) (logs δ P key (t+1) ω) (fun i=>le_max_left _ _) (fun i=>le_max_left _ _)
    hb hM (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω)
    (SideActualEdits.flags_supported δ P key t ω) (SideActualEdits.flags_supported δ P key (t+1) ω)
    a (proportion_mem hcw hp δ P key b t ω) (D:=scale δ P key t ω) (E:=scale δ P key (t+1) ω)
  have hd1:(d (t+1) ω).data=fromLog (sides δ P key (t+1) ω) (sideFlags δ P key (t+1) ω)
      16 (b t ω) (scale δ P key (t+1) ω) cw ell (logs δ P key (t+1) ω)
      (by norm_num) hcw hp (fun i=>le_max_left _ _):=by dsimp [d,input]; rw [hbe]
  rw [hd1]
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (SideActualEdits.flags_change hδ hδu P key t ω he) (SideEdits.Q_nonneg hcw hp.le)))

lemma post_actual {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0<cw) (hel:1≤ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (hb:1≤b t ω)
    (hM:∀ s i,b t ω+cw*logs δ P key s ω i/ell≤5) (hbe:b t ω=b (t+1) ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let hp:0<ell:=lt_of_lt_of_le zero_lt_one hel
    let d:=input hcw hp δ P key b
    let a:=proportion hcw hp δ P key b t ω
    let z:=SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks a
    |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks z-
      (family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks z|≤
      SideEdits.K cw ell*(40*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))) := by
  intro hp d a z
  have hh:=SideEdits.post_edit hcw hel (sides δ P key t ω) (sides δ P key (t+1) ω)
    (sideFlags δ P key t ω) (sideFlags δ P key (t+1) ω)
    (logs δ P key t ω) (logs δ P key (t+1) ω) (fun i=>le_max_left _ _) (fun i=>le_max_left _ _)
    hb (hM t) (hM (t+1)) (scale_nonneg δ P key (t+1) ω) (d (t+1) ω).ranks
    (fun ir=>((P ir.1 ir.2).range (t+1) ω).1) a (proportion_mem hcw hp δ P key b t ω)
    (D:=scale δ P key t ω)
  have hd1:(d (t+1) ω).data=fromLog (sides δ P key (t+1) ω) (sideFlags δ P key (t+1) ω)
      16 (b t ω) (scale δ P key (t+1) ω) cw ell (logs δ P key (t+1) ω)
      (by norm_num) hcw hp (fun i=>le_max_left _ _):=by dsimp [d,input]; rw [hbe]
  dsimp only at hh
  rw [←hd1] at hh
  have hK:0≤SideEdits.K cw ell:=by
    unfold SideEdits.K
    have hl:=Real.log_nonneg (show (1:ℝ)≤17 by norm_num)
    positivity
  exact hh.trans (mul_le_mul_of_nonneg_left (SideActualEdits.logs_charge hδ hδu hcw hp P key b t ω
    (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω) he) hK)

end KServer.SidePayment

end


noncomputable section
open scoped BigOperators
namespace KServer.SideFixed
open SideFamilies
attribute [local instance] Classical.decEq
variable {Ω J R:Type} [Fintype J] [Fintype R]
lemma payment (d:ℕ→Ω→CausalSide.Input J R) (t:ℕ) (ω:Ω)
    (he:(d t ω).epoch=(d (t+1) ω).epoch)
    (hWW:(d t ω).data.W=(d (t+1) ω).data.W)
    (hb:1≤(d t ω).data.b) (hD:0≤(d (t+1) ω).data.D)
    (hM:∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤5)
    (hW:10<(d t ω).data.W) (hp:∀ ir,0≤(d (t+1) ω).ranks ir) :
    let old:=(d t ω).data
    let new:=(d (t+1) ω).data
    let p:=(d (t+1) ω).ranks
    let a:=CausalSide.run 40 d t ω
    new.D*ChangingDomains.variation (CausalSide.run 40 d (t+1) ω) a≤
      (family 40).value old p a-(family 40).value new p (CausalSide.run 40 d (t+1) ω)+
      |(family 40).value (prepareData old new) p a-(family 40).value old p a|+
      |(family 40).value new p (SideFamilies.transport 40 old new p a)-
        (family 40).value (prepareData old new) p (SideFamilies.transport 40 old new p a)| := by
  have hh:=CausalSide.ordinary_payment d (M:=5) t ω he hWW hb hD hM (by norm_num; exact hW) hp
  simpa only [show (8:ℝ)*5=40 by norm_num] using hh
lemma payment_of_edits (d:ℕ→Ω→CausalSide.Input J R) (t:ℕ) (ω:Ω)
    (he:(d t ω).epoch=(d (t+1) ω).epoch)
    (hWW:(d t ω).data.W=(d (t+1) ω).data.W)
    (hb:1≤(d t ω).data.b) (hD:0≤(d (t+1) ω).data.D)
    (hM:∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤5)
    (hW:10<(d t ω).data.W) (hp:∀ ir,0≤(d (t+1) ω).ranks ir) (u v:ℝ)
    (hpre: |(family 40).value (prepareData (d t ω).data (d (t+1) ω).data)
      (d (t+1) ω).ranks (CausalSide.run 40 d t ω)-
      (family 40).value (d t ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω)|≤u)
    (hpost: |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω))-
      (family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω))|≤v) :
    (d (t+1) ω).data.D*ChangingDomains.variation (CausalSide.run 40 d (t+1) ω) (CausalSide.run 40 d t ω)≤
      (family 40).value (d t ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (CausalSide.run 40 d (t+1) ω)+u+v := by
  exact (payment d t ω he hWW hb hD hM hW hp).trans (add_le_add (add_le_add le_rfl hpre) hpost)

end KServer.SideFixed

end


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SidePayment
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide
open SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J]  [Fintype R]
variable {w:Ω→ℝ}

lemma ordinary {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0<cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (hb:1≤b t ω) (hbu:b t ω≤4) (hbe:b t ω=b (t+1) ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      SideEdits.L cw ell*|scale δ P key (t+1) ω-scale δ P key t ω|+
      SideEdits.Q cw ell*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      40*SideEdits.K cw ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
  intro ell hel d a
  have hell:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
  have hM (s:ℕ) (i:J):b t ω+cw*logs δ P key s ω i/ell≤5:=by
    have h:=SideActualEdits.theta_bound hδ hδu hk hcw hcwu P key hs s ω i
    change cw*logs δ P key s ω i/ell≤1 at h
    linarith
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hpre:=pre_actual hδ hδu hcw hell P key b t ω (by linarith) (hM t) hbe he
  have hpost:=post_actual hδ hδu hcw hell P key b t ω hb hM hbe he
  have hpst : |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (a t ω))-
      (family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (a t ω))|≤
    40*SideEdits.K cw ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
    simpa only [mul_left_comm,mul_assoc] using hpost
  have hpay:=SideFixed.payment_of_edits d t ω he rfl hb (scale_nonneg δ P key (t+1) ω)
    (fun i _=>hM t i) (by norm_num : (10:ℝ)<16) (fun ir=>(hp ir).1) _ _ hpre hpst
  dsimp only [a,proportion,d] at *
  simpa only [input,fromLog,add_assoc] using hpay

end KServer.SidePayment

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideActualBounds
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide
open SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w:Ω→ℝ}

omit [DecidableEq J] in
lemma scale_bound {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    StarSide.scale δ P key t ω≤41*EpochSchedule.total (vector cutoff δ P ω t) := by
  have h:=CoarseScale.scale_bound (by norm_num [cutoff] : 0<cutoff) hδ hδu P t ω
    (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)
    (EpochSchedule.run_valid (vector cutoff δ P ω) (fun s=>key s ω) (vector_nonneg cutoff δ P ω) t)
  change CoarseScale.scale δ P t ω _≤_ at h
  unfold CoarseScale.scale at h
  unfold StarSide.scale mark
  cases hm : EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s => key s ω) t) <;>
    simpa only [hm, Option.elim,CoarseScale.noncore,coarseFlex] using h

lemma core_bound {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hcw:0<cw) (hel:0<ell)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ) (t:ℕ) (ω:Ω)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) :
    (∑ i,core (input hcw hel δ P key b t ω).data p i)≤40*EpochSchedule.total (vector cutoff δ P ω t) := by
  unfold EpochSchedule.total
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  apply le_trans _ (ScheduleEdits.count_bound hδ hδu (P i) t ω)
  apply sum_le_sum
  intro r _
  change (if sideFlags δ P key t ω i r then p (i,r) else 0)≤
    (if CoreFlags.flag (P i r) t ω then 1 else 0)
  by_cases hf:CoreFlags.flag (P i r) t ω=true
  · simp only [sideFlags,hf,ite_true]
    split_ifs <;> first | exact (hp (i,r)).2 | norm_num
  · simp [sideFlags,hf]

lemma endpoint {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0<cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (hb:0≤b t ω) (hbu:b t ω≤4)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    |(family 40).value (d t ω).data p (a t ω)|≤
      200000*(1/cw+1)*ell*EpochSchedule.total (vector cutoff δ P ω t) := by
  intro ell hel d a
  have hell:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
  have hM (i:J):b t ω+cw*logs δ P key t ω i/ell≤5:=by
    have h:=SideActualEdits.theta_bound hδ hδu hk hcw hcwu P key hs t ω i
    change cw*logs δ P key t ω i/ell≤1 at h
    linarith
  have h:=SideProfile.endpoint hcw hell (sides δ P key t ω) (sideFlags δ P key t ω)
    (logs δ P key t ω) (fun i=>le_max_left _ _) hb hM (scale_nonneg δ P key t ω)
    p (fun ir=>(hp ir).1) (a t ω) (proportion_mem hcw hel δ P key b t ω)
  change |(family 40).value (d t ω).data p (a t ω)|≤
    640*(1/cw+1)*ell*scale δ P key t ω+(3600/cw*ell)*(∑ i,core (d t ω).data p i) at h
  have hD:=mul_le_mul_of_nonneg_left (scale_bound hδ hδu P key t ω)
    (show 0≤640*(1/cw+1)*ell by positivity)
  have hB:=mul_le_mul_of_nonneg_left (core_bound hδ hδu hcw hel P key b t ω p hp)
    (show 0≤3600/cw*ell by positivity)
  have hn:=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t)
  have he:0≤ell*EpochSchedule.total (vector cutoff δ P ω t):=mul_nonneg hel.le hn
  have hc:0≤1/cw*(ell*EpochSchedule.total (vector cutoff δ P ω t)):=by positivity
  change (3600/cw*ell)*(∑ i,core (d t ω).data p i)≤_ at hB
  simp only [div_eq_mul_inv,one_mul] at h hD hB he hc ⊢
  nlinarith only [h,hD,hB,he,hc]

lemma variation_bound {cw ell:ℝ} (hcw:0<cw) (hel:0<ell) (δ:ℝ)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ) (t:ℕ) (ω:Ω) :
    ChangingDomains.variation (proportion hcw hel δ P key b (t+1) ω) (proportion hcw hel δ P key b t ω)≤32 := by
  have ha:=proportion_mem hcw hel δ P key b t ω
  have ha':=proportion_mem hcw hel δ P key b (t+1) ω
  calc _≤∑ i,(proportion hcw hel δ P key b (t+1) ω i+proportion hcw hel δ P key b t ω i) := by
        exact sum_le_sum fun i _=>(abs_sub _ _).trans_eq (by rw [abs_of_nonneg (ha'.1 i),abs_of_nonneg (ha.1 i)])
       _≤32 := by rw [sum_add_distrib]; linarith [ha.2.1,ha'.2.1]

end KServer.SideActualBounds

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SidePayment
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J]  [Fintype R]
variable {w:Ω→ℝ}

def expense (cw ell δ:ℝ) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) : ℝ :=
  if epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1) then
    SideEdits.L cw ell*|scale δ P key (t+1) ω-scale δ P key t ω|+
      SideEdits.Q cw ell*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      40*SideEdits.K cw ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))
  else 300000*(1/cw+1)*ell*(EpochSchedule.total (vector cutoff δ P ω t)+EpochSchedule.total (vector cutoff δ P ω (t+1)))

lemma payment {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0<cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (hb:∀ s,1≤b s ω) (hbu:∀ s,b s ω≤4)
    (hbe: key t ω=key (t+1) ω→b t ω=b (t+1) ω) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+expense cw ell δ P key t ω := by
  intro ell hel d a
  by_cases he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)
  · have hp:=ordinary hδ hδu hk hcw hcwu P key b hs t ω (hb t) (hbu t)
      (hbe (SideActualEdits.ordinary_key (vector cutoff δ P ω) (fun s=>key s ω) t he)) he
    change _≤(family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_+_+_ at hp
    simpa only [expense,ite_eq_left he,add_assoc] using hp
  · have h0:=SideActualBounds.endpoint hδ hδu hk hcw hcwu P key b hs t ω
      (by linarith [hb t] : 0≤b t ω) (hbu t) (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω)
    have h1:=SideActualBounds.endpoint hδ hδu hk hcw hcwu P key b hs (t+1) ω
      (by linarith [hb (t+1)] : 0≤b (t+1) ω) (hbu (t+1)) (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω)
    change |(family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)|≤_ at h0
    change |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)|≤_ at h1
    have hv:=SideActualBounds.variation_bound hcw hel δ P key b t ω
    change ChangingDomains.variation (a (t+1) ω) (a t ω)≤32 at hv
    have hmv:=mul_le_mul_of_nonneg_left hv (scale_nonneg δ P key (t+1) ω)
    have hD:=SideActualBounds.scale_bound hδ hδu P key (t+1) ω
    have hel1:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
    have hold:=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t)
    have hnew:=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω (t+1))
    have hc:1≤(1/cw+1)*ell:=by
      have hc:0≤1/cw:=by positivity
      nlinarith only [hel1,hc]
    have hcost:=mul_le_mul_of_nonneg_right hc hnew
    have hor:0≤(1/cw+1)*ell*EpochSchedule.total (vector cutoff δ P ω t):=by positivity
    rw [expense,ite_eq_right he]
    have hlo:=neg_abs_le ((family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω))
    have hhi:=le_abs_self ((family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))
    dsimp only [ell] at *
    nlinarith only [h0,h1,hmv,hD,hcost,hor,hlo,hhi,hnew]

end KServer.SidePayment

end


/-! Fixed absolute coefficients for actual simplex/side edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def simplexConstant:ℝ:=(26*C+4)*flagConstant+320*C*activeConstant+
  2976*C*sideRefreshConstant+(520*C+80)*wholesaleConstant
def sideConstant:ℝ:=SideEdits.L cw 1*scaleConstant+SideEdits.Q cw 1*flagConstant+
  40*SideEdits.K cw 1*activeConstant+300000*(1/cw+1)*wholesaleConstant
lemma edit_constants_nonneg:0≤ simplexConstant ∧ 0≤ sideConstant:=by
  rcases constants_nonneg with ⟨ha,hp,hf⟩
  rcases more_constants_nonneg with ⟨hh,hs,hr⟩
  have hC:0< C:=positive.2.2.2.2.1
  have hc:0< cw:=positive.2.2.2.1
  have hl:0≤ Real.log 17:=Real.log_nonneg (by norm_num)
  dsimp only [simplexConstant,sideConstant,SideEdits.L,SideEdits.Q,SideEdits.K]
  constructor <;> positivity

lemma simplex_expense (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) {ell:ℝ} (hell:1≤ ell)
    (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (ScheduledPayment.expense C ell ds P (key Q))≤ simplexConstant*ell*stock P Q N:=by
  have he:total w N (ScheduledPayment.expense C ell ds P (key Q))=
      (26*C*ell+4)*total w N (flags P)+320*C*ell*total w N (ActualCharges.active P)+
      2976*C*ell*total w N (sideRefresh P Q)+(520*C*ell+80)*total w N (wholesale P Q):=by
    change total w N (fun t ω=>(26*C*ell+4)*flags P t ω+320*C*ell*ActualCharges.active P t ω+
      2976*C*ell*sideRefresh P Q t ω+(520*C*ell+80)*wholesale P Q t ω)=_
    rw [total_add,total_add,total_add,total_mul,total_mul,total_mul,total_mul]
  have hf:=flags_bound hw hw1 P Q N
  have ha:=active_bound hw hw1 P Q N
  have hr:=sideRefresh_bound hw hw1 P Q N
  have hh:=wholesale_bound hw hw1 P Q hs N
  have hC:=positive.2.2.2.2.1
  have hstock:=stock_nonneg hw P Q N
  have hflag:=mul_nonneg constants_nonneg.2.2 hstock
  have hwhole:=mul_nonneg more_constants_nonneg.1 hstock
  have hb:total w N (ScheduledPayment.expense C ell ds P (key Q))≤
      (26*C*ell+4)*(flagConstant*stock P Q N)+320*C*ell*(activeConstant*stock P Q N)+
      2976*C*ell*(sideRefreshConstant*stock P Q N)+(520*C*ell+80)*(wholesaleConstant*stock P Q N):=by
    rw [he]
    gcongr
  dsimp only [simplexConstant]
  nlinarith [mul_nonneg (sub_nonneg.mpr hell) hflag,mul_nonneg (sub_nonneg.mpr hell) hwhole]

lemma side_expense_step {ell:ℝ} (hell:0≤ ell) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    SidePayment.expense cw ell ds P (key Q) t ω≤
      SideEdits.L cw ell*|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|+
      SideEdits.Q cw ell*flags P t ω+40*SideEdits.K cw ell*ActualCharges.active P t ω+
      300000*(1/cw+1)*ell*wholesale P Q t ω:=by
  have hc:0< cw:=positive.2.2.2.1
  have hl:0≤ Real.log 17:=Real.log_nonneg (by norm_num)
  have hf:=flags_nonneg P t ω
  have ha:=active_nonneg P t ω
  have hd:=abs_nonneg (ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω)
  have hw:=wholesale_nonneg P Q t ω
  unfold SidePayment.expense
  split_ifs
  · change _≤ SideEdits.L cw ell*|StarSide.scale ds P (key Q) (t+1) ω-StarSide.scale ds P (key Q) t ω|+
      SideEdits.Q cw ell*flags P t ω+40*SideEdits.K cw ell*ActualCharges.active P t ω+_
    exact le_add_of_nonneg_right (by positivity)
  · have he:EpochSchedule.reset (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
      (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t):=by
      exact not_not.mp (fun hn=> by rename_i hh; exact hh ((epoch_same_iff _ _ t).mpr hn))
    rw [wholesale,EpochSchedule.wholesale,ite_eq_left he]
    dsimp only [SideEdits.L,SideEdits.Q,SideEdits.K]
    have h1:0≤ SideEdits.L cw ell*|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|:=by
      dsimp only [SideEdits.L]; positivity
    have h2:0≤ SideEdits.Q cw ell*flags P t ω:=by dsimp only [SideEdits.Q]; positivity
    have h3:0≤40*SideEdits.K cw ell*ActualCharges.active P t ω:=by dsimp only [SideEdits.K]; positivity
    dsimp only [SideEdits.L,SideEdits.Q,SideEdits.K] at h1 h2 h3
    linarith

lemma side_expense (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) {ell:ℝ} (hell:0≤ ell)
    (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (SidePayment.expense cw ell ds P (key Q))≤ sideConstant*ell*stock P Q N:=by
  have h:=total_mono hw (N:=N) (side_expense_step hell P Q)
  rw [total_add,total_add,total_add,total_mul,total_mul,total_mul,total_mul] at h
  have hD:=scale_bound hw hw1 P Q hs N
  have hf:=flags_bound hw hw1 P Q N
  have ha:=active_bound hw hw1 P Q N
  have hh:=wholesale_bound hw hw1 P Q hs N
  have hc:0< cw:=positive.2.2.2.1
  have hl:0≤ Real.log 17:=Real.log_nonneg (by norm_num)
  calc _≤ _:=h
       _≤ SideEdits.L cw ell*(scaleConstant*stock P Q N)+SideEdits.Q cw ell*(flagConstant*stock P Q N)+
      40*SideEdits.K cw ell*(activeConstant*stock P Q N)+300000*(1/cw+1)*ell*(wholesaleConstant*stock P Q N):=by
        dsimp only [SideEdits.L,SideEdits.Q,SideEdits.K]
        gcongr
       _= _:=by dsimp only [sideConstant,SideEdits.L,SideEdits.Q,SideEdits.K]; ring
end KServer.ActualCharges

end

end OAI
