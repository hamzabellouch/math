import Mathlib
import OAI.Combinatorics.KServer.RosterEdits

namespace OAI

/-! Literal conditional averaging for the hidden optimum's stationary members.
Only conditioning on the true request prefix is used; tape averages may be
performed first without conditioning on a surviving random roster. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HiddenAverages
open FiniteExperiment PosteriorRanks RankTracking
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [NeZero k] in
lemma counting_integral (c:Configuration k Y) (f:Y→ℝ) :
    (∑ y,metricCount c y*f y)=∑ i,f (c i) := by
  classical
  simp only [metricCount,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp

lemma expected_counting_test (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:ℕ) (f:(Fin H→Y)→Y→ℝ)
    (hf:∀ y,Adapted (requestHistory t) (fun σ=>f σ y)) :
    avg law.val (fun σ=>∑ y,mu s law t σ y*f σ y)=
      avg law.val (fun σ=>∑ i,f σ (hidden s σ t i)) := by
  rw [avg_sum]
  have he y : avg law.val (fun σ=>mu s law t σ y*f σ y)=
      avg law.val (fun σ=>metricCount (hidden s σ t) y*f σ y) := by
    simpa only [mu,mul_comm] using weighted_posterior law.property.1 (requestHistory t)
      (fun σ=>metricCount (hidden s σ t) y) (fun σ=>f σ y) (hf y)
  simp_rw [he]
  rw [←avg_sum]
  congr 1
  funext σ
  exact counting_integral _ _

lemma expected_before_test (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (f:(Fin H→Y)→Y→ℝ)
    (hf:∀ y,Adapted (requestHistory (t.val+1)) (fun σ=>f σ y)) :
    avg law.val (fun σ=>∑ y,muBefore s law t σ y*f σ y)=
      avg law.val (fun σ=>∑ i,f σ (hidden s σ t i)) := by
  rw [avg_sum]
  have he y : avg law.val (fun σ=>muBefore s law t σ y*f σ y)=
      avg law.val (fun σ=>metricCount (hidden s σ t) y*f σ y) := by
    simpa only [muBefore,mul_comm] using weighted_posterior law.property.1 (requestHistory (t.val+1))
      (fun σ=>metricCount (hidden s σ t) y) (fun σ=>f σ y) (hf y)
  simp_rw [he]
  rw [←avg_sum]
  congr 1
  funext σ
  exact counting_integral _ _

lemma expected_mover_test (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (f:(Fin H→Y)→Y→ℝ)
    (hf:∀ y,Adapted (requestHistory (t.val+1)) (fun σ=>f σ y)) :
    avg law.val (fun σ=>∑ y,nu s law t σ y*f σ y)=
      avg law.val (fun σ=>f σ (hidden s σ t (mover s σ t))) := by
  classical
  rw [avg_sum]
  have he y : avg law.val (fun σ=>nu s law t σ y*f σ y)=
      avg law.val (fun σ=>(if hidden s σ t (mover s σ t)=y then 1 else 0)*f σ y) := by
    simpa only [nu,mul_comm] using weighted_posterior law.property.1 (requestHistory (t.val+1))
      (fun σ=>if hidden s σ t (mover s σ t)=y then (1:ℝ) else 0) (fun σ=>f σ y) (hf y)
  simp_rw [he]
  rw [←avg_sum]
  congr 1
  funext σ
  simp

def stationary (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (σ:Fin H→Y) (y:Y) : ℝ := muBefore s law t σ y-nu s law t σ y

lemma stationary_nonneg (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (σ:Fin H→Y) (y:Y) : 0 ≤ stationary s law t σ y :=
  sub_nonneg.mpr (nu_le_muBefore s law t σ y)

lemma stationary_le (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (σ:Fin H→Y) (hs:0<law.val σ) (y:Y) : stationary s law t σ y ≤ mu s law (t.val+1) σ y := by
  rw [mu_move s law t σ hs y]
  dsimp only [stationary]
  split_ifs <;> linarith

lemma stationary_identity (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (σ:Fin H→Y) (hs:0<law.val σ) (y:Y) :
    stationary s law t σ y=mu s law (t.val+1) σ y-(if σ t=y then 1 else 0) := by
  classical
  rw [mu_move s law t σ hs y]
  dsimp only [stationary]
  ring

lemma expected_stationary_test (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (f:(Fin H→Y)→Y→ℝ)
    (hf:∀ y,Adapted (requestHistory (t.val+1)) (fun σ=>f σ y)) :
    avg law.val (fun σ=>∑ y,stationary s law t σ y*f σ y)=
      avg law.val (fun σ=>∑ i∈univ.erase (mover s σ t),f σ (hidden s σ t i)) := by
  classical
  simp only [stationary,sub_mul,sum_sub_distrib,avg_sub]
  rw [expected_before_test s law t f hf,expected_mover_test s law t f hf,←avg_sub]
  congr 1
  funext σ
  exact (sum_erase_eq_sub (mem_univ (mover s σ t))).symm

end KServer.HiddenAverages

end


/-! Literal tier edit potentials along the selected hidden optimum.
Retirement averages are over the complete independent tape, before request
prefix conditioning.  All quantities below refer to constructed keys. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierTemporal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [NeZero k] in
lemma mean_add (r:ℝ) (f g:Tape Y k H r→ℝ) :
    mean r (fun a=>f a+g a)=mean r f+mean r g := by simp [mean,mul_add,sum_add_distrib]
omit [NeZero k] in
lemma mean_sub (r:ℝ) (f g:Tape Y k H r→ℝ) :
    mean r (fun a=>f a-g a)=mean r f-mean r g := by simp [mean,mul_sub,sum_sub_distrib]
omit [NeZero k] in
lemma mean_sum (r:ℝ) {I:Type*} (S:Finset I) (f:I→Tape Y k H r→ℝ) :
    mean r (fun a=>∑ i∈S,f i a)=∑ i∈S,mean r (f i) := by
  simp only [mean,mul_sum]
  exact sum_comm

lemma mover_inner (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p≤heavyGamma*r) :
    LevelTierEdits.charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i (σ t)-
      uncovered s law hr.le σ a t i p ≤ 0 := by
  rw [heavy_inner_charge s law hr σ a t i p hh hp,zero_add,
    covered_qualified s law hr σ a t i hin.1]
  exact sub_nonpos.mpr (ActualRoster.indicator_nonneg _)

lemma mover_mean_inner (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hin:inserted s law r σ t i)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r))) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i (σ t)-uncovered s law hr.le σ a t i p) ≤
        if heavyGamma*r<dist (σ t) p then 49/(tierK (height i):ℝ) else 0 := by
  split_ifs with hp
  · exact mover_mean s law hr σ t i p hin
  · exact (mean_mono hr (fun a=>mover_inner s law hr σ a t i p hin hh (le_of_not_gt hp))).trans_eq (mean_const hr 0)

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma dyadic_exp_sum (k:ℕ) : (∑ i:Tier k,Real.exp (-height i))≤1 := by
  have hc (i:ℕ) : (i:ℝ)+1≤(2:ℝ)^i := by
    induction i with
    | zero => norm_num
    | succ i ih =>
      rw [pow_succ,Nat.cast_add,Nat.cast_one]
      have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
      nlinarith
  calc _ ≤ ∑ i:Tier k,Real.exp (-(i.val+1:ℝ)) := by
         apply sum_le_sum
         intro i _
         exact Real.exp_le_exp.mpr (neg_le_neg (hc i.val))
       _ ≤ _ := by
         have he:=Fin.sum_univ_eq_sum_range (fun n:ℕ=>Real.exp (-(n+1:ℝ))) (TierDyadic.index (Real.log k)+1)
         rw [he]
         exact tier_weight_sum _

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma dyadic_reciprocal_sum (k:ℕ) : (∑ i:Tier k,1/(tierK (height i):ℝ))≤1 := by
  refine (sum_le_sum (fun i (_:i∈univ)=>?_)).trans (dyadic_exp_sum k)
  have hi:=height_ge i
  have hb:=tier_reciprocal_absorb hi
  have he:Real.exp (-2*height i)≤Real.exp (-height i):=Real.exp_le_exp.mpr (by linarith)
  have ht:64*heavyDelta≤1:=by norm_num [heavyDelta]
  exact hb.trans ((mul_le_mul_of_nonneg_left he (by norm_num [heavyDelta])).trans
    (mul_le_of_le_one_left (Real.exp_nonneg _) ht))

def potential (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) : ℝ :=
  ∑ l:Fin k,uncovered s law hr σ a t i (hidden s σ t l)

def editCost (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) : ℝ :=
  ∑ l:Fin k,LevelTierEdits.charge s law hr σ a t i (hidden s σ t l)

lemma potential_bounds (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) :
    potential s law hr σ a t i∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact sum_nonneg (fun l _=>ActualRoster.indicator_nonneg _)
  · unfold potential uncovered
    exact (sum_le_sum (fun l (_:l∈univ)=>ActualRoster.indicator_le_one _)).trans_eq (by simp)

lemma potential_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) :
    editCost s law hr σ a t i+potential s law hr σ a (t.val+1) i-potential s law hr σ a t i=
      (∑ l∈univ.erase (mover s σ t),(LevelTierEdits.charge s law hr σ a t i (hidden s σ t l)+
        uncovered s law hr σ a (t.val+1) i (hidden s σ t l)-uncovered s law hr σ a t i (hidden s σ t l)))+
      (LevelTierEdits.charge s law hr σ a t i (hidden s σ t (mover s σ t))+
        uncovered s law hr σ a (t.val+1) i (σ t)-uncovered s law hr σ a t i (hidden s σ t (mover s σ t))) := by
  have he:potential s law hr σ a (t.val+1) i=
    (∑ l∈univ.erase (mover s σ t),uncovered s law hr σ a (t.val+1) i (hidden s σ t l))+
      uncovered s law hr σ a (t.val+1) i (σ t) := by
    unfold potential
    rw [←sum_erase_add _ _ (mem_univ (mover s σ t)),hidden_covers]
    congr 1
    apply sum_congr rfl
    intro l hl
    congr 1
    have he:=congrFun (hidden_step s σ t) l
    simpa [serve,(mem_erase.mp hl).1] using he
  rw [he]
  unfold editCost potential
  have hC:=sum_erase_add univ (fun l:Fin k=>LevelTierEdits.charge s law hr σ a t i (hidden s σ t l)) (mem_univ (mover s σ t))
  have hU:=sum_erase_add univ (fun l:Fin k=>uncovered s law hr σ a t i (hidden s σ t l)) (mem_univ (mover s σ t))
  simp only [sum_sub_distrib,sum_add_distrib]
  linarith

end KServer.TierTemporal

end


/-! True-prefix payment of literal tier retirement errors by the posterior
insertion mass.  No conditioning on the realized random tape is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierAverages
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def region (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) : Finset Y :=
  tierRegion tierTemplate r heavyGamma heavyDelta (mu s law (t.val+1) σ) (σ t)

def test (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) : ℝ :=
  if inserted s law r σ t i then indicator (p∈region s law r σ t) else 0

lemma test_nonneg (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) :
    0≤test s law r σ t i p := by unfold test; split_ifs; exact indicator_nonneg _; rfl

lemma inserted_adapted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (i:Tier k)
    (σ ρ:Fin H→Y) (hh:requestHistory (t.val+1) σ=requestHistory (t.val+1) ρ) :
    inserted s law r σ t i ↔ inserted s law r ρ t i := by
  have hm (ω:Fin H→Y) : inserted s law r ω t i ↔
    (t:ℕ)∈roster s law tierTemplate r tierGamma (height i) (tierK (height i)) ω (t.val+1) := by
    rw [roster,Chronological.schedule_mem]
    exact (and_iff_right (Nat.lt_succ_self t.val)).symm
  rw [hm,hm,roster_adapted s law tierTemplate r tierGamma (height i) (tierK (height i)) (t.val+1) σ ρ hh]

lemma test_adapted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (i:Tier k) (p:Y) :
    Adapted (requestHistory (t.val+1)) (fun σ=>test s law r σ t i p) := by
  intro σ ρ hh
  have hm:mu s law (t.val+1) σ=mu s law (t.val+1) ρ:=funext (fun y=>mu_adapted s law (t.val+1) y σ ρ hh)
  simp only [test,region,inserted_adapted s law r t i σ ρ hh,hm,request_of_history t σ ρ hh]

lemma retirement_region (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (t:Fin H) (p:Y)
    (hp:dist (σ t) p≤22*r)
    (hh:¬(mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r)) ∧ dist (σ t) p≤heavyGamma*r)) :
    p∈region s law r σ t := by
  unfold region tierRegion
  split_ifs with h
  · refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by nlinarith⟩,?_⟩
    intro hm
    exact hh ⟨h,(mem_filter.mp hm).2⟩
  · apply mem_filter.mpr ⟨mem_univ _,?_⟩
    norm_num [tierTemplate]
    nlinarith

lemma stationary_test_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i p-uncovered s law hr.le σ a t i p) ≤
      (98/(tierK (height i):ℝ))*test s law r σ t i p := by
  by_cases hin:inserted s law r σ t i
  · have hb:=stationary_mean s law hr σ t i p hin
    refine hb.trans ?_
    rw [test,ite_eq_left hin]
    split_ifs with he
    · rw [indicator,ite_eq_left (retirement_region s law hr σ t p he.1 he.2),mul_one]
    · exact mul_nonneg (by positivity) (indicator_nonneg _)
  · rw [test,ite_eq_right hin,mul_zero]
    have he (a:Tape Y k H r):LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i p-uncovered s law hr.le σ a t i p=0:=
        no_insert_stationary s law hr.le σ a t i p hin
    simp only [he,mean_const hr,le_refl]

lemma test_mass (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) :
    (∑ y,mu s law (t.val+1) σ y*test s law r σ t i y)=
      if inserted s law r σ t i then mass (mu s law (t.val+1) σ) (region s law r σ t) else 0 := by
  unfold test
  split_ifs with h
  · simp only [indicator,mul_ite,mul_one,mul_zero]
    rw [←sum_filter]
    congr 1
    ext y
    simp
  · simp

lemma expected_stationary_bound (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (i:Tier k) :
    avg law.val (fun σ=>∑ l∈univ.erase (mover s σ t),test s law r σ t i (hidden s σ t l)) ≤
      avg law.val (fun σ=>if inserted s law r σ t i then mass (mu s law (t.val+1) σ) (region s law r σ t) else 0) := by
  rw [←expected_stationary_test s law t (fun σ p=>test s law r σ t i p) (test_adapted s law r t i)]
  trans avg law.val (fun σ=>∑ y,mu s law (t.val+1) σ y*test s law r σ t i y)
  · apply sum_le_sum
    intro σ _
    by_cases hs:0<law.val σ
    · apply mul_le_mul_of_nonneg_left _ hs.le
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (stationary_le s law t σ hs y) (test_nonneg s law r σ t i y)
    · have hz:law.val σ=0:=le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp only [hz,zero_mul,le_refl]
  · apply le_of_eq
    congr 1
    funext σ
    exact test_mass s law r σ t i

lemma nonheavy_mass (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (hs:0<law.val σ) (t:Fin H)
    (hh:¬ mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r))) :
      1 ≤ mass (mu s law (t.val+1) σ) (region s law r σ t) := by
  unfold region tierRegion
  rw [ite_eq_right hh]
  have hm:σ t∈ball (σ t) (100*tierTemplate.R*r):=by
    simp only [ball,mem_filter,mem_univ,true_and,dist_self]
    norm_num [tierTemplate]
    positivity
  exact (mu_served s law t σ hs).trans (single_le_sum (fun y _=>mu_nonneg s law (t.val+1) σ y) hm)

end KServer.TierAverages

end


/-! Literal one-step tier cost + potential accounting at the true observation
filtration. The insertion term is the existing geometric pilot charge. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal TierAverages ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def paidMass (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) : ℝ :=
  if inserted s law r σ t i then mass (mu s law (t.val+1) σ) (region s law r σ t) else 0

lemma paidMass_nonneg (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) :
    0≤paidMass s law r σ t i := by
  unfold paidMass
  split_ifs
  · exact mass_nonneg (mu_nonneg s law (t.val+1) σ) _
  · rfl

lemma paidMass_charge (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) :
    r*paidMass s law r σ t i=TierProcess.charge s law tierTemplate r heavyGamma tierGamma heavyDelta
      (height i) (tierK (height i)) t σ := by
  unfold paidMass TierProcess.charge
  change r*(if inserted s law r σ t i then _ else 0)=(if inserted s law r σ t i then _ else 0)
  split_ifs <;> first | rfl | simp

lemma mover_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (hs:0<law.val σ) (t:Fin H) (i:Tier k) (p:Y) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i (σ t)-uncovered s law hr.le σ a t i p) ≤
      (49/(tierK (height i):ℝ))*paidMass s law r σ t i+
      (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) p)+
      LevelNoInsert.error s law hr.le σ t i p := by
  have hC:(0:ℝ)≤49/(tierK (height i):ℝ):=by positivity
  have hP:=mul_nonneg hC (paidMass_nonneg s law r σ t i)
  have hD:=mul_nonneg hC (indicator_nonneg (heavyGamma*r<dist (σ t) p))
  by_cases hin:inserted s law r σ t i
  · rw [LevelNoInsert.error,ite_eq_left hin,add_zero]
    by_cases hh:mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
        (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r))
    · have hb:=mover_mean_inner s law hr σ t i p hin hh
      have he:(if heavyGamma*r<dist (σ t) p then 49/(tierK (height i):ℝ) else 0)=
          (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) p):=by
        unfold indicator
        split_ifs <;> ring
      rw [he] at hb
      linarith
    · have hm:=nonheavy_mass s law hr σ hs t hh
      have hp:1≤paidMass s law r σ t i:=by rw [paidMass,ite_eq_left hin]; exact hm
      have hb:=mover_mean s law hr σ t i p hin
      have hm:=mul_le_mul_of_nonneg_left hp hC
      linarith
  · rw [LevelNoInsert.error,ite_eq_right hin]
    linarith

lemma average_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (t:Fin H) (i:Tier k) :
    avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t i+
      TierTemporal.potential s law hr.le σ a (t.val+1) i-TierTemporal.potential s law hr.le σ a t i)) ≤
      (147/(tierK (height i):ℝ))*avg law.val (fun σ=>paidMass s law r σ t i)+
      (49/(tierK (height i):ℝ))*avg law.val (fun σ=>indicator (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t))))+
      avg law.val (fun σ=>LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t))) := by
  let stationaryTerm:=fun σ=>∑ l∈univ.erase (mover s σ t),test s law r σ t i (hidden s σ t l)
  have hpoint (σ:Fin H→Y) (hs:0<law.val σ):
      mean r (fun a=>editCost s law hr.le σ a t i+TierTemporal.potential s law hr.le σ a (t.val+1) i-
        TierTemporal.potential s law hr.le σ a t i) ≤
      (98/(tierK (height i):ℝ))*stationaryTerm σ+
        ((49/(tierK (height i):ℝ))*paidMass s law r σ t i+
        (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t)))+
        LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t))) := by
    simp_rw [potential_step,mean_add,mean_sum]
    apply add_le_add _ (mover_bound s law hr σ hs t i _)
    have hd:TierTemporal.finDecEq k=instDecidableEqFin k:=Subsingleton.elim _ _
    rw [hd]
    exact (sum_le_sum (fun l (_:l∈univ.erase (mover s σ t))=>
      stationary_test_bound s law hr σ t i (hidden s σ t l))).trans_eq (mul_sum _ _ _).symm
  have hb:avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t i+
      TierTemporal.potential s law hr.le σ a (t.val+1) i-TierTemporal.potential s law hr.le σ a t i)) ≤
        avg law.val (fun σ=>(98/(tierK (height i):ℝ))*stationaryTerm σ+
        ((49/(tierK (height i):ℝ))*paidMass s law r σ t i+
        (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t)))+
        LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t)))) := by
    apply sum_le_sum
    intro σ _
    by_cases hs:0<law.val σ
    · exact mul_le_mul_of_nonneg_left (hpoint σ hs) hs.le
    · have hz:law.val σ=0:=le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp only [hz,zero_mul,le_refl]
  simp only [avg_add,avg_mul] at hb
  have hs:=mul_le_mul_of_nonneg_left (expected_stationary_bound s law r t i)
    (show (0:ℝ)≤98/(tierK (height i):ℝ) by positivity)
  change (98/(tierK (height i):ℝ))*avg law.val stationaryTerm ≤
    (98/(tierK (height i):ℝ))*avg law.val (fun σ=>paidMass s law r σ t i) at hs
  have hc:(147/(tierK (height i):ℝ))=98/(tierK (height i):ℝ)+49/(tierK (height i):ℝ):=by ring
  rw [hc,add_mul]
  linarith only [hb,hs]

end KServer.TierBudget

end


/-! Horizon-independent endpoint bound for the actual dyadic-tier edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierGlobal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal TierAverages ActualRoster TierBudget
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma telescope_budget (p:ℕ→ℝ) (c b:Fin H→ℝ)
    (hs:∀ t,c t+p (t.val+1)-p t≤b t) (hF:0≤p H) :
    (∑ t,c t) ≤ ∑ t,b t+p 0 := by
  have hd:(∑ t:Fin H,(p (t.val+1)-p t))=p H-p 0 := by
    calc _ = ∑ t∈range H,(p (t+1)-p t) := Fin.sum_univ_eq_sum_range (fun t:ℕ=>p (t+1)-p t) H
         _ = _ := sum_range_sub p H
  have he:=sum_le_sum (fun t (_:t∈univ)=>hs t)
  have heq:(∑ t:Fin H,(c t+p (t.val+1)-p t))=(∑ t,c t)+(p H-p 0):=by
    simp_rw [show ∀ t:Fin H,c t+p (t.val+1)-p t=c t+(p (t.val+1)-p t) by intro t; ring]
    rw [sum_add_distrib,hd]
  rw [heq] at he
  linarith

lemma potential_mean_bounds (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (t:ℕ) (i:Tier k) :
    avg law.val (fun σ=>mean r (fun a=>TierTemporal.potential s law hr.le σ a t i))∈Set.Icc 0 (k:ℝ) := by
  constructor
  · calc 0 = avg law.val (fun _=>mean (Y:=Y) (k:=k) (H:=H) r (fun _=>0)) := by
           rw [mean_const hr,avg_const _ law.property.2]
         _ ≤ _ := avg_mono law.property.1 (fun σ=>mean_mono hr
           (fun a=>(potential_bounds s law hr.le σ a t i).1))
  · calc _ ≤ avg law.val (fun _=>mean (Y:=Y) (k:=k) (H:=H) r (fun _=>(k:ℝ))) :=
           avg_mono law.property.1 (fun σ=>mean_mono hr
             (fun a=>(potential_bounds s law hr.le σ a t i).2))
         _ = _ := by rw [mean_const hr,avg_const _ law.property.2]

lemma tier_budget (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r) (i:Tier k) :
    (∑ t:Fin H,avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t i))) ≤
      (147/(tierK (height i):ℝ))*(∑ t:Fin H,avg law.val (fun σ=>paidMass s law r σ t i))+
      (49/(tierK (height i):ℝ))*(∑ t:Fin H,avg law.val (fun σ=>indicator
        (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t)))))+
      (∑ t:Fin H,avg law.val (fun σ=>LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t))))+k := by
  have hs:=fun t:Fin H=>average_step s law hr t i
  simp only [mean_sub,mean_add,avg_sub,avg_add] at hs
  have hb:=telescope_budget (fun t=>avg law.val (fun σ=>mean r
    (fun a=>TierTemporal.potential s law hr.le σ a t i))) _ _ hs
    (potential_mean_bounds s law hr H i).1
  simp only [sum_add_distrib,←mul_sum] at hb
  exact hb.trans (add_le_add le_rfl (potential_mean_bounds s law hr 0 i).2)

omit [Fintype Y] in
lemma actual_move_cost (s:Configuration k Y) (σ:Fin H→Y) :
    (∑ t:Fin H,dist (σ t) (hidden s σ t (mover s σ t)))=optimalCost s (List.ofFn σ) := by
  simp_rw [dist_comm (σ _),←hidden_movement]
  exact hidden_total_cost s σ

lemma far_scales {r₀ τ d:ℝ} (hr:0<r₀) (hτ:2≤τ) (hd:0≤d) (n:ℕ) :
    (∑ j∈range n,radius r₀ τ j*indicator (heavyGamma*radius r₀ τ j<d)) ≤ 2*d/heavyGamma := by
  have hg:(0:ℝ)<heavyGamma:=by norm_num [heavyGamma]
  have hb:=radius_truncated_sum hr.le hτ (div_nonneg hd hg.le) n
  have he:2*(d/heavyGamma)=2*d/heavyGamma:=by ring
  refine (sum_le_sum (fun j (_:j∈range n)=>?_)).trans (hb.trans_eq he)
  by_cases hj:heavyGamma*radius r₀ τ j<d
  · have hle:radius r₀ τ j≤d/heavyGamma:=(le_div_iff₀ hg).mpr (by linarith)
    simp only [indicator,ite_eq_left hj,mul_one,ite_eq_left hle,le_refl]
  · simp only [indicator,ite_eq_right hj,mul_zero]
    split_ifs
    · exact (radius_pos hr (by linarith) j).le
    · rfl

end KServer.TierGlobal

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierScaleBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal TierAverages ActualRoster TierBudget TierGlobal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma avg_finset_sum {Ω I:Type*} [Fintype Ω] (w:Ω→ℝ) (S:Finset I) (f:I→Ω→ℝ) :
    avg w (fun ω=>∑ i∈S,f i ω)=∑ i∈S,avg w (f i) := by
  simp only [avg,mul_sum]
  exact sum_comm

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma factor_sum {I:Type*} [Fintype I] (f:I→ℝ) (c M:ℝ) :
    c*(∑ i,f i)*M=∑ i,c*f i*M := by rw [mul_sum,sum_mul]

lemma insertion_budget (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ) (i:Tier k) :
    (∑ j∈range n,radius r₀ τ j*((147/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>paidMass s law (radius r₀ τ j) σ t i)))) ≤
      147*Real.exp (-height i)*(tierDrift*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ))+
      147*Real.exp (-height i)*(∑ j∈range n,2*radius r₀ τ j*(k:ℝ)) := by
  have hb:=weighted_insertion_budget s law n hr hτ (height_ge i)
  have he:(∑ j∈range n,radius r₀ τ j*((147/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>paidMass s law (radius r₀ τ j) σ t i))))=
      147*(∑ t:Fin H,avg law.val (fun σ=>∑ j∈range n,
        TierProcess.charge s law tierTemplate (radius r₀ τ j) heavyGamma tierGamma heavyDelta
          (height i) (tierK (height i)) t σ/(tierK (height i):ℝ))) := by
    simp_rw [←paidMass_charge,div_eq_mul_inv,avg_finset_sum]
    rw [sum_comm]
    simp only [mul_sum,avg]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro σ _
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤147)).trans_eq (by ring)

lemma insertion_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ) :
    (∑ i:Tier k,∑ j∈range n,radius r₀ τ j*((147/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>paidMass s law (radius r₀ τ j) σ t i)))) ≤
      147*(tierDrift*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ))+
      147*(∑ j∈range n,2*radius r₀ τ j*(k:ℝ)) := by
  let A:=tierDrift*(1+Real.log ((k:ℝ)+1))*(∑ σ,law.val σ*optimalCost s (List.ofFn σ))
  let B:=∑ j∈range n,2*radius r₀ τ j*(k:ℝ)
  have hn:0≤A:=by
    apply mul_nonneg
    · apply mul_nonneg
      · exact driftConstant_nonneg tierTemplate 60 (by norm_num [tierGamma]) (by norm_num [tierDelta])
      · have hl:0≤Real.log ((k:ℝ)+1):= Real.log_nonneg (by have hk:=Nat.cast_nonneg (α:=ℝ) k; linarith)
        linarith
    · exact sum_nonneg (fun σ _=>mul_nonneg (law.property.1 σ) (optimalCost_nonneg s (List.ofFn σ)))
  have he:0≤B:=sum_nonneg (fun j _=>by
    have hj:=(radius_pos (τ:=τ) hr (by linarith) j).le
    exact mul_nonneg (mul_nonneg (by norm_num) hj) (Nat.cast_nonneg k))
  calc _ ≤ ∑ i:Tier k,(147*Real.exp (-height i)*A+147*Real.exp (-height i)*B) :=
           sum_le_sum (fun i (_:i∈univ)=>insertion_budget s law hr hτ n i)
       _ = 147*(∑ i:Tier k,Real.exp (-height i))*(A+B) := by
           simp only [mul_add,mul_sum,sum_mul,sum_add_distrib]
       _ ≤ 147*1*(A+B) := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (dyadic_exp_sum k) (by norm_num)) (add_nonneg hn he)
       _ = _ := by ring

lemma far_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ) :
    (∑ i:Tier k,∑ j∈range n,radius r₀ τ j*((49/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>indicator (heavyGamma*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t))))))) ≤
      (98/heavyGamma)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)) := by
  let M:ℝ:=∑ t:Fin H,avg law.val (fun σ=>∑ j∈range n,radius r₀ τ j*
    indicator (heavyGamma*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t))))
  have hM: M≤(2/heavyGamma)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)):=by
    have hb:=sum_le_sum (fun t (_:t∈univ)=>avg_mono law.property.1 (fun σ=>
      far_scales hr hτ (dist_nonneg (x:=σ t) (y:=hidden s σ t (mover s σ t))) n))
    have he:(∑ t:Fin H,avg law.val (fun σ=>2*dist (σ t) (hidden s σ t (mover s σ t))/heavyGamma))=
        (2/heavyGamma)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)):=by
      simp only [avg]
      rw [sum_comm,mul_sum]
      apply sum_congr rfl
      intro σ _
      rw [←actual_move_cost s σ]
      simp only [mul_sum]
      apply sum_congr rfl
      intro t _
      ring
    exact hb.trans_eq he
  have hn:0≤M:=by
    exact sum_nonneg (fun t _=>sum_nonneg (fun σ _=>mul_nonneg (law.property.1 σ)
      (sum_nonneg (fun j _=>mul_nonneg (radius_pos (τ:=τ) hr (by linarith) j).le (indicator_nonneg _)))))
  have he:(∑ i:Tier k,∑ j∈range n,radius r₀ τ j*((49/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>indicator (heavyGamma*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t)))))))=
      49*(∑ i:Tier k,1/(tierK (height i):ℝ))*M := by
    rw [factor_sum]
    apply sum_congr rfl
    intro i _
    unfold M
    simp_rw [avg_finset_sum,avg_mul]
    rw [sum_comm]
    simp only [mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro t _
    ring
  rw [he]
  have hsum:=mul_le_mul_of_nonneg_left (dyadic_reciprocal_sum k) (by positivity : (0:ℝ)≤49*M)
  have hbound:=mul_le_mul_of_nonneg_left hM (by norm_num : (0:ℝ)≤49)
  calc _ ≤ 49*M := by nlinarith only [hsum]
       _ ≤ _ := hbound.trans_eq (by ring)

lemma noinsert_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ) :
    (∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t))))) ≤
      (32*(1+Real.log k)+31440*Real.log k)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)) := by
  have hb:=sum_le_sum (fun t (_:t∈univ)=>sum_le_sum (fun σ (_:σ∈univ)=>show
    law.val σ*(∑ j∈range n,radius r₀ τ j*(∑ i:Tier k,
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t)))) ≤
    law.val σ*((32*(1+Real.log k)+31440*Real.log k)*
      dist (σ t) (hidden s σ t (mover s σ t))) from by
        by_cases hs:law.val σ=0
        · simp only [hs,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (LevelNoInsert.scales_error s law σ
            (lt_of_le_of_ne (law.property.1 σ) (Ne.symm hs)) t _ hr hτ n) (law.property.1 σ)))
  have he:(∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t)))))=
      ∑ t:Fin H,∑ σ,law.val σ*(∑ j∈range n,radius r₀ τ j*(∑ i:Tier k,
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t)))) := by
    simp only [avg,mul_sum]
    calc _ = ∑ j∈range n,∑ t:Fin H,∑ σ,∑ i:Tier k,
        radius r₀ τ j*(law.val σ*LevelNoInsert.error s law
          (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
          (hidden s σ t (mover s σ t))) := by
            rw [sum_comm]
            apply sum_congr rfl
            intro j _
            rw [sum_comm]
            apply sum_congr rfl
            intro t _
            rw [sum_comm]
         _ = _ := by
            rw [sum_comm]
            apply sum_congr rfl
            intro t _
            rw [sum_comm]
            apply sum_congr rfl
            intro σ _
            apply sum_congr rfl
            intro j _
            exact sum_congr rfl (fun i _=>by ring)
  rw [he]
  refine hb.trans_eq ?_
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro σ _
  rw [←actual_move_cost s σ]
  simp only [mul_sum]
  exact sum_congr rfl (fun t _=>by ring)

end KServer.TierScaleBudget

end


/-! Literal deterministic heavy-center schedule and its clipped distance profile,
§07 of the current manuscript. Random heavy radii do not affect this schedule. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyEdit

/-- The heavy profile is zero up to radius 9 and one from radius 10. -/
def ramp (u : ℝ) : ℝ := min 1 (max 0 (u-9))
lemma ramp_bounds (u : ℝ) : ramp u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma ramp_zero {u : ℝ} (hu : u ≤ 9) : ramp u=0 := by
  simp [ramp,max_eq_left (by linarith : u-9 ≤ 0)]
lemma ramp_one {u : ℝ} (hu : 10 ≤ u) : ramp u=1 := by
  exact min_eq_left ((by linarith : 1 ≤ u-9).trans (le_max_right _ _))
lemma ramp_lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ |u-v| := by
  rw [abs_le]
  constructor <;> unfold ramp <;>
    simp only [min_def,max_def] <;> split_ifs <;>
    have h1 := le_abs_self (u-v) <;> have h2 := neg_le_abs (u-v) <;> linarith

attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

/-- Finite minimum with a default value 1, also for the empty center set. -/
def profile (r : ℝ) (C : Finset Y) (y : Y) : ℝ :=
  (insert 1 (C.image (fun a => ramp (dist a y/r)))).min' ⟨1,mem_insert_self _ _⟩

lemma profile_nonneg (r : ℝ) (C : Finset Y) (y : Y) : 0 ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · norm_num
  · obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    exact (ramp_bounds _).1

lemma profile_le_one (r : ℝ) (C : Finset Y) (y : Y) : profile r C y ≤ 1 :=
  min'_le _ _ (mem_insert_self _ _)
lemma profile_bounds (r : ℝ) (C : Finset Y) (y : Y) : profile r C y ∈ Set.Icc 0 1 :=
  ⟨profile_nonneg _ _ _,profile_le_one _ _ _⟩
lemma profile_le (r : ℝ) {C : Finset Y} {a : Y} (ha : a∈C) (y : Y) :
    profile r C y ≤ ramp (dist a y/r) :=
  min'_le _ _ (mem_insert_of_mem (mem_image.mpr ⟨a,ha,rfl⟩))
lemma le_profile (r : ℝ) (C : Finset Y) (y : Y) {u : ℝ} (hu : u ≤ 1)
    (h : ∀ a∈C,u ≤ ramp (dist a y/r)) : u ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact hu
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact h a ha
lemma profile_empty (r : ℝ) (y : Y) : profile r ∅ y=1 := by
  simp [profile]
lemma profile_eq_one {r : ℝ} (hr : 0<r) {C : Finset Y} {y : Y}
    (h : ∀ a∈C,10*r ≤ dist a y) : profile r C y=1 := by
  apply le_antisymm (profile_le_one _ _ _)
  apply le_profile _ _ _ le_rfl
  intro a ha
  rw [ramp_one ((le_div_iff₀ hr).mpr (h a ha))]
lemma profile_eq_zero {r : ℝ} (hr : 0<r) {C : Finset Y} {a y : Y}
    (ha : a∈C) (hay : dist a y ≤ 9*r) : profile r C y=0 := by
  apply le_antisymm _ (profile_nonneg _ _ _)
  exact (profile_le r ha y).trans_eq (ramp_zero ((div_le_iff₀ hr).mpr hay))

lemma profile_gt_witness {r : ℝ} {C : Finset Y} {y : Y} {u : ℝ}
    (hu : u ≤ 1) (h : profile r C y<u) :
    ∃ a∈C,ramp (dist a y/r)<u := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (le_profile r C y hu hn)) h

lemma profile_lipschitz {r : ℝ} (hr : 0<r) (C : Finset Y) (y z : Y) :
    |profile r C y-profile r C z| ≤ dist y z/r := by
  have hdir (y z : Y) : profile r C y-profile r C z ≤ dist y z/r := by
    suffices profile r C y-dist y z/r ≤ profile r C z by linarith
    apply le_profile r C z
    · linarith [profile_le_one r C y,div_nonneg (dist_nonneg (x := y) (y := z)) hr.le]
    · intro a ha
      have hl := ramp_lipschitz (dist a y/r) (dist a z/r)
      have hm : |dist a y-dist a z| ≤ dist y z := by
        simpa only [dist_comm a] using abs_dist_sub_le y z a
      rw [←sub_div,abs_div,abs_of_pos hr] at hl
      have hb := hl.trans (div_le_div_of_nonneg_right hm hr.le)
      have hc := (le_abs_self (ramp (dist a y/r)-ramp (dist a z/r))).trans hb
      linarith [profile_le r ha y]
  rw [abs_sub_le_iff]
  exact ⟨hdir y z,by simpa only [dist_comm z y] using hdir z y⟩


open HeavyCenters HeavyLabels HeavyKeys

lemma profile_far {r:ℝ} (hr:0<r) (C:Finset Y) {x p:Y}
    (hp:120*r<dist x p) : profile r (replace r C x) p=profile r C p := by
  apply le_antisymm
  · apply le_profile _ _ _ (profile_le_one _ _ _)
    intro a ha
    by_cases hax:100*r<dist a x
    · exact profile_le r (mem_insert_of_mem (mem_filter.mpr ⟨ha,hax⟩)) p
    · have ht:=dist_triangle x a p
      rw [dist_comm x a] at ht
      have hap:10*r≤dist a p:=by linarith
      rw [ramp_one ((le_div_iff₀ hr).mpr hap)]
      exact profile_le_one _ _ _
  · apply le_profile _ _ _ (profile_le_one _ _ _)
    intro a ha
    rcases mem_insert.mp ha with hax|ha
    · subst a
      rw [ramp_one ((le_div_iff₀ hr).mpr (by linarith))]
      exact profile_le_one _ _ _
    · exact profile_le r (mem_filter.mp ha).1 p

variable [Fintype Y]

def oldKey (C:Finset Y) (rad:Y→ℝ) (lab:Y→Pool Y) (p:Y) : Option (Pool Y) :=
  (centerKey C rad p).map lab

def newKey (C D:Finset Y) (rad:Y→ℝ) (lab prev:Y→Pool Y) (r:ℝ) (x:Y) (R:ℝ)
    (p:Y) : Option (Pool Y) :=
  (centerKey (replace r C x) (Function.update rad x R) p).map
    (updatedLabel C D rad lab prev x R)

omit [Fintype Y] in
lemma replace_separated {r:ℝ} {C:Finset Y} {x:Y}
    (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b)) :
    (replace r C x:Set Y).Pairwise (fun a b=>100*r<dist a b) := by
  intro a ha b hb hn
  rcases mem_insert.mp ha with hax|ha
  · subst a
    have hb':=(mem_insert.mp hb).resolve_left (Ne.symm hn)
    simpa only [dist_comm] using (mem_filter.mp hb').2
  · rcases mem_insert.mp hb with hbx|hb
    · subst b; exact (mem_filter.mp ha).2
    · exact hC (mem_filter.mp ha).1 (mem_filter.mp hb).1 hn

omit [Fintype Y] in
lemma new_radius {r R:ℝ} (hr:0<r) {C:Finset Y} {x:Y} {rad:Y→ℝ}
    (hrad:∀ a∈C,rad a≤20*r) (hR:R≤20*r) :
    ∀ a∈replace r C x,Function.update rad x R a≤20*r := by
  intro a ha
  rcases mem_insert.mp ha with hax|ha
  · subst a; simpa only [Function.update_self] using hR
  · have hn:a≠x:=by intro he; have h:=(mem_filter.mp ha).2; rw [he,dist_self] at h; linarith
    simpa only [Function.update_of_ne hn] using hrad a (mem_filter.mp ha).1

lemma inner_reuses {r R:ℝ} (hr:0<r) {C D:Finset Y} {x p a:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r))
    (ha:a∈C) (hap:dist a p≤10*r) (hxp:dist x p≤3*r) :
    oldKey C rad lab p=newKey C D rad lab prev r x R p := by
  have haP:dist a p≤rad a:=by linarith [(hrad a ha).1]
  have hxP:dist x p≤R:=by linarith [hR.1]
  have ho:centerKey C rad p=some a:=
    (centerKey_some hr hC (fun a ha=>(hrad a ha).2)).mpr ⟨ha,haP⟩
  have hn:centerKey (replace r C x) (Function.update rad x R) p=some x:=
    (centerKey_some hr (replace_separated hC) (new_radius hr (fun a ha=>(hrad a ha).2) hR.2)).mpr
      ⟨mem_insert_self _ _,by simpa only [Function.update_self] using hxP⟩
  have hl:=inserted_reuses (D:=D) (label:=lab) (prev:=prev) hr hC
    (fun a ha=>(hrad a ha).2) hR.2 (mem_filter.mpr ⟨ha,⟨p,haP,hxP⟩⟩)
  simp only [oldKey,newKey,ho,hn,Option.map_some,updatedLabel,Function.update_self,hl]

lemma keys_far {r R:ℝ} (hr:0<r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a≤20*r) (hR:R≤20*r) (hp:120*r<dist x p) :
    oldKey C rad lab p=newKey C D rad lab prev r x R p := by
  have hnc:¬dist x p≤R:=by linarith
  cases he:centerKey C rad p with
  | none =>
    have hn:centerKey (replace r C x) (Function.update rad x R) p=none:=by
      apply (centerKey_none _ _ _).mpr
      intro a ha
      rcases mem_insert.mp ha with hax|ha
      · subst a; simpa only [Function.update_self] using lt_of_not_ge hnc
      · have hax:a≠x:=by intro hh; have h:=(mem_filter.mp ha).2; rw [hh,dist_self] at h; linarith
        rw [Function.update_of_ne hax]
        exact (centerKey_none C rad p).mp he a (mem_filter.mp ha).1
    simp only [oldKey,newKey,he,hn,Option.map_none]
  | some a =>
    obtain ⟨ha,hap⟩:=(centerKey_some hr hC hrad).mp he
    have ht:=dist_triangle x a p
    rw [dist_comm x a] at ht
    have hax:100*r<dist a x:=by linarith [hrad a ha]
    have han:a≠x:=by intro hh; rw [hh,dist_self] at hax; linarith
    have hn:centerKey (replace r C x) (Function.update rad x R) p=some a:=by
      apply (centerKey_some hr (replace_separated hC) (new_radius hr hrad hR)).mpr
      exact ⟨mem_insert_of_mem (mem_filter.mpr ⟨ha,hax⟩),by simpa only [Function.update_of_ne han] using hap⟩
    simp only [oldKey,newKey,he,hn,Option.map_some,updatedLabel,Function.update_of_ne han]

lemma inner_paid {r R:ℝ} (hr:0<r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r))
    (hxp:dist x p≤3*r) :
    (if oldKey C rad lab p≠newKey C D rad lab prev r x R p then (1:ℝ) else 0) +
      profile r (replace r C x) p-profile r C p≤0 := by
  have hn:profile r (replace r C x) p=0:=profile_eq_zero hr (mem_insert_self _ _) (by linarith)
  rw [hn]
  by_cases he:∃ a∈C,dist a p≤10*r
  · obtain ⟨a,ha,hap⟩:=he
    rw [ite_eq_right (not_not.mpr (inner_reuses hr hC hrad hR ha hap hxp))]
    linarith [profile_nonneg r C p]
  · have hp:profile r C p=1:=by
      apply profile_eq_one hr
      intro a ha
      exact le_of_lt (lt_of_not_ge (fun hh=>he ⟨a,ha,hh⟩))
    rw [hp]
    split_ifs <;> norm_num

/-- Source heavy edit charge table for a stationary member. -/
theorem stationary {r R:ℝ} (hr:0<r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r)) :
    (if oldKey C rad lab p≠newKey C D rad lab prev r x R p then (1:ℝ) else 0) +
      profile r (replace r C x) p-profile r C p≤
        if 3*r<dist x p ∧ dist x p≤120*r then 2 else 0 := by
  by_cases hnear:dist x p≤3*r
  · rw [ite_eq_right (show ¬(3*r<dist x p ∧ dist x p≤120*r) from fun h=>not_lt_of_ge hnear h.1)]
    exact inner_paid hr hC hrad hR hnear
  · by_cases hfar:120*r<dist x p
    · rw [profile_far hr C hfar,ite_eq_right (show ¬(3*r<dist x p ∧ dist x p≤120*r) from fun h=>not_le_of_gt hfar h.2),
        ite_eq_right (not_not.mpr (keys_far (D:=D) (lab:=lab) (prev:=prev) hr hC (fun a ha=>(hrad a ha).2) hR.2 hfar))]
      ring_nf
      exact le_rfl
    · rw [ite_eq_left (show 3*r<dist x p ∧ dist x p≤120*r from ⟨lt_of_not_ge hnear,le_of_not_gt hfar⟩)]
      have ho:=profile_nonneg r C p
      have hn:=profile_le_one r (replace r C x) p
      split_ifs <;> linarith

/-- Source heavy edit charge table for the designated mover. -/
theorem mover {r R:ℝ} (hr:0<r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r)) :
    (if oldKey C rad lab p≠newKey C D rad lab prev r x R p then (1:ℝ) else 0) +
      profile r (replace r C x) x-profile r C p≤ if 3*r<dist x p then 1 else 0 := by
  by_cases hnear:dist x p≤3*r
  · have hh:=inner_paid (D:=D) (lab:=lab) (prev:=prev) hr hC hrad hR hnear
    have hp:profile r (replace r C x) p=0:=profile_eq_zero hr (mem_insert_self _ _) (by linarith)
    have hx:profile r (replace r C x) x=0:=profile_eq_zero hr (mem_insert_self _ _) (by simpa only [dist_self] using (mul_nonneg (by norm_num : (0:ℝ)≤9) hr.le))
    rw [ite_eq_right (not_lt_of_ge hnear),hx]
    simpa only [hp] using hh
  · rw [ite_eq_left (lt_of_not_ge hnear)]
    have hx:profile r (replace r C x) x=0:=profile_eq_zero hr (mem_insert_self _ _) (by simpa only [dist_self] using (mul_nonneg (by norm_num : (0:ℝ)≤9) hr.le))
    rw [hx]
    have ho:=profile_nonneg r C p
    split_ifs <;> linarith
end KServer.HeavyEdit

end


/-! The actual heavy-priority stage, including its deterministic clipped-ramp
potential and the true hidden trajectory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyTemporal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw PriorityKeys ActualRoster
open HeavyCenters HeavySchedule HeavyLabels LevelRetirement RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def active (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) : Prop :=
  Active r heavyGamma heavyDelta (centers s law r heavyGamma heavyDelta σ t)
    (mu s law (t.val+1) σ) (σ t)

def charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (p:Y) : ℝ :=
  indicator (PriorityKeys.key (stageBefore (keys s law hr σ a t) (keys s law hr σ a (t+1)) none) p≠
    PriorityKeys.key (stageAfter (keys s law hr σ a t) (keys s law hr σ a (t+1)) none) p)

def profile (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:ℕ) (p:Y) : ℝ :=
  HeavyEdit.profile r (centers s law r heavyGamma heavyDelta σ t) p

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma ite_indicator (P:Prop) (d:Decidable P) : @ite ℝ P d 1 0=indicator P := by
  by_cases h:P <;> simp [indicator,h]

lemma charge_le (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (p:Y) :
    charge s law hr σ a t p ≤ indicator
      (HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t p≠
        HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t+1) p) :=
  stage_charge _ _ _ _

lemma active_keys (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (ha:active s law r σ t) (p:Y) :
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t.val+1) p=
      HeavyEdit.newKey (centers s law r heavyGamma heavyDelta σ t)
      (centers s law r heavyGamma heavyDelta σ (t.val-1))
      (run s law r heavyGamma heavyDelta σ a.1 t).rad
      (run s law r heavyGamma heavyDelta σ a.1 t).label
      (run s law r heavyGamma heavyDelta σ a.1 t).previous r (σ t)
      (FiniteUniform.radius r (a.1 t)) p := by
  simp only [HeavyKeys.key,centers_succ,HeavyCenters.step,run,t.isLt,dite_eq_left,active] at ha ⊢
  simp only [ite_eq_left ha]
  rfl

lemma inactive_keys (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (ha:¬active s law r σ t) (p:Y) :
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t.val+1) p=
      HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t p := by
  simp only [HeavyKeys.key,centers_succ,HeavyCenters.step,run,t.isLt,dite_eq_left,active] at ha ⊢
  simp only [ite_eq_right ha]

lemma inactive_charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (ha:¬active s law r σ t) (p:Y) :
    charge s law hr σ a t p=0 := by
  have hb:=charge_le s law hr σ a t p
  rw [inactive_keys s law r σ a t ha p] at hb
  simp only [ne_self_iff_false,indicator,ite_false] at hb
  exact le_antisymm hb (indicator_nonneg _)

lemma active_profile (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (t:Fin H) (ha:active s law r σ t) (p:Y) :
    profile s law r σ (t.val+1) p=HeavyEdit.profile r
      (replace r (centers s law r heavyGamma heavyDelta σ t) (σ t)) p := by
  dsimp only [active] at ha
  simp only [profile,centers_succ,HeavyCenters.step,ite_eq_left ha]

lemma inactive_profile (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (t:Fin H) (ha:¬active s law r σ t) (p:Y) :
    profile s law r σ (t.val+1) p=profile s law r σ t p := by
  dsimp only [active] at ha
  simp only [profile,centers_succ,HeavyCenters.step,ite_eq_right ha]

lemma stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (p:Y) :
    charge s law hr.le σ a t p+profile s law r σ (t.val+1) p-profile s law r σ t p ≤
      if active s law r σ t then 2*indicator (3*r<dist (σ t) p ∧ dist (σ t) p≤120*r) else 0 := by
  by_cases ha:active s law r σ t
  · rw [ite_eq_left ha,active_profile s law r σ t ha p]
    have hc:=charge_le s law hr.le σ a t p
    rw [active_keys s law r σ a t ha p] at hc
    have hb:=HeavyEdit.stationary (x:=σ t) (D:=centers s law r heavyGamma heavyDelta σ (t.val-1))
      (lab:=(run s law r heavyGamma heavyDelta σ a.1 t).label)
      (prev:=(run s law r heavyGamma heavyDelta σ a.1 t).previous) hr
      (centers_separated s law r heavyGamma heavyDelta σ t)
      (run_valid s law hr heavyGamma heavyDelta σ a.1 t).1 (FiniteUniform.radius_range hr (a.1 t))
      (p:=p)
    simp only [HeavyKeys.key] at hc
    have he:(if 3*r<dist (σ t) p ∧ dist (σ t) p≤120*r then (2:ℝ) else 0)=
        2*indicator (3*r<dist (σ t) p ∧ dist (σ t) p≤120*r):=by
      unfold indicator
      split_ifs <;> norm_num
    rw [he] at hb
    dsimp only [profile]
    simp only [HeavyEdit.oldKey] at hb
    apply (sub_le_sub (add_le_add hc (le_refl _)) (le_refl _)).trans
    convert hb using 1; first | rfl | (simp only [indicator]; congr 4)
  · rw [ite_eq_right ha,inactive_charge s law hr.le σ a t ha p,inactive_profile s law r σ t ha p]
    ring_nf
    exact le_rfl


def heavy (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) : Prop :=
  mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
    (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r))

lemma mover (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (p:Y) :
    charge s law hr.le σ a t p+profile s law r σ (t.val+1) (σ t)-profile s law r σ t p ≤
      indicator (3*r<dist (σ t) p)+(if heavy s law r σ t then 0 else dist (σ t) p/r) := by
  by_cases ha:active s law r σ t
  · have hh:heavy s law r σ t:=ha.1
    rw [active_profile s law r σ t ha (σ t),ite_eq_left hh]
    have hc:=charge_le s law hr.le σ a t p
    rw [active_keys s law r σ a t ha p] at hc
    have hb:=HeavyEdit.mover (x:=σ t) (D:=centers s law r heavyGamma heavyDelta σ (t.val-1))
      (lab:=(run s law r heavyGamma heavyDelta σ a.1 t).label)
      (prev:=(run s law r heavyGamma heavyDelta σ a.1 t).previous) hr
      (centers_separated s law r heavyGamma heavyDelta σ t)
      (run_valid s law hr heavyGamma heavyDelta σ a.1 t).1 (FiniteUniform.radius_range hr (a.1 t))
      (p:=p)
    simp only [HeavyKeys.key] at hc
    simp only [HeavyEdit.oldKey] at hb
    dsimp only [profile]
    simp only [add_zero]
    apply (sub_le_sub (add_le_add hc (le_refl _)) (le_refl _)).trans
    convert hb using 1 <;> first | rfl | (simp only [indicator]; congr 4)
  · rw [inactive_charge s law hr.le σ a t ha p,inactive_profile s law r σ t ha (σ t)]
    by_cases hh:heavy s law r σ t
    · rw [ite_eq_left hh]
      have he:∃ a∈centers s law r heavyGamma heavyDelta σ t,dist a (σ t)≤8*r:=by
        by_contra hn
        push Not at hn
        exact ha ⟨hh,hn⟩
      obtain ⟨b,hb,hbd⟩:=he
      have hz:profile s law r σ t (σ t)=0:=HeavyEdit.profile_eq_zero hr hb (by linarith)
      rw [hz]
      have hp:=HeavyEdit.profile_nonneg r (centers s law r heavyGamma heavyDelta σ t) p
      have hi:=indicator_nonneg (3*r<dist (σ t) p)
      dsimp only [profile]
      linarith
    · rw [ite_eq_right hh]
      have hb:=(le_abs_self _).trans (HeavyEdit.profile_lipschitz hr
        (centers s law r heavyGamma heavyDelta σ t) (σ t) p)
      have hi:=indicator_nonneg (3*r<dist (σ t) p)
      dsimp only [profile]
      linarith

end KServer.HeavyTemporal

end


/-! True-prefix causality of the literal fixed-label complete level map.
The finite permanent colors and cooldown reservations do not read the future. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeysAdapted
open FiniteExperiment TierProcess Chronological ActualRoster LevelKeys LevelLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [NeZero k] in
lemma history_mono {t T:ℕ} (ht:t≤T) (σ ρ:Fin H→Y)
    (hh:requestHistory T σ=requestHistory T ρ) : requestHistory t σ=requestHistory t ρ := by
  rw [requestHistory_eq_iff] at hh ⊢
  funext i
  by_cases hi:i.val<t
  · have hiT:i.val<T:=lt_of_lt_of_le hi ht
    have he:=congrFun hh i
    simpa only [requestPrefix,ite_eq_left hi,ite_eq_left hiT] using he
  · simp only [requestPrefix,ite_eq_right hi]

lemma run_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (r γ δ:ℝ) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    HeavySchedule.run s law r γ δ σ tape t=HeavySchedule.run s law r γ δ ρ tape t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h0:requestHistory t σ=requestHistory t ρ:=requestHistory_refines t σ ρ hh
    have hd:=ih h0
    have hc:=HeavyCenters.centers_adapted s law r γ δ t σ ρ h0
    have hp:=HeavyCenters.centers_adapted s law r γ δ (t-1) σ ρ (history_mono (Nat.sub_le _ _) σ ρ h0)
    have hm:mu s law (t+1) σ=mu s law (t+1) ρ:=funext (fun p=>mu_adapted s law (t+1) p σ ρ hh)
    simp only [HeavySchedule.run,hd,hc,hp,hm]
    by_cases ht:t<H
    · simp only [dite_eq_left ht]
      rw [request_of_history ⟨t,ht⟩ σ ρ hh]
    · simp only [dite_eq_right ht]

lemma heavy_key_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (r γ δ:ℝ) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (p:Y)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    HeavyKeys.key s law r γ δ σ tape t p=HeavyKeys.key s law r γ δ ρ tape t p := by
  unfold HeavyKeys.key
  rw [run_adapted s law r γ δ tape t σ ρ hh,HeavyCenters.centers_adapted s law r γ δ t σ ρ hh]

lemma reserved_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) (r γ h:ℝ) (K t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    reserved (request s σ) r K (qualifies s law T r γ h σ) t=
      reserved (request s ρ) r K (qualifies s law T r γ h ρ) t := by
  change young (request s σ) (roster s law T r γ h K σ t) (20*r) (K^2)=_
  have he:=roster_adapted s law T r γ h K t σ ρ hh
  change _=young (request s ρ) (roster s law T r γ h K ρ t) (20*r) (K^2)
  rw [←he]
  unfold young
  apply filter_congr
  intro i hi
  rw [ShortRoster.age_congr (request_adapted s (roster_before s law T r γ h K σ t i hi) σ ρ hh)
    (fun j hj=>request_adapted s (roster_before s law T r γ h K σ t j hj) σ ρ hh)]

lemma conflicts_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) (r γ h:ℝ) (K t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    conflicts (request s σ) r K (qualifies s law T r γ h σ) t=
      conflicts (request s ρ) r K (qualifies s law T r γ h ρ) t := by
  unfold conflicts
  rw [reserved_adapted s law T r γ h K t σ ρ hh,
    reserved_adapted s law T r γ h K (t-1) σ ρ (history_mono (Nat.sub_le _ _) σ ρ hh)]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma stage_congr {M t:ℕ} (hM:0<M) {c d:ℕ→Finset ℕ}
    (hc:∀ j,(c j).card<M) (hd:∀ j,(d j).card<M) (he:∀ j,j<t→c j=d j) :
    OnlineLabels.stage hM c hc t=OnlineLabels.stage hM d hd t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp:=ih (fun j hj=>he j (by omega))
    simp only [OnlineLabels.stage,hp,he t (by omega)]

lemma label_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) {r:ℝ} (hr:0≤r) (γ h:ℝ) (K t i:ℕ) (hi:i<t)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) i=
      Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i := by
  unfold Chronological.label OnlineLabels.color
  have he:=stage_congr (t:=i+1) (pool_pos (Y:=Y) K)
    (conflicts_card (request s σ) hr K (qualifies s law T r γ h σ))
    (conflicts_card (request s ρ) hr K (qualifies s law T r γ h ρ))
    (fun j hj=>conflicts_adapted s law T r γ h K j σ ρ (history_mono (by omega) σ ρ hh))
  exact congrFun he i

lemma first_congr {c d:ℕ→Y} {I:Finset ℕ} {r:ℝ} {K:ℕ}
    (hc:∀ j∈I,c j=d j) (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (p:Y) :
    first c I r life rad p=first d I r life rad p := by
  have he:covered c I r life rad p=covered d I r life rad p:=by
    funext i
    apply propext
    unfold covered present
    by_cases hi:(i:ℕ)∈I
    · rw [ShortRoster.age_congr (hc i hi) hc,hc i hi]
    · simp only [hi,false_and]
  unfold first
  rw [he]

lemma tier_key_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) {r:ℝ} (hr:0≤r) (γ h:ℝ) (K:ℕ)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    TierKeys.key (request s σ) hr K (qualifies s law T r γ h σ) life rad t p=
      TierKeys.key (request s ρ) hr K (qualifies s law T r γ h ρ) life rad t p := by
  have hR:=roster_adapted s law T r γ h K t σ ρ hh
  have hf:first (request s σ) (roster s law T r γ h K σ t) r life rad p=
      first (request s ρ) (roster s law T r γ h K ρ t) r life rad p:=by
    exact (first_congr (fun j hj=>request_adapted s (roster_before s law T r γ h K σ t j hj) σ ρ hh) life rad p).trans
      (congrArg (fun I=>first (request s ρ) I r life rad p) hR)
  change (first (request s σ) (roster s law T r γ h K σ t) r life rad p).map
    (fun j:Fin H=>Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) j)=
    (first (request s ρ) (roster s law T r γ h K ρ t) r life rad p).map
    (fun j:Fin H=>Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) j)
  refine (Option.map_congr ?_).trans (congrArg (fun z=>z.map
    (fun j:Fin H=>Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) j)) hf)
  intro i he
  have hi:=(first_some_iff (request s σ) (roster s law T r γ h K σ t) r life rad p i).mp he
  exact label_adapted s law T hr γ h K t i
    (roster_before s law T r γ h K σ t i hi.1.1.1) σ ρ hh

lemma keys_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0≤r) (a:Tape Y k H r) (t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    keys s law hr σ a t=keys s law hr ρ a t := by
  funext i p
  cases i with
  | none => exact heavy_key_adapted s law _ _ _ a.1 t p σ ρ hh
  | some i =>
    exact tier_key_adapted s law tierTemplate hr tierGamma (height i) (tierK (height i))
      (a.2 i).1 (a.2 i).2 t p σ ρ hh

lemma map_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0≤r) (a:Tape Y k H r) (t:ℕ) (p:Y) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    LevelKeys.map s law hr σ a t p=LevelKeys.map s law hr ρ a t p := by
  unfold LevelKeys.map
  rw [keys_adapted s law hr a t σ ρ hh]

end KServer.KeysAdapted

end


/-! True-prefix heavy edit accounting. The deterministic profile is telescoped
on the hidden labeled optimum; no surviving-radius conditioning is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw PriorityKeys ActualRoster
open HeavyCenters HeavySchedule HeavyLabels LevelRetirement RankTracking PosteriorRanks
open HiddenAverages HeavyTemporal TierGlobal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def test (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (p:Y) : ℝ :=
  if active s law r σ t then indicator (3*r<dist (σ t) p ∧ dist (σ t) p≤120*r) else 0

lemma test_nonneg (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (p:Y) :
    0≤test s law r σ t p := by unfold test; split_ifs; exact indicator_nonneg _; rfl

lemma test_adapted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (p:Y) :
    Adapted (requestHistory (t.val+1)) (fun σ=>test s law r σ t p) := by
  intro σ ρ hh
  have hm:mu s law (t.val+1) σ=mu s law (t.val+1) ρ:=funext (fun y=>mu_adapted s law (t.val+1) y σ ρ hh)
  have hp:requestHistory t.val σ=requestHistory t.val ρ:=by
    exact KeysAdapted.history_mono (Nat.le_succ _) σ ρ hh
  have hc:=centers_adapted s law r heavyGamma heavyDelta t.val σ ρ hp
  simp only [test,active,hm,hc,request_of_history t σ ρ hh]
  congr 4

lemma test_mass (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) :
    (∑ y,mu s law (t.val+1) σ y*test s law r σ t y)=
      if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0 := by
  unfold test
  split_ifs
  · simp only [indicator,mul_ite,mul_one,mul_zero]
    rw [←sum_filter]
    congr 1
  · simp

lemma stationary_bound (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) :
    avg law.val (fun σ=>∑ l∈univ.erase (FiniteExperiment.mover s σ t),test s law r σ t (hidden s σ t l)) ≤
      avg law.val (fun σ=>if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0) := by
  rw [←expected_stationary_test s law t (fun σ p=>test s law r σ t p) (test_adapted s law r t)]
  trans avg law.val (fun σ=>∑ y,mu s law (t.val+1) σ y*test s law r σ t y)
  · apply sum_le_sum
    intro σ _
    by_cases hs:0<law.val σ
    · apply mul_le_mul_of_nonneg_left _ hs.le
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (stationary_le s law t σ hs y) (test_nonneg s law r σ t y)
    · have hz:law.val σ=0:=le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp only [hz,zero_mul,le_refl]
  · apply le_of_eq
    congr 1
    funext σ
    exact test_mass s law r σ t

def potential (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:ℕ) : ℝ :=
  ∑ l,HeavyTemporal.profile s law r σ t (hidden s σ t l)

def editCost (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) : ℝ :=
  ∑ l,HeavyTemporal.charge s law hr σ a t (hidden s σ t l)

lemma potential_bounds (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:ℕ) :
    potential s law r σ t∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact sum_nonneg (fun l _=>HeavyEdit.profile_nonneg _ _ _)
  · exact (sum_le_sum (fun l (_:l∈univ)=>HeavyEdit.profile_le_one _ _ _)).trans_eq (by simp)

lemma potential_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) :
    editCost s law hr σ a t+potential s law r σ (t.val+1)-potential s law r σ t=
      (∑ l∈univ.erase (FiniteExperiment.mover s σ t),(HeavyTemporal.charge s law hr σ a t (hidden s σ t l)+
        HeavyTemporal.profile s law r σ (t.val+1) (hidden s σ t l)-HeavyTemporal.profile s law r σ t (hidden s σ t l)))+
      (HeavyTemporal.charge s law hr σ a t (hidden s σ t (FiniteExperiment.mover s σ t))+
        HeavyTemporal.profile s law r σ (t.val+1) (σ t)-HeavyTemporal.profile s law r σ t (hidden s σ t (FiniteExperiment.mover s σ t))) := by
  have he:potential s law r σ (t.val+1)=
    (∑ l∈univ.erase (FiniteExperiment.mover s σ t),HeavyTemporal.profile s law r σ (t.val+1) (hidden s σ t l))+
      HeavyTemporal.profile s law r σ (t.val+1) (σ t) := by
    unfold potential
    rw [←sum_erase_add _ _ (mem_univ (FiniteExperiment.mover s σ t)),hidden_covers]
    congr 1
    apply sum_congr rfl
    intro l hl
    congr 1
    have he:=congrFun (hidden_step s σ t) l
    simpa [serve,(mem_erase.mp hl).1] using he
  rw [he]
  unfold editCost potential
  have hC:=sum_erase_add univ (fun l:Fin k=>HeavyTemporal.charge s law hr σ a t (hidden s σ t l)) (mem_univ (FiniteExperiment.mover s σ t))
  have hU:=sum_erase_add univ (fun l:Fin k=>HeavyTemporal.profile s law r σ t (hidden s σ t l)) (mem_univ (FiniteExperiment.mover s σ t))
  simp only [sum_sub_distrib,sum_add_distrib]
  linarith

lemma step_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) :
    editCost s law hr.le σ a t+potential s law r σ (t.val+1)-potential s law r σ t≤
      2*(∑ l∈univ.erase (FiniteExperiment.mover s σ t),test s law r σ t (hidden s σ t l))+
      indicator (3*r<dist (σ t) (hidden s σ t (FiniteExperiment.mover s σ t)))+
      (if heavy s law r σ t then 0 else dist (σ t) (hidden s σ t (FiniteExperiment.mover s σ t))/r) := by
  rw [potential_step]
  have hs:=sum_le_sum (fun l (_:l∈univ.erase (FiniteExperiment.mover s σ t))=>HeavyTemporal.stationary s law hr σ a t (hidden s σ t l))
  have he: (∑ l∈univ.erase (FiniteExperiment.mover s σ t),(if active s law r σ t then
      2*indicator (3*r<dist (σ t) (hidden s σ t l) ∧ dist (σ t) (hidden s σ t l)≤120*r) else 0))=
      2*(∑ l∈univ.erase (FiniteExperiment.mover s σ t),test s law r σ t (hidden s σ t l)) := by
    unfold test
    split_ifs
    · rw [mul_sum]
    · simp
  rw [he] at hs
  have hm:=HeavyTemporal.mover s law hr σ a t (hidden s σ t (FiniteExperiment.mover s σ t))
  linarith

lemma average_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (t:Fin H) :
    avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t))+
      avg law.val (fun σ=>potential s law r σ (t.val+1))-
      avg law.val (fun σ=>potential s law r σ t) ≤
    2*avg law.val (fun σ=>if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0)+
      avg law.val (fun σ=>indicator (3*r<dist (σ t) (hidden s σ t (mover s σ t))))+
      avg law.val (fun σ=>if heavy s law r σ t then 0 else dist (σ t) (hidden s σ t (mover s σ t))/r) := by
  have hb:=avg_mono law.property.1 (fun σ=>(mean_mono hr (fun a=>step_bound s law hr σ a t)))
  simp only [TierTemporal.mean_sub,TierTemporal.mean_add,mean_const hr,avg_add,avg_sub,avg_mul] at hb
  have hs:=stationary_bound s law r t
  linarith

lemma mean_bounds (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:ℕ) :
    avg law.val (fun σ=>potential s law r σ t)∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact (show 0=avg law.val (fun _=>0) by rw [avg_const _ law.property.2]).le.trans
      (avg_mono law.property.1 (fun σ=>(potential_bounds s law r σ t).1))
  · calc _ ≤ avg law.val (fun _=>(k:ℝ)) := avg_mono law.property.1 (fun σ=>(potential_bounds s law r σ t).2)
         _ = _ := avg_const _ law.property.2 _

lemma heavy_budget (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r) :
    (∑ t:Fin H,avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t))) ≤
    2*(∑ t:Fin H,avg law.val (fun σ=>if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0))+
      (∑ t:Fin H,avg law.val (fun σ=>indicator (3*r<dist (σ t) (hidden s σ t (mover s σ t)))))+
      (∑ t:Fin H,avg law.val (fun σ=>if heavy s law r σ t then 0 else dist (σ t) (hidden s σ t (mover s σ t))/r))+k := by
  have hb:=telescope_budget (fun t=>avg law.val (fun σ=>potential s law r σ t)) _ _
    (average_step s law hr) (mean_bounds s law r H).1
  simp only [sum_add_distrib,←mul_sum] at hb
  exact hb.trans (add_le_add le_rfl (mean_bounds s law r 0).2)

end KServer.HeavyBudget

end

end OAI
