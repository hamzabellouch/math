import Mathlib
import OAI.Combinatorics.KServer.AllocationMovement
import OAI.Combinatorics.KServer.Hierarchy
import OAI.Combinatorics.KServer.PartitionBudget

namespace OAI

/-! The posterior counting measure is built from labeled hidden positions.
Integrating adapted metric tests is exactly conditional expectation, and
prefix quota domination is relative to this measure, not an extra premise. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PosteriorCounting
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking PosteriorRanks HierarchyCounts
variable {Ω Y A:Type} [Fintype Ω] [Fintype Y] [Fintype A]
variable {w:Ω→ℝ} (hw:∀ ω,0≤w ω) {k:ℕ}

def atoms (q:Fin k→Y) (y:Y):ℝ:=∑ l:Fin k,if q l=y then 1 else 0

def measure (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω) (y:Y):ℝ:=
  posterior w H (fun ρ=>atoms (q ρ) y) ω

omit [Fintype Y] in
lemma atoms_nonneg (q:Fin k→Y) (y:Y):0≤atoms q y:=by
  exact sum_nonneg fun _ _=>by split_ifs <;> norm_num

lemma atoms_total (q:Fin k→Y):(∑ y,atoms q y)=(k:ℝ):=by
  unfold atoms
  rw [sum_comm]
  simp

include hw in
omit [Fintype Y] in
lemma measure_nonneg (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω) (y:Y):
    0 ≤ measure (w:=w) H q ω y:=posterior_nonneg hw H (fun _=>atoms_nonneg _ _) ω

omit [Fintype Y] in
lemma measure_adapted (H:Ω→ℕ) (q:Ω→Fin k→Y) (y:Y):
    Adapted H (fun ω=>measure (w:=w) H q ω y):=posterior_adapted w H _

include hw in
lemma measure_total (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω) (hω:0<w ω):
    (∑ y,measure (w:=w) H q ω y)=(k:ℝ):=by
  unfold measure
  rw [←posterior_sum]
  exact posterior_fiber_const ω (fun _ _=>atoms_total _) (positive_mass hw H ω hω).ne'

lemma atoms_integral (q:Fin k→Y) (f:Y→ℝ):
    (∑ y,atoms q y*f y)=∑ l:Fin k,f (q l):=by
  unfold atoms
  simp only [sum_mul,ite_mul,one_mul,zero_mul]
  rw [sum_comm]
  simp

lemma conditional_integral (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω)
    (F:Ω→Y→ℝ) (hF:∀ ρ,H ρ=H ω→F ρ=F ω):
    (∑ y,measure (w:=w) H q ω y*F ω y)=
      posterior w H (fun ρ=>∑ l:Fin k,F ρ (q ρ l)) ω:=by
  unfold measure
  simp_rw [←posterior_mul]
  rw [←posterior_sum]
  unfold posterior numerator
  congr 1
  apply sum_congr rfl
  intro ρ hρ
  dsimp only
  rw [atoms_integral,hF ρ (mem_filter.mp hρ).2]

lemma conditional_mean (H:Ω→ℕ) (f:Ω→ℝ) (ω:Ω):
    (∑ ρ,conditional w H ω ρ*f ρ)=posterior w H f ω:=by
  unfold conditional posterior numerator
  simp only [ite_mul,zero_mul,div_mul_eq_mul_div]
  rw [←sum_filter,←sum_div]
  rfl

omit [Fintype A] in
lemma prefix_mass (H:Ω→ℕ) (maps:Ω→ℕ→Y→A) (q:Ω→Fin k→Y)
    {d:ℕ} (word:Fin d→A) (ω:Ω) (hm:∀ ρ,H ρ=H ω→maps ρ=maps ω):
    (∑ y∈univ.filter (hit (maps ω) word),measure (w:=w) H q ω y)=
      posterior w H (fun ρ=>(count (maps ρ) word (q ρ):ℝ)) ω:=by
  unfold measure posterior numerator
  rw [←sum_div]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro ρ hρ
  rw [←mul_sum]
  congr 1
  have he:=hm ρ (mem_filter.mp hρ).2
  dsimp only
  rw [he]
  unfold atoms count
  rw [sum_comm]
  simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply sum_congr rfl
  intro l _
  simp [eq_comm]

lemma size_prefix_bound (H:ℕ→Ω→ℕ)
    (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)
    {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω) (hω:0<w ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω):
    HierarchicalRanks.size hw H hr maps q word t ω≤
      ∑ y∈univ.filter (hit (maps t ω) word),measure (w:=w) (H t) (q t) ω y:=by
  rw [prefix_mass (H t) (maps t) (q t) word ω hm,HierarchicalRanks.size_eq]
  rw [←conditional_mean]
  exact (HierarchyCounts.compatible w hw (H t) ω hω (maps t) word (q t)
    (z:=0) (by norm_num)).2.2

end KServer.PosteriorCounting

end


/-! Removing null atoms preserves the literal conditional experiment. This
allows quota feasibility to be used only on positive posterior fibers. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PositiveExperiment
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω:Type} [Fintype Ω]

abbrev Support (w:Ω→ℝ):= {ω:Ω // 0<w ω}

def weight (w:Ω→ℝ):Support w→ℝ:=fun ω=>w ω.val

omit [Fintype Ω] in
lemma weight_pos (w:Ω→ℝ) (ω:Support w):0<weight w ω:=ω.property

lemma sum_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (f:Ω→ℝ):
    (∑ ω:Support w,weight w ω*f ω.val)=∑ ω,w ω*f ω:=by
  have hh:=Fintype.sum_subtype_add_sum_subtype (fun ω=>0<w ω) (fun ω=>w ω*f ω)
  have hz:(∑ ω:{ω:Ω // ¬0<w ω},w ω.val*f ω.val)=0:=by
    apply sum_eq_zero
    intro ω _
    have he:w ω.val=0:=le_antisymm (le_of_not_gt ω.property) (hw ω.val)
    rw [he,zero_mul]
  simpa only [hz,add_zero,weight] using hh

lemma weight_sum {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1):
    (∑ ω:Support w,weight w ω)=1:=by
  simpa only [mul_one] using (sum_support hw (fun _=>1)).trans (by simpa only [mul_one] using hw1)

lemma mass_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (h:ℕ):
    PosteriorRanks.mass (weight w) (fun ω=>H ω.val) h=PosteriorRanks.mass w H h:=by
  simpa only [PosteriorRanks.mass,PosteriorRanks.fiber,sum_filter,mul_ite,mul_one,mul_zero]
    using sum_support hw (fun ω=>if H ω=h then 1 else 0)

lemma numerator_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (f:Ω→ℝ) (h:ℕ):
    PosteriorRanks.numerator (weight w) (fun ω=>H ω.val) (fun ω=>f ω.val) h=
      PosteriorRanks.numerator w H f h:=by
  simpa only [PosteriorRanks.numerator,PosteriorRanks.fiber,sum_filter,mul_ite,mul_zero]
    using sum_support hw (fun ω=>if H ω=h then f ω else 0)

lemma posterior_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (f:Ω→ℝ) (ω:Support w):
    posterior (weight w) (fun ρ=>H ρ.val) (fun ρ=>f ρ.val) ω=posterior w H f ω.val:=by
  simp only [posterior,mass_support hw,numerator_support hw]

lemma measure_support {Y:Type} [Fintype Y] {k:ℕ} {w:Ω→ℝ} (hw:∀ ω,0≤w ω)
    (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Support w) (y:Y):
    PosteriorCounting.measure (w:=weight w) (fun ρ=>H ρ.val) (fun ρ=>q ρ.val) ω y=
      PosteriorCounting.measure (w:=w) H q ω.val y:=
  posterior_support hw H (fun ρ=>PosteriorCounting.atoms (q ρ) y) ω

end KServer.PositiveExperiment

end


/-! The single positive finite joint request/tape experiment for every scale.
All maps use precisely the request history and the independent finite tapes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointExperiment
open FiniteExperiment PartitionProbabilities RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ}

instance (priority := 2000) levelTapeFintype (r:ℝ):Fintype (LevelKeys.Tape Y k H r):=by
  letI (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
  infer_instance

abbrev Tape (Y:Type) [MetricSpace Y] [Fintype Y] (k H L:ℕ) (r:Fin L→ℝ):=
  (d:Fin L)→LevelKeys.Tape Y k H (r d)

def tapeWeight (r:Fin L→ℝ):Tape Y k H L r→ℝ:=
  productWeight (fun d=>LevelLaw.weight (Y:=Y) (k:=k) (H:=H) (r d))

lemma tapeWeight_sum {r:Fin L→ℝ} (hr:∀ d,0<r d):
    (∑ a:Tape Y k H L r,tapeWeight r a)=1:=by
  unfold tapeWeight
  convert productWeight_sum (fun d=>LevelLaw.weight (Y:=Y) (k:=k) (H:=H) (r d))
    (fun d=>LevelLaw.weight_sum (Y:=Y) (k:=k) (H:=H) (hr d)) using 1
  congr 1
  ext x
  simp only [mem_univ]

lemma tapeWeight_nonneg {r:Fin L→ℝ} (hr:∀ d,0<r d) (a:Tape Y k H L r):
    0≤tapeWeight r a:=
  productWeight_nonneg (fun d b=>LevelLaw.weight_nonneg (Y:=Y) (k:=k) (H:=H) (hr d) b) a

def tapeLaw {r:Fin L→ℝ} (hr:∀ d,0<r d):FiniteDistribution (Tape Y k H L r):=
  ⟨tapeWeight r,tapeWeight_nonneg hr,tapeWeight_sum hr⟩

abbrev Raw (Y:Type) [MetricSpace Y] [Fintype Y] (k H L:ℕ) (r:Fin L→ℝ):=
  (Fin H→Y)×Tape Y k H L r

variable (law:FiniteDistribution (Fin H→Y)) {r:Fin L→ℝ} (hr:∀ d,0<r d)

def rawWeight:Raw Y k H L r→ℝ:=FiniteExperiment.weight law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr)
abbrev Atom:=PositiveExperiment.Support (rawWeight (k:=k) law hr)
def weight:Atom (k:=k) law hr→ℝ:=PositiveExperiment.weight (rawWeight law hr)

lemma raw_nonneg (ω:Raw Y k H L r):0≤rawWeight law hr ω:=
  FiniteExperiment.weight_nonneg law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr) ω
lemma weight_pos (ω:Atom (k:=k) law hr):0<weight law hr ω:=ω.property
lemma weight_nonneg (ω:Atom (k:=k) law hr):0≤weight law hr ω:=(weight_pos law hr ω).le
lemma weight_sum:(∑ ω:Atom (k:=k) law hr,weight law hr ω)=1:=
  PositiveExperiment.weight_sum (raw_nonneg law hr) (FiniteExperiment.weight_sum law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr))

lemma avg_raw (f:Raw Y k H L r→ℝ):
    avg (weight (k:=k) law hr) (fun ω=>f ω.val)=avg (rawWeight law hr) f:=
  PositiveExperiment.sum_support (raw_nonneg law hr) f

lemma request_pos (ω:Atom (k:=k) law hr):0<law.val ω.val.1:=by
  have hp:=weight_pos law hr ω
  change 0<law.val ω.val.1*(tapeLaw (Y:=Y) (k:=k) (H:=H) hr).val ω.val.2 at hp
  exact pos_of_mul_pos_left hp ((tapeLaw (Y:=Y) (k:=k) (H:=H) hr).property.1 ω.val.2)

lemma tape_pos (ω:Atom (k:=k) law hr):0<(tapeLaw (Y:=Y) (k:=k) (H:=H) hr).val ω.val.2:=by
  have hp:=weight_pos law hr ω
  change 0<law.val ω.val.1*(tapeLaw (Y:=Y) (k:=k) (H:=H) hr).val ω.val.2 at hp
  exact pos_of_mul_pos_right hp (law.property.1 _)

def history (t:ℕ) (ω:Atom (k:=k) law hr):ℕ:=FiniteExperiment.history t ω.val

lemma history_refines (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr (t+1) ω=history law hr (t+1) ρ):
    history law hr t ω=history law hr t ρ:=FiniteExperiment.history_refines t ω.val ρ.val h

lemma history_eq (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr t ω=history law hr t ρ):
    ω.val.2=ρ.val.2 ∧ requestPrefix ω.val.1 t=requestPrefix ρ.val.1 t:=
  (FiniteExperiment.history_eq_iff t ω.val ρ.val).mp h

variable [NeZero k] (s:Configuration k Y)

def hidden (t:ℕ) (ω:Atom (k:=k) law hr):Fin k→Y:=FiniteExperiment.hidden s ω.val.1 t

def maps (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (y:Y):LevelKeys.Key Y k:=
  if hd:d<L then LevelKeys.map s law (hr ⟨d,hd⟩).le ω.val.1 (ω.val.2 ⟨d,hd⟩) t y
  else Sum.inr y

lemma maps_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr t ω=history law hr t ρ):maps law hr s t ω=maps law hr s t ρ:=by
  obtain ⟨ht,hp⟩:=history_eq law hr t ω ρ h
  have hh:requestHistory t ω.val.1=requestHistory t ρ.val.1:=
    (requestHistory_eq_iff _ _ _).mpr hp
  funext d y
  unfold maps
  split_ifs with hd
  · rw [ht]
    exact KeysAdapted.map_adapted s law (hr ⟨d,hd⟩).le (ρ.val.2 ⟨d,hd⟩) t y _ _ hh
  · rfl

lemma measure_eq (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    PosteriorCounting.measure (w:=weight law hr) (history law hr t) (hidden law hr s t) ω y=
      mu s law t ω.val.1 y:=by
  change posterior (PositiveExperiment.weight (rawWeight law hr))
    (fun z=>FiniteExperiment.history t z.val)
    (fun z=>PosteriorCounting.atoms (FiniteExperiment.hidden s z.val.1 t) y) ω=_
  rw [PositiveExperiment.posterior_support (raw_nonneg law hr) (FiniteExperiment.history t)
    (fun z:Raw Y k H L r=>PosteriorCounting.atoms (FiniteExperiment.hidden s z.1 t) y) ω]
  unfold rawWeight FiniteExperiment.mu
  convert posterior_tape_irrelevant law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr) t ω.val (tape_pos law hr ω).ne' (fun σ=>PosteriorCounting.atoms (FiniteExperiment.hidden s σ t) y) using 1
  simp only [FiniteExperiment.metricCount,PosteriorCounting.atoms]

omit [NeZero k] in
lemma request_history (t:Fin H) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr (t.val+1) ω=history law hr (t.val+1) ρ):ω.val.1 t=ρ.val.1 t:=
  prefix_request t (history_eq law hr _ ω ρ h).2

lemma hidden_covers (t:Fin H) (ω:Atom (k:=k) law hr):
    ∃ i,hidden law hr s (t.val+1) ω i=ω.val.1 t:=
  ⟨mover s ω.val.1 t,FiniteExperiment.hidden_covers s ω.val.1 t⟩

omit [NeZero k] in
lemma scale_mean (d:Fin L) (f:(Fin H→Y)→LevelKeys.Tape Y k H (r d)→ℝ):
    avg (weight (k:=k) law hr) (fun ω=>f ω.val.1 (ω.val.2 d))=
      avg law.val (fun σ=>LevelRetirement.mean (r d) (f σ)):=by
  rw [avg_raw law hr (fun ω:Raw Y k H L r=>f ω.1 (ω.2 d))]
  unfold RankTracking.avg rawWeight FiniteExperiment.weight
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro σ _
  simp only [mul_assoc,←mul_sum]
  congr 1
  unfold tapeLaw tapeWeight LevelRetirement.mean
  convert FiniteTape.marginal (fun j=>LevelLaw.weight (r j))
    (fun j=>LevelLaw.weight_sum (hr j)) d (f σ) using 1
  congr 1
  ext x
  simp only [mem_univ]

end KServer.JointExperiment

end


/-! The dependent permanent key alphabet is genuinely finite. -/
noncomputable section
namespace KServer.LevelKeys
instance alphabetFintype {Y:Type*} [Fintype Y] (k:ℕ) (i:Structure k):Fintype (Alphabet Y k i):=by
  cases i <;> dsimp only [Alphabet] <;> infer_instance
end KServer.LevelKeys

end


/-! Endpoint costs on the actual schedule are charged to active size, rather
than to all inactive fixed labels. This is needed for wholesale edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledEndpoint
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma masked_value_bound (C ell : ℝ) (d : Data J R) (p : J×R→ℝ) (a : J→ℝ) {L:ℝ}
    (hc : ∀ ir,|coefficient C ell d a ir|≤L)
    (hp : ∀ ir,p ir∈Set.Icc 0 1) :
    |(family C ell).value d p a|≤L*(∑ i,∑ r,if d.flags i r then (1:ℝ) else 0) := by
  change |0+∑ ir,coefficient C ell d a ir*p ir|≤_
  rw [zero_add]
  calc _≤∑ ir,|coefficient C ell d a ir*p ir|:= abs_sum_le_sum_abs _ _
       _≤∑ ir:J×R,L*(if d.flags ir.1 ir.2 then (1:ℝ) else 0) := by
        apply sum_le_sum
        intro ir _
        by_cases hf:d.flags ir.1 ir.2=true
        · simp only [hf,ite_true,mul_one,abs_mul,abs_of_nonneg (hp ir).1]
          exact (mul_le_mul_of_nonneg_left (hp ir).2 (abs_nonneg _)).trans (by simpa using hc ir)
        · have hz:coefficient C ell d a ir=0 := by simp [coefficient,hf]
          simp [hz,hf]
       _= _ := by rw [←mul_sum,Fintype.sum_prod_type]

lemma actual_bound {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0≤C) (hct : 0≤ct) (hctu : ct*20002≤1) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (a:J→ℝ) (ha:a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) :
    |(family C (1+Real.log (k+1))).value
      (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data p a|≤
      520*C*(1+Real.log (k+1))*EpochSchedule.total (vector cutoff δ P ω t) := by
  have hel : 0≤1+Real.log (k+1) := by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  have hL : 0≤13*C*(1+Real.log (k+1)) := by positivity
  have hh:=masked_value_bound C (1+Real.log (k+1))
    (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data p a
    (ScheduledSlope.actual_bound hδ hδu hC hct hctu hk P key hs t ω a ha) hp
  have hn:(∑ i,∑ r,if (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data.flags i r
      then (1:ℝ) else 0)≤40*EpochSchedule.total (vector cutoff δ P ω t) := by
    simp only [StarSimplex.input,data_flags,StarSimplex.flags]
    change (∑ i,TrackedCaps.count (P i) t ω)≤40*(∑ i,vector cutoff δ P ω t i)
    rw [mul_sum]
    exact sum_le_sum fun i _=>ScheduleEdits.count_bound hδ hδu (P i) t ω
  calc _≤13*C*(1+Real.log (k+1))*(40*EpochSchedule.total (vector cutoff δ P ω t)) :=
        hh.trans (mul_le_mul_of_nonneg_left hn hL)
       _= _ := by ring

end KServer.ScheduledEndpoint

end

end OAI
