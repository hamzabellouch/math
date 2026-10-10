import Mathlib
import OAI.Combinatorics.KServer.AnchorTravel

namespace OAI

/-! Literal retained-heavy anchor data and chronological payment on the one
joint request/tape experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))
local instance keyDecEq : DecidableEq (LevelKeys.Key Y k) := Classical.decEq _
abbrev J:=HeavyLabels.Pool Y
local instance poolDecEq : DecidableEq (J (Y:=Y)) := Classical.decEq _

def key (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L):Y→Option (J (Y:=Y)):=
  HeavyKeys.key s law (r d) heavyGamma heavyDelta ω.val.1 (ω.val.2 d).1 t

def anchor (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L):J (Y:=Y)→Y:=
  heavyAnchor s law (r d) ω.val.1 (ω.val.2 d).1 t

def b (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):ℝ:=
  band s law hr hk t ω d.val (slot (k:=k) a)

def u (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):ℝ:=
  reference s law hr d.val (slot (k:=k) a) t ω

def c (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):ℝ:=
  b s law hr hk t ω d a/u s law hr t ω d a

def present (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):Prop:=
  HeavyAnchorDynamics.present s law (r d) ω.val.1 (ω.val.2 d).1 t a

lemma cell_eq (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    univ.filter (fun y=>key s law hr t ω d y=some a)=
      HeavyAnchorDynamics.cell s law (hr d).le ω.val.1 (ω.val.2 d) t a:=by
  apply Finset.ext
  intro y
  simp only [HeavyAnchorDynamics.cell,mem_filter,mem_univ,true_and]
  exact (HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t y a).symm

lemma mass_eq (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    (∑ y∈univ.filter (fun y=>key s law hr t ω d y=some a),FiniteExperiment.mu s law t ω.val.1 y)=
      size s law hr d.val (slot (k:=k) a) t ω-1:=by
  rw [JointAllocation.size_mass,add_sub_cancel_left]
  apply sum_congr
  · ext y
    simp only [mem_filter,mem_univ,true_and]
    exact (HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t y a).symm
  · intro y _; rfl

lemma b_nonneg (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    0≤b s law hr hk t ω d a:=band_nonneg s law hr hk t ω d.val _
lemma u_pos (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    0<u s law hr t ω d a:=reference_pos s law hr d.val _ t ω
lemma c_bounds (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    c s law hr hk t ω d a∈Set.Icc 0 ((6/5:ℝ)*72):=
  coefficient_bounds s law hr hk t ω d.val _

lemma absent_band (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y))
    (ha:¬present s law hr t ω d a):b s law hr hk t ω d a=0:=by
  have he:=HeavyAnchorDynamics.absent_cell s law (hr d) ω.val.1 (ω.val.2 d) t a ha
  have hh:=JointAllocation.band_capacity s law hr hk t ω d.val (slot (k:=k) a)
  rw [←mass_eq s law hr t ω d a,cell_eq,he,sum_empty,mul_zero] at hh
  exact le_antisymm hh (b_nonneg s law hr hk t ω d a)

lemma integral_eq (μ:Y→ℝ) (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)) (z:Y):
    slotIntegral μ (key s law hr t ω d) z (r d) a=
      integral μ (HeavyAnchorDynamics.cell s law (hr d).le ω.val.1 (ω.val.2 d) t a) z (r d):=by
  unfold slotIntegral integral
  rw [cell_eq]

lemma slot_payment (t:Fin H) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    let μ:=FiniteExperiment.mu s law (t.val+1) ω.val.1
    let bn:=b s law hr hk (t.val+1) ω d a
    let bo:=b s law hr hk t.val ω d a
    let un:=u s law hr (t.val+1) ω d a
    let uo:=u s law hr t.val ω d a
    let an:=anchor s law hr (t.val+1) ω d a
    let ao:=anchor s law hr t.val ω d a
    r d*(bn/un)*slotIntegral μ (key s law hr (t.val+1) ω d) an (r d) a-
      r d*(bo/uo)*slotIntegral μ (key s law hr (t.val+1) ω d) ao (r d) a+
      (if present s law hr t.val ω d a ∧ present s law hr (t.val+1) ω d a ∧ ao≠an then r d*bn else 0)/4≤
        (6/5:ℝ)*72*r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t.val ω+
          2*(6/5:ℝ)*r d*|bn-bo|:=by
  dsimp only
  let M:=size s law hr d.val (slot (k:=k) a) (t.val+1) ω-1
  have hMs:1+M=size s law hr d.val (slot (k:=k) a) (t.val+1) ω:=by dsimp only [M]; ring
  have hM:0≤M:=sub_nonneg.mpr (size_range s law hr d.val _ (t.val+1) ω).1
  have hμ:=FiniteExperiment.mu_nonneg s law (t.val+1) ω.val.1
  have hI:=slotIntegral_bound hμ (key s law hr (t.val+1) ω d) (anchor s law hr t.val ω d a) (r d) a
  have hJ:=slotIntegral_bound hμ (key s law hr (t.val+1) ω d) (anchor s law hr (t.val+1) ω d a) (r d) a
  rw [mass_eq] at hI hJ
  have hbu : b s law hr hk t.val ω d a≤(6/5:ℝ)*72*u s law hr t.val ω d a:=
    (div_le_iff₀ (u_pos s law hr t.val ω d a)).mp (c_bounds s law hr hk t.val ω d a).2
  have hn:1+M≤(6/5:ℝ)*u s law hr (t.val+1) ω d a:=by
    rw [hMs]
    exact (reference_comparison s law hr d.val (slot (k:=k) a) (t.val+1) ω).2
  have he:u s law hr (t.val+1) ω d a=if KeySizeTracking.refresh (1+M) (u s law hr t.val ω d a) then 1+M else u s law hr t.val ω d a:=by
    rw [hMs]
    rfl
  have hh:=slot_stage (hr d).le (b_nonneg s law hr hk t.val ω d a)
    (b_nonneg s law hr hk (t.val+1) ω d a) (u_pos s law hr t.val ω d a)
    (u_pos s law hr (t.val+1) ω d a) (by norm_num : (0:ℝ)≤72) hM
    ⟨slotIntegral_nonneg hμ _ _ _ _,hI⟩ hJ hbu hn he
    (present s law hr t.val ω d a) (present s law hr (t.val+1) ω d a)
    (anchor s law hr t.val ω d a≠anchor s law hr (t.val+1) ω d a)
    (absent_band s law hr hk (t.val+1) ω d a) (absent_band s law hr hk t.val ω d a)
    (by intro _ _ h; rw [not_not.mp h]) ?_
  · convert hh using 1
    rw [hMs]
    rfl
  · intro ho hn' hm
    rw [integral_eq,integral_eq]
    exact moving_drop s law (hr d) ω.val.1 (request_pos law hr ω) (ω.val.2 d) t a ho hn' hm
      (u_pos s law hr (t.val+1) ω d a) (b_nonneg s law hr hk (t.val+1) ω d a) (by
        have href:=(reference_comparison s law hr d.val (slot (k:=k) a) (t.val+1) ω).1
        have hmass:AnchorTravel.mass (FiniteExperiment.mu s law (t.val+1) ω.val.1)
            (HeavyAnchorDynamics.cell s law (hr d).le ω.val.1 (ω.val.2 d) (t.val+1) a)=
              size s law hr d.val (slot (k:=k) a) (t.val+1) ω-1:=by
          unfold AnchorTravel.mass
          rw [←cell_eq]
          exact mass_eq s law hr (t.val+1) ω d a
        rw [hmass]
        change reference s law hr d.val (slot (k:=k) a) (t.val+1) ω≤_
        linarith)

end KServer.JointHeavy

end


/-! Adapted chronological stage aggregation, retaining signed filtering. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))
attribute [local instance] keyDecEq poolDecEq

lemma key_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    key s law hr t ω=key s law hr t ρ:=by
  obtain ⟨ht,hp⟩:=history_eq law hr t ω ρ hh
  funext d y
  unfold key
  rw [ht]
  exact KeysAdapted.heavy_key_adapted s law _ _ _ _ t y _ _ ((FiniteExperiment.requestHistory_eq_iff _ _ _).mpr hp)

lemma anchor_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    anchor s law hr t ω=anchor s law hr t ρ:=by
  obtain ⟨ht,hp⟩:=history_eq law hr t ω ρ hh
  funext d
  unfold anchor
  rw [ht]
  exact KeysAdapted.heavy_anchor_adapted s law _ _ t _ _ ((FiniteExperiment.requestHistory_eq_iff _ _ _).mpr hp)

lemma c_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    c s law hr hk t ω=c s law hr hk t ρ:=by
  funext d a
  unfold c b u
  rw [band_adapted s law hr hk t ω ρ hh,reference_adapted s law hr d.val (slot (k:=k) a) t ω ρ hh]

lemma prepared_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr (t+1) ω=history law hr (t+1) ρ):
    familyTest r (c s law hr hk t ω) (anchor s law hr t ω) (key s law hr (t+1) ω)=
      familyTest r (c s law hr hk t ρ) (anchor s law hr t ρ) (key s law hr (t+1) ρ):=by
  rw [c_adapted s law hr hk t ω ρ (history_refines law hr t ω ρ hh),
    anchor_adapted s law hr t ω ρ (history_refines law hr t ω ρ hh),key_adapted s law hr (t+1) ω ρ hh]

lemma current_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    familyTest r (c s law hr hk t ω) (anchor s law hr t ω) (key s law hr t ω)=
      familyTest r (c s law hr hk t ρ) (anchor s law hr t ρ) (key s law hr t ρ):=by
  rw [c_adapted s law hr hk t ω ρ hh,anchor_adapted s law hr t ω ρ hh,key_adapted s law hr t ω ρ hh]

def travel (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ d:Fin L,∑ a:J (Y:=Y),if present s law hr t ω d a ∧ present s law hr (t+1) ω d a ∧
    anchor s law hr t ω d a≠anchor s law hr (t+1) ω d a then r d*b s law hr hk (t+1) ω d a else 0

def charge (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ d:Fin L,∑ a:J (Y:=Y),((6/5:ℝ)*72*r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω+
    2*(6/5:ℝ)*r d*|b s law hr hk (t+1) ω d a-b s law hr hk t ω d a|)

def potential (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ i:Fin k,familyTest r (c s law hr hk t ω) (anchor s law hr t ω) (key s law hr t ω) (hidden law hr s t ω i)

lemma stage_payment (t:Fin H) (ω:Atom (k:=k) law hr):
    familyIntegral (PosteriorCounting.measure (w:=weight law hr) (history law hr (t.val+1)) (hidden law hr s (t.val+1)) ω)
      r (c s law hr hk (t.val+1) ω) (anchor s law hr (t.val+1) ω) (key s law hr (t.val+1) ω)-
    familyIntegral (PosteriorCounting.measure (w:=weight law hr) (history law hr (t.val+1)) (hidden law hr s (t.val+1)) ω)
      r (c s law hr hk t.val ω) (anchor s law hr t.val ω) (key s law hr (t.val+1) ω)+
      travel s law hr hk t.val ω/4≤charge s law hr hk t.val ω:=by
  have hm:PosteriorCounting.measure (w:=weight law hr) (history law hr (t.val+1)) (hidden law hr s (t.val+1)) ω=
      FiniteExperiment.mu s law (t.val+1) ω.val.1:=by funext y; exact measure_eq law hr s (t.val+1) ω y
  rw [hm]
  have hh:=sum_le_sum (s:=(univ:Finset (Fin L))) (fun d _=>sum_le_sum (s:=(univ:Finset (J (Y:=Y))))
    (fun a _=>slot_payment s law hr hk t ω d a))
  simp only [sum_add_distrib,sum_sub_distrib,←sum_div] at hh
  simpa only [familyIntegral,c,travel,charge,sum_add_distrib] using hh

lemma expected_payment (t:Fin H) {C:ℝ}
    (hcut:∀ ω i,(∑ d,cutoff (r d) (c s law hr hk t.val ω d) (anchor s law hr t.val ω d)
      (key s law hr t.val ω d (hidden law hr s t.val ω i)) (hidden law hr s t.val ω i))≤C):
    avg (weight law hr) (potential s law hr hk (t.val+1))-
      avg (weight law hr) (potential s law hr hk t.val)+avg (weight law hr) (travel s law hr hk t.val)/4≤
        ((6/5:ℝ)*72)*avg (weight law hr) (fun ω=>∑ i:Fin k,∑ d:Fin L,r d*(if
          key s law hr (t.val+1) ω d (hidden law hr s (t.val+1) ω i)=key s law hr t.val ω d (hidden law hr s t.val ω i)
          then 0 else 1))+
        C/3*avg (weight law hr) (fun ω=>∑ i:Fin k,dist (hidden law hr s t.val ω i) (hidden law hr s (t.val+1) ω i))+
        avg (weight law hr) (charge s law hr hk t.val):=
  expected_step (weight_nonneg law hr) (history law hr (t.val+1)) (hidden law hr s t.val) (hidden law hr s (t.val+1))
    hr (by norm_num) (c s law hr hk t.val) (c s law hr hk (t.val+1)) (anchor s law hr t.val) (anchor s law hr (t.val+1))
    (key s law hr t.val) (key s law hr (t.val+1)) (c_bounds s law hr hk t.val) hcut
    (prepared_adapted s law hr hk t.val) (current_adapted s law hr hk (t.val+1))
    (travel s law hr hk t.val) (charge s law hr hk t.val) (stage_payment s law hr hk t)

end KServer.JointHeavy

end


/-! The actual old heavy-slot coefficients have logarithmic all-scale sum. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq keyDecEq poolDecEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

def selected (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y) (d:ℕ):Option (LevelKeys.Key Y k):=
  if hd:d<L then HeavyAnchorDynamics.selected s law (r ⟨d,hd⟩) ω.val.1 (ω.val.2 ⟨d,hd⟩).1 t y else none

lemma selected_term (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y) (d:Fin L)
    (R τ:ℝ):
    PrefixTree.selectedMass (LevelKeys.Key Y k) L (park s law hr hk t ω) (selected s law hr t ω y) d.val/
      PrefixTree.selectedDenominator (LevelKeys.Key Y k)
        (PosteriorCounting.measure (w:=weight law hr) (history law hr t) (hidden law hr s t) ω)
        y (ParkedCoefficients.radius R τ) (selected s law hr t ω y)
        (fun j a=>reference s law hr j a t ω) d.val=
      cutoff (r d) (c s law hr hk t ω d) (anchor s law hr t ω d) (key s law hr t ω d y) y:=by
  have hs:selected s law hr t ω y d.val=(match key s law hr t ω d y with
    | none=>none
    | some a=>if dist (anchor s law hr t ω d a) y<7*r d then some (slot (k:=k) a) else none):=by
      simp only [selected,dite_eq_left d.isLt,HeavyAnchorDynamics.selected,key,anchor]
      rfl
  rw [PrefixTree.selectedMass,PrefixTree.selectedBand,PrefixTree.selectedDenominator,hs]
  cases he:key s law hr t ω d y with
  | none=>simp only [cutoff,sum_empty,zero_div]
  | some a=>
    simp only [cutoff]
    split_ifs with hd
    · rfl
    · simp only [sum_empty,zero_div]

lemma cutoff_sum (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y)
    {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (hrad:∀ d,r d=ParkedCoefficients.radius R τ d.val):
    (∑ d:Fin L,cutoff (r d) (c s law hr hk t ω d) (anchor s law hr t ω d)
      (key s law hr t ω d y) y)≤
        (7*((6/5:ℝ)*72)/Real.log 2+2*(6/5:ℝ)*72)*(1+Real.log ((k:ℝ)+1)):=by
  have hh:=PrefixTree.selected_coefficients (LevelKeys.Key Y k) L (weight_nonneg law hr)
    (history law hr) (history_refines law hr) (maps law hr s) (hidden law hr s) hk
    (weight_pos law hr) t ω (fun ρ h=>maps_adapted law hr s t ρ ω h)
    (selected s law hr t ω y) y (fun j a=>reference s law hr j a t ω) hR hτ
    (fun j a=>reference_pos s law hr j a t ω) ?_ ?_ ?_ ?_
  · dsimp only at hh
    rw [←Fin.sum_univ_eq_sum_range] at hh
    change (∑ d:Fin L,PrefixTree.selectedMass (LevelKeys.Key Y k) L (park s law hr hk t ω)
      (selected s law hr t ω y) d.val/_)≤_ at hh
    simpa only [selected_term s law hr hk t ω y _ R τ] using hh
  · intro j a
    unfold Rounding.countingMass
    rw [←size_mass_joint s law hr j a t ω]
    exact (reference_comparison s law hr j a t ω).2
  · intro j a ha z hz
    unfold selected at ha
    split_ifs at ha with hj
    · have he:=HeavyAnchorDynamics.selected_close s law (hr ⟨j,hj⟩) ω.val.1 (ω.val.2 ⟨j,hj⟩) t y a ha z (by
        simpa only [maps,dite_eq_left hj] using hz)
      simpa only [hrad] using he
  · intro j a ha z hz
    unfold selected at ha
    split_ifs at ha with hj
    · have he:=HeavyAnchorDynamics.selected_contains s law (hr ⟨j,hj⟩) ω.val.1 (ω.val.2 ⟨j,hj⟩) t y a ha z (by
        simpa only [hrad] using hz)
      simpa only [maps,dite_eq_left hj] using he
  · intro j a b hab
    by_cases hj:j<L
    · have he:=LevelKeys.cell_diameter s law (hr ⟨j,hj⟩) ω.val.1 (ω.val.2 ⟨j,hj⟩) t a b (by
        simpa only [maps,dite_eq_left hj] using hab)
      simpa only [hrad] using he
    · have he:a=b:=Sum.inr.inj (by simpa only [maps,dite_eq_right hj] using hab)
      rw [he,dist_self]
      exact mul_nonneg (by norm_num) (div_nonneg hR (pow_nonneg (by linarith) _))

end KServer.JointHeavy

end


/-! Literal size-reference refresh budget summed over the fixed key inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeyReferences
open RankTracking PosteriorRanks ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) (hw1:∑ ω,w ω=1)
variable (H:ℕ→Ω→ℕ) (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

include hw hwpos hr in
omit [Fintype A] [Fintype Y] in
lemma refresh_nonneg (d:ℕ) (a:A) (t:ℕ) (ω:Ω):
    0≤KeySizeTracking.refreshCost (size (w:=w) H maps q d a) t ω:=by
  unfold KeySizeTracking.refreshCost
  split_ifs
  · exact add_nonneg (le_trans (by norm_num) (reference_range H maps q hw hwpos hr d a t ω).1)
      (le_trans (by norm_num) (reference_range H maps q hw hwpos hr d a (t+1) ω).1)
  · rfl

omit [Fintype Ω] [Fintype Y] in
lemma count_variation (d t:ℕ) (ω:Ω):
    (∑ a:A,|count maps q d a (t+1) ω-count maps q d a t ω|)≤
      2*HierarchicalQuota.keyCross maps q d t ω:=
  HierarchicalQuota.histogram_distance (fun i=>maps (t+1) ω d (q (t+1) ω i))
    (fun i=>maps t ω d (q t ω i))

include hw hwpos hw1 hr in
omit [Fintype Y] in
lemma refresh_all (d N:ℕ):
    (∑ a:A,total w N (KeySizeTracking.refreshCost (size (w:=w) H maps q d a)))≤
      288*(1+Real.log ((k:ℝ)+1))*total w N (HierarchicalQuota.keyCross maps q d)+
        Fintype.card A*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1)))):=by
  have hh:=sum_le_sum (s:=(univ:Finset A)) (fun a _=>refresh_budget H maps q hw hwpos hr hw1 d a N)
  simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul] at hh
  have he:(∑ a:A,∑ t∈range N,avg w (fun ω=>|count maps q d a (t+1) ω-count maps q d a t ω|))=
      total w N (fun t ω=>∑ a:A,|count maps q d a (t+1) ω-count maps q d a t ω|):=by
    unfold total
    rw [sum_comm]
    simp only [avg_sum]
  rw [he] at hh
  have hl:0≤1+Real.log ((k:ℝ)+1):=by
    have :=Real.log_nonneg (by have :=Nat.cast_nonneg (α:=ℝ) k; linarith : (1:ℝ)≤(k:ℝ)+1)
    linarith
  have hc:=mul_le_mul_of_nonneg_left (total_mono hw (N:=N) (count_variation maps q d))
    (mul_nonneg (by norm_num : (0:ℝ)≤144) hl)
  rw [total_mul] at hc
  change (∑ a,total w N _)≤_ at hh
  nlinarith

include hw hwpos hw1 hr in
omit [Fintype Y] in
lemma refresh_subset {J:Type} [Fintype J] (f:J→A) (hf:Function.Injective f) (d N:ℕ):
    (∑ j:J,total w N (KeySizeTracking.refreshCost (size (w:=w) H maps q d (f j))))≤
      288*(1+Real.log ((k:ℝ)+1))*total w N (HierarchicalQuota.keyCross maps q d)+
        Fintype.card A*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1)))):=by
  apply le_trans _ (refresh_all hw hwpos hw1 H hr maps q d N)
  let F:=fun a=>total w N (KeySizeTracking.refreshCost (size (w:=w) H maps q d a))
  change (∑ j,F (f j))≤∑ a,F a
  calc _ = ∑ a∈univ.image f,F a := (sum_image (fun i _ j _ h=>hf h)).symm
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun a _ _=>total_nonneg hw (refresh_nonneg hw hwpos H hr maps q d a))
end KServer.KeyReferences

end


/-! Fixed bands are disjoint inventories, so grouping never enlarges variation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I V:Type} [Fintype I] [Fintype V]

lemma disjoint_variation (F:I→Finset V) (hd:Set.PairwiseDisjoint (↑(univ:Finset I)) F)
    (p q W:V→ℝ) (w:I→ℝ) (hw:∀ i,0≤w i) (hW:∀ v,0≤W v)
    (he:∀ i v,v∈F i→w i=W v):
    (∑ i,w i*|(∑ v∈F i,q v)-(∑ v∈F i,p v)|)≤∑ v,W v*|q v-p v|:=by
  have hs:(∑ i,w i*|(∑ v∈F i,q v)-(∑ v∈F i,p v)|)≤
      ∑ i,∑ v∈F i,W v*|q v-p v|:=by
    apply sum_le_sum
    intro i _
    rw [←sum_sub_distrib]
    calc _ ≤ w i * ∑ v∈F i,|q v-p v|:=mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hw i)
         _ = _:=by
          rw [mul_sum]
          exact sum_congr rfl (fun v hv=>by rw [he i v hv])
  rw [←sum_biUnion hd] at hs
  exact hs.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _=>mul_nonneg (hW v) (abs_nonneg _)))

variable (A:Type) [Fintype A] (L:ℕ)
lemma bands_disjoint {J:Type} [Fintype J] (f:J→A) (hf:Function.Injective f):
    Set.PairwiseDisjoint (↑(univ:Finset (Fin L×J))) (fun i:Fin L×J=>band A L i.1.val (f i.2)):=by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hi hj
  obtain ⟨hdi,hai⟩:=(mem_filter.mp hi).2
  obtain ⟨hdj,haj⟩:=(mem_filter.mp hj).2
  have hd:i.1=j.1:=Fin.ext (by omega)
  have ha:i.2=j.2:=hf (Option.some.inj (hai.symm.trans haj))
  exact hij (Prod.ext hd ha)

lemma band_variation {J:Type} [Fintype J] (f:J→A) (hf:Function.Injective f)
    (p q W:Node A L→ℝ) (r:Fin L→ℝ) (hr:∀ d,0≤r d) (hW:∀ v,0≤W v)
    (he:∀ d a v,v∈band A L d.val (f a)→ r d=W v):
    (∑ d:Fin L,∑ a:J,r d*|bandMass A L q d.val (f a)-bandMass A L p d.val (f a)|)≤
      ∑ v,W v*|q v-p v|:=by
  have hh:=disjoint_variation (fun i:Fin L×J=>band A L i.1.val (f i.2))
    (bands_disjoint A L f hf) p q W (fun i=>r i.1) (fun i=>hr i.1) hW
    (fun i v hv=>he i.1 i.2 v hv)
  simpa only [Fintype.sum_prod_type,bandMass] using hh
end KServer.PrefixTree

end


/-! Full signed heavy-travel telescope for the actual joint experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
open RankTracking PosteriorRanks ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq keyDecEq poolDecEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

lemma potential_bounds (t:ℕ) (ω:Atom (k:=k) law hr):
    potential s law hr hk t ω∈Set.Icc 0 (((6/5:ℝ)*72)*k*(∑ d,r d)):=
  raw_bounds (fun d=>(hr d).le) (by norm_num) _ _ _ _ (c_bounds s law hr hk t ω)

lemma heavy_eq_of_map_eq (t t':ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (x y:Y)
    (he:maps law hr s t ω d.val x=maps law hr s t' ω d.val y):
    key s law hr t ω d x=key s law hr t' ω d y:=by
  have hmem a:
      key s law hr t ω d x=some a ↔ key s law hr t' ω d y=some a:=by
    have h1:=HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t x a
    have h2:=HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t' y a
    change _↔_ at h1 h2
    have hm:LevelKeys.map s law (hr d).le ω.val.1 (ω.val.2 d) t x=
        LevelKeys.map s law (hr d).le ω.val.1 (ω.val.2 d) t' y:=by
      simpa only [maps,dite_eq_left d.isLt] using he
    exact h1.symm.trans ((congrArg (fun z=>z=slot (k:=k) a) hm).to_iff.trans h2)
  cases h1:key s law hr t ω d x with
  | none=>
    cases h2:key s law hr t' ω d y with
    | none=>rfl
    | some a=>exact False.elim (by have hh:=(hmem a).mpr h2; rw [h1] at hh; cases hh)
  | some a=>exact ((hmem a).mp h1).symm

lemma heavy_cross_le (t:ℕ) (ω:Atom (k:=k) law hr):
    (∑ i:Fin k,∑ d:Fin L,r d*(if key s law hr (t+1) ω d (hidden law hr s (t+1) ω i)=
      key s law hr t ω d (hidden law hr s t ω i) then 0 else 1))≤
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω:=by
  rw [sum_comm]
  apply sum_le_sum
  intro d _
  unfold HierarchicalQuota.keyCross
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hr d).le
  by_cases he:maps law hr s (t+1) ω d.val (hidden law hr s (t+1) ω i)=
      maps law hr s t ω d.val (hidden law hr s t ω i)
  · simp only [ite_eq_left he,ite_eq_left (heavy_eq_of_map_eq s law hr (t+1) t ω d _ _ he),le_refl]
  · simp only [ite_eq_right he]
    split_ifs <;> norm_num

lemma travel_raw {C:ℝ} {R τ:ℝ} (hR:0≤R) (hτ:2≤τ)
    (hrad:∀ d,r d=ParkedCoefficients.radius R τ d.val)
    (hC:(7*((6/5:ℝ)*72)/Real.log 2+2*(6/5:ℝ)*72)*(1+Real.log ((k:ℝ)+1))≤C):
    total (weight law hr) H (travel s law hr hk)≤
      4*((6/5:ℝ)*72)*total (weight law hr) H (fun t ω=>
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
      4*C/3*total (weight law hr) H (fun t ω=>(∑ i:Fin k,dist (hidden law hr s t ω i) (hidden law hr s (t+1) ω i)))+
      4*total (weight law hr) H (charge s law hr hk)+4*(((6/5:ℝ)*72)*k*(∑ d,r d)):=by
  let P:=fun t=>avg (weight law hr) (potential s law hr hk t)
  let E:=fun t=> ((6/5:ℝ)*72)*avg (weight law hr) (fun ω=>
      ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
    C/3*avg (weight law hr) (fun ω=>(∑ i:Fin k,dist (hidden law hr s t ω i) (hidden law hr s (t+1) ω i)))+
      avg (weight law hr) (charge s law hr hk t)
  have hp:0≤P H:=sum_nonneg (fun ω _=>mul_nonneg (weight_nonneg law hr ω) (potential_bounds s law hr hk H ω).1)
  have hb:P 0≤((6/5:ℝ)*72)*k*(∑ d,r d):=by
    have hh:=avg_mono (weight_nonneg law hr) (fun ω=>(potential_bounds s law hr hk 0 ω).2)
    simpa only [avg_const,weight_sum,one_mul] using hh
  have hs:∀ t,t<H→P (t+1)-P t+avg (weight law hr) (travel s law hr hk t)/4≤E t:=by
    intro t ht
    have hh:=expected_payment s law hr hk ⟨t,ht⟩ (fun ω i=>(cutoff_sum s law hr hk t ω
      (hidden law hr s t ω i) hR hτ hrad).trans hC)
    have hx:=mul_le_mul_of_nonneg_left (avg_mono (weight_nonneg law hr) (heavy_cross_le s law hr t))
        (by norm_num : (0:ℝ)≤(6/5:ℝ)*72)
    change _≤_ at hh
    dsimp only [P,E]
    linarith
  have hh:=chronological_telescope P (fun t=>avg (weight law hr) (travel s law hr hk t)) E H hp hb hs
  simp only [E,sum_add_distrib,←mul_sum] at hh
  change total _ _ _≤_ at hh
  convert hh using 1
  unfold total
  ring
end KServer.JointHeavy

end


/-! Actual heavy references and fixed-band changes, charged to full-key
transport and the variation of the complete park inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
open RankTracking PosteriorRanks ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq keyDecEq poolDecEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

omit [MetricSpace Y] [NeZero k] in
lemma slot_injective:Function.Injective (slot (Y:=Y) (k:=k)):=by
  intro a b he
  exact Sigma.mk.inj_iff.mp (Sum.inl.inj he) |>.2 |> eq_of_heq

lemma refresh_bound (N:ℕ):
    total (weight law hr) N (fun t ω=>∑ d:Fin L,∑ a:J (Y:=Y),
      r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω)≤
      288*(1+Real.log ((k:ℝ)+1))*total (weight law hr) N (fun t ω=>
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
      (∑ d,r d)*(Fintype.card (LevelKeys.Key Y k)*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))))):=by
  have esize (d:ℕ) (a:LevelKeys.Key Y k):
      size s law hr d a=KeyReferences.size (w:=weight law hr) (history law hr)
        (maps law hr s) (hidden law hr s) d a:=rfl
  have hh:=sum_le_sum (s:=(univ:Finset (Fin L))) (fun d _=>mul_le_mul_of_nonneg_left
    (KeyReferences.refresh_subset (weight_nonneg law hr) (weight_pos law hr) (weight_sum law hr)
      (history law hr) (history_refines law hr) (maps law hr s) (hidden law hr s)
      (slot (k:=k)) slot_injective d.val N) (hr d).le)
  calc
    _ = ∑ d:Fin L,r d*total (weight law hr) N (fun t ω=>∑ a:J (Y:=Y),
      KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω):=by
        simp only [total_sum,total_mul,mul_sum]
    _ ≤ ∑ d:Fin L,r d*(288*(1+Real.log ((k:ℝ)+1))*
      total (weight law hr) N (HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val)+
      Fintype.card (LevelKeys.Key Y k)*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))))):=by
        simp only [esize,total_sum]
        exact hh
    _ = _:=by
      simp only [total_sum,total_mul,mul_add,sum_add_distrib,mul_sum,sum_mul]
      congr 1
      apply sum_congr rfl
      intro d _
      ring

lemma band_variation_bound (t:ℕ) (ω:Atom (k:=k) law hr)
    (W:PrefixTree.Node (LevelKeys.Key Y k) L→ℝ) (hW:∀ v,0≤W v)
    (he:∀ d a v,v∈PrefixTree.band (LevelKeys.Key Y k) L d.val (slot (k:=k) a)→ r d=W v):
    (∑ d:Fin L,∑ a:J (Y:=Y),r d*|b s law hr hk (t+1) ω d a-b s law hr hk t ω d a|)≤
      ∑ v,W v*|park s law hr hk (t+1) ω v-park s law hr hk t ω v|:=
  PrefixTree.band_variation (LevelKeys.Key Y k) L (slot (k:=k)) slot_injective _ _ W r
    (fun d=>(hr d).le) hW he

lemma charge_bound (N:ℕ) (W:PrefixTree.Node (LevelKeys.Key Y k) L→ℝ) (hW:∀ v,0≤W v)
    (he:∀ d a v,v∈PrefixTree.band (LevelKeys.Key Y k) L d.val (slot (k:=k) a)→ r d=W v):
    total (weight law hr) N (charge s law hr hk)≤
      ((6/5:ℝ)*72)*288*(1+Real.log ((k:ℝ)+1))*total (weight law hr) N (fun t ω=>
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
      2*(6/5:ℝ)*total (weight law hr) N (fun t ω=>∑ v,W v*|park s law hr hk (t+1) ω v-park s law hr hk t ω v|)+
      ((6/5:ℝ)*72)*(∑ d,r d)*(Fintype.card (LevelKeys.Key Y k)*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))))):=by
  have h1:=mul_le_mul_of_nonneg_left (refresh_bound s law hr N) (by norm_num : (0:ℝ)≤(6/5:ℝ)*72)
  have h2:=mul_le_mul_of_nonneg_left (total_mono (weight_nonneg law hr) (N:=N)
    (fun t ω=>band_variation_bound s law hr hk t ω W hW he)) (by norm_num : (0:ℝ)≤2*(6/5:ℝ))
  have heqpoint (t:ℕ) (ω:Atom (k:=k) law hr):charge s law hr hk t ω=
      ((6/5:ℝ)*72)*(∑ d:Fin L,∑ a:J (Y:=Y),
        r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω)+
      2*(6/5:ℝ)*(∑ d:Fin L,∑ a:J (Y:=Y),
        r d*|b s law hr hk (t+1) ω d a-b s law hr hk t ω d a|):=by
    simp only [JointHeavy.charge,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro a _
    ring
  have heq:=congrArg (total (weight law hr) N) (funext (fun t=>funext (heqpoint t)))
  simp only [total_add,total_mul] at heq
  rw [heq]
  nlinarith
end KServer.JointHeavy

end


/-! Completion of the genuine observed prefix to an atom is used only on
positive fibers. Impossible histories receive the fixed root stock. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHistory
open JointExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

omit [MetricSpace Y] [Fintype Y] in
lemma prefix_of_take_eq (σ ρ:Fin H→Y) (t:ℕ)
    (h:(List.ofFn σ).take t=(List.ofFn ρ).take t):
    FiniteExperiment.requestPrefix σ t=FiniteExperiment.requestPrefix ρ t:=by
  funext i
  by_cases hi:i.val<t
  · have hh:=congrArg (fun xs:List Y=>xs[i.val]?) h
    simpa only [List.getElem?_take,ite_eq_left hi,List.getElem?_ofFn,dite_eq_left i.isLt,
      Fin.eta,FiniteExperiment.requestPrefix,ite_eq_left hi] using hh
  · simp only [FiniteExperiment.requestPrefix,ite_eq_right hi]

def Observed (a:Tape Y k H L r) (h:List Y) (ω:Atom (k:=k) law hr):Prop:=
  ω.val.2=a ∧ h.length≤H ∧ (List.ofFn ω.val.1).take h.length=h

omit [NeZero k] in
lemma observed_true (ω:Atom (k:=k) law hr) (t:ℕ) (ht:t≤H):
    Observed law hr ω.val.2 ((List.ofFn ω.val.1).take t) ω:=by
  have he:((List.ofFn ω.val.1).take t).length=t:=by simp only [List.length_take,List.length_ofFn,Nat.min_eq_left ht]
  exact ⟨rfl,by rwa [he],by rw [he]⟩

omit [NeZero k] in
lemma observed_history (a:Tape Y k H L r) (h:List Y) (ω ρ:Atom (k:=k) law hr)
    (hω:Observed law hr a h ω) (hρ:Observed law hr a h ρ):
    history law hr h.length ω=history law hr h.length ρ:=by
  apply (FiniteExperiment.history_eq_iff _ _ _).mpr
  exact ⟨hω.1.trans hρ.1.symm,prefix_of_take_eq ω.val.1 ρ.val.1 h.length (hω.2.2.trans hρ.2.2.symm)⟩

def q (a:Tape Y k H L r) (h:List Y):PrefixTree.Node (LevelKeys.Key Y k) L→ℝ:=
  if hp:∃ ω,Observed law hr a h ω then
    JointAllocation.quota s law hr hk h.length hp.choose
  else TreeRounding.stockMass (k:ℤ)

lemma q_eq (a:Tape Y k H L r) (h:List Y) (ω:Atom (k:=k) law hr)
    (hω:Observed law hr a h ω):q s law hr hk a h=JointAllocation.quota s law hr hk h.length ω:=by
  have hp:∃ ω,Observed law hr a h ω:=⟨ω,hω⟩
  rw [q,dite_eq_left hp]
  exact JointAllocation.quota_adapted s law hr hk _ hp.choose ω
    (observed_history law hr a h hp.choose ω hp.choose_spec hω)

lemma q_nonneg (a:Tape Y k H L r) (h:List Y) (v:PrefixTree.Node (LevelKeys.Key Y k) L):
    0≤q s law hr hk a h v:=by
  unfold q
  split_ifs with hp
  · exact JointAllocation.quota_nonneg s law hr hk _ _ v
  · unfold TreeRounding.stockMass; split_ifs <;> positivity

lemma q_park_nonneg (a:Tape Y k H L r) (h:List Y) (v:PrefixTree.Node (LevelKeys.Key Y k) L):
    0≤(PrefixTree.tree (LevelKeys.Key Y k) L).park (q s law hr hk a h) v:=by
  unfold q
  split_ifs with hp
  · exact JointAllocation.park_nonneg s law hr hk _ _ v
  · rw [TreeRounding.stockMass_park]
    unfold TreeRounding.stockMass; split_ifs <;> positivity

lemma q_root (a:Tape Y k H L r) (h:List Y):q s law hr hk a h 0=(k:ℝ):=by
  unfold q
  split_ifs with hp
  · exact PrefixTree.Q_root _ L _ _ _ _ _ hk _ _
  · simp only [TreeRounding.stockMass,ite_true,Int.cast_natCast]

def anchors (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (key:LevelKeys.Key Y k):Y:=
  if hd:d<L then LevelKeys.anchor s law (hr ⟨d,hd⟩).le ω.val.1 (ω.val.2 ⟨d,hd⟩) t key else s 0

lemma anchors_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr t ω=history law hr t ρ):anchors s law hr t ω=anchors s law hr t ρ:=by
  obtain ⟨ha,hp⟩:=history_eq law hr t ω ρ h
  funext d key
  unfold anchors
  split_ifs with hd
  · rw [ha]
    exact congrFun (KeysAdapted.anchor_adapted s law (hr ⟨d,hd⟩).le (ρ.val.2 ⟨d,hd⟩) t ω.val.1 ρ.val.1
      ((FiniteExperiment.requestHistory_eq_iff _ _ _).mpr hp)) key
  · rfl

def a (tape:Tape Y k H L r) (h:List Y):ℕ→LevelKeys.Key Y k→Y:=
  if hp:∃ ω,Observed law hr tape h ω then anchors s law hr h.length hp.choose else fun _ _=>s 0

lemma a_eq (tape:Tape Y k H L r) (h:List Y) (ω:Atom (k:=k) law hr)
    (hω:Observed law hr tape h ω):a s law hr tape h=anchors s law hr h.length ω:=by
  have hp:∃ ω,Observed law hr tape h ω:=⟨ω,hω⟩
  rw [a,dite_eq_left hp]
  exact anchors_adapted s law hr _ _ _ (observed_history law hr tape h hp.choose ω hp.choose_spec hω)
end KServer.JointHistory

end

end OAI
