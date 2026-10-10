import Mathlib
import OAI.Combinatorics.KServer.PrefixAllocation

namespace OAI

/-! The actual retained heavy label, not an assumed anchor motion rule. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma key_iff (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r)
    (t:ℕ) (x:Y) (a:Pool Y):
    HeavyKeys.key s law r heavyGamma heavyDelta σ tape t x=some a ↔
      ∃ c∈centers s law r heavyGamma heavyDelta σ t,
        (run s law r heavyGamma heavyDelta σ tape t).label c=a ∧
        dist c x≤(run s law r heavyGamma heavyDelta σ tape t).rad c:=by
  have hv:=run_valid s law hr heavyGamma heavyDelta σ tape t
  have hC:=centers_separated s law r heavyGamma heavyDelta σ t
  unfold HeavyKeys.key
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨c,hc,ha⟩
    obtain ⟨hm,hd⟩:=(HeavyKeys.centerKey_some hr hC (fun c hc=>(hv.1 c hc).2)).mp hc
    exact ⟨c,hm,ha,hd⟩
  · rintro ⟨c,hm,ha,hd⟩
    exact ⟨c,(HeavyKeys.centerKey_some hr hC (fun c hc=>(hv.1 c hc).2)).mpr ⟨hm,hd⟩,ha⟩

lemma anchor_eq (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r)
    (t:ℕ) {c:Y} {a:Pool Y} (hc:c∈centers s law r heavyGamma heavyDelta σ t)
    (ha:(run s law r heavyGamma heavyDelta σ tape t).label c=a):
    heavyAnchor s law r σ tape t a=c:=by
  have he:∃ b∈centers s law r heavyGamma heavyDelta σ t,
      (run s law r heavyGamma heavyDelta σ tape t).label b=a:=⟨c,hc,ha⟩
  rw [heavyAnchor,dite_eq_left he]
  exact (run_valid s law hr heavyGamma heavyDelta σ tape t).2
    he.choose_spec.1 hc (he.choose_spec.2.trans ha.symm)

lemma common_centers (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r)
    (t:Fin H) {a b:Y}
    (ha:a∈centers s law r heavyGamma heavyDelta σ t.val)
    (hb:b∈centers s law r heavyGamma heavyDelta σ (t.val+1))
    (he:(run s law r heavyGamma heavyDelta σ tape t.val).label a=
      (run s law r heavyGamma heavyDelta σ tape (t.val+1)).label b):
    a=b ∨ (b=σ t ∧ 8*r<dist a b ∧ dist a b≤40*r ∧
      Active r heavyGamma heavyDelta (centers s law r heavyGamma heavyDelta σ t.val)
        (mu s law (t.val+1) σ) (σ t)):=by
  have hv:=run_valid s law hr heavyGamma heavyDelta σ tape t.val
  rw [centers_succ,step] at hb
  simp only [run,t.isLt,↓reduceDIte] at he
  split_ifs at hb he with hA
  · by_cases hbx:b=σ t
    · subst b
      simp only [updatedLabel,Function.update_self] at he
      have hov:=existing_match hv.2 ha he.symm
      have hd:=overlap_distance (fun c hc=>(hv.1 c hc).2)
        (FiniteUniform.radius_range hr (tape t)).2 hov
      exact Or.inr ⟨rfl,hA.2 a ha,hd,hA⟩
    · have hbC: b∈centers s law r heavyGamma heavyDelta σ t.val:=
        (mem_filter.mp ((mem_insert.mp hb).resolve_left hbx)).1
      simp only [updatedLabel,Function.update_of_ne hbx] at he
      exact Or.inl (hv.2 ha hbC he)
  · exact Or.inl (hv.2 ha hb he)

end KServer.HeavyAnchorDynamics

end


/-! The first-priority heavy region is its full ball, including boundaries. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def slot (a:Pool Y):Key Y k:=Sum.inl ⟨none,a⟩

lemma level_heavy (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0≤r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x:Y) (a:Pool Y):
    map s law hr σ tape t x=slot (k:=k) a ↔
      HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t x=some a:=by
  let ks:=keys s law hr σ tape t
  change PriorityKeys.key ks x=Sum.inl ⟨none,a⟩ ↔ ks none x=some a
  constructor
  · intro he
    unfold PriorityKeys.key at he
    cases hs:PriorityKeys.selected ks x with
    | none=>rw [hs] at he; cases he
    | some z=>
      rw [hs] at he
      have hz:z=⟨none,a⟩:=Sum.inl.inj he
      subst z
      exact (PriorityKeys.selected_some ks x hs).1
  · intro ha
    have h:(PriorityKeys.covered ks x).Nonempty:=
      ⟨none,mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩⟩
    have hm:(PriorityKeys.covered ks x).min' h=none:=by
      apply le_antisymm
      · exact min'_le _ _ (mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩)
      · exact bot_le
    obtain ⟨b,hb,hs⟩:=PriorityKeys.selected_some_of_mem ks x h
    have he:(⟨(PriorityKeys.covered ks x).min' h,b⟩:Sigma (Alphabet Y k))=⟨none,a⟩:=by
      generalize hi : (PriorityKeys.covered ks x).min' h = i at b hb hm ⊢
      clear hi
      have hi0 : i=none:=hm
      subst i
      have hab:b=a:=Option.some.inj (hb.symm.trans ha)
      subst b
      rfl
    rw [he] at hs
    simp only [PriorityKeys.key,hs]

lemma region_ball (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) {c:Y} {a:Pool Y}
    (hc:c∈centers s law r heavyGamma heavyDelta σ t)
    (ha:(run s law r heavyGamma heavyDelta σ tape.1 t).label c=a):
    (univ.filter (fun x=>map s law hr.le σ tape t x=slot (k:=k) a))=
      ball c ((run s law r heavyGamma heavyDelta σ tape.1 t).rad c):=by
  ext x
  simp only [mem_filter,mem_univ,true_and,ball,level_heavy]
  rw [key_iff s law hr σ tape.1 t x a]
  constructor
  · rintro ⟨b,hb,hl,hd⟩
    have he: b=c:=(run_valid s law hr heavyGamma heavyDelta σ tape.1 t).2 hb hc (hl.trans ha.symm)
    simpa only [he] using hd
  · intro hd
    exact ⟨c,hc,ha,hd⟩

lemma heavy_mass_comparison (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (hσ:0<law.val σ) (tape:Tape Y k H r) (t:Fin H)
    (hA:Active r heavyGamma heavyDelta (centers s law r heavyGamma heavyDelta σ t.val)
      (mu s law (t.val+1) σ) (σ t)):
    let R:=(run s law r heavyGamma heavyDelta σ tape.1 (t.val+1)).rad (σ t)
    ball (σ t) (heavyGamma*r) ⊆ ball (σ t) R ∧
      mass (mu s law (t.val+1) σ) (ball (σ t) R)≤
        (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r)) ∧
      1≤ mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r)):=by
  dsimp only
  have hR:(run s law r heavyGamma heavyDelta σ tape.1 (t.val+1)).rad (σ t)∈Set.Icc (16*r) (20*r):=by
    exact (run_valid s law hr heavyGamma heavyDelta σ tape.1 (t.val+1)).1 _
      (by rw [centers_succ,step,ite_eq_left hA]; exact mem_insert_self _ _)
  have hγ:0≤heavyGamma ∧ heavyGamma≤16:=by norm_num [heavyGamma]
  refine ⟨ball_mono (by nlinarith [hR.1]),?_,?_⟩
  · exact (mass_mono (fun z=>mu_nonneg s law (t.val+1) σ z)
      (ball_mono (by nlinarith [hR.2]))).trans hA.1
  · have hx:σ t∈ball (σ t) (heavyGamma*r):=by
      simp only [ball,mem_filter,mem_univ,true_and,dist_self]
      exact mul_nonneg hγ.1 hr.le
    exact (mu_served s law t σ hσ).trans
      (single_le_sum (fun z _=>mu_nonneg s law (t.val+1) σ z) hx)
end KServer.HeavyAnchorDynamics

end


/-! The metric and heavy-ball payment portions of §08's anchor travel proof.
These are required by the open finite-law construction, not a new main result.
The clipped ramp and rho=6/5 are the exact source choices. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel

def ramp (u : ℝ) : ℝ := min 1 (max 0 ((u-4)/3))

lemma ramp_nonneg (u : ℝ) : 0 ≤ ramp u := le_min (by norm_num) (le_max_left _ _)
lemma ramp_le_one (u : ℝ) : ramp u ≤ 1 := min_le_left _ _
lemma ramp_zero {u : ℝ} (h : u ≤ 4) : ramp u=0 := by
  unfold ramp
  rw [max_eq_left (by linarith),min_eq_right (by norm_num)]
lemma ramp_one {u : ℝ} (h : 7 ≤ u) : ramp u=1 := by
  unfold ramp
  rw [max_eq_right (by linarith),min_eq_left (by linarith)]

lemma ramp_lipschitz (a b : ℝ) : |ramp b-ramp a| ≤ |b-a|/3 := by
  rw [abs_le]
  constructor <;> unfold ramp <;>
    simp only [min_def,max_def] <;> split_ifs <;>
    have h1 := le_abs_self (b-a) <;> have h2 := neg_le_abs (b-a) <;> linarith

variable {Y : Type*} [MetricSpace Y]

/-- Actual pointwise metric motion inequality, including the saturation cutoff.
No independence between the old point and an updated history is required. -/
theorem ramp_motion {a y z : Y} {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    r*c*max 0 (ramp (dist a z/r)-ramp (dist a y/r)) ≤
      if dist a y < 7*r then dist y z/3*c else 0 := by
  by_cases hh : dist a y < 7*r
  · rw [ite_eq_left hh]
    have h := ramp_lipschitz (dist a y/r) (dist a z/r)
    have hmetric : |dist a z-dist a y| ≤ dist y z := by
      rw [abs_le]
      constructor
      · linarith [dist_triangle a z y,dist_comm z y]
      · linarith [dist_triangle a y z]
    have habs : |dist a z/r-dist a y/r| = |dist a z-dist a y|/r := by
      rw [←sub_div,abs_div,abs_of_pos hr]
    rw [habs] at h
    have hbound : ramp (dist a z/r)-ramp (dist a y/r) ≤ dist y z/r/3 :=
      (le_abs_self _).trans (h.trans (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hmetric hr.le) (by norm_num)))
    have hmax := max_le (by positivity : (0:ℝ) ≤ dist y z/r/3) hbound
    have hm := mul_le_mul_of_nonneg_left hmax (mul_nonneg hr.le hc)
    convert hm using 1; first | rfl | field_simp
  · rw [ite_eq_right hh]
    have hsat : 7 ≤ dist a y/r := (le_div_iff₀ hr).mpr (le_of_not_gt hh)
    rw [ramp_one hsat,max_eq_left (by linarith [ramp_le_one (dist a z/r)]),mul_zero]

/-- On the heavy inner ball the new ramp vanishes and the old ramp is one. -/
lemma inner_ramp {a x z : Y} {r γ : ℝ} (hr : 0 < r) (hγ : γ < 1/100)
    (hax : 8*r < dist a x) (hxz : dist x z ≤ γ*r) :
    ramp (dist x z/r)=0 ∧ ramp (dist a z/r)=1 := by
  have htri := dist_triangle a z x
  rw [dist_comm z x] at htri
  constructor
  · apply ramp_zero
    apply (div_le_iff₀ hr).mpr
    nlinarith
  · apply ramp_one
    apply (le_div_iff₀ hr).mpr
    nlinarith

variable [DecidableEq Y]

def integral (w : Y → ℝ) (C : Finset Y) (a : Y) (r : ℝ) : ℝ :=
  ∑ z ∈ C, w z*ramp (dist a z/r)

def mass (w : Y → ℝ) (C : Finset Y) : ℝ := ∑ z ∈ C, w z

omit [DecidableEq Y] in
lemma integral_bounds {w : Y → ℝ} {C : Finset Y} {a : Y} {r : ℝ}
    (hw : ∀ z ∈ C, 0 ≤ w z) : integral w C a r ∈ Set.Icc 0 (mass w C) := by
  constructor
  · exact sum_nonneg fun z hz => mul_nonneg (hw z hz) (ramp_nonneg _)
  · apply sum_le_sum
    intro z hz
    exact mul_le_of_le_one_right (hw z hz) (ramp_le_one _)

/-- The heavy condition gives the actual unnormalized potential drop on a
retained reuse, with C the new heavy key's entire ball and S its inner ball. -/
theorem heavy_integral_drop {w : Y → ℝ} {C S : Finset Y} {a x : Y} {r γ δ : ℝ}
    (hw : ∀ z ∈ C, 0 ≤ w z) (hSC : S ⊆ C)
    (hr : 0 < r) (hγ : γ < 1/100) (hax : 8*r < dist a x)
    (hS : ∀ z ∈ S, dist x z ≤ γ*r)
    (hheavy : mass w C ≤ (1+δ)*mass w S) :
    integral w C x r-integral w C a r ≤ -(1-δ)*mass w S := by
  have hpoint : ∀ z ∈ C, w z*ramp (dist x z/r)-w z*ramp (dist a z/r) ≤
      w z-2*(if z ∈ S then w z else 0) := by
    intro z hz
    by_cases hs : z ∈ S
    · have hh := inner_ramp hr hγ hax (hS z hs)
      rw [hh.1,hh.2,ite_eq_left hs]
      ring_nf
      exact le_rfl
    · rw [ite_eq_right hs,mul_zero,sub_zero]
      nlinarith [mul_nonneg (hw z hz) (ramp_nonneg (dist a z/r)),
        mul_le_of_le_one_right (hw z hz) (ramp_le_one (dist x z/r))]
  have hsum := sum_le_sum hpoint
  have hrestrict : (∑ z ∈ C, if z ∈ S then w z else 0) = mass w S := by
    unfold mass
    rw [←sum_filter]
    rw [filter_mem_eq_inter,inter_eq_right.mpr hSC]
  rw [sum_sub_distrib,sum_sub_distrib,←mul_sum,hrestrict] at hsum
  change integral w C x r-integral w C a r ≤ mass w C-2*mass w S at hsum
  linarith

/-- Exact rho=6/5 normalization. H≥1 is used in the held-size comparison. -/
theorem retained_anchor_payment {w : Y → ℝ} {C S : Finset Y} {a x : Y}
    {r γ δ u b : ℝ} (hw : ∀ z ∈ C, 0 ≤ w z) (hSC : S ⊆ C)
    (hr : 0 < r) (hγ : γ < 1/100) (hδ : δ ≤ 1/100)
    (hax : 8*r < dist a x) (hS : ∀ z ∈ S, dist x z ≤ γ*r)
    (hheavy : mass w C ≤ (1+δ)*mass w S) (hH : 1 ≤ mass w S)
    (hu : 0 < u) (href : u ≤ (6/5)*(1+mass w C)) (hb : 0 ≤ b) :
    r*b/u*(integral w C x r-integral w C a r) ≤ -r*b/4 := by
  have hdrop := heavy_integral_drop hw hSC hr hγ hax hS hheavy
  have hM : u ≤ (6/5)*(2+δ)*mass w S := by nlinarith
  have hcoef : u ≤ 4*(1-δ)*mass w S := by
    have hp : 0 ≤ mass w S := by linarith
    have hh : (6/5)*(2+δ) ≤ 4*(1-δ) := by linarith
    exact hM.trans (mul_le_mul_of_nonneg_right hh hp)
  have hratio : (1:ℝ)/4 ≤ (1-δ)*mass w S/u := by
    apply (le_div_iff₀ hu).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_left hdrop (div_nonneg (mul_nonneg hr.le hb) hu.le)
  have hp := mul_le_mul_of_nonneg_left hratio (mul_nonneg hr.le hb)
  calc _ ≤ r*b/u*(-(1-δ)*mass w S) := hm
       _ = -(r*b*((1-δ)*mass w S/u)) := by ring
       _ ≤ -(r*b*(1/4)) := neg_le_neg hp
       _ = -r*b/4 := by ring

/-- Positive normalization-refresh jumps are paid by the old-plus-new size
charge; no invalid comparison of the new integral to the old reference is used. -/
theorem normalization_refresh {r b I s u C : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hI : 0 ≤ I) (hs : 0 < s) (hu : 0 < u)
    (hIs : I ≤ s) (hbu : b ≤ (6/5)*C*u) :
    r*b*I*(1/s-1/u) ≤ (6/5)*C*r*u := by
  by_cases h : u ≤ s
  · have h1 : 1/s-1/u ≤ 0 := sub_nonpos.mpr (one_div_le_one_div_of_le hu h)
    have hleft := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hr hb) hI) h1
    have hright : 0 ≤ (6/5)*C*r*u := by nlinarith [mul_nonneg hr hb, mul_le_mul_of_nonneg_left hbu hr]
    exact hleft.trans hright
  · have hdrop : r*b*I*(1/s-1/u) ≤ r*b := by
      have hdiv : I/s ≤ 1 := (div_le_one hs).mpr hIs
      have hp := mul_le_mul_of_nonneg_left hdiv (mul_nonneg hr hb)
      have hn := div_nonneg (mul_nonneg (mul_nonneg hr hb) hI) hu.le
      calc _ = r*b*(I/s)-r*b*I/u := by ring
           _ ≤ _ := by linarith
    exact hdrop.trans (by nlinarith [mul_le_mul_of_nonneg_left hbu hr])

end KServer.AnchorTravel

end


/-! The actual retained label releases the ramp credit. All geometry and the
one-unit inner mass are obtained from the actual embedding and served hidden
trajectory, not postulated as an anchor-payment interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def present (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (a:Pool Y):Prop:=
  ∃ c∈centers s law r heavyGamma heavyDelta σ t,
    (run s law r heavyGamma heavyDelta σ tape t).label c=a

def cell (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0≤r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (a:Pool Y):Finset Y:=
  univ.filter (fun x=>map s law hr σ tape t x=slot (k:=k) a)

lemma absent_cell (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (a:Pool Y)
    (ha:¬present s law r σ tape.1 t a):cell s law hr.le σ tape t a=∅:=by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he:HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t x=some a:=
    (level_heavy s law hr.le σ tape t x a).mp (mem_filter.mp hx).2
  obtain ⟨c,hc,hl,_⟩:=(key_iff s law hr σ tape.1 t x a).mp he
  exact ha ⟨c,hc,hl⟩

lemma present_cell (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (a:Pool Y)
    (ha:present s law r σ tape.1 t a):
    ∃ c∈centers s law r heavyGamma heavyDelta σ t,
      heavyAnchor s law r σ tape.1 t a=c ∧
      cell s law hr.le σ tape t a=ball c ((run s law r heavyGamma heavyDelta σ tape.1 t).rad c):=by
  obtain ⟨c,hc,hl⟩:=ha
  exact ⟨c,hc,anchor_eq s law hr σ tape.1 t hc hl,region_ball s law hr σ tape t hc hl⟩

lemma moving_drop (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (hσ:0<law.val σ) (tape:Tape Y k H r) (t:Fin H)
    (a:Pool Y) (hold:present s law r σ tape.1 t.val a)
    (hnew:present s law r σ tape.1 (t.val+1) a)
    (hmove:heavyAnchor s law r σ tape.1 t.val a≠heavyAnchor s law r σ tape.1 (t.val+1) a)
    {u b:ℝ} (hu:0<u) (hb:0≤b)
    (href:u≤(6/5:ℝ)*(1+AnchorTravel.mass (mu s law (t.val+1) σ)
      (cell s law hr.le σ tape (t.val+1) a))):
    r*b/u*(AnchorTravel.integral (mu s law (t.val+1) σ) (cell s law hr.le σ tape (t.val+1) a)
      (heavyAnchor s law r σ tape.1 (t.val+1) a) r-
      AnchorTravel.integral (mu s law (t.val+1) σ) (cell s law hr.le σ tape (t.val+1) a)
      (heavyAnchor s law r σ tape.1 t.val a) r)≤-r*b/4:=by
  obtain ⟨c,hc,hl⟩:=hold
  obtain ⟨d,hd,hl'⟩:=hnew
  have ha:=anchor_eq s law hr σ tape.1 t.val hc hl
  have ha':=anchor_eq s law hr σ tape.1 (t.val+1) hd hl'
  have hcd:c≠d:=by intro he; exact hmove (ha.trans (he.trans ha'.symm))
  obtain ⟨hdx,hfar,_,hA⟩:=(common_centers s law hr σ tape.1 t hc hd (hl.trans hl'.symm)).resolve_left hcd
  have hanew:=ha'.trans hdx
  rw [hdx] at hd hl' hfar
  have hcell:=region_ball s law hr σ tape (t.val+1) hd hl'
  have hmass:=heavy_mass_comparison s law hr σ hσ tape t hA
  change _ ∧ _ ∧ _ at hmass
  change cell s law hr.le σ tape (t.val+1) a=_ at hcell
  rw [hcell] at href
  rw [ha,hanew,hcell]
  exact AnchorTravel.retained_anchor_payment
    (fun z _=>mu_nonneg s law (t.val+1) σ z) hmass.1 hr
    (by norm_num [heavyGamma]) (by norm_num [heavyDelta]) hfar
    (fun z hz=>(mem_filter.mp hz).2) hmass.2.1 hmass.2.2 hu href hb

end KServer.HeavyAnchorDynamics

end


/-! The old ramp cutoff selects a heavy ball containing the unit-radius ball
about the old point and lying inside its twenty-seven-radius neighborhood. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def selected (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (y:Y):Option (Key Y k):=
  match HeavyKeys.key s law r heavyGamma heavyDelta σ tape t y with
  | none=>none
  | some a=>if dist (heavyAnchor s law r σ tape t a) y<7*r then some (slot (k:=k) a) else none

lemma selected_data (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (y:Y) (a:Key Y k)
    (ha:selected s law r σ tape.1 t y=some a):
    ∃ c∈centers s law r heavyGamma heavyDelta σ t,
      a=slot (k:=k) ((run s law r heavyGamma heavyDelta σ tape.1 t).label c) ∧
      dist c y<7*r:=by
  unfold selected at ha
  cases he:HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t y with
  | none=>rw [he] at ha; cases ha
  | some b=>
    rw [he] at ha
    dsimp only at ha
    split_ifs at ha with hd
    · obtain ⟨c,hc,hl,_⟩:=(key_iff s law hr σ tape.1 t y b).mp he
      rw [anchor_eq s law hr σ tape.1 t hc hl] at hd
      exact ⟨c,hc,(Option.some.inj ha).symm.trans (congrArg (slot (k:=k)) hl.symm),hd⟩

lemma selected_close (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (y:Y) (a:Key Y k)
    (ha:selected s law r σ tape.1 t y=some a) (z:Y)
    (hz:map s law hr.le σ tape t z=a):dist y z≤27*r:=by
  obtain ⟨c,hc,rfl,hd⟩:=selected_data s law hr σ tape t y a ha
  have hb:=region_ball s law hr σ tape t hc rfl
  have hz':z∈ball c ((run s law r heavyGamma heavyDelta σ tape.1 t).rad c):=by
    rw [←hb]; exact mem_filter.mpr ⟨mem_univ _,hz⟩
  have hr':=(run_valid s law hr heavyGamma heavyDelta σ tape.1 t).1 c hc
  have hh:=dist_triangle y c z
  rw [dist_comm y c] at hh
  have hd':=(mem_filter.mp hz').2
  change dist c z≤_ at hd'
  linarith [hr'.2]

lemma selected_contains (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (y:Y) (a:Key Y k)
    (ha:selected s law r σ tape.1 t y=some a) (z:Y) (hz:dist y z≤r):
    map s law hr.le σ tape t z=a:=by
  obtain ⟨c,hc,rfl,hd⟩:=selected_data s law hr σ tape t y a ha
  apply (level_heavy s law hr.le σ tape t z _).mpr
  apply (key_iff s law hr σ tape.1 t z _).mpr
  refine ⟨c,hc,rfl,?_⟩
  have hr':=(run_valid s law hr heavyGamma heavyDelta σ tape.1 t).1 c hc
  have hh:=dist_triangle c y z
  linarith [hr'.1]

end KServer.HeavyAnchorDynamics

end


/-! The pointwise drift comparison for the old heavy-slot ramp coefficients.
It applies to an arbitrary coupled old/new member, without independence. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y J D:Type*} [MetricSpace Y]

def term (r:ℝ) (c:J→ℝ) (a:J→Y) (key:Option J) (y:Y):ℝ:=
  match key with
  | none=>0
  | some j=>r*c j*ramp (dist (a j) y/r)

def cutoff (r:ℝ) (c:J→ℝ) (a:J→Y) (key:Option J) (y:Y):ℝ:=
  match key with
  | none=>0
  | some j=>if dist (a j) y<7*r then c j else 0

lemma cutoff_nonneg {r:ℝ} {c:J→ℝ} {a:J→Y} (hc:∀ j,0≤c j) (key:Option J) (y:Y):
    0≤cutoff r c a key y:=by
  cases key with
  | none=>rfl
  | some j=>dsimp [cutoff]; split_ifs <;> [exact hc j; rfl]

lemma term_bounds {r M:ℝ} {c:J→ℝ} {a:J→Y}
    (hr:0≤r) (hM:0≤M) (hc:∀ j,c j∈Set.Icc 0 M) (key:Option J) (y:Y):
    term r c a key y∈Set.Icc 0 (r*M):=by
  cases key with
  | none=>exact ⟨le_rfl,mul_nonneg hr hM⟩
  | some j=>
    dsimp [term]
    exact ⟨mul_nonneg (mul_nonneg hr (hc j).1) (ramp_nonneg _),
      (mul_le_of_le_one_right (mul_nonneg hr (hc j).1) (ramp_le_one _)).trans
        (mul_le_mul_of_nonneg_left (hc j).2 hr)⟩

lemma term_motion {r M:ℝ} {c:J→ℝ} {a:J→Y}
    (hr:0<r) (hM:0≤M) (hc:∀ j,c j∈Set.Icc 0 M) (old new:Option J) (y z:Y):
    term r c a new z-term r c a old y≤
      M*r*(if new=old then 0 else 1)+dist y z/3*cutoff r c a old y:=by
  by_cases he:new=old
  · subst new
    rw [ite_eq_left rfl,mul_zero,zero_add]
    cases old with
    | none=>simp only [term,cutoff,sub_self,mul_zero,le_refl]
    | some j=>
      have hh:=ramp_motion (a:=a j) (y:=y) (z:=z) hr (hc j).1
      simp only [term,cutoff]
      calc _ = r*c j*(ramp (dist (a j) z/r)-ramp (dist (a j) y/r)):=by ring
           _ ≤ r*c j*max 0 (ramp (dist (a j) z/r)-ramp (dist (a j) y/r)):=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg hr.le (hc j).1)
           _ ≤ _:=by simpa only [mul_ite,mul_zero] using hh
  · rw [ite_eq_right he,mul_one]
    have hnew:term r c a new z≤r*M:=(term_bounds hr.le hM hc new z).2
    have hold:0≤term r c a old y:=(term_bounds hr.le hM hc old y).1
    have hcut:0≤dist y z/3*cutoff r c a old y:=
      mul_nonneg (div_nonneg dist_nonneg (by norm_num)) (cutoff_nonneg (fun j=>(hc j).1) old y)
    nlinarith

variable [Fintype D]

theorem member_drift {r:D→ℝ} {M C:ℝ} {c:D→J→ℝ} {a:D→J→Y}
    (hr:∀ d,0<r d) (hM:0≤M) (hc:∀ d j,c d j∈Set.Icc 0 M)
    (old new:D→Y→Option J) (y z:Y)
    (hcut:(∑ d,cutoff (r d) (c d) (a d) (old d y) y)≤C):
    (∑ d,term (r d) (c d) (a d) (new d z) z)-
      (∑ d,term (r d) (c d) (a d) (old d y) y)≤
      M*(∑ d,r d*(if new d z=old d y then 0 else 1))+C/3*dist y z:=by
  rw [←sum_sub_distrib]
  have hh:=sum_le_sum (s:=(univ:Finset D)) (fun d _=>term_motion (a:=a d) (hr d) hM (hc d) (old d y) (new d z) y z)
  simp only [sum_add_distrib,mul_assoc,←mul_sum] at hh
  have hm:=mul_le_mul_of_nonneg_left hcut (div_nonneg (dist_nonneg (x:=y) (y:=z)) (by norm_num : (0:ℝ)≤3))
  nlinarith

end KServer.AnchorTravel

end


/-! Exact finite conditional integration for the chronological ramp. These
identities do not discard a filtering term after an adaptive choice. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω Y D J:Type} [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J]
variable [MetricSpace Y] {w:Ω→ℝ} {k:ℕ}

omit [MetricSpace Y] in
lemma conditional_average (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (q:Ω→Fin k→Y)
    (F:Ω→Y→ℝ) (hF:∀ ω ρ,H ω=H ρ→F ω=F ρ):
    avg w (fun ω=>∑ y,PosteriorCounting.measure (w:=w) H q ω y*F ω y)=
      avg w (fun ω=>∑ i:Fin k,F ω (q ω i)):=by
  have he:(fun ω=>∑ y,PosteriorCounting.measure (w:=w) H q ω y*F ω y)=
      posterior w H (fun ω=>∑ i:Fin k,F ω (q ω i)):=by
    funext ω
    exact PosteriorCounting.conditional_integral H q ω F (fun ρ h=>hF ρ ω h)
  rw [he]
  exact posterior_avg hw H _

def slotIntegral (μ:Y→ℝ) (key:Y→Option J) (a:Y) (r:ℝ) (j:J):ℝ:=
  ∑ y∈univ.filter (fun y=>key y=some j),μ y*ramp (dist a y/r)

lemma integral_term (μ:Y→ℝ) (key:Y→Option J) (a:J→Y) (r:ℝ) (c:J→ℝ):
    (∑ j,r*c j*slotIntegral μ key (a j) r j)=∑ y,μ y*term r c a (key y) y:=by
  simp only [slotIntegral,sum_filter,mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  cases he:key y with
  | none=>simp [term]
  | some j=>simp [term,mul_left_comm]

omit [Fintype J] in
lemma slotIntegral_nonneg {μ:Y→ℝ} (hμ:∀ y,0≤μ y) (key:Y→Option J) (a:Y) (r:ℝ) (j:J):
    0 ≤ slotIntegral μ key a r j:=
  sum_nonneg (fun y _=>mul_nonneg (hμ y) (ramp_nonneg _))

omit [Fintype J] in
lemma slotIntegral_bound {μ:Y→ℝ} (hμ:∀ y,0≤μ y) (key:Y→Option J) (a:Y) (r:ℝ) (j:J):
    slotIntegral μ key a r j≤∑ y∈univ.filter (fun y=>key y=some j),μ y:=by
  apply sum_le_sum
  intro y _
  exact mul_le_of_le_one_right (hμ y) (ramp_le_one _)

omit [Fintype Y] [Fintype J] in
lemma expected_membership (hw:∀ ω,0≤w ω)
    {r:D→ℝ} {M C:ℝ} {c:Ω→D→J→ℝ} {a:Ω→D→J→Y}
    (hr:∀ d,0<r d) (hM:0≤M) (hc:∀ ω d j,c ω d j∈Set.Icc 0 M)
    (old new:Ω→D→Y→Option J) (q q':Ω→Fin k→Y)
    (hcut:∀ ω i,(∑ d,cutoff (r d) (c ω d) (a ω d) (old ω d (q ω i)) (q ω i))≤C):
    avg w (fun ω=>(∑ i:Fin k,∑ d,term (r d) (c ω d) (a ω d) (new ω d (q' ω i)) (q' ω i))-
      (∑ i:Fin k,∑ d,term (r d) (c ω d) (a ω d) (old ω d (q ω i)) (q ω i)))≤
      M*avg w (fun ω=>∑ i:Fin k,∑ d,r d*(if new ω d (q' ω i)=old ω d (q ω i) then 0 else 1))+
        C/3*avg w (fun ω=>∑ i:Fin k,dist (q ω i) (q' ω i)):=by
  have hh:=avg_mono hw (fun ω=>sum_le_sum (s:=(univ:Finset (Fin k)))
    (fun i _=>member_drift hr hM (hc ω) (old ω) (new ω) (q ω i) (q' ω i) (hcut ω i)))
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,avg_add,avg_mul] at hh
  exact hh

omit [Fintype Y] [Fintype J] in
lemma raw_bounds {r:D→ℝ} {M:ℝ} (hr:∀ d,0≤r d) (hM:0≤M)
    (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J) (q:Fin k→Y)
    (hc:∀ d j,c d j∈Set.Icc 0 M):
    (∑ i:Fin k,∑ d,term (r d) (c d) (a d) (key d (q i)) (q i))∈
      Set.Icc 0 (M*k*(∑ d,r d)):=by
  constructor
  · exact sum_nonneg (fun i _=>sum_nonneg (fun d _=>(term_bounds (hr d) hM (hc d) _ _).1))
  · calc _≤∑ i:Fin k,∑ d,r d*M:=sum_le_sum (fun i _=>sum_le_sum
            (fun d _=>(term_bounds (hr d) hM (hc d) _ _).2))
         _ = _:=by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←sum_mul]; ring

end KServer.AnchorTravel

end


/-! Scalar chronological accounting in the source order: membership, reference,
park, anchor. The normalization comparison is used only after its refresh. -/
noncomputable section
namespace KServer.AnchorTravel

lemma reference_step {r b M I u C:ℝ}
    (hr:0≤r) (hb:0≤b) (hI:I∈Set.Icc 0 M) (hM:0≤M) (hu:0<u)
    (hC:0≤C) (hbu:b≤(6/5:ℝ)*C*u):
    let un:=if KeySizeTracking.refresh (1+M) u then 1+M else u
    r*b/un*I-r*b/u*I≤(6/5:ℝ)*C*r*
      (if KeySizeTracking.refresh (1+M) u then u+un else 0):=by
  dsimp only
  split_ifs with h
  · have hh:=normalization_refresh hr hb hI.1 (by linarith : 0<1+M) hu
      (by linarith [hI.2] : I≤1+M) hbu
    have he:r*b/(1+M)*I-r*b/u*I=r*b*I*(1/(1+M)-1/u):=by ring
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith : u≤u+(1+M))
      (by positivity))
  · simp only [sub_self,mul_zero,le_refl]

lemma park_step {r b c u I:ℝ} (hr:0≤r) (hu:0<u)
    (hI:0≤I) (hIu:I≤(6/5:ℝ)*u):
    r*c/u*I-r*b/u*I≤(6/5:ℝ)*r*|c - b|:=by
  have hcoef:I/u≤(6/5:ℝ):=(div_le_iff₀ hu).mpr hIu
  have hcoef0:0≤I/u:=div_nonneg hI hu.le
  calc _ = r*(c-b)*(I/u):=by ring
       _ ≤ r*|c - b| * (I/u):=mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_abs_self _) hr) hcoef0
       _ ≤ r*|c - b| * (6/5:ℝ):=mul_le_mul_of_nonneg_left hcoef (mul_nonneg hr (abs_nonneg _))
       _ = _:=by ring

lemma anchor_step {r b c u I J:ℝ} (hr:0≤r) (hc:0≤c) (hu:0<u)
    (hI:0≤I) (hJ:J≤(6/5:ℝ)*u)
    (oldPresent newPresent moving:Prop) [Decidable oldPresent] [Decidable newPresent] [Decidable moving]
    (habs:¬newPresent→c=0) (hbirth:¬oldPresent→b=0)
    (hsame:oldPresent→newPresent→¬moving→J=I)
    (hdrop:oldPresent→newPresent→moving→ r*c/u*(J-I)≤ -r*c/4):
    r*c/u*J-r*c/u*I+
      (if oldPresent ∧ newPresent ∧ moving then r*c/4 else 0)≤
        (6/5:ℝ)*r*|c - b|:=by
  have hpos:0≤(6/5:ℝ)*r*|c - b|:=by positivity
  by_cases hn:newPresent
  · by_cases ho:oldPresent
    · by_cases hm:moving
      · rw [ite_eq_left ⟨ho,hn,hm⟩]
        have hh:=hdrop ho hn hm
        nlinarith
      · rw [ite_eq_right (by simp only [hm,and_false,not_false_eq_true]),hsame ho hn hm]
        simpa only [sub_self,add_zero] using hpos
    · rw [ite_eq_right (by simp only [ho,false_and,not_false_eq_true]),add_zero,hbirth ho,sub_zero,abs_of_nonneg hc]
      have hh:=mul_le_mul_of_nonneg_left hJ (div_nonneg (mul_nonneg hr hc) hu.le)
      have hz:0≤r*c/u*I:=mul_nonneg (div_nonneg (mul_nonneg hr hc) hu.le) hI
      have he:r*c/u*((6/5:ℝ)*u)=(6/5:ℝ)*r*c:=by field_simp
      rw [he] at hh
      linarith
  · rw [ite_eq_right (by simp only [hn,and_false,false_and,not_false_eq_true]),habs hn]
    simp only [mul_zero,zero_div,zero_mul,sub_self,add_zero]
    positivity

lemma chronological_step {r b c u v A B E travel refresh variation:ℝ}
    (href:r*b/v*B-r*b/u*B≤refresh)
    (hpark:r*c/v*B-r*b/v*B≤variation)
    (hanchor:r*c/v*E-r*c/v*B+travel/4≤variation):
    r*c/v*E-r*b/u*A+travel/4≤
      (r*b/u*B-r*b/u*A)+refresh+2*variation:=by
  linarith

end KServer.AnchorTravel

end


/-! Signed chronological potential, with old coefficients throughout the
membership comparison. The final telescope keeps a single finite endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω Y D J:Type} [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J]
variable [MetricSpace Y] {w:Ω→ℝ} {k:ℕ}

def familyTest (r:D→ℝ) (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J) (y:Y):ℝ:=
  ∑ d,term (r d) (c d) (a d) (key d y) y

def familyIntegral (μ:Y→ℝ) (r:D→ℝ) (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J):ℝ:=
  ∑ d,∑ j,r d*c d j*slotIntegral μ (key d) (a d j) (r d) j

lemma familyIntegral_eq (μ:Y→ℝ) (r:D→ℝ) (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J):
    familyIntegral μ r c a key=∑ y,μ y*familyTest r c a key y:=by
  simp only [familyIntegral,integral_term,familyTest,mul_sum]
  rw [sum_comm]

lemma expected_step (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (q q':Ω→Fin k→Y)
    {r:D→ℝ} {M C:ℝ} (hr:∀ d,0<r d) (hM:0≤M)
    (c c':Ω→D→J→ℝ) (a a':Ω→D→J→Y) (old new:Ω→D→Y→Option J)
    (hc:∀ ω d j,c ω d j∈Set.Icc 0 M)
    (hcut:∀ ω i,(∑ d,cutoff (r d) (c ω d) (a ω d) (old ω d (q ω i)) (q ω i))≤C)
    (had:∀ ω ρ,H ω=H ρ→familyTest r (c ω) (a ω) (new ω)=familyTest r (c ρ) (a ρ) (new ρ))
    (had':∀ ω ρ,H ω=H ρ→familyTest r (c' ω) (a' ω) (new ω)=familyTest r (c' ρ) (a' ρ) (new ρ))
    (travel charge:Ω→ℝ)
    (hstage:∀ ω,familyIntegral (PosteriorCounting.measure (w:=w) H q' ω) r (c' ω) (a' ω) (new ω)-
      familyIntegral (PosteriorCounting.measure (w:=w) H q' ω) r (c ω) (a ω) (new ω)+travel ω/4≤charge ω):
    avg w (fun ω=>∑ i:Fin k,familyTest r (c' ω) (a' ω) (new ω) (q' ω i))-
      avg w (fun ω=>∑ i:Fin k,familyTest r (c ω) (a ω) (old ω) (q ω i))+
      avg w travel/4≤
        M*avg w (fun ω=>∑ i:Fin k,∑ d,r d*(if new ω d (q' ω i)=old ω d (q ω i) then 0 else 1))+
        C/3*avg w (fun ω=>∑ i:Fin k,dist (q ω i) (q' ω i))+avg w charge:=by
  have hh:=avg_mono hw hstage
  simp only [familyIntegral_eq,avg_add,avg_sub] at hh
  have hd:avg w (fun ω=>travel ω/4)=avg w travel/4:=by
    unfold RankTracking.avg
    rw [sum_div]
    apply sum_congr rfl
    intro ω _
    ring
  rw [hd,conditional_average hw H q' _ had,conditional_average hw H q' _ had'] at hh
  have hm:=expected_membership hw hr hM hc old new q q' hcut
  simp only [avg_sub] at hm
  change _≤_ at hm
  dsimp only [familyTest] at hh ⊢
  linarith

omit [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J] [MetricSpace Y] in
lemma chronological_telescope (P T E:ℕ→ℝ) (N:ℕ) {B:ℝ}
    (hP:0≤P N) (hB:P 0≤B)
    (hstep:∀ t,t<N→P (t+1)-P t+T t/4≤E t):
    (∑ t∈range N,T t)≤4*(∑ t∈range N,E t)+4*B:=by
  have he:(∑ t∈range N,(P (t+1)-P t))=P N-P 0:=by
    clear hP hstep
    induction N with
    | zero=>simp
    | succ N ih=>rw [sum_range_succ,ih]; ring
  have hh:=sum_le_sum (s:=range N) (fun t ht=>hstep t (mem_range.mp ht))
  simp only [sum_add_distrib,←sum_div,he] at hh
  linarith

end KServer.AnchorTravel

end


/-! A literal single-slot ordered update: held reference, park, retained anchor. -/
noncomputable section
namespace KServer.AnchorTravel

lemma slot_stage {r b c u v M I J C:ℝ} (hr:0≤r) (hb:0≤b) (hc:0≤c)
    (hu:0<u) (hv:0<v) (hC:0≤C) (hM:0≤M)
    (hI:I∈Set.Icc 0 M) (hJ:J≤M)
    (hbu:b≤(6/5:ℝ)*C*u) (hn:1+M≤(6/5:ℝ)*v)
    (he:v=if KeySizeTracking.refresh (1+M) u then 1+M else u)
    (oldPresent newPresent moving:Prop) [Decidable oldPresent] [Decidable newPresent] [Decidable moving]
    (habs:¬newPresent→c=0) (hbirth:¬oldPresent→b=0)
    (hsame:oldPresent→newPresent→¬moving→J=I)
    (hdrop:oldPresent→newPresent→moving→ r*c/v*(J-I)≤ -r*c/4):
    r*(c/v)*J-r*(b/u)*I+
      (if oldPresent ∧ newPresent ∧ moving then r*c else 0)/4≤
        (6/5:ℝ)*C*r*(if KeySizeTracking.refresh (1+M) u then u+v else 0)+
          2*(6/5:ℝ)*r*|c-b|:=by
  have href:=reference_step hr hb hI hM hu hC hbu
  change _≤_ at href
  rw [←he] at href
  have hMv : M ≤ (6/5:ℝ)*v := (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num)).trans hn
  have hp:=park_step (b:=b) (c:=c) hr hv hI.1 (hI.2.trans hMv)
  have ha:=anchor_step (b:=b) (I:=I) hr hc hv hI.1 (hJ.trans hMv)
    oldPresent newPresent moving habs hbirth hsame hdrop
  have ht:(if oldPresent ∧ newPresent ∧ moving then r*c else 0)/4=
      if oldPresent ∧ newPresent ∧ moving then r*c/4 else 0:=by split_ifs <;> simp
  rw [ht]
  simp only [mul_div_assoc] at href hp ha ⊢
  linarith

end KServer.AnchorTravel

end


/-! True prefix measurability of the literal permanent anchors, including
unused labels. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeysAdapted
open FiniteExperiment TierProcess Chronological ActualRoster LevelKeys LevelLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma heavy_anchor_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (r:ℝ) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ):
    heavyAnchor s law r σ tape t=heavyAnchor s law r ρ tape t:=by
  funext a
  unfold heavyAnchor
  rw [run_adapted s law r heavyGamma heavyDelta tape t σ ρ hh,
    HeavyCenters.centers_adapted s law r heavyGamma heavyDelta t σ ρ hh]

lemma tier_anchor_adapted [Nonempty Y] (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) {r:ℝ} (hr:0≤r) (γ h:ℝ) (K t:ℕ)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ):
    TierKeys.anchor (request s σ) hr K (qualifies s law T r γ h σ) t=
      TierKeys.anchor (request s ρ) hr K (qualifies s law T r γ h ρ) t:=by
  funext a
  have hR:=reserved_adapted s law T r γ h K t σ ρ hh
  have hlabel:∀ i,i∈reserved (request s σ) r K (qualifies s law T r γ h σ) t→
      Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) i=
        Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i:=by
    intro i hi
    exact label_adapted s law T hr γ h K t i (reserved_before _ _ _ _ _ _ hi) σ ρ hh
  by_cases he:∃ i∈reserved (request s σ) r K (qualifies s law T r γ h σ) t,
      Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) i=a
  · obtain ⟨i,hi,ha⟩:=he
    have hi':i∈reserved (request s ρ) r K (qualifies s law T r γ h ρ) t:=hR ▸ hi
    have ha':Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i=a:=
      (hlabel i hi).symm.trans ha
    rw [←ha,TierKeys.anchor_record _ _ _ _ hi,ha,←ha',TierKeys.anchor_record _ _ _ _ hi']
    exact request_adapted s (reserved_before _ _ _ _ _ _ hi) σ ρ hh
  · have he':¬∃ i∈reserved (request s ρ) r K (qualifies s law T r γ h ρ) t,
        Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i=a:=by
      rintro ⟨i,hi,ha⟩
      have hi':i∈reserved (request s σ) r K (qualifies s law T r γ h σ) t:=hR.symm ▸ hi
      exact he ⟨i,hi',(hlabel i hi').trans ha⟩
    simp only [TierKeys.anchor,dite_eq_right he,dite_eq_right he']

lemma anchor_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0≤r) (a:Tape Y k H r) (t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ):
    LevelKeys.anchor s law hr σ a t=LevelKeys.anchor s law hr ρ a t:=by
  let : Nonempty Y := ⟨s 0⟩
  have he:LevelKeys.anchors s law hr σ a t=LevelKeys.anchors s law hr ρ a t:=by
    funext i
    cases i with
    | none=>exact heavy_anchor_adapted s law r a.1 t σ ρ hh
    | some i=>exact tier_anchor_adapted s law tierTemplate hr tierGamma (height i) (tierK (height i)) t σ ρ hh
  unfold LevelKeys.anchor
  rw [he]

end KServer.KeysAdapted

end

end OAI
