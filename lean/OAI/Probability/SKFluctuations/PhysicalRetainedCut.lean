import Mathlib
import OAI.Probability.SKFluctuations.PhysicalDyadicClock

namespace OAI

/-! Physical Retained Cut. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem sampled_split_mass {ι : Type} [Fintype ι] (q : ℝ → ι → ℝ≥0) (as : List PositiveMass)
    (a u : ℝ) :
    physicalCutMass a (sampleClockSteps q a as)
      (splitClockSteps u (sampleClockSteps q a as)).1.length=partitionSample id a as u := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    rw [sampleClockSteps,splitClockSteps,partitionSample_cons]
    by_cases hbu : b.val ≤ u
    · rw [ite_eq_left hbu,ite_eq_right (not_lt.mpr hbu)]
      exact ih b.val
    · rw [ite_eq_right hbu,ite_eq_left (lt_of_not_ge hbu)]
      rfl

 theorem sampled_retained_mass {ι : Type} [Fintype ι] (q : ℝ → ι → ℝ≥0) (as : List PositiveMass)
    (ha : MassOrdered 0 as) (u : PositiveMass) (hu : u ∈ as) :
    physicalCutMass 0 (sampleClockSteps q 0 as)
      (splitClockSteps u.val (sampleClockSteps q 0 as)).1.length=u.val := by
  rw [sampled_split_mass,partitionSample_at_node id as ha hu]
  rfl

 theorem splitClockSteps_length_le {ι : Type} [Fintype ι] (steps : List (GaussianStep ι)) (u : ℝ) :
    (splitClockSteps u steps).1.length ≤ steps.length := by
  have h := congrArg List.length (splitClockSteps_append u steps)
  rw [List.length_append] at h
  omega

 def physicalRetainedIndex {ι : Type} [Fintype ι] (steps : List (GaussianStep ι)) (u : ℝ) :
    Fin (steps.length+2) :=
    ⟨(splitClockSteps u steps).1.length,by have h := splitClockSteps_length_le steps u; omega⟩

 theorem physicalRetainedIndex_mono {ι : Type} [Fintype ι] (steps : List (GaussianStep ι)) :
    Monotone (physicalRetainedIndex steps) :=
  fun _ _ huv => splitClockSteps_length_monotone steps huv

 theorem physicalRetainedIndex_mass {ι : Type} [Fintype ι] (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : PositiveMass) (hu : u ∈ as) :
    physicalCutMass 0 (sampleClockSteps q 0 as)
      (physicalRetainedIndex (sampleClockSteps q 0 as) u.val).val=u.val :=
  sampled_retained_mass q as ha u hu

 theorem physicalRetainedIndex_after {ι : Type} [Fintype ι] (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : PositiveMass) (hu : u ∈ as)
    (i : ℕ) (hi : physicalCutMass 0 (sampleClockSteps q 0 as) i < u.val) :
    i ≤ (physicalRetainedIndex (sampleClockSteps q 0 as) u.val).val := by
  by_contra hle
  have hx := physicalCutMass_monotone (sampleClockSteps q 0 as)
    (sampleClockSteps_ordered q as ha) (Nat.le_of_lt (lt_of_not_ge hle))
  rw [physicalRetainedIndex_mass q as ha u hu] at hx
  exact (not_le_of_gt hi) hx

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped NNReal

 theorem physicalQuantileGrid_retained {ι : Type} [Fintype ι]
    (q : ℝ → ι → ℝ≥0) (as : List PositiveMass) (has : MassOrdered 0 as)
    {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ≤ 1) (hc : 0 < c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (u : PositiveMass) (humem : u ∈ as) (huu₀ : u₀ ≤ u.val) (hu₁ : u.val ≤ 1) :
    physicalQuantileGrid hr hu hc hk hkc hm hM α (sampleClockSteps q 0 as)
      (sampleClockSteps_ordered q as has) (physicalRetainedIndex (sampleClockSteps q 0 as) u.val)=
        (constrainedQuantile hr hc hk hkc hm hM α ⟨u.val,huu₀,hu₁⟩).val := by
  unfold physicalQuantileGrid
  congr 2
  apply Subtype.ext
  simp only [physicalRetainedIndex_mass q as has u humem,max_eq_right huu₀]

 theorem physical_retained_interval_after (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (p q : ℕ) (i : ℕ) (hip : i ≤ p) :
    ∀ j ∈ physicalIntervalCells steps p q, i ≤ j.val := by
  intro j hj
  have hpj := (Finset.mem_filter.mp hj).2.1
  omega

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped NNReal

 theorem retainedConstrainedWindow (n : ℕ) (q₀ : ℝ → FeatureIndex n → ℝ≥0)
    (as : List PositiveMass) (has : MassOrdered 0 as)
    {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ≤ 1) (hu₀ : 0 ≤ u₀) (hc : 0 < c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ M u)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (p q : PositiveMass) (hpm : p ∈ as) (hqm : q ∈ as)
    (hp₀ : u₀ ≤ p.val) (hq₁ : q.val ≤ 1) (hpq : p.val < q.val)
    (xs η D₀ cl cu R F ε : ℝ) (J : ℕ)
    (hcl : 0 < cl) (hcu : 0 ≤ cu) (hD : 0 < D₀) (hR : 0 < R)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/R ≤ F) (hJ : 1 ≤ J)
    (hε : 0 ≤ ε) :
    let hM₁ := hM 1 (by norm_num)
    let a := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨p.val,hp₀,hpq.le.trans hq₁⟩).val
    let b := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨q.val,hp₀.trans hpq.le,hq₁⟩).val
    let steps := sampleClockSteps q₀ 0 as
    let hs := sampleClockSteps_ordered q₀ as has
    let r := physicalQuantileGrid hr hu hc hk hkc hm hM₁ α steps hs
    (∀ j : Fin (steps.length+1), r j.succ-r j.castSucc ≤ ε) →
    xs ≤ a → 0 < η → η ≤ a → ε ≤ a/2 → r₀ < a/2 →
    (2:ℝ)^J*b ≤ 1 → R ≤ (2:ℝ)^J*a →
    (∀ t ∈ Icc (a/2) ((2:ℝ)^J*b), cl*t ≤ α.val.val t ∧ α.val.val t ≤ cu*t) →
    ∃ w : PhysicalBandWindow n steps xs,
      w.radius=r ∧ w.selected=physicalIntervalCells steps
        (physicalRetainedIndex steps p.val).val (physicalRetainedIndex steps q.val).val ∧
      w.a=a ∧ w.b=b ∧ w.mass=q.val-p.val ∧ w.A=M q.val ∧
      w.η=η ∧ w.D₀=D₀ ∧ w.c₀=cl/2 ∧ w.C=cu ∧ w.R=R ∧ w.F=F ∧ w.depth=J := by
  dsimp only
  intro hmesh hxs hη hηa hεa hr₀ hT hRJ hreg
  let hM₁ := hM 1 (by norm_num)
  let steps := sampleClockSteps q₀ 0 as
  let hs := sampleClockSteps_ordered q₀ as has
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM₁ α steps hs
  let pi := physicalRetainedIndex steps p.val
  let qi := physicalRetainedIndex steps q.val
  have hpiqi : pi ≤ qi := physicalRetainedIndex_mono steps hpq.le
  have hpcoord : physicalCutMass 0 steps pi.val=p.val := physicalRetainedIndex_mass q₀ as has p hpm
  have hqcoord : physicalCutMass 0 steps qi.val=q.val := physicalRetainedIndex_mass q₀ as has q hqm
  have hpa := physicalQuantileGrid_retained q₀ as has hr hu hc hk hkc hm hM₁ α p hpm hp₀ (hpq.le.trans hq₁)
  have hqa := physicalQuantileGrid_retained q₀ as has hr hu hc hk hkc hm hM₁ α q hqm (hp₀.trans hpq.le) hq₁
  have hupp : u₀ ≤ physicalCutMass 0 steps pi.val := by rw [hpcoord]; exact hp₀
  have hmass : physicalCutMass 0 steps pi.val < physicalCutMass 0 steps qi.val := by rw [hpcoord,hqcoord]; exact hpq
  let w := constrainedPhysicalWindow n steps hs hr hu hu₀ hc hk hkc hm hM α
    xs η D₀ cl cu R F ε J pi qi hpiqi hupp hmass hcl hcu hD hR hFmass hFradius hJ hε
    hmesh (by simpa only [steps,hs,pi,hpa] using hxs) hη (by simpa only [steps,hs,pi,hpa] using hηa)
    (by simpa only [steps,hs,pi,hpa] using hεa) (by simpa only [steps,hs,pi,hpa] using hr₀)
    (by simpa only [steps,hs,qi,hqa] using hT) (by simpa only [steps,hs,pi,hpa] using hRJ)
    (by simpa only [steps,hs,pi,qi,hpa,hqa] using hreg)
  refine ⟨w,rfl,rfl,hpa,hqa,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change physicalWindowMass steps 0 (physicalIntervalCells steps pi.val qi.val)=q.val-p.val
    rw [physicalIntervalMass steps 0 hpiqi (by have hh := qi.isLt; omega),hpcoord,hqcoord]
  · change M (physicalCutMass 0 steps qi.val)=M q.val
    rw [hqcoord]

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem sampledFieldDuration_radius (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (α : ℝ → ℝ) (r : Fin ((sampleClockSteps (completedPathClock n b h) 0 as).length+2) → ℝ)
    (s : ℝ)
    (hcoord : physicalCutMass 0 (sampleClockSteps (completedPathClock n b h) 0 as) (radiusGridCut r s)=
      α (radiusGridPoint r s)) :
    let steps := sampleClockSteps (completedPathClock n b h) 0 as
    physicalFieldDuration (fun st => st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (radiusGridCut r s))=
      (h (α (radiusGridPoint r s)):ℝ)-(h 0:ℝ) := by
  dsimp only
  rw [sampledFieldDuration_index n hn b h hb hh as ha (radiusGridCut r s)
    (by simpa only [sampleClockSteps_length] using radiusGridCut_le r s),hcoord]

 theorem sampledFieldClock_radius_difference (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (α : ℝ → ℝ) (r : Fin ((sampleClockSteps (completedPathClock n b h) 0 as).length+2) → ℝ)
    (s t : ℝ)
    (hs : physicalCutMass 0 (sampleClockSteps (completedPathClock n b h) 0 as) (radiusGridCut r s)=
      α (radiusGridPoint r s))
    (ht : physicalCutMass 0 (sampleClockSteps (completedPathClock n b h) 0 as) (radiusGridCut r t)=
      α (radiusGridPoint r t)) :
    let steps := sampleClockSteps (completedPathClock n b h) 0 as
    let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
    physicalFieldDuration d (steps.take (radiusGridCut r t))-
      physicalFieldDuration d (steps.take (radiusGridCut r s))=
      (h (α (radiusGridPoint r t)):ℝ)-(h (α (radiusGridPoint r s)):ℝ) := by
  dsimp only
  rw [sampledFieldDuration_radius n hn b h hb hh as ha α r t ht,
    sampledFieldDuration_radius n hn b h hb hh as ha α r s hs]
  ring

end SKFluctuations

 

 

namespace SKFluctuations
open Set

 theorem radiusSampledStrength_growth {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r)
    {H e : ℝ → ℝ} {a T κ δ s t : ℝ} (hκ : 0 ≤ κ)
    (he : ∀ v ∈ Icc a T, 0 ≤ e v) (hem : AntitoneOn e (Icc a T))
    (hH : ∀ x ∈ Icc a T, ∀ y ∈ Icc a T, x ≤ y → κ*e y*(y-x) ≤ H y-H x)
    (hδ : 0 ≤ δ) (hlo : a ≤ s-δ) (hhi : t ≤ T) (hst : s ≤ t)
    (h₀ : r 0<s) (h₁ : t ≤ r (Fin.last (N+1)))
    (hmesh : ∀ j : Fin (N+1), r j.succ-r j.castSucc ≤ δ) :
    κ*e t*(t-s-δ) ≤ H (radiusGridPoint r t)-H (radiusGridPoint r s) := by
  have ht : t ∈ Icc a T := ⟨by linarith,hhi⟩
  apply radiusSampledClock_growth_local r hr (mul_nonneg hκ (he t ht)) hst h₀ h₁ hmesh
  intro x hx y hy hxy
  have hx' : x ∈ Icc a T := ⟨hlo.trans hx.1,hx.2.trans hhi⟩
  have hy' : y ∈ Icc a T := ⟨hlo.trans hy.1,hy.2.trans hhi⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hem hy' ht hy.2) hκ) (sub_nonneg.mpr hxy)).trans
      (hH x hx' y hy' hxy)

 theorem radiusPrecedingClocks {N : ℕ} (r : Fin (N+2) → ℝ) (hr : Monotone r)
    {H e : ℝ → ℝ} {a b T κ δ η K : ℝ}
    (ha : 0<a) (hab : a ≤ b) (hK : 1 ≤ K) (hb : b ≤ K*a) (hT : 2*b ≤ T)
    (hκ : 0 ≤ κ) (hη : 0<η) (hηa : η ≤ a) (hδ : 0 ≤ δ) (hδη : δ ≤ η/8)
    (he : ∀ v ∈ Icc (a/2) T, 0 ≤ e v) (hem : AntitoneOn e (Icc (a/2) T))
    (her : MonotoneOn (fun v => v*e v) (Icc (a/2) T))
    (hH : ∀ x ∈ Icc (a/2) T, ∀ y ∈ Icc (a/2) T, x ≤ y → κ*e y*(y-x) ≤ H y-H x)
    (h₀ : r 0<a/2) (h₁ : T ≤ r (Fin.last (N+1)))
    (hmesh : ∀ j : Fin (N+1), r j.succ-r j.castSucc ≤ δ) :
    (∀ s ∈ Ioc a b, κ*e a*η/(8*(K+1)) ≤ 
      H (radiusGridPoint r (s+η))-H (radiusGridPoint r s)) ∧
    (∀ s ∈ Icc (2*a) T, κ*e a*η/(8*(K+1)) ≤ 
      H (radiusGridPoint r s)-H (radiusGridPoint r (3*s/4))) := by
  have hKp : 0<K+1 := by linarith
  have haI : a ∈ Icc (a/2) T := by constructor <;> linarith
  have hea := he a haI
  have hδa : δ ≤ a/8 := by linarith
  constructor
  · intro s hs
    have ht : s+η ∈ Icc (a/2) T := by constructor <;> linarith [hs.1,hs.2]
    have het := he (s+η) ht
    have hrp := her haI ht (by linarith [hs.1])
    have hsize : s+η ≤ (K+1)*a := by nlinarith [hs.2]
    have hprod := mul_le_mul_of_nonneg_right hsize het
    have hratio : e a/(K+1) ≤ e (s+η) := by
      apply (div_le_iff₀ hKp).mpr
      apply (mul_le_mul_iff_right₀ ha).mp
      nlinarith
    have hh := radiusSampledStrength_growth r hr hκ he hem hH hδ
      (show a/2 ≤ s-δ by linarith [hs.1]) ht.2 (show s ≤ s+η by linarith)
      (show r 0<s by linarith [hs.1]) (ht.2.trans h₁) hmesh
    calc κ*e a*η/(8*(K+1))=(κ*η/8)*(e a/(K+1)) := by rw [mul_comm 8 (K+1), div_mul_eq_div_div]; ring
         _ ≤ (κ*η/8)*e (s+η) := mul_le_mul_of_nonneg_left hratio (by positivity)
         _ ≤ κ*e (s+η)*((s+η)-s-δ) := by
           have hm := mul_le_mul_of_nonneg_left (show η/8 ≤ (s+η)-s-δ by linarith) (mul_nonneg hκ het)
           nlinarith
         _ ≤ _ := hh
  · intro s hs
    have hsI : s ∈ Icc (a/2) T := ⟨by linarith [hs.1],hs.2⟩
    have hes := he s hsI
    have hrp := her haI hsI (by linarith [hs.1])
    have hη' : η/(K+1) ≤ a := by
      apply (div_le_iff₀ hKp).mpr
      nlinarith
    have hh := radiusSampledStrength_growth r hr hκ he hem hH hδ
      (show a/2 ≤ 3*s/4-δ by linarith [hs.1]) hs.2 (show 3*s/4 ≤ s by linarith [hs.1])
      (show r 0<3*s/4 by linarith [hs.1]) (hs.2.trans h₁) hmesh
    calc κ*e a*η/(8*(K+1))=(κ*e a/8)*(η/(K+1)) := by rw [mul_comm 8 (K+1), div_mul_eq_div_div]; ring
         _ ≤ (κ*e a/8)*a := mul_le_mul_of_nonneg_left hη' (by positivity)
         _ ≤ (κ/8)*(s*e s) := by nlinarith [mul_le_mul_of_nonneg_left hrp (show 0 ≤ κ/8 by positivity)]
         _ ≤ κ*e s*(s-3*s/4-δ) := by
           have hm := mul_le_mul_of_nonneg_left (show s/8 ≤ s-3*s/4-δ by linarith [hs.1]) (mul_nonneg hκ hes)
           nlinarith
         _ ≤ _ := hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped NNReal

 theorem physicalConstrainedClockLengths (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (has : MassOrdered 0 as)
    {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ≤ 1) (hu₀ : 0 ≤ u₀) (hc : 0 < c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    {e : ℝ → ℝ} {a ab T κ ε η K : ℝ}
    (ha : 0 < a) (hab : a ≤ ab) (hK : 1 ≤ K) (hbK : ab ≤ K*a)
    (hT : 2*ab ≤ T) (hT₁ : T ≤ 1) (hr₀ : r₀ < a/2)
    (hκ : 0 ≤ κ) (hη : 0 < η) (hηa : η ≤ a) (hε : 0 ≤ ε) (hεη : ε ≤ η/8)
    (he : ∀ v ∈ Icc (a/2) T, 0 ≤ e v) (hem : AntitoneOn e (Icc (a/2) T))
    (her : MonotoneOn (fun v => v*e v) (Icc (a/2) T))
    (hH : ∀ x ∈ Icc (a/2) T, ∀ y ∈ Icc (a/2) T, x ≤ y →
      κ*e y*(y-x) ≤ (h (α.val.val y):ℝ)-(h (α.val.val x):ℝ))
    (hmesh : let steps := sampleClockSteps (completedPathClock n b h) 0 as
      let hs := sampleClockSteps_ordered (completedPathClock n b h) as has
      ∀ j : Fin (steps.length+1),
        physicalQuantileGrid hr hu hc hk hkc hm hM α steps hs j.succ-
          physicalQuantileGrid hr hu hc hk hkc hm hM α steps hs j.castSucc ≤ ε) :
    let steps := sampleClockSteps (completedPathClock n b h) 0 as
    let hs := sampleClockSteps_ordered (completedPathClock n b h) as has
    let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps hs
    let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
    (∀ s ∈ Ioc a ab, κ*e a*η/(8*(K+1)) ≤
      physicalFieldDuration d (steps.take (radiusGridCut r (s+η)))-
        physicalFieldDuration d (steps.take (radiusGridCut r s))) ∧
    (∀ s ∈ Icc (2*a) T, κ*e a*η/(8*(K+1)) ≤
      physicalFieldDuration d (steps.take (radiusGridCut r s))-
        physicalFieldDuration d (steps.take (radiusGridCut r (3*s/4)))) := by
  dsimp only at hmesh ⊢
  let steps := sampleClockSteps (completedPathClock n b h) 0 as
  let hs := sampleClockSteps_ordered (completedPathClock n b h) as has
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps hs
  have hrm := physicalQuantileGrid_mono hr hu hc hk hkc hm hM α steps hs
  have hfirst : r 0 < a/2 := by
    dsimp only [r]; rw [physicalQuantileGrid_first hr hu hc hk hkc hm hM α steps hs hu₀]; exact hr₀
  have hlast : T ≤ r (Fin.last (steps.length+1)) := by
    dsimp only [r]; rw [physicalQuantileGrid_last]; exact hT₁
  have hg := radiusPrecedingClocks r hrm ha hab hK hbK hT hκ hη hηa hε hεη he hem her hH hfirst hlast hmesh
  have hcoord (s : ℝ) (hslo : a ≤ s) (hshi : s ≤ T) :
      physicalCutMass 0 steps (radiusGridCut r s)=α.val.val (radiusGridPoint r s) := by
    exact physicalQuantileSample_coord hr hu hc hk hkc hm hM α steps hs
      (show r₀ < s-ε by linarith) (hshi.trans hT₁) hmesh hε hu₀
  constructor
  · intro s hsi
    rw [sampledFieldClock_radius_difference n hn b h hb hh as has α.val.val r s (s+η)
      (hcoord s hsi.1.le (by linarith [hsi.2]))
      (hcoord (s+η) (by linarith [hsi.1]) (by linarith [hsi.2]))]
    exact hg.1 s hsi
  · intro s hsi
    rw [sampledFieldClock_radius_difference n hn b h hb hh as has α.val.val r (3*s/4) s
      (hcoord (3*s/4) (by linarith [hsi.1]) (by linarith [hsi.1,hsi.2]))
      (hcoord s (by linarith [hsi.1]) hsi.2)]
    exact hg.2 s hsi

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
namespace PhysicalBandWindow
variable {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}

 theorem nearCoefficient_bound (ha : OrderedSteps 0 steps) (hxs : 0<xs)
    (k : ℕ) (w : PhysicalBandWindow n steps xs) (hb : w.b≤2*w.a) :
    w.nearCoefficient k≤
      (12*w.C*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹)*(1+3*w.C)^2)*
        w.A*w.η*w.a^3 := by
  have ha0 : 0<w.a := hxs.trans_le w.xa
  have hb0 : 0<w.b := ha0.trans_le w.ab
  have h2 : (2:ℝ)≤(2:ℝ)^w.depth := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) w.depth_pos
  have hupper : w.b+w.η ≤ (2:ℝ)^w.depth*w.b := by
    calc w.b+w.η≤2*w.b := by linarith [w.η_le,w.ab]
         _≤_ := mul_le_mul_of_nonneg_right h2 hb0.le
  have hc := (w.mass_comparable (w.b+w.η) ⟨by linarith [w.ab,w.η_pos],hupper⟩).2
  have hmid : xs+physicalCutMass 0 steps (radiusGridCut w.radius (w.b+w.η))≤
      (1+3*w.C)*w.a := by
    have ht := mul_le_mul_of_nonneg_left (show w.b+w.η≤3*w.a by linarith [w.η_le]) w.C_nonneg
    nlinarith [w.xa]
  have hz : 0≤xs+physicalCutMass 0 steps (radiusGridCut w.radius (w.b+w.η)) :=
    add_nonneg hxs.le (physicalCutMass_mem steps ha _).1
  have hC := w.C_nonneg
  have hA := w.A_nonneg
  have hη := w.η_pos
  have hN : 0≤nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹) :=
    Real.rpow_nonneg (nearPairMomentConstant_nonneg _) _
  have hcprod : w.C*(w.b+w.η)≤3*w.C*w.a := by
    nlinarith [mul_le_mul_of_nonneg_left
      (show w.b+w.η≤3*w.a by linarith [w.η_le]) hC]
  calc w.nearCoefficient k=
      (w.C*(w.b+w.η))*(4*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹))*
        (w.A*w.η)*(xs+physicalCutMass 0 steps (radiusGridCut w.radius (w.b+w.η)))^2 := by
          unfold nearCoefficient; ring
       _≤ (3*w.C*w.a)*(4*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹))*
          (w.A*w.η)*((1+3*w.C)*w.a)^2 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcprod (by positivity)) (by positivity))
            (pow_le_pow_left₀ hz hmid 2) (sq_nonneg _) (by positivity)
       _=_ := by ring

 theorem farCoefficient_bound (k : ℕ) (w : PhysicalBandWindow n steps xs)
    {v e ρ L : ℝ} (hn : 0<(n:ℝ)) (hv : 0<v) (he : 0<e) (hρ : 0<ρ) (hL : 0<L)
    (hm : w.mass≤2*w.C*v) (hD : ρ*v*e/L≤w.D₀) :
    w.mass*w.farCoefficient k≤
      (8*w.C*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2))*
        L/((n:ℝ)*e*v^4*ρ)*v^4 := by
  have hC := w.C_nonneg
  have hDw := w.D₀_pos
  let P := 4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2)
  have hP : 0≤P := by dsimp [P]; positivity
  have hnum : 0≤2*w.C*v*P := by positivity
  have hden : 0<(n:ℝ)*(ρ*v*e/L) := by positivity
  have hden' : (n:ℝ)*(ρ*v*e/L)≤(n:ℝ)*w.D₀ := mul_le_mul_of_nonneg_left hD hn.le
  calc w.mass*w.farCoefficient k = w.mass*P/((n:ℝ)*w.D₀) := by unfold farCoefficient; dsimp [P]; ring
       _ ≤ (2*w.C*v)*P/((n:ℝ)*w.D₀) := by gcongr
       _ ≤ (2*w.C*v)*P/((n:ℝ)*(ρ*v*e/L)) :=
          div_le_div_of_nonneg_left hnum hden hden'
       _ = _ := by dsimp [P]; field_simp; ring

end PhysicalBandWindow
end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem geometric_mean_balance {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    let ρ := 1/Real.sqrt (A*B)
    A*ρ=Real.sqrt (A/B) ∧ (B*ρ)⁻¹=Real.sqrt (A/B) := by
  dsimp only
  constructor
  · rw [mul_one_div,Real.sqrt_mul hA.le,←div_div,Real.div_sqrt,←Real.sqrt_div hA.le]
  · have hs : Real.sqrt (A*B)≠0 := (Real.sqrt_pos_of_pos (mul_pos hA hB)).ne'
    have he : (B*(1/Real.sqrt (A*B)))⁻¹=Real.sqrt (A*B)/B := by field_simp
    rw [he,Real.sqrt_mul hA.le,Real.sqrt_div hA.le]
    have hb := Real.sq_sqrt hB.le
    have hsB : Real.sqrt B≠0 := (Real.sqrt_pos_of_pos hB).ne'
    field_simp
    nlinarith

namespace PhysicalBandWindow
variable {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}

 def nearScaleConstant (k : ℕ) (w : PhysicalBandWindow n steps xs) : ℝ :=
    12*w.C*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹)*(1+3*w.C)^2
 def farScaleConstant (k : ℕ) (w : PhysicalBandWindow n steps xs) : ℝ :=
    8*w.C*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2)
 def scaleFactor (k : ℕ) (w : PhysicalBandWindow n steps xs) (L : ℝ) : ℝ :=
    (w.depth+3:ℕ)^3*(w.nearScaleConstant k+w.farScaleConstant k*L)

 theorem coefficient_balanced (ha : OrderedSteps 0 steps) (hxs : 0<xs)
    (k : ℕ) (w : PhysicalBandWindow n steps xs) (hb : w.b ≤ 2*w.a)
    (hm : w.mass ≤ 2*w.C*w.a) {e L : ℝ} (hn : 0<(n:ℝ)) (he : 0<e) (hL : 0<L)
    (hA : 0<w.A)
    (hη : w.η=(1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a)
    (hD : (1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a*e/L ≤ w.D₀) :
    w.coefficient k ≤ w.scaleFactor k L*Real.sqrt (w.A/((n:ℝ)*e*w.a^4))*w.a^4 := by
  have ha0 : 0<w.a := hxs.trans_le w.xa
  let B := (n:ℝ)*e*w.a^4
  let ρ := 1/Real.sqrt (w.A*B)
  have hB : 0<B := by dsimp [B]; positivity
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hbal := geometric_mean_balance hA hB
  change w.A*ρ=Real.sqrt (w.A/B) ∧ (B*ρ)⁻¹=Real.sqrt (w.A/B) at hbal
  have hnear := nearCoefficient_bound ha hxs k w hb
  rw [hη] at hnear
  change w.nearCoefficient k ≤ w.nearScaleConstant k*w.A*(ρ*w.a)*w.a^3 at hnear
  have hnear' : w.nearCoefficient k ≤ w.nearScaleConstant k*Real.sqrt (w.A/B)*w.a^4 := by
    calc _ ≤ _ := hnear
         _ = w.nearScaleConstant k*(w.A*ρ)*w.a^4 := by ring
         _ = _ := by rw [hbal.1]
  have hfar := farCoefficient_bound k w hn ha0 he hρ hL hm hD
  change w.mass*w.farCoefficient k ≤ w.farScaleConstant k*L/(B*ρ)*w.a^4 at hfar
  rw [div_eq_mul_inv,hbal.2] at hfar
  calc w.coefficient k=(w.depth+3:ℕ)^3*(w.nearCoefficient k+w.mass*w.farCoefficient k) := rfl
       _ ≤ (w.depth+3:ℕ)^3*(w.nearScaleConstant k*Real.sqrt (w.A/B)*w.a^4+
          w.farScaleConstant k*L*Real.sqrt (w.A/B)*w.a^4) :=
            mul_le_mul_of_nonneg_left (add_le_add hnear' hfar) (by positivity)
       _ = _ := by unfold scaleFactor; dsimp only [B]; ring

 theorem loss_bound (hxs : 0<xs) (k : ℕ) (w : PhysicalBandWindow n steps xs)
    {c ε : ℝ} (hc : 0<c) (hε : 0 ≤ ε) (hm : c*w.a ≤ w.mass)
    (hcoeff : w.coefficient k ≤ ε*w.a^4) :
    w.loss k ≤ (2/c)*Real.sqrt ((1+(2*(k+1:ℕ):ℝ)^2/3)*ε)*w.a := by
  have ha0 : 0<w.a := hxs.trans_le w.xa
  have hma : 0<c*w.a := mul_pos hc ha0
  have hmi : w.mass⁻¹ ≤ (c*w.a)⁻¹ := inv_anti₀ hma hm
  have hK : 0 ≤ (1+(2*(k+1:ℕ):ℝ)^2/3) := by positivity
  have hC := w.coefficient_nonneg hxs k
  have heq : (1+(2*(k+1:ℕ):ℝ)^2/3)*(c*w.a)⁻¹^2*(ε*w.a^4)=
      ((1+(2*(k+1:ℕ):ℝ)^2/3)*ε)*(w.a/c)^2 := by field_simp
  unfold loss
  calc 2*Real.sqrt ((1+(2*(k+1:ℕ):ℝ)^2/3)*w.mass⁻¹^2*w.coefficient k)
      ≤ 2*Real.sqrt ((1+(2*(k+1:ℕ):ℝ)^2/3)*(c*w.a)⁻¹^2*(ε*w.a^4)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.sqrt_le_sqrt
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr w.mass_pos.le) hmi 2) hK)
          hcoeff hC (by positivity)
      _ = _ := by rw [heq,Real.sqrt_mul (mul_nonneg hK hε),Real.sqrt_sq (div_nonneg ha0.le hc.le)]; ring

end PhysicalBandWindow
end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
namespace PhysicalBandWindow
variable {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}

 theorem nearCoefficient_general (ha : OrderedSteps 0 steps) (hxs : 0<xs)
    (k : ℕ) (w : PhysicalBandWindow n steps xs) {K : ℝ} (hK : 1≤K) (hb : w.b≤K*w.a) :
    w.nearCoefficient k≤
      (4*(K+1)*w.C*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹)*(1+(K+1)*w.C)^2)*
        w.A*w.η*w.a^3 := by
  have ha0 : 0<w.a := hxs.trans_le w.xa
  have hb0 : 0<w.b := ha0.trans_le w.ab
  have h2 : (2:ℝ)≤(2:ℝ)^w.depth := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) w.depth_pos
  have hupper : w.b+w.η ≤ (2:ℝ)^w.depth*w.b := by
    calc w.b+w.η≤2*w.b := by linarith [w.η_le,w.ab]
         _≤_ := mul_le_mul_of_nonneg_right h2 hb0.le
  have hc := (w.mass_comparable (w.b+w.η) ⟨by linarith [w.ab,w.η_pos],hupper⟩).2
  have hsize : w.b+w.η≤(K+1)*w.a := by nlinarith [w.η_le]
  have hmid : xs+physicalCutMass 0 steps (radiusGridCut w.radius (w.b+w.η))≤
      (1+(K+1)*w.C)*w.a := by
    have ht := mul_le_mul_of_nonneg_left hsize w.C_nonneg
    nlinarith [w.xa]
  have hz : 0≤xs+physicalCutMass 0 steps (radiusGridCut w.radius (w.b+w.η)) :=
    add_nonneg hxs.le (physicalCutMass_mem steps ha _).1
  have hC := w.C_nonneg
  have hA := w.A_nonneg
  have hη := w.η_pos
  have hN : 0≤nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹) :=
    Real.rpow_nonneg (nearPairMomentConstant_nonneg _) _
  have hK0 : 0≤K+1 := by linarith
  have hcprod : w.C*(w.b+w.η)≤(K+1)*w.C*w.a := by
    nlinarith [mul_le_mul_of_nonneg_left hsize hC]
  calc w.nearCoefficient k=
      (w.C*(w.b+w.η))*(4*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹))*
        (w.A*w.η)*(xs+physicalCutMass 0 steps (radiusGridCut w.radius (w.b+w.η)))^2 := by
          unfold nearCoefficient; ring
       _≤ ((K+1)*w.C*w.a)*(4*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹))*
          (w.A*w.η)*((1+(K+1)*w.C)*w.a)^2 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcprod (by positivity)) (by positivity))
            (pow_le_pow_left₀ hz hmid 2) (sq_nonneg _) (by positivity)
       _=_ := by ring

 theorem farCoefficient_general (k : ℕ) (w : PhysicalBandWindow n steps xs)
    {v e ρ L K : ℝ} (hn : 0<(n:ℝ)) (hv : 0<v) (he : 0<e) (hρ : 0<ρ) (hL : 0<L)
    (hK : 0≤K) (hm : w.mass≤K*w.C*v) (hD : ρ*v*e/L≤w.D₀) :
    w.mass*w.farCoefficient k≤
      (4*K*w.C*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2))*
        L/((n:ℝ)*e*v^4*ρ)*v^4 := by
  have hC := w.C_nonneg
  have hDw := w.D₀_pos
  let P := 4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2)
  have hP : 0≤P := by dsimp [P]; positivity
  have hnum : 0≤K*w.C*v*P := by positivity
  have hden : 0<(n:ℝ)*(ρ*v*e/L) := by positivity
  have hden' : (n:ℝ)*(ρ*v*e/L)≤(n:ℝ)*w.D₀ := mul_le_mul_of_nonneg_left hD hn.le
  calc w.mass*w.farCoefficient k = w.mass*P/((n:ℝ)*w.D₀) := by unfold farCoefficient; dsimp [P]; ring
       _ ≤ (K*w.C*v)*P/((n:ℝ)*w.D₀) := by gcongr
       _ ≤ (K*w.C*v)*P/((n:ℝ)*(ρ*v*e/L)) := div_le_div_of_nonneg_left hnum hden hden'
       _ = _ := by dsimp [P]; field_simp

end PhysicalBandWindow
end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
namespace PhysicalBandWindow
variable {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}

 def generalNearScaleConstant (k : ℕ) (w : PhysicalBandWindow n steps xs) (K : ℝ) : ℝ :=
    4*(K+1)*w.C*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹)*(1+(K+1)*w.C)^2
 def generalFarScaleConstant (k : ℕ) (w : PhysicalBandWindow n steps xs) (K : ℝ) : ℝ :=
    4*K*w.C*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2)
 def generalScaleFactor (k : ℕ) (w : PhysicalBandWindow n steps xs) (K L : ℝ) : ℝ :=
    (w.depth+3:ℕ)^3*(w.generalNearScaleConstant k K+w.generalFarScaleConstant k K*L)

 theorem coefficient_balanced_general (ha : OrderedSteps 0 steps) (hxs : 0<xs)
    (k : ℕ) (w : PhysicalBandWindow n steps xs) {K : ℝ} (hK : 1≤K) (hb : w.b ≤ K*w.a)
    (hm : w.mass ≤ K*w.C*w.a) {e L : ℝ} (hn : 0<(n:ℝ)) (he : 0<e) (hL : 0<L)
    (hA : 0<w.A)
    (hη : w.η=(1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a)
    (hD : (1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a*e/L ≤ w.D₀) :
    w.coefficient k ≤ w.generalScaleFactor k K L*Real.sqrt (w.A/((n:ℝ)*e*w.a^4))*w.a^4 := by
  have ha0 : 0<w.a := hxs.trans_le w.xa
  let B := (n:ℝ)*e*w.a^4
  let ρ := 1/Real.sqrt (w.A*B)
  have hB : 0<B := by dsimp [B]; positivity
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hbal := geometric_mean_balance hA hB
  change w.A*ρ=Real.sqrt (w.A/B) ∧ (B*ρ)⁻¹=Real.sqrt (w.A/B) at hbal
  have hnear := nearCoefficient_general ha hxs k w hK hb
  rw [hη] at hnear
  change w.nearCoefficient k ≤ w.generalNearScaleConstant k K*w.A*(ρ*w.a)*w.a^3 at hnear
  have hnear' : w.nearCoefficient k ≤ w.generalNearScaleConstant k K*Real.sqrt (w.A/B)*w.a^4 := by
    calc _ ≤ _ := hnear
         _ = w.generalNearScaleConstant k K*(w.A*ρ)*w.a^4 := by ring
         _ = _ := by rw [hbal.1]
  have hfar := farCoefficient_general k w hn ha0 he hρ hL (by linarith : 0≤K) hm hD
  change w.mass*w.farCoefficient k ≤ w.generalFarScaleConstant k K*L/(B*ρ)*w.a^4 at hfar
  rw [div_eq_mul_inv,hbal.2] at hfar
  calc w.coefficient k=(w.depth+3:ℕ)^3*(w.nearCoefficient k+w.mass*w.farCoefficient k) := rfl
       _ ≤ (w.depth+3:ℕ)^3*(w.generalNearScaleConstant k K*Real.sqrt (w.A/B)*w.a^4+
          w.generalFarScaleConstant k K*L*Real.sqrt (w.A/B)*w.a^4) :=
            mul_le_mul_of_nonneg_left (add_le_add hnear' hfar) (by positivity)
       _ = _ := by unfold generalScaleFactor; dsimp only [B]; ring

end PhysicalBandWindow
end SKFluctuations

end

end OAI
