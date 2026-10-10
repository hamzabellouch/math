import Mathlib
import OAI.Probability.SKFluctuations.CavityFrozenJet

namespace OAI

/-! Cavity Graph Parity. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal

 

def siteMonomial {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (σ : T.Assignment) : List T.Slot → ℝ
  | [] => 1
  | a::es => spinValue (T.atSlot σ a).2 * siteMonomial T σ es

 
def blockDegree {S : Type*} {as : List PositiveMass} (T : ClockTree S as)
    (U : ℕ) (s : T.Slot) : List T.Slot → ℕ
  | [] => 0
  | a::es => (if U ≤ T.splitIndex s a then 1 else 0)+blockDegree T U s es

theorem siteMonomial_gauge {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (U : ℕ) (hU : U ≤ as.length)
    (s : T.Slot) (σ : T.Assignment) (es : List T.Slot) :
    siteMonomial T (T.cutGaugeEquiv (rowSpinFlip n) U (T.gaugeAt U s) σ) es =
      (-1:ℝ)^(blockDegree T U s es)*siteMonomial T σ es := by
  induction es with
  | nil => simp [siteMonomial,blockDegree]
  | cons a es ih =>
    simp only [siteMonomial,blockDegree,ih,T.atSlot_gaugeAt (rowSpinFlip n) U hU s a σ]
    split_ifs with ha
    · simp only [rowSpinFlip_apply,spinValue_not,pow_add,pow_one]
      ring
    · simp only [Nat.zero_add]
      ring

 

theorem cutDisorderExpect_graph_odd (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (hU0 : 0 < U) (t : ℝ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (hU : U ≤ as.length) (s : T.Slot) (es : List T.Slot)
    (hes : Odd (blockDegree T U s es)) (P : T.cavityLeft.Assignment → ℝ)
    (x : FullCoordinate n → ℝ) (hs : ∀ i, x (.inl (.inr i)) = 0)
    (hr : ∀ i, x (.inr i) = 0) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => P (T.cavityAssignment σ).1*siteMonomial T σ es) x = 0 := by
  apply cutDisorderExpect_odd n q U hU0 t b h K T (T.gaugeAt U s) _ _ x hs hr
  intro σ
  have hrest := T.cavityAssignment_cutGauge_left Equiv.boolNot U (T.gaugeAt U s) σ
  change (T.cavityAssignment (T.cutGaugeEquiv (rowSpinFlip n) U (T.gaugeAt U s) σ)).1 = _ at hrest
  rw [hrest,siteMonomial_gauge T U hU s σ es,hes.neg_one_pow]
  ring

theorem blockDegree_append {S : Type*} {as : List PositiveMass} (T : ClockTree S as)
    (U : ℕ) (s : T.Slot) (es fs : List T.Slot) :
    blockDegree T U s (es++fs) = blockDegree T U s es+blockDegree T U s fs := by
  induction es with
  | nil => simp [blockDegree]
  | cons a es ih => simp only [List.cons_append,blockDegree,ih,Nat.add_assoc]

 

theorem blockDegree_pair_even {S : Type*} {as : List PositiveMass} (T : ClockTree S as)
    (U : ℕ) (s a b : T.Slot) (hab : (U ≤ T.splitIndex s a) ↔ (U ≤ T.splitIndex s b)) :
    Even (blockDegree T U s [a,b]) := by
  by_cases ha : U ≤ T.splitIndex s a
  · have hb := hab.mp ha
    simp [blockDegree,ha,hb]
  · have hb : ¬ U ≤ T.splitIndex s b := fun hb => ha (hab.mpr hb)
    simp [blockDegree,ha,hb]

end SKFluctuations.Cavity

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem cutCenteredJet_zero_low (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (s r : T.Slot) (hU : U ≤ as.length) (hsr : T.splitIndex s r < U)
    (P : T.cavityLeft.Assignment → ℝ) (x : ActiveCoordinate n → ℝ)
    (hx : ∀ i, x (.inr i) = 0) (t : ℝ) :
    cutCenteredJet n q U b h K T P (sitePair T s r) x 0 0 t = 0 := by
  simp only [cutCenteredJet,productJet3,Fin.val_zero,cutLowJet_zero n q U b h K T ho]
  rw [cutDisorderExpect_sitePair_zero n q U t b h K T s r hU hsr P (cavityEmbed x) hx
      (fun i => by simp [cavityEmbed])]
  have hz := cutDisorderExpect_sitePair_zero n q U 0 b h K T s r hU hsr (fun _ => 1) (cavityEmbed x) hx
      (fun i => by simp [cavityEmbed])
  simp only [one_mul] at hz
  rw [hz]
  simp

 

theorem cutSitePair_frozen_decomposition (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (P : T.cavityLeft.Assignment → ℝ)
    (x : ActiveCoordinate n → ℝ) (hq0 : ∀ j i, 0 ≤ q j i)
    (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (ho : MassOrdered 0 as) (s r : T.Slot) (hU : U ≤ as.length)
    (hsr : T.splitIndex s r < U) (hx : ∀ i, x (.inr i) = 0) :
    cutCenteredJet n q U b h K T P (sitePair T s r) x 0 1 1 =
      cutFrozenCenteredJet n q U b h K T P (sitePair T s r) x 1 0 0+
      cutFrozenCenteredJet n q U b h K T P (sitePair T s r) x 1 1 0+
      (1/2:ℝ)*cutFrozenCenteredJet n q U b h K T P (sitePair T s r) x 2 0 0+
      (∫ t in (0:ℝ)..1, (1-t)*cutFrozenCenteredJet n q U b h K T P (sitePair T s r) x 1 2 t)+
      (1/2:ℝ)*(∫ t in (0:ℝ)..1, cutFrozenCenteredJet n q U b h K T P (sitePair T s r) x 2 1 t)+
      (1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*∫ t in (0:ℝ)..1,
        cutCenteredMixedJet n q U b h K T P (sitePair T s r) x 3 l t := by
  rw [cutCenteredJet_frozen_decomposition n q U b h K T P (sitePair T s r) x
    hq0 hq hb hh hK hbm hhm hKm ho,
    cutCenteredJet_zero_low n q U b h K T ho s r hU hsr P x hx,zero_add]

end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 
def ClockExpr.iterSource (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (E : ClockExpr S as) (vs : List (ι → ℝ)) : ClockExpr S as :=
  vs.foldl (fun F v => F.source φ v) E

omit [Fintype ι] [Fintype S] [Nonempty S] in
 theorem ClockExpr.iterSource_append (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (E : ClockExpr S as) (vs : List (ι → ℝ)) (v : ι → ℝ) :
    E.iterSource φ (vs++[v]) = (E.iterSource φ vs).source φ v := by
  simp only [ClockExpr.iterSource,List.foldl_append,List.foldl_cons,List.foldl_nil]

 

 theorem ClockTree.eval_iterSource_testExpr {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ)
    (vs : List (ι → ℝ)) (x : ι → ℝ) :
    ((T.testExpr P).iterSource φ vs).eval w φ q x =
      ReplicaTree.sourceJet w φ a vs (T.realize (fun j i => Real.toNNReal (q j i)))
        (fun σ => P ((T.assignmentEquiv (fun j i => Real.toNNReal (q j i))).symm σ)) x := by
  induction vs using List.reverseRecOn generalizing x with
  | nil =>
    rw [show (T.testExpr P).iterSource φ [] = T.testExpr P from rfl,
      T.eval_testExpr hw φ ho, T.expect_realize]
    rfl
  | append_singleton vs v ih =>
    rw [ClockExpr.iterSource_append]
    have h₁ := ((T.testExpr P).iterSource φ vs).hasDerivAt_source hw φ ho q v x 0
    have h₂ := ReplicaTree.sourceJet_hasDerivAt hw φ vs
      (T.realize (fun j i => Real.toNNReal (q j i))) (clockSteps_ordered ho _)
      (fun σ => P ((T.assignmentEquiv (fun j i => Real.toNNReal (q j i))).symm σ)) v x 0
    have he : (fun s : ℝ => ((T.testExpr P).iterSource φ vs).eval w φ q (x+s • v)) =
        (fun s : ℝ => ReplicaTree.sourceJet w φ a vs
          (T.realize (fun j i => Real.toNNReal (q j i)))
          (fun σ => P ((T.assignmentEquiv (fun j i => Real.toNNReal (q j i))).symm σ)) (x+s • v)) := funext (fun s => ih _)
    rw [he] at h₁
    simpa only [zero_smul,add_zero] using h₁.unique h₂

 theorem ClockTree.eval_iterSource_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ)
    (vs : List (ι → ℝ)) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : ∀ σ, |P σ| ≤ C) (hφ : ∀ v ∈ vs, ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    |((T.testExpr P).iterSource φ vs).eval w φ q x| ≤
      (ReplicaTree.attachmentCount T.leaves vs.length:ℝ)*C*D^vs.length := by
  rw [T.eval_iterSource_testExpr hw φ ho]
  exact ReplicaTree.sourceJet_abs_le hw φ vs _ (clockSteps_ordered ho _)
    (by rw [ClockTree.realize_leaves]) hC hD (fun σ => hP _) hφ x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators
variable {ι S : Type*}

 

def splitIndex : {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) →
    T.Slot → T.Slot → ℕ
  | _, .leaf => fun _ _ => 0
  | _, .step _ T => fun s t => 1+T.splitIndex s t
  | _, .fork T U => fun s t => Sum.elim
      (fun s => Sum.elim (fun t => T.splitIndex s t) (fun _ => 0) t)
      (fun s => Sum.elim (fun _ => 0) (fun t => U.splitIndex s t) t) s

 theorem splitIndex_symm {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (s t : T.Slot) : T.splitIndex s t = T.splitIndex t s := by
  induction T with
  | leaf => rfl
  | step st T ih => exact congrArg (1+·) (ih s t)
  | fork T U ihT ihU => cases s <;> cases t <;> first | rfl | exact ihT _ _ | exact ihU _ _

 theorem splitIndex_le {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (s t : T.Slot) : T.splitIndex s t ≤ steps.length := by
  induction T with
  | leaf => exact le_rfl
  | step st T ih => simpa only [splitIndex,List.length_cons,Nat.add_comm 1] using Nat.succ_le_succ (ih s t)
  | fork T U ihT ihU => cases s <;> cases t <;> first | exact ihT _ _ | exact ihU _ _ | exact Nat.zero_le _

 theorem splitIndex_self {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (s : T.Slot) : T.splitIndex s s = steps.length := by
  induction T with
  | leaf => rfl
  | step st T ih => simp only [splitIndex,ih,List.length_cons,Nat.add_comm 1]
  | fork T U ihT ihU => cases s <;> first | exact ihT _ | exact ihU _

 theorem markedAttach_preserves_split {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (a : ℝ) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a) (s t : T.Slot) :
    p.tree.splitIndex (p.embed s) (p.embed t) = T.splitIndex s t := by
  induction T generalizing a with
  | leaf =>
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    rcases List.mem_singleton.mp hp with rfl
    rfl
  | step st T ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    obtain ⟨p,hmem,rfl⟩ := List.mem_map.mp hp
    exact congrArg (1+·) (ih st.1 p hmem s t)
  | fork T U ihT ihU =>
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨p,hmem,rfl⟩ := List.mem_map.mp hp
      cases s <;> cases t <;> first | rfl | exact ihT a p hmem _ _
    · obtain ⟨p,hmem,rfl⟩ := List.mem_map.mp hp
      cases s <;> cases t <;> first | rfl | exact ihU a p hmem _ _

 theorem markedAttach_variation {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) :
    ((T.markedAttach a).map fun p => |p.coeff|).sum = 2*(T.leaves:ℝ)-a := by
  have h := T.attach_variation ha
  rw [← T.markedAttach_forget a] at h
  simpa only [variation,List.map_map,Function.comp_def,MarkedPlacement.toPlacement] using h

 theorem markedAttach_leaves {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (a : ℝ) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a) :
    p.tree.leaves ≤ T.leaves+1 := by
  apply T.attach_leaves a p.toPlacement
  rw [← T.markedAttach_forget a]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

variable [Fintype ι] [Fintype S]
 

def profilePairExpectation (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  ((T.markedAttach a).map fun p => p.coeff*
    ((p.tree.markedAttach a).map fun q => q.coeff*
      q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*
        K (q.tree.splitIndex (q.embed p.mark) q.mark)
          (p.spin (q.restrict σ)) (q.spin σ)) x).sum).sum

 theorem profilePairExpectation_const (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (C : S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P (fun _ => C) x = T.markedPairExpectation w φ a P C x := rfl

 theorem profilePairExpectation_add (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (K L : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P (fun j s t => K j s t+L j s t) x =
      T.profilePairExpectation w φ a P K x+T.profilePairExpectation w φ a P L x := by
  simp only [profilePairExpectation,mul_add,expect_add,List.sum_map_add]

 theorem profilePairExpectation_smul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (c : ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P (fun j s t => c*K j s t) x =
      c*T.profilePairExpectation w φ a P K x := by
  simp only [profilePairExpectation,mul_left_comm _ c,expect_const_mul,List.sum_map_mul_left]

 omit [Fintype ι] [Fintype S] in
 theorem marked_list_weight_abs_le {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (MarkedPlacement T)) (F : MarkedPlacement T → ℝ) {C : ℝ}
    (hF : ∀ p ∈ ps, |F p| ≤ C) :
    |(ps.map fun p => p.coeff*F p).sum| ≤ (ps.map fun p => |p.coeff|).sum*C := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF p List.mem_cons_self) (abs_nonneg _))
      (ih (fun q hq => hF q (List.mem_cons_of_mem _ hq))))

variable [Nonempty S]
 

 theorem profilePairExpectation_abs_le {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) {P : T.Assignment → ℝ} {K : ℕ → S → S → ℝ}
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : ∀ σ, |P σ| ≤ C)
    (hK : ∀ j ≤ steps.length, ∀ s t, |K j s t| ≤ D) (x : ι → ℝ) :
    |T.profilePairExpectation w φ a P K x| ≤ 4*(T.leaves:ℝ)*(T.leaves+1)*C*D := by
  let B := 2*((T.leaves:ℝ)+1)*C*D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hinner (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a) :
      |((p.tree.markedAttach a).map fun q => q.coeff*
        q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*
          K (q.tree.splitIndex (q.embed p.mark) q.mark)
            (p.spin (q.restrict σ)) (q.spin σ)) x).sum| ≤ B := by
    apply (marked_list_weight_abs_le _ _ (fun q _ => q.tree.expect_abs_le hw φ ha
      (fun σ => by
        rw [abs_mul]
        exact mul_le_mul (hP _) (hK _ (q.tree.splitIndex_le _ _) _ _) (abs_nonneg _) hC) x)).trans
    rw [p.tree.markedAttach_variation ha]
    have hl : (p.tree.leaves:ℝ) ≤ T.leaves+1 := by exact_mod_cast T.markedAttach_leaves a p hp
    dsimp [B]
    have ha0 := ha.bounds.1
    nlinarith [mul_nonneg hC hD]
  apply (marked_list_weight_abs_le _ _ hinner).trans
  rw [T.markedAttach_variation ha]
  have ha0 := ha.bounds.1
  change (2*(T.leaves:ℝ)-a)*B ≤ _
  calc
    _ ≤ 2*(T.leaves:ℝ)*B := mul_le_mul_of_nonneg_right (by linarith) hB
    _ = _ := by dsimp [B]; ring

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 

def MarkedPlacement.profileTerm {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (p : MarkedPlacement T) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  p.tree.expect w φ (fun σ => P (p.restrict σ)*
    K (p.tree.splitIndex (p.embed s) p.mark) (T.atSlot (p.restrict σ) s) (p.spin σ)) x

def profileRowList {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (MarkedPlacement T)) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  (ps.map fun p => p.coeff*p.profileTerm w φ s P K x).sum

def profileRow {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  profileRowList (T.markedAttach a) w φ s P K x

 theorem profilePair_eq_rows (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P K x =
    ((T.markedAttach a).map fun p => p.coeff*p.tree.profileRow w φ a p.mark
      (fun σ => P (p.restrict σ)) K x).sum := by
  simp only [profilePairExpectation,profileRow,profileRowList,MarkedPlacement.profileTerm,MarkedPlacement.spin_at]

 theorem profileRow_const_separable (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (A B : S → ℝ) (x : ι → ℝ) :
    T.profileRow w φ a s P (fun _ σ τ => A σ*B τ) x =
      T.row w φ a (fun σ => P σ*A (T.atSlot σ s)) B x := by
  unfold profileRow profileRowList row rowList
  rw [← T.markedAttach_forget a,List.map_map]
  simp only [MarkedPlacement.profileTerm,Placement.eval,mul_assoc,Function.comp_def]

 theorem profileRow_add (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (K L : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profileRow w φ a s P (fun j σ τ => K j σ τ+L j σ τ) x =
      T.profileRow w φ a s P K x+T.profileRow w φ a s P L x := by
  simp only [profileRow,profileRowList,MarkedPlacement.profileTerm,mul_add,expect_add,List.sum_map_add]

 theorem profileRow_smul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (c : ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profileRow w φ a s P (fun j σ τ => c*K j σ τ) x =
      c*T.profileRow w φ a s P K x := by
  simp only [profileRow,profileRowList,MarkedPlacement.profileTerm,mul_left_comm _ c,expect_const_mul,List.sum_map_mul_left]

 theorem profileTerm_fresh_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (c : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (MarkedPlacement.fresh T c).profileTerm w φ s P K x = 0 := by
  simp [MarkedPlacement.profileTerm,MarkedPlacement.fresh,Placement.fresh,splitIndex,hK,expect]

 theorem profileTerm_left (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (p : MarkedPlacement T)
    (U : ReplicaTree ι S steps) (s : T.Slot) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    (p.left U).profileTerm w φ (.inl s) P K x =
      U.expect w φ (fun τ => p.profileTerm w φ s (fun σ => P (σ,τ)) K x) x := by
  change (p.tree.fork U).expect w φ (fun σ => P (p.restrict σ.1,σ.2)*
    K (p.tree.splitIndex (p.embed s) p.mark) (T.atSlot (p.restrict σ.1) s) (p.spin σ.1)) x = _
  rw [expect_fork]
  simp only [MarkedPlacement.profileTerm,expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

 theorem profileTerm_right (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {U : ReplicaTree ι S steps}
    (p : MarkedPlacement U) (s : U.Slot) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    (p.right T).profileTerm w φ (.inr s) P K x =
      T.expect w φ (fun σ => p.profileTerm w φ s (fun τ => P (σ,τ)) K x) x := by
  exact expect_fork w φ T p.tree _ x

 theorem profileTerm_cross_left_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {U : ReplicaTree ι S steps}
    (p : MarkedPlacement U) (s : T.Slot) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (p.right T).profileTerm w φ (.inl s) P K x = 0 := by
  simp [MarkedPlacement.profileTerm,MarkedPlacement.right,Placement.right,splitIndex,hK,expect]

 theorem profileTerm_cross_right_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (p : MarkedPlacement T)
    (U : ReplicaTree ι S steps) (s : U.Slot) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (p.left U).profileTerm w φ (.inr s) P K x = 0 := by
  simp [MarkedPlacement.profileTerm,MarkedPlacement.left,Placement.left,splitIndex,hK,expect]

 theorem profileRowList_map_left (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (U : ReplicaTree ι S steps)
    (ps : List (MarkedPlacement T)) (s : T.Slot) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    profileRowList (ps.map (MarkedPlacement.left U)) w φ (.inl s) P K x =
      U.expect w φ (fun τ => profileRowList ps w φ s (fun σ => P (σ,τ)) K x) x := by
  induction ps with
  | nil => simp [profileRowList,expect]
  | cons p ps ih =>
    change p.coeff*(p.left U).profileTerm w φ (.inl s) P K x +
      profileRowList (ps.map (MarkedPlacement.left U)) w φ (.inl s) P K x = _
    rw [profileTerm_left,ih]
    simp only [profileRowList,List.map_cons,List.sum_cons,expect_add,expect_const_mul]

 theorem profileRowList_map_right (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {U : ReplicaTree ι S steps}
    (ps : List (MarkedPlacement U)) (s : U.Slot) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    profileRowList (ps.map (MarkedPlacement.right T)) w φ (.inr s) P K x =
      T.expect w φ (fun σ => profileRowList ps w φ s (fun τ => P (σ,τ)) K x) x := by
  induction ps with
  | nil => simp [profileRowList,expect]
  | cons p ps ih =>
    change p.coeff*(p.right T).profileTerm w φ (.inr s) P K x +
      profileRowList (ps.map (MarkedPlacement.right T)) w φ (.inr s) P K x = _
    rw [profileTerm_right,ih]
    simp only [profileRowList,List.map_cons,List.sum_cons,expect_add,expect_const_mul]

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem profileRowList_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (MarkedPlacement T)) {a : ℝ} (ha : OrderedSteps a steps)
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (k : ℕ) :
    BddSmooth k (profileRowList ps w φ s P K) := by
  induction ps with
  | nil => exact BddSmooth.const k 0
  | cons p ps ih =>
    exact (p.tree.expect_smooth hw φ ha _ k |>.const_mul p.coeff).add ih

 theorem profileTerm_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} {T : ReplicaTree ι S tail}
    (p : MarkedPlacement T) (m : ℝ) (q : ι → ℝ≥0) (ha : OrderedSteps m tail)
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    (p.step (m,q)).profileTerm w φ s P K x = shiftedMean
      (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
      (p.profileTerm w φ s P (fun j => K (j+1))) x := by
  change (p.tree.step (m,q)).expect w φ
    (fun σ => P (p.restrict σ)*K (1+p.tree.splitIndex (p.embed s) p.mark)
      (T.atSlot (p.restrict σ) s) (p.spin σ)) x = shiftedMean _ m _
    (p.tree.expect w φ (fun σ => P (p.restrict σ)*K (p.tree.splitIndex (p.embed s) p.mark+1)
      (T.atSlot (p.restrict σ) s) (p.spin σ))) x
  simpa only [Nat.add_comm 1] using expect_step hw φ p.tree m q ha
    (fun σ => P (p.restrict σ)*K (p.tree.splitIndex (p.embed s) p.mark+1)
      (T.atSlot (p.restrict σ) s) (p.spin σ)) x

 theorem profileRowList_map_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} {T : ReplicaTree ι S tail}
    (ps : List (MarkedPlacement T)) (m : ℝ) (q : ι → ℝ≥0) (ha : OrderedSteps m tail)
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    profileRowList (ps.map (MarkedPlacement.step (m,q))) w φ s P K x = shiftedMean
      (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
      (profileRowList ps w φ s P (fun j => K (j+1))) x := by
  induction ps with
  | nil => simp [profileRowList,shiftedMean,tiltedMean]
  | cons p ps ih =>
    change p.coeff*(p.step (m,q)).profileTerm w φ s P K x+
      profileRowList (ps.map (MarkedPlacement.step (m,q))) w φ s P K x =
      shiftedMean _ m _ (fun y => p.coeff*p.profileTerm w φ s P (fun j => K (j+1)) y+
        profileRowList ps w φ s P (fun j => K (j+1)) y) x
    rw [profileTerm_step hw φ p m q ha,ih]
    have he : BddSmooth 0 (p.profileTerm w φ s P (fun j => K (j+1))) :=
      p.tree.expect_smooth hw φ ha _ 0
    rw [shiftedMean_add (he.const_mul p.coeff)
        (profileRowList_smooth hw φ ps ha s P _ 0)
        (gaussianHierarchy_integrable hw φ tail ha m q x),shiftedMean_const_mul]

 theorem profileRow_step_zero {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} (T : ReplicaTree ι S tail)
    (m : ℝ) (q : ι → ℝ≥0) {a : ℝ} (ha : OrderedSteps a ((m,q)::tail))
    (s : T.Slot) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (T.step (m,q)).profileRow w φ a s P K x = shiftedMean
      (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
      (T.profileRow w φ m s P (fun j => K (j+1))) x := by
  change (a-m)*(MarkedPlacement.fresh (T.step (m,q)) (a-m)).profileTerm w φ s P K x+
    profileRowList ((T.markedAttach m).map (MarkedPlacement.step (m,q))) w φ s P K x = _
  rw [profileTerm_fresh_zero w φ _ _ _ _ _ hK,mul_zero,zero_add,
    profileRowList_map_step hw φ _ m q ha.2.2.2]
  rfl

omit [Nonempty S] in
 theorem profileRow_fork_left_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps) (a : ℝ)
    (s : T.Slot) (P : (T.fork U).Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (T.fork U).profileRow w φ a (.inl s) P K x =
      U.expect w φ (fun τ => T.profileRow w φ a s (fun σ => P (σ,τ)) K x) x := by
  simp only [profileRow,markedAttach,profileRowList,List.map_cons,List.sum_cons,
    List.map_append,List.sum_append,MarkedPlacement.fresh,Placement.fresh]
  have hf := profileTerm_fresh_zero w φ (T.fork U) (-a) (.inl s) P K hK x
  change -a*(MarkedPlacement.fresh (T.fork U) (-a)).profileTerm w φ (.inl s) P K x+
    (profileRowList ((T.markedAttach a).map (MarkedPlacement.left U)) w φ (.inl s) P K x+
      profileRowList ((U.markedAttach a).map (MarkedPlacement.right T)) w φ (.inl s) P K x) = _
  rw [hf,mul_zero,zero_add,profileRowList_map_left]
  have hz : profileRowList ((U.markedAttach a).map (MarkedPlacement.right T))
      w φ (.inl s) P K x = 0 := by
    simp only [profileRowList,List.map_map,Function.comp_def]
    simp [profileTerm_cross_left_zero w φ T _ s P K hK x]
  rw [hz,add_zero]
  rfl

omit [Nonempty S] in
 theorem profileRow_fork_right_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps) (a : ℝ)
    (s : U.Slot) (P : (T.fork U).Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (T.fork U).profileRow w φ a (.inr s) P K x =
      T.expect w φ (fun σ => U.profileRow w φ a s (fun τ => P (σ,τ)) K x) x := by
  change -a*(MarkedPlacement.fresh (T.fork U) (-a)).profileTerm w φ (.inr s) P K x+
    profileRowList (((T.markedAttach a).map (MarkedPlacement.left U))++
      ((U.markedAttach a).map (MarkedPlacement.right T))) w φ (.inr s) P K x = _
  rw [profileTerm_fresh_zero w φ _ _ _ _ _ hK,mul_zero,zero_add]
  unfold profileRowList
  rw [List.map_append,List.sum_append]
  have hz : profileRowList ((T.markedAttach a).map (MarkedPlacement.left U))
      w φ (.inr s) P K x = 0 := by
    simp only [profileRowList,List.map_map,Function.comp_def]
    simp [profileTerm_cross_right_zero w φ _ U s P K hK x]
  change profileRowList ((T.markedAttach a).map (MarkedPlacement.left U)) w φ (.inr s) P K x+
    profileRowList ((U.markedAttach a).map (MarkedPlacement.right T)) w φ (.inr s) P K x = _
  rw [hz,zero_add,profileRowList_map_right]
  rfl

end SKFluctuations.Hierarchy.ReplicaTree

end

end OAI
