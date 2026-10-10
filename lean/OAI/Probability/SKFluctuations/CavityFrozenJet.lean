import Mathlib
import OAI.Probability.SKFluctuations.CavityMixedInsertion

namespace OAI

/-! Cavity Frozen Jet. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators
section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
  {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)

 
def cutFrozenLowHighJet (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (k r : ℕ) (t : ℝ) : ℝ :=
  ((ClockPolynomial.finiteLowJet (T.testExpr P) (fullFeature n)
    (cutLSlope n U 0 b h K) (cutLowError n U b h K) k).finiteIterInsert
      (fullFeature n) (cutTSlope n U 0 b h K) r).finiteEval
        (fullWeight n) (fullFeature n) 1 0 (cutFullVariance n q U 0 t b h K) x

 theorem cutFrozenLowHighJet_continuous (P : T.Assignment → ℝ)
    (x : FullCoordinate n → ℝ) (k r : ℕ) :
    Continuous (cutFrozenLowHighJet n q U b h K T P x k r) := by
  exact ClockPolynomial.finiteEval_continuous (fullWeight_pos n) (fullFeature n) _
    (fun _ => 1) continuous_const 0 _ (cutFullVariance_continuous_t n q U b h K 0)
    (fun _ => x) continuous_const

 theorem cutFrozenLowHighJet_endpoint (P : T.Assignment → ℝ)
    (x : FullCoordinate n → ℝ) (k : ℕ) :
    cutFrozenLowHighJet n q U b h K T P x k 0 1 =
      cutLowJet n q U b h K T P x k 0 1 := rfl

variable (P : T.cavityLeft.Assignment → ℝ) (Q : T.cavityRight.Assignment → ℝ)
  (x : ActiveCoordinate n → ℝ)

 
def cutFrozenCenteredJet (k : Fin 4) (r : ℕ) (t : ℝ) : ℝ :=
  cutFrozenLowHighJet n q U b h K T
    (fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2) (cavityEmbed x) k r t -
  productJet3
    (fun i => cutLowJet n q U b h K T (fun σ => Q (T.cavityAssignment σ).2) (cavityEmbed x) i 0 0)
    (fun i => cutFrozenLowHighJet n q U b h K T (fun σ => P (T.cavityAssignment σ).1)
      (cavityEmbed x) i r t) k

 theorem cutFrozenCenteredJet_continuous (k : Fin 4) (r : ℕ) :
    Continuous (cutFrozenCenteredJet n q U b h K T P Q x k r) := by
  apply (cutFrozenLowHighJet_continuous n q U b h K T _ _ _ _).sub
  exact productJet3_continuous _ _ (fun _ => continuous_const)
    (fun _ => cutFrozenLowHighJet_continuous n q U b h K T _ _ _ _) k

 theorem cutFrozenCenteredJet_endpoint (k : Fin 4) :
    cutFrozenCenteredJet n q U b h K T P Q x k 0 1 =
      cutCenteredJet n q U b h K T P Q x k 0 1 := rfl

variable (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
  (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
  (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
  (ho : MassOrdered 0 as)
include hq0 hq hb hh hK hbm hhm hKm ho

 theorem cutFrozenLowHighJet_hasDerivAt (P : T.Assignment → ℝ)
    (x : FullCoordinate n → ℝ) (k r : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (cutFrozenLowHighJet n q U b h K T P x k r)
      (cutFrozenLowHighJet n q U b h K T P x k (r+1) t) t := by
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutTBase n q U 0 b h K 0 i+s*cutTSlope n U 0 b h K 0 i := by
    intro s hs i
    have hn := cutFullVariance_nonneg n q U (l := 0) (by norm_num) ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
    simpa only [cutFullVariance_t_affine, Pi.zero_apply] using hn
  have hd := ClockPolynomial.hasDerivAt_finite_frozen (fullWeight_pos n) (fullFeature n)
    ((ClockPolynomial.finiteLowJet (T.testExpr P) (fullFeature n)
      (cutLSlope n U 0 b h K) (cutLowError n U b h K) k).finiteIterInsert
        (fullFeature n) (cutTSlope n U 0 b h K) r) ho 0
      (cutTBase n q U 0 b h K) (cutTSlope n U 0 b h K)
      (cutT_affine_monotone n q U (by norm_num) hq hb hh hK hbm hhm hKm) hr ht 1 x
  have he (s : ℝ) : (fun j i => cutTBase n q U 0 b h K j i+s*cutTSlope n U 0 b h K j i) =
      cutFullVariance n q U 0 s b h K := (cutFullVariance_t_affine n q U 0 s b h K).symm
  simp only [he] at hd
  exact hd

 theorem cutFrozenCenteredJet_hasDerivAt (k : Fin 4) (r : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (cutFrozenCenteredJet n q U b h K T P Q x k r)
      (cutFrozenCenteredJet n q U b h K T P Q x k (r+1) t) t := by
  apply (cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK hbm hhm hKm ho _ _ _ _ ht).sub
  exact productJet3_hasDerivAt_right _ _ _
    (fun _ => cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK hbm hhm hKm ho _ _ _ _ ht) k

 

theorem cutCenteredJet_frozen_decomposition :
    cutCenteredJet n q U b h K T P Q x 0 1 1 =
      cutCenteredJet n q U b h K T P Q x 0 0 1+
      cutFrozenCenteredJet n q U b h K T P Q x 1 0 0+
      cutFrozenCenteredJet n q U b h K T P Q x 1 1 0+
      (1/2:ℝ)*cutFrozenCenteredJet n q U b h K T P Q x 2 0 0+
      (∫ t in (0:ℝ)..1, (1-t)*cutFrozenCenteredJet n q U b h K T P Q x 1 2 t)+
      (1/2:ℝ)*(∫ t in (0:ℝ)..1, cutFrozenCenteredJet n q U b h K T P Q x 2 1 t)+
      (1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*∫ t in (0:ℝ)..1,
        cutCenteredMixedJet n q U b h K T P Q x 3 l t := by
  have hA := second_jet_remainder
    (cutFrozenCenteredJet n q U b h K T P Q x 1 0)
    (cutFrozenCenteredJet n q U b h K T P Q x 1 1)
    (cutFrozenCenteredJet n q U b h K T P Q x 1 2)
    (cutFrozenCenteredJet_continuous n q U b h K T P Q x 1 0)
    (cutFrozenCenteredJet_continuous n q U b h K T P Q x 1 1)
    (cutFrozenCenteredJet_continuous n q U b h K T P Q x 1 2)
    (fun _ ht => cutFrozenCenteredJet_hasDerivAt n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 1 0 ht)
    (fun _ ht => cutFrozenCenteredJet_hasDerivAt n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 1 1 ht)
  have hB := first_jet_remainder
    (cutFrozenCenteredJet n q U b h K T P Q x 2 0)
    (cutFrozenCenteredJet n q U b h K T P Q x 2 1)
    (cutFrozenCenteredJet_continuous n q U b h K T P Q x 2 0)
    (cutFrozenCenteredJet_continuous n q U b h K T P Q x 2 1)
    (fun _ ht => cutFrozenCenteredJet_hasDerivAt n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 2 0 ht)
  rw [cutFrozenCenteredJet_endpoint] at hA hB
  rw [cutCenteredJet_third_mixed_remainder n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho,
    hA,hB]
  ring

end
end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {S ι : Type*}

 

@[reducible] def ClockTree.CutGauge {as : List PositiveMass} (T : ClockTree S as) (u : ℕ) : Type :=
  match u with
  | 0 => Bool
  | u+1 => match T with
      | .leaf => Bool
      | .step _ T => T.CutGauge u
      | .fork T V => T.CutGauge (u+1) × V.CutGauge (u+1)
termination_by structural T

def ClockTree.assignmentGauge (π : S ≃ S) : {as : List PositiveMass} →
    (T : ClockTree S as) → T.Assignment ≃ T.Assignment
  | _, .leaf => π
  | _, .step _ T => T.assignmentGauge π
  | _, .fork T V => (T.assignmentGauge π).prodCongr (V.assignmentGauge π)

def ClockTree.cutGaugeEquiv (π : S ≃ S) : {as : List PositiveMass} →
    (T : ClockTree S as) → (u : ℕ) → T.CutGauge u → T.Assignment ≃ T.Assignment
  | _, .leaf, 0, g => if (g : Bool) = true then π else Equiv.refl _
  | _, .step a T, 0, g => if (g : Bool) = true then (T.step a).assignmentGauge π else Equiv.refl _
  | _, .fork T V, 0, g => if (g : Bool) = true then (T.fork V).assignmentGauge π else Equiv.refl _
  | _, .leaf, _+1, g => if (g : Bool) = true then π else Equiv.refl _
  | _, .step _ T, u+1, g => T.cutGaugeEquiv π u g
  | _, .fork T V, u+1, g => (T.cutGaugeEquiv π (u+1) g.1).prodCongr (V.cutGaugeEquiv π (u+1) g.2)

variable [Fintype ι] [Fintype S]
 theorem ClockTree.weight_gauge (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (L x) = φ s x)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (hL : ∀ j, MeasurePreserving L (Measure.pi fun i => gaussianReal 0 (q j i))
      (Measure.pi fun i => gaussianReal 0 (q j i))) (σ : T.Assignment) (x : ι → ℝ) :
    T.weight w φ q (T.assignmentGauge π σ) (L x) = T.weight w φ q σ x := by
  induction T generalizing q x with
  | leaf => exact spinWeight_equiv L π hw hφ x σ
  | @step a as T ih =>
    simp only [ClockTree.weight_step,ClockTree.assignmentGauge]
    apply shiftedMean_equiv L (hL 0) a.val
    · apply gaussianHierarchy_equiv L π hw hφ
      intro p hp
      have hm : ∀ cs : List PositiveMass, ∀ v : ℕ → ι → ℝ≥0,
          (∀ j, MeasurePreserving L (Measure.pi fun i => gaussianReal 0 (v j i))
            (Measure.pi fun i => gaussianReal 0 (v j i))) →
          ∀ p ∈ clockSteps cs v, MeasurePreserving L (Measure.pi fun i => gaussianReal 0 (p.2 i))
            (Measure.pi fun i => gaussianReal 0 (p.2 i)) := by
        intro cs; induction cs with
        | nil => simp [clockSteps]
        | cons b bs ih =>
          intro v hv p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hv 0
          · exact ih (fun j => v (j+1)) (fun j => hv (j+1)) p hp
      exact hm as (fun j => q (j+1)) (fun j => hL (j+1)) p hp
    · exact fun y => ih _ (fun j => hL (j+1)) σ y
  | fork T V ihT ihV =>
    change T.weight w φ q (T.assignmentGauge π σ.1) (L x) *
      V.weight w φ q (V.assignmentGauge π σ.2) (L x) = _
    rw [ihT q hL,ihV q hL]
    rfl

 theorem gaussian_coordinate_zero_ae (q : ι → ℝ≥0) (i : ι) (hi : q i = 0) :
    ∀ᵐ z ∂Measure.pi (fun j => gaussianReal 0 (q j)), z i = 0 := by
  have h : ∀ᵐ z ∂gaussianReal 0 (q i), z = 0 := by simp [hi]
  exact (measurePreserving_eval (fun j => gaussianReal 0 (q j)) i).quasiMeasurePreserving.ae h

 

 theorem ClockTree.weight_cutGauge
    (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (L x) = φ s x)
    {as : List PositiveMass} (T : ClockTree S as) (u : ℕ) (q : ℕ → ι → ℝ≥0)
    (hL : ∀ j, MeasurePreserving L (Measure.pi fun i => gaussianReal 0 (q j i))
      (Measure.pi fun i => gaussianReal 0 (q j i)))
    (hz : ∀ j < u, ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0 (q j i)), L z = z)
    (g : T.CutGauge u) (σ : T.Assignment) (x : ι → ℝ) (hx : L x = x) :
    T.weight w φ q (T.cutGaugeEquiv π u g σ) x = T.weight w φ q σ x := by
  induction T generalizing u q x with
  | leaf =>
    cases u <;> cases g
    all_goals first | rfl | simpa only [ClockTree.cutGaugeEquiv, ite_eq_left rfl, ite_true, ClockTree.weight_leaf, hx] using spinWeight_equiv L π hw hφ x σ
  | @step a as T ih =>
    cases u with
    | zero =>
      cases g
      · rfl
      · simpa only [ClockTree.cutGaugeEquiv, ite_eq_left rfl, ite_true, hx] using (T.step a).weight_gauge L π hw hφ q hL σ x
    | succ u =>
      simp only [ClockTree.cutGaugeEquiv,ClockTree.weight_step,shiftedMean,tiltedMean]
      congr 1
      apply integral_congr_ae
      filter_upwards [hz 0 (Nat.zero_lt_succ u)] with z hzflip
      rw [ih u (fun j => q (j+1)) (fun j => hL (j+1))
        (fun j hj => hz (j+1) (Nat.succ_lt_succ hj)) g σ (x+z) (by rw [map_add,hx,hzflip])]
  | @fork as T V ihT ihV =>
    cases u with
    | zero =>
      cases g
      · rfl
      · simpa only [ClockTree.cutGaugeEquiv, ite_eq_left rfl, ite_true, hx] using (T.fork V).weight_gauge L π hw hφ q hL σ x
    | succ u =>
      change T.weight w φ q (T.cutGaugeEquiv π (u+1) g.1 σ.1) x *
        V.weight w φ q (V.cutGaugeEquiv π (u+1) g.2 σ.2) x = _
      rw [ihT _ q hL hz g.1 σ.1 x hx,ihV _ q hL hz g.2 σ.2 x hx]
      rfl

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {S ι : Type*}

 theorem ClockTree.cutGaugeEquiv_zero_cases (π : S ≃ S) {as : List PositiveMass}
    (T : ClockTree S as) (g : T.CutGauge 0) :
    T.cutGaugeEquiv π 0 g = T.assignmentGauge π ∨
      T.cutGaugeEquiv π 0 g = Equiv.refl _ := by
  cases T <;> cases g <;> first | exact Or.inl rfl | exact Or.inr rfl

variable [Fintype ι] [Fintype S]
 

 theorem ClockTree.weight_cutGauge_endpoint
    (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (L x) = φ s x)
    {as : List PositiveMass} (T : ClockTree S as) (u : ℕ) (q : ℕ → ι → ℝ≥0)
    (hL : ∀ j, MeasurePreserving L (Measure.pi fun i => gaussianReal 0 (q j i))
      (Measure.pi fun i => gaussianReal 0 (q j i)))
    (hz : ∀ j, j+1 < u → ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0 (q j i)), L z = z)
    (g : T.CutGauge u) (σ : T.Assignment) (x : ι → ℝ) (hx : L x = x) :
    T.weight w φ q (T.cutGaugeEquiv π u g σ) x = T.weight w φ q σ x := by
  induction T generalizing u q x with
  | leaf =>
    cases u <;> cases g
    all_goals first | rfl | simpa only [ClockTree.cutGaugeEquiv, ite_eq_left rfl, ite_true,
      ClockTree.weight_leaf, hx] using spinWeight_equiv L π hw hφ x σ
  | @step a as T ih =>
    cases u with
    | zero =>
      cases g
      · rfl
      · simpa only [ClockTree.cutGaugeEquiv, ite_eq_left rfl, ite_true, hx] using
          (T.step a).weight_gauge L π hw hφ q hL σ x
    | succ u =>
      cases u with
      | zero =>
        simp only [ClockTree.cutGaugeEquiv]
        rcases T.cutGaugeEquiv_zero_cases π g with he | he
        · rw [he]
          simpa only [hx,ClockTree.assignmentGauge] using (T.step a).weight_gauge L π hw hφ q hL σ x
        · rw [he]; rfl
      | succ u =>
        simp only [ClockTree.cutGaugeEquiv,ClockTree.weight_step,shiftedMean,tiltedMean]
        congr 1
        apply integral_congr_ae
        filter_upwards [hz 0 (by omega)] with z hzflip
        rw [ih (u+1) (fun j => q (j+1)) (fun j => hL (j+1))
          (fun j hj => hz (j+1) (by omega)) g σ (x+z) (by rw [map_add,hx,hzflip])]
  | @fork as T V ihT ihV =>
    cases u with
    | zero =>
      cases g
      · rfl
      · simpa only [ClockTree.cutGaugeEquiv, ite_eq_left rfl, ite_true, hx] using
          (T.fork V).weight_gauge L π hw hφ q hL σ x
    | succ u =>
      change T.weight w φ q (T.cutGaugeEquiv π (u+1) g.1 σ.1) x *
        V.weight w φ q (V.cutGaugeEquiv π (u+1) g.2 σ.2) x = _
      rw [ihT _ q hL hz g.1 σ.1 x hx,ihV _ q hL hz g.2 σ.2 x hx]
      rfl

 theorem ClockTree.expect_cutGauge_odd
    (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (L x) = φ s x)
    {as : List PositiveMass} (T : ClockTree S as) (u : ℕ) (q : ℕ → ι → ℝ≥0)
    (hL : ∀ j, MeasurePreserving L (Measure.pi fun i => gaussianReal 0 (q j i))
      (Measure.pi fun i => gaussianReal 0 (q j i)))
    (hz : ∀ j, j+1 < u → ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0 (q j i)), L z = z)
    (g : T.CutGauge u) (P : T.Assignment → ℝ)
    (hP : ∀ σ, P (T.cutGaugeEquiv π u g σ) = -P σ)
    (x : ι → ℝ) (hx : L x = x) : T.expect w φ q P x = 0 := by
  have he := (T.cutGaugeEquiv π u g).sum_comp (fun σ => T.weight w φ q σ x*P σ)
  simp_rw [T.weight_cutGauge_endpoint L π hw hφ u q hL hz g _ x hx,hP,
    mul_neg,Finset.sum_neg_distrib] at he
  unfold ClockTree.expect
  linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal

 theorem rowDriverFlip_gaussian_fixed_ae (n : ℕ) (v : FullCoordinate n → ℝ≥0)
    (hs : ∀ i, v (.inl (.inr i)) = 0) (hr : ∀ i, v (.inr i) = 0) :
    ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0 (v i)), rowDriverFlip n z = z := by
  have hsz : ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0 (v i)), ∀ i, z (.inl (.inr i)) = 0 :=
    ae_all_iff.mpr (fun i => gaussian_coordinate_zero_ae v _ (hs i))
  have hrz : ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0 (v i)), ∀ i, z (.inr i) = 0 :=
    ae_all_iff.mpr (fun i => gaussian_coordinate_zero_ae v _ (hr i))
  filter_upwards [hsz,hrz] with z hs hr
  exact rowDriverFlip_fixed n z hs hr

 theorem cutFullVariance_zero_scalar (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (t : ℝ) (b h K : ℕ → ℝ) {j : ℕ} (hj : j < U) (i : Fin 1) :
    cutFullVariance n q U 0 t b h K j (.inl (.inr i)) = 0 := by
  simp [cutFullVariance,fullVariance,relocatedClock,hj]

 theorem cutFullVariance_zero_row (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (t : ℝ) (b h K : ℕ → ℝ) {j : ℕ} (hj : j < U) (i : DormantCoordinate n) :
    cutFullVariance n q U 0 t b h K j (.inr i) = 0 := by
  cases i <;> simp [cutFullVariance,fullVariance,relocatedClock,hj]

 

 theorem cutDisorderWeight_gauge (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (hU : 0 < U) (t : ℝ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (g : T.CutGauge U) (σ : T.Assignment) (x : FullCoordinate n → ℝ)
    (hs : ∀ i, x (.inl (.inr i)) = 0) (hr : ∀ i, x (.inr i) = 0) :
    T.disorderWeight (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (T.cutGaugeEquiv (rowSpinFlip n) U g σ) x =
    T.disorderWeight (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K) σ x := by
  let v := cutFullVariance n q U 0 t b h K
  have hvS {j : ℕ} (hj : j < U) (i : Fin 1) : v j (.inl (.inr i)) = 0 :=
    cutFullVariance_zero_scalar n q U t b h K hj i
  have hvR {j : ℕ} (hj : j < U) (i : DormantCoordinate n) : v j (.inr i) = 0 :=
    cutFullVariance_zero_row n q U t b h K hj i
  have hz0 : ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (v 0 i-0))),
      rowDriverFlip n z = z := by
    apply rowDriverFlip_gaussian_fixed_ae n
    · intro i; simp only [hvS hU i,sub_zero,Real.toNNReal_zero]
    · intro i; simp only [hvR hU i,sub_zero,Real.toNNReal_zero]
  have hz (j : ℕ) (hj : j+1 < U) : ∀ᵐ z ∂Measure.pi (fun i => gaussianReal 0
      (cumulativeIncrements (v 0) (fun k => v (k+1)) j i)), rowDriverFlip n z = z := by
    apply rowDriverFlip_gaussian_fixed_ae n
    · intro i
      cases j with
      | zero => simp [cumulativeIncrements,hvS hU i,hvS hj i]
      | succ j => simp [cumulativeIncrements,hvS hj i,hvS (show j+1 < U by omega) i]
    · intro i
      cases j with
      | zero => simp [cumulativeIncrements,hvR hU i,hvR hj i]
      | succ j => simp [cumulativeIncrements,hvR hj i,hvR (show j+1 < U by omega) i]
  change (∫ z, T.weight (fullWeight n) (fullFeature n)
      (cumulativeIncrements (v 0) (fun j => v (j+1)))
      (T.cutGaugeEquiv (rowSpinFlip n) U g σ) (x+z)
      ∂Measure.pi fun i => gaussianReal 0 (Real.toNNReal (v 0 i-0))) = _
  apply integral_congr_ae
  filter_upwards [hz0] with z hzflip
  exact T.weight_cutGauge_endpoint (rowDriverFlip n) (rowSpinFlip n)
    (fullWeight_rowSpinFlip n) (fullFeature_rowFlip n) U _
    (fun j => rowDriverFlip_gaussian n _) hz g σ (x+z)
    (by rw [map_add,rowDriverFlip_fixed n x hs hr,hzflip])

 theorem cutDisorderExpect_odd (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (hU : 0 < U) (t : ℝ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (g : T.CutGauge U) (P : T.Assignment → ℝ)
    (hP : ∀ σ, P (T.cutGaugeEquiv (rowSpinFlip n) U g σ) = -P σ)
    (x : FullCoordinate n → ℝ)
    (hs : ∀ i, x (.inl (.inr i)) = 0) (hr : ∀ i, x (.inr i) = 0) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K) P x = 0 := by
  have he := (T.cutGaugeEquiv (rowSpinFlip n) U g).sum_comp (fun σ =>
    T.disorderWeight (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K) σ x*P σ)
  simp_rw [cutDisorderWeight_gauge n q U hU t b h K T g _ x hs hr,hP,
    mul_neg,Finset.sum_neg_distrib] at he
  unfold ClockTree.disorderExpect
  linarith

end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

@[reducible] def Slot : {as : List PositiveMass} → ClockTree S as → Type
  | _, .leaf => Unit
  | _, .step _ T => T.Slot
  | _, .fork T V => T.Slot ⊕ V.Slot

def atSlot : {as : List PositiveMass} → (T : ClockTree S as) → T.Assignment → T.Slot → S
  | _, .leaf => fun σ _ => σ
  | _, .step _ T => T.atSlot
  | _, .fork T V => fun σ => Sum.elim (T.atSlot σ.1) (V.atSlot σ.2)

def splitIndex : {as : List PositiveMass} → (T : ClockTree S as) → T.Slot → T.Slot → ℕ
  | _, .leaf => fun _ _ => 0
  | _, .step _ T => fun s t => 1+T.splitIndex s t
  | _, .fork T V => fun s t => Sum.elim
      (fun s => Sum.elim (T.splitIndex s) (fun _ => 0) t)
      (fun s => Sum.elim (fun _ => 0) (V.splitIndex s) t) s

 theorem splitIndex_self {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) :
    T.splitIndex s s = as.length := by
  induction T with
  | leaf => rfl
  | step a T ih => simp only [splitIndex,ih,List.length_cons,Nat.add_comm]
  | fork T V ihT ihV => cases s <;> first | exact ihT _ | exact ihV _

def offGauge : {as : List PositiveMass} → (T : ClockTree S as) → (u : ℕ) → T.CutGauge u
  | _, .leaf, 0 => false
  | _, .leaf, _+1 => false
  | _, .step _ _, 0 => false
  | _, .fork _ _, 0 => false
  | _, .step _ T, u+1 => T.offGauge u
  | _, .fork T V, u+1 => (T.offGauge (u+1),V.offGauge (u+1))

def gaugeAt : {as : List PositiveMass} → (T : ClockTree S as) → (u : ℕ) → T.Slot → T.CutGauge u
  | _, .leaf, 0, _ => true
  | _, .leaf, _+1, _ => true
  | _, .step _ _, 0, _ => true
  | _, .fork _ _, 0, _ => true
  | _, .step _ T, u+1, s => T.gaugeAt u s
  | _, .fork T V, u+1, s => Sum.elim
      (fun s => (T.gaugeAt (u+1) s,V.offGauge (u+1)))
      (fun s => (T.offGauge (u+1),V.gaugeAt (u+1) s)) s

 theorem atSlot_assignmentGauge (π : S ≃ S) {as : List PositiveMass}
    (T : ClockTree S as) (σ : T.Assignment) (s : T.Slot) :
    T.atSlot (T.assignmentGauge π σ) s = π (T.atSlot σ s) := by
  induction T with
  | leaf => rfl
  | step a T ih => exact ih σ s
  | fork T V ihT ihV => cases s <;> first | exact ihT _ _ | exact ihV _ _

 theorem cutGaugeEquiv_off (π : S ≃ S) {as : List PositiveMass}
    (T : ClockTree S as) (u : ℕ) : T.cutGaugeEquiv π u (T.offGauge u) = Equiv.refl _ := by
  induction T generalizing u with
  | leaf => cases u <;> rfl
  | step a T ih => cases u with
    | zero => rfl
    | succ u => exact ih u
  | fork T V ihT ihV => cases u with
    | zero => rfl
    | succ u =>
      change (T.cutGaugeEquiv π (u+1) (T.offGauge (u+1))).prodCongr
        (V.cutGaugeEquiv π (u+1) (V.offGauge (u+1))) = _
      rw [ihT,ihV]
      rfl

 
 theorem atSlot_gaugeAt (π : S ≃ S) {as : List PositiveMass}
    (T : ClockTree S as) (u : ℕ) (hu : u ≤ as.length) (s t : T.Slot) (σ : T.Assignment) :
    T.atSlot (T.cutGaugeEquiv π u (T.gaugeAt u s) σ) t =
      if u ≤ T.splitIndex s t then π (T.atSlot σ t) else T.atSlot σ t := by
  induction T generalizing u with
  | leaf =>
    have : u = 0 := by simp only [List.length_nil] at hu; omega
    subst u
    rfl
  | step a T ih =>
    cases u with
    | zero => simpa only [gaugeAt,cutGaugeEquiv,ite_true,Nat.zero_le] using
        (T.step a).atSlot_assignmentGauge π σ t
    | succ u =>
      simpa only [gaugeAt,cutGaugeEquiv,atSlot,splitIndex,Nat.add_comm 1,Nat.succ_le_succ_iff]
        using ih u (by simpa using hu) s t σ
  | fork T V ihT ihV =>
    cases u with
    | zero => simpa only [gaugeAt,cutGaugeEquiv,ite_true,Nat.zero_le] using
        (T.fork V).atSlot_assignmentGauge π σ t
    | succ u =>
      cases s <;> cases t
      · exact ihT (u+1) hu _ _ _
      · simp [gaugeAt,cutGaugeEquiv,atSlot,splitIndex,cutGaugeEquiv_off]
      · simp [gaugeAt,cutGaugeEquiv,atSlot,splitIndex,cutGaugeEquiv_off]
      · exact ihV (u+1) hu _ _ _

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S B : Type*}

def cavityRightSlot : {as : List PositiveMass} → (T : ClockTree (S × B) as) → T.Slot ≃ T.cavityRight.Slot
  | _, .leaf => Equiv.refl _
  | _, .step _ T => T.cavityRightSlot
  | _, .fork T V => T.cavityRightSlot.sumCongr V.cavityRightSlot

 theorem atSlot_cavityRight {as : List PositiveMass} (T : ClockTree (S × B) as)
    (σ : T.Assignment) (s : T.Slot) :
    T.cavityRight.atSlot (T.cavityAssignment σ).2 (T.cavityRightSlot s) = (T.atSlot σ s).2 := by
  induction T with
  | leaf => rfl
  | step a T ih => exact ih σ s
  | fork T V ihT ihV => cases s <;> first | exact ihT _ _ | exact ihV _ _

 theorem cavityAssignment_gauge_left (π : B ≃ B) {as : List PositiveMass}
    (T : ClockTree (S × B) as) (σ : T.Assignment) :
    (T.cavityAssignment (T.assignmentGauge ((Equiv.refl S).prodCongr π) σ)).1 =
      (T.cavityAssignment σ).1 := by
  induction T with
  | leaf => rfl
  | step a T ih => exact ih σ
  | fork T V ihT ihV => exact Prod.ext (ihT σ.1) (ihV σ.2)

 theorem cavityAssignment_cutGauge_left (π : B ≃ B) {as : List PositiveMass}
    (T : ClockTree (S × B) as) (u : ℕ) (g : T.CutGauge u) (σ : T.Assignment) :
    (T.cavityAssignment (T.cutGaugeEquiv ((Equiv.refl S).prodCongr π) u g σ)).1 =
      (T.cavityAssignment σ).1 := by
  induction T generalizing u with
  | leaf => cases u <;> cases g <;> rfl
  | step a T ih =>
    cases u with
    | zero =>
      cases g
      · rfl
      · exact (T.step a).cavityAssignment_gauge_left π σ
    | succ u => exact ih u g σ
  | fork T V ihT ihV =>
    cases u with
    | zero =>
      cases g
      · rfl
      · exact (T.fork V).cavityAssignment_gauge_left π σ
    | succ u => exact Prod.ext (ihT (u+1) g.1 σ.1) (ihV (u+1) g.2 σ.2)

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal

 
def sitePair {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (s t : T.Slot) (τ : T.cavityRight.Assignment) : ℝ :=
  spinValue (T.cavityRight.atSlot τ (T.cavityRightSlot s))*
  spinValue (T.cavityRight.atSlot τ (T.cavityRightSlot t))

 theorem sitePair_apply {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (s t : T.Slot) (σ : T.Assignment) :
    sitePair T s t (T.cavityAssignment σ).2 =
      spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2 := by
  simp only [sitePair,T.atSlot_cavityRight]

 

theorem cutDisorderExpect_sitePair_zero (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (t : ℝ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (s r : T.Slot)
    (hU : U ≤ as.length) (hsr : T.splitIndex s r < U)
    (P : T.cavityLeft.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (hs : ∀ i, x (.inl (.inr i)) = 0) (hr : ∀ i, x (.inr i) = 0) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => P (T.cavityAssignment σ).1*sitePair T s r (T.cavityAssignment σ).2) x = 0 := by
  apply cutDisorderExpect_odd n q U (by omega) t b h K T (T.gaugeAt U s) _ _ x hs hr
  intro σ
  have hss : U ≤ T.splitIndex s s := by rw [T.splitIndex_self]; exact hU
  have hrest := T.cavityAssignment_cutGauge_left Equiv.boolNot U (T.gaugeAt U s) σ
  change (T.cavityAssignment (T.cutGaugeEquiv (rowSpinFlip n) U (T.gaugeAt U s) σ)).1 = _ at hrest
  rw [hrest,sitePair_apply,sitePair_apply,T.atSlot_gaugeAt (rowSpinFlip n) U hU s s σ,
    T.atSlot_gaugeAt (rowSpinFlip n) U hU s r σ,ite_eq_left hss,ite_eq_right (not_le.mpr hsr)]
  simp only [rowSpinFlip_apply,spinValue_not]
  ring

 

theorem scalarSitePair_zero (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (s r : T.Slot) (hU : U ≤ as.length) (hsr : T.splitIndex s r < U)
    (x : ActiveCoordinate n → ℝ) (hx : ∀ i, x (.inr i) = 0) :
    T.cavityRight.disorderExpect (fun _ : Bool => (1/2:ℝ)) scalarFeature 0
      (fun j _ => relocatedClock U 0 K j) (sitePair T s r) (fun i => x (.inr i)) = 0 := by
  have he := cutDisorderExpect_sitePair_zero n q U 0 b h K T s r hU hsr (fun _ => 1)
    (cavityEmbed x) hx (fun i => by simp [cavityEmbed])
  rw [cutDisorderExpect_scalar_product n q U 0 b h K T ho (fun _ => 1) (sitePair T s r) x] at he
  rw [T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,one_mul] at he
  exact he

end SKFluctuations.Cavity

end

end OAI
