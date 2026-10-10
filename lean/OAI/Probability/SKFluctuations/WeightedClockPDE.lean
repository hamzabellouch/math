import Mathlib
import OAI.Probability.SKFluctuations.ScalarArbitraryConcat

namespace OAI

/-! Weighted Clock P D E. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

noncomputable def weightedP (u : ℝ × ℝ → ℝ) (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  invariantP a (realSpatialJet u 2 z) (realSpatialJet u 3 z) (realSpatialJet u 4 z)
noncomputable def weightedQ (u : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  invariantQ (realSpatialJet u 2 z) (realSpatialJet u 3 z) (realSpatialJet u 4 z) (realSpatialJet u 5 z)
noncomputable def weightedR (u : ℝ × ℝ → ℝ) (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  invariantR a (realSpatialJet u 2 z) (realSpatialJet u 3 z) (realSpatialJet u 4 z) (realSpatialJet u 5 z)

section Space
variable {u : ℝ × ℝ → ℝ} (hu : ∀ k, SpatialRegular k u)
include hu

theorem weightedP_continuous (a : ℝ) : Continuous (weightedP u a) := by
  change Continuous (fun z => -a*(realSpatialJet u 2 z)^3-realSpatialJet u 2 z*realSpatialJet u 4 z/2+(realSpatialJet u 3 z)^2/2)
  exact (((continuous_const.mul ((realSpatialJet_continuous hu 2).pow 3)).sub
    (((realSpatialJet_continuous hu 2).mul (realSpatialJet_continuous hu 4)).div_const 2)).add
    (((realSpatialJet_continuous hu 3).pow 2).div_const 2))

theorem weightedQ_continuous : Continuous (weightedQ u) := by
  change Continuous (fun z => -(realSpatialJet u 2 z)^2*realSpatialJet u 5 z/2+2*realSpatialJet u 2 z*realSpatialJet u 3 z*realSpatialJet u 4 z-3*(realSpatialJet u 3 z)^3/2)
  have h2 := realSpatialJet_continuous hu 2
  have h3 := realSpatialJet_continuous hu 3
  have h4 := realSpatialJet_continuous hu 4
  have h5 := realSpatialJet_continuous hu 5
  fun_prop

theorem weightedR_continuous (a : ℝ) : Continuous (weightedR u a) := by
  exact (weightedQ_continuous hu).add
    (((continuous_const.mul (realSpatialJet_continuous hu 3)).mul (weightedP_continuous hu a)).div_const 2)

theorem weightedP_space (a t x : ℝ) : deriv (fun y => weightedP u a (t,y)) x =
    invariantPx a (realSpatialJet u 2 (t,x)) (realSpatialJet u 3 (t,x))
      (realSpatialJet u 4 (t,x)) (realSpatialJet u 5 (t,x)) := by
  exact ((hasDerivAt_invariantP a (realSpatialJet_hasDerivAt hu 2 t x)
    (realSpatialJet_hasDerivAt hu 3 t x) (realSpatialJet_hasDerivAt hu 4 t x)).congr_deriv
      (invariantPD_space ..)).deriv

theorem weightedP_space_two (a t x : ℝ) : deriv (deriv (fun y => weightedP u a (t,y))) x =
    invariantPxx a (realSpatialJet u 2 (t,x)) (realSpatialJet u 3 (t,x))
      (realSpatialJet u 4 (t,x)) (realSpatialJet u 5 (t,x)) (realSpatialJet u 6 (t,x)) := by
  rw [show deriv (fun y => weightedP u a (t,y)) = _ from funext (weightedP_space hu a t)]
  exact (hasDerivAt_invariantPx a (realSpatialJet_hasDerivAt hu 2 t x)
    (realSpatialJet_hasDerivAt hu 3 t x) (realSpatialJet_hasDerivAt hu 4 t x)
    (realSpatialJet_hasDerivAt hu 5 t x)).deriv

theorem weightedQ_space (t x : ℝ) : deriv (fun y => weightedQ u (t,y)) x =
    invariantQx (realSpatialJet u 2 (t,x)) (realSpatialJet u 3 (t,x))
      (realSpatialJet u 4 (t,x)) (realSpatialJet u 5 (t,x)) (realSpatialJet u 6 (t,x)) := by
  exact ((hasDerivAt_invariantQ (realSpatialJet_hasDerivAt hu 2 t x)
    (realSpatialJet_hasDerivAt hu 3 t x) (realSpatialJet_hasDerivAt hu 4 t x)
    (realSpatialJet_hasDerivAt hu 5 t x)).congr_deriv (invariantQD_space ..)).deriv

theorem weightedQ_space_two (t x : ℝ) : deriv (deriv (fun y => weightedQ u (t,y))) x =
    invariantQxx (realSpatialJet u 2 (t,x)) (realSpatialJet u 3 (t,x))
      (realSpatialJet u 4 (t,x)) (realSpatialJet u 5 (t,x)) (realSpatialJet u 6 (t,x))
      (realSpatialJet u 7 (t,x)) := by
  rw [show deriv (fun y => weightedQ u (t,y)) = _ from funext (weightedQ_space hu t)]
  exact (hasDerivAt_invariantQx (realSpatialJet_hasDerivAt hu 2 t x)
    (realSpatialJet_hasDerivAt hu 3 t x) (realSpatialJet_hasDerivAt hu 4 t x)
    (realSpatialJet_hasDerivAt hu 5 t x) (realSpatialJet_hasDerivAt hu 6 t x)).deriv

theorem weightedR_space (a t x : ℝ) : deriv (fun y => weightedR u a (t,y)) x =
    invariantRx a (realSpatialJet u 2 (t,x)) (realSpatialJet u 3 (t,x))
      (realSpatialJet u 4 (t,x)) (realSpatialJet u 5 (t,x)) (realSpatialJet u 6 (t,x)) := by
  exact ((hasDerivAt_invariantR a (realSpatialJet_hasDerivAt hu 2 t x)
    (realSpatialJet_hasDerivAt hu 3 t x) (realSpatialJet_hasDerivAt hu 4 t x)
    (realSpatialJet_hasDerivAt hu 5 t x)).congr_deriv (invariantRD_space ..)).deriv

theorem weightedR_space_two (a t x : ℝ) : deriv (deriv (fun y => weightedR u a (t,y))) x =
    invariantRxx a (realSpatialJet u 2 (t,x)) (realSpatialJet u 3 (t,x))
      (realSpatialJet u 4 (t,x)) (realSpatialJet u 5 (t,x)) (realSpatialJet u 6 (t,x))
      (realSpatialJet u 7 (t,x)) := by
  rw [show deriv (fun y => weightedR u a (t,y)) = _ from funext (weightedR_space hu a t)]
  exact (hasDerivAt_invariantRx a (realSpatialJet_hasDerivAt hu 2 t x)
    (realSpatialJet_hasDerivAt hu 3 t x) (realSpatialJet_hasDerivAt hu 4 t x)
    (realSpatialJet_hasDerivAt hu 5 t x) (realSpatialJet_hasDerivAt hu 6 t x)).deriv
end Space

section Time
variable {u : ℝ × ℝ → ℝ} {a : ℝ}
  (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
  (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
    ((1/2:ℝ)*(spatialJet u 2 (t,x)+a*(spatialJet u 1 (t,x))^2)) t)
  {t x : ℝ} (ht : 0 < t)

include hu hPDE ht

local notation "j" => realSpatialJet u

theorem realJet_two_time : HasDerivAt (fun s => j 2 (s,x))
    (j 4 (t,x)/2+a*((j 2 (t,x))^2+j 1 (t,x)*j 3 (t,x))) t := by
  simpa only [realSpatialJet_eq_spatialJet hu ht,div_eq_mul_inv,one_mul,mul_comm] using
    realSpatialJet_time_transfer hu (x := x) ht 2 (spatialJet_two_timePDE hu hPDE ht)

theorem realJet_three_time : HasDerivAt (fun s => j 3 (s,x))
    (j 5 (t,x)/2+a*(3*j 2 (t,x)*j 3 (t,x)+j 1 (t,x)*j 4 (t,x))) t := by
  simpa only [realSpatialJet_eq_spatialJet hu ht,div_eq_mul_inv,one_mul,mul_comm] using
    realSpatialJet_time_transfer hu (x := x) ht 3 (spatialJet_three_timePDE hu hPDE ht)

theorem realJet_four_time : HasDerivAt (fun s => j 4 (s,x))
    (j 6 (t,x)/2+a*(3*(j 3 (t,x))^2+4*j 2 (t,x)*j 4 (t,x)+j 1 (t,x)*j 5 (t,x))) t := by
  simpa only [realSpatialJet_eq_spatialJet hu ht,div_eq_mul_inv,one_mul,mul_comm] using
    realSpatialJet_time_transfer hu (x := x) ht 4 (spatialJet_four_timePDE hu hPDE ht)

theorem realJet_five_time : HasDerivAt (fun s => j 5 (s,x))
    (j 7 (t,x)/2+a*(10*j 3 (t,x)*j 4 (t,x)+5*j 2 (t,x)*j 5 (t,x)+j 1 (t,x)*j 6 (t,x))) t := by
  simpa only [realSpatialJet_eq_spatialJet hu ht,div_eq_mul_inv,one_mul,mul_comm] using
    realSpatialJet_time_transfer hu (x := x) ht 5 (spatialJet_five_timePDE hu hPDE ht)

theorem weightedP_time (hs : ∀ k, SpatialRegular k u) (hh : j 2 (t,x) ≠ 0) :
    HasDerivAt (fun s => weightedP u a (s,x))
      (deriv (deriv (fun y => weightedP u a (t,y))) x/2+
        (a*j 1 (t,x)-j 3 (t,x)/j 2 (t,x))*deriv (fun y => weightedP u a (t,y)) x+
        (j 4 (t,x)/j 2 (t,x)+3*a*j 2 (t,x))*weightedP u a (t,x)) t := by
  rw [weightedP_space hs,weightedP_space_two hs]
  exact (hasDerivAt_invariantP a (realJet_two_time hu hPDE ht)
    (realJet_three_time hu hPDE ht) (realJet_four_time hu hPDE ht)).congr_deriv
      (invariantP_time_algebra a _ _ _ _ _ _ hh)

theorem weightedQ_time (hs : ∀ k, SpatialRegular k u) (hh : j 2 (t,x) ≠ 0) :
    HasDerivAt (fun s => weightedQ u (s,x))
      (deriv (deriv (fun y => weightedQ u (t,y))) x/2+
        (a*j 1 (t,x)-2*j 3 (t,x)/j 2 (t,x))*deriv (fun y => weightedQ u (t,y)) x+
        (4*j 4 (t,x)/j 2 (t,x)-(j 3 (t,x)/j 2 (t,x))^2+7*a*j 2 (t,x))*weightedQ u (t,x)-
        3*j 3 (t,x)*((j 3 (t,x))^2-j 2 (t,x)*j 4 (t,x))*weightedP u a (t,x)/(j 2 (t,x))^2) t := by
  rw [weightedQ_space hs,weightedQ_space_two hs]
  exact (hasDerivAt_invariantQ (realJet_two_time hu hPDE ht)
    (realJet_three_time hu hPDE ht) (realJet_four_time hu hPDE ht)
    (realJet_five_time hu hPDE ht)).congr_deriv (invariantQ_time_algebra a _ _ _ _ _ _ _ hh)

theorem weightedR_time (hs : ∀ k, SpatialRegular k u) (hh : j 2 (t,x) ≠ 0) :
    HasDerivAt (fun s => weightedR u a (s,x))
      (deriv (deriv (fun y => weightedR u a (t,y))) x/2+
        (a*j 1 (t,x)-2*j 3 (t,x)/j 2 (t,x))*deriv (fun y => weightedR u a (t,y)) x+
        (3*(j 3 (t,x)/j 2 (t,x))^2/4+9*j 4 (t,x)/(4*j 2 (t,x))+13*a*j 2 (t,x)/2)*weightedR u a (t,x)-
        weightedP u a (t,x)*weightedQ u (t,x)/(2*(j 2 (t,x))^2)+
        3*j 3 (t,x)*(weightedP u a (t,x))^2/(4*(j 2 (t,x))^2)) t := by
  rw [weightedR_space hs,weightedR_space_two hs]
  exact (hasDerivAt_invariantR a (realJet_two_time hu hPDE ht)
    (realJet_three_time hu hPDE ht) (realJet_four_time hu hPDE ht)
    (realJet_five_time hu hPDE ht)).congr_deriv (invariantR_time_algebra a _ _ _ _ _ _ _ hh)
end Time
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.scalarClockJet (J : HeatJet 0) (m : ℝ) (k : ℕ)
    (t : ℝ) (x : Fin 1 → ℝ) : ℝ := realSpatialJet (J.scalarClockPlane m) k (t,x 0)

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m)
include hG hm

theorem HeatJet.scalarClockJet_continuous (k : ℕ) :
    Continuous (fun p : ℝ × (Fin 1 → ℝ) => J.scalarClockJet m k p.1 p.2) :=
  (realSpatialJet_continuous (J.scalarClockPlane_spatialRegular hG hm) k).comp
    (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))

theorem HeatJet.scalarClockJet_bound (k : ℕ) :
    AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => J.scalarClockJet m (k+1) p.1 p.2) := by
  obtain ⟨K,hK,hb⟩ := J.scalarClockPlane_positiveJets_uniformBounded hG hm k
  exact ⟨K,hK,fun p => hb (p.1,p.2 0)⟩

theorem HeatJet.scalarClockJet_line (k : ℕ) (t : ℝ) (x v : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => J.scalarClockJet m k t (x+r • v))
      (∑ i, v i*J.scalarClockJet m (k+1) t (x+s • v)) s := by
  have hd := (realSpatialJet_hasDerivAt (J.scalarClockPlane_spatialRegular hG hm) k t (x 0+s*v 0)).comp s
    (((hasDerivAt_id s).mul_const (v 0)).const_add (x 0))
  convert hd using 1 <;> first | rfl | (simp only [Fin.sum_univ_one,HeatJet.scalarClockJet,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring)

theorem HeatJet.scalarClockJet_coord (k : ℕ) (t : ℝ) (i : Fin 1) (x : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => J.scalarClockJet m k t (x+r • Pi.single i 1))
      (J.scalarClockJet m (k+1) t (x+s • Pi.single i 1)) s := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa only [Fin.sum_univ_one,Pi.single_eq_same,one_mul] using J.scalarClockJet_line hG hm k t x (Pi.single 0 1) s

omit hG in
theorem HeatJet.scalarClockJet_one (t : ℝ) (x : Fin 1 → ℝ) :
    J.scalarClockJet m 1 t x = (J.evolve hm t).G 0 x := by
  have hx : (fun _ : Fin 1 => x 0) = x := by ext i; rw [Fin.eq_zero i]
  dsimp only [HeatJet.scalarClockJet,realSpatialJet]
  change deriv (fun y => (J.evolve hm t).F (fun _ => y)) (x 0) = _
  rw [((J.evolve hm t).scalar_derivF (x 0)).deriv,hx]

omit hG in
theorem HeatJet.scalarClockJet_two (t : ℝ) (x : Fin 1 → ℝ) :
    J.scalarClockJet m 2 t x = (J.evolve hm t).H 0 x := by
  have hx : (fun _ : Fin 1 => x 0) = x := by ext i; rw [Fin.eq_zero i]
  have he : (fun y => realSpatialJet (J.scalarClockPlane m) 1 (t,y)) =
      fun y => (J.evolve hm t).G 0 (fun _ => y) := funext (fun y => J.scalarClockJet_one hm t (fun _ => y))
  change deriv (fun y => realSpatialJet (J.scalarClockPlane m) 1 (t,y)) (x 0) = _
  rw [he,((J.evolve hm t).scalar_derivG (x 0)).deriv,hx]

noncomputable def HeatJet.scalarJetTest (k : ℕ) (t : ℝ) : HeatJet 0 :=
  { J.evolve hm t with
    A := J.scalarClockJet m (k+1) t
    A₁ := fun _ => J.scalarClockJet m (k+2) t
    A₂ := fun _ => J.scalarClockJet m (k+3) t
    smoothA := J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 k t
    smoothA₁ := fun _ => J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 (k+1) t
    smoothA₂ := fun _ => J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 (k+2) t
    derivA := J.scalarClockJet_line hG hm (k+1) t
    derivA₁ := J.scalarClockJet_coord hG hm (k+2) t }

noncomputable def HeatJet.scalarJetFamily (k : ℕ) : HeatJetFamily 0 :=
  { J.family hm with
    J := J.scalarJetTest hG hm k
    continuousA := J.scalarClockJet_continuous hG hm (k+1)
    continuousA₁ := fun _ => J.scalarClockJet_continuous hG hm (k+2)
    continuousA₂ := fun _ => J.scalarClockJet_continuous hG hm (k+3)
    boundedA := J.scalarClockJet_bound hG hm k
    boundedA₁ := fun _ => J.scalarClockJet_bound hG hm (k+1)
    boundedA₂ := fun _ => J.scalarClockJet_bound hG hm (k+2) }

end

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.scalarGapEnergy (J : HeatJet 0) (m T s : ℝ) (x : Fin 1 → ℝ) : ℝ :=
  clockTest m (clockContinuation m J.F (T-s))
    (fun y => (J.scalarClockJet m 2 (T-s) y)^2) s x

noncomputable def HeatJet.scalarGapCurvature (J : HeatJet 0) (m T s : ℝ) (x : Fin 1 → ℝ) : ℝ :=
  clockTest m (clockContinuation m J.F (T-s))
    (fun y => (J.scalarClockJet m 3 (T-s) y)^2-2*m*(J.scalarClockJet m 2 (T-s) y)^3) s x

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
  {m : ℝ} (hm : 0 < m)
include hG hH hm

private theorem ScalarGapEnergy_scalar_jet_two_time {t : ℝ} (ht : 0 < t) (x : Fin 1 → ℝ) :
    HasDerivAt (fun r => J.scalarClockJet m 2 r x)
      (J.scalarClockJet m 4 t x/2+m*((J.scalarClockJet m 2 t x)^2+
        J.scalarClockJet m 1 t x*J.scalarClockJet m 3 t x)) t :=
  realJet_two_time (J.scalarClockPlane_contDiffOn hG hH hm)
    (fun _ y hs => J.scalarClockPlane_timePDE hG hH hm hs y) ht

omit hH in
private theorem ScalarGapEnergy_scalar_energy_rate_algebra (t : ℝ) (y : Fin 1 → ℝ) :
    (J.scalarJetTest hG hm 1 t).square.testRate m y-
      2*(J.scalarClockJet m 2 t y*(J.scalarClockJet m 4 t y/2+
        m*((J.scalarClockJet m 2 t y)^2+J.scalarClockJet m 1 t y*J.scalarClockJet m 3 t y))) =
      (J.scalarClockJet m 3 t y)^2-2*m*(J.scalarClockJet m 2 t y)^3 := by
  dsimp only [HeatJet.testRate,HeatJet.scalarJetTest,HeatJet.square]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Nat.reduceAdd]
  rw [← J.scalarClockJet_one hm t y]
  ring

theorem HeatJet.hasDerivAt_scalarGapEnergy {T s : ℝ} (hs : s ∈ Ioo 0 T) (x : Fin 1 → ℝ) :
    HasDerivAt (fun r => J.scalarGapEnergy m T r x) (J.scalarGapCurvature m T s x) s := by
  let j := J.scalarClockJet m
  let B : ℝ → (Fin 1 → ℝ) → ℝ := fun t y => 2*(j 2 t y*(j 4 t y/2+m*((j 2 t y)^2+j 1 t y*j 3 t y)))
  have hc (k : ℕ) : Continuous (fun p : ℝ × (Fin 1 → ℝ) => j k p.1 p.2) :=
    J.scalarClockJet_continuous hG hm k
  have hb (k : ℕ) : AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => j (k+1) p.1 p.2) :=
    J.scalarClockJet_bound hG hm k
  have hcB : Continuous (fun p : ℝ × (Fin 1 → ℝ) => B p.1 p.2) :=
    ((hc 2).mul (((hc 4).div_const 2).add ((((hc 2).pow 2).add ((hc 1).mul (hc 3))).const_mul m))).const_mul 2
  have hbB : AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => B p.1 p.2) := by
    simpa only [B,pow_two,div_eq_mul_inv,one_mul,mul_comm,Nat.reduceAdd] using
      ((hb 1).mul (((hb 3).const_mul (1/2:ℝ)).add ((((hb 1).mul (hb 1)).add ((hb 0).mul (hb 2))).const_mul m))).const_mul 2
  have hsB (t : ℝ) : BddSmooth 0 (B t) := by
    have hb (k : ℕ) := J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 k t
    simpa only [B,j,HeatJet.scalarClockJet,pow_two,div_eq_mul_inv,one_mul,mul_comm,Nat.reduceAdd] using
      ((hb 1).mul (((hb 3).const_mul (1/2:ℝ)).add ((((hb 1).mul (hb 1)).add ((hb 0).mul (hb 2))).const_mul m))).const_mul 2
  let V := (J.scalarJetFamily hG hm 1).square
  have hdF : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun q => (V.J q).F y)
      ((V.J r).potentialRate m y) r := by
    intro r hr y
    exact J.evolve_time_F hm hr.1 y
  have hdA : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun q => (V.J q).A y) (B r y) r := by
    intro r hr y
    apply ((ScalarGapEnergy_scalar_jet_two_time J hG hH hm hr.1 y).pow 2).congr_deriv
    simp only [B,j,pow_one,Nat.reduceSub,Nat.cast_ofNat]
    ring
  have hd := V.hasDerivAt_backwardTest hcB hbB hsB hdF hdA hs x
  apply hd.congr_deriv
  change clockTest m _ (fun y => (J.scalarJetTest hG hm 1 (T-s)).square.testRate m y-B (T-s) y) s x = _
  have he : (fun y => (J.scalarJetTest hG hm 1 (T-s)).square.testRate m y-B (T-s) y) =
      fun y => (j 3 (T-s) y)^2-2*m*(j 2 (T-s) y)^3 := by
    funext y
    exact ScalarGapEnergy_scalar_energy_rate_algebra J hG hm (T-s) y
  rw [he]
  rfl

omit hH in
theorem HeatJet.continuous_scalarGapEnergy (T : ℝ) (x : Fin 1 → ℝ) :
    Continuous (fun s => J.scalarGapEnergy m T s x) := by
  let V := (J.scalarJetFamily hG hm 1).square
  obtain ⟨K,_,hK⟩ := V.boundedA
  exact (dynamic_clockTest_continuous V.lipschitz V.continuousF V.continuousA
    (fun t y => hK (t,y)) m x).comp (continuous_id.prodMk (continuous_const.sub continuous_id))

omit hH in
theorem HeatJet.continuous_scalarGapCurvature (T : ℝ) (x : Fin 1 → ℝ) :
    Continuous (fun s => J.scalarGapCurvature m T s x) := by
  let j := J.scalarClockJet m
  have hc (k : ℕ) := J.scalarClockJet_continuous hG hm k
  have hb (k : ℕ) := J.scalarClockJet_bound hG hm k
  have hcA : Continuous (fun p : ℝ × (Fin 1 → ℝ) => (j 3 p.1 p.2)^2-2*m*(j 2 p.1 p.2)^3) :=
    ((hc 3).pow 2).sub (((hc 2).pow 3).const_mul (2*m))
  have hbA : AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => (j 3 p.1 p.2)^2-2*m*(j 2 p.1 p.2)^3) := by
    simpa only [j,pow_two,pow_succ,pow_zero,mul_one,one_mul,Nat.reduceAdd] using
      ((hb 2).mul (hb 2)).sub ((((hb 1).mul (hb 1)).mul (hb 1)).const_mul (2*m))
  obtain ⟨K,_,hK⟩ := hbA
  exact (dynamic_clockTest_continuous (J.family hm).lipschitz (J.family hm).continuousF hcA
    (fun t y => hK (t,y)) m x).comp (continuous_id.prodMk (continuous_const.sub continuous_id))

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem BddSmooth.pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {f : E → ℝ} (hf : BddSmooth k f) (n : ℕ) : BddSmooth k (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using BddSmooth.const k (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem AbsBounded.pow {E : Type*} {f : E → ℝ} (hf : AbsBounded f) (n : ℕ) :
    AbsBounded (fun x => (f x)^n) := by
  obtain ⟨K,hK,hb⟩ := hf
  exact ⟨K^n,pow_nonneg hK _,fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x) n⟩

noncomputable def HeatJet.gapTest0 (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  (J.scalarClockJet m 3 t y)^2-2*m*(J.scalarClockJet m 2 t y)^3
noncomputable def HeatJet.gapTest1 (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  2*(J.scalarClockJet m 3 t y*J.scalarClockJet m 4 t y)-
    6*m*((J.scalarClockJet m 2 t y)^2*J.scalarClockJet m 3 t y)
noncomputable def HeatJet.gapTest2 (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  2*((J.scalarClockJet m 4 t y)^2+J.scalarClockJet m 3 t y*J.scalarClockJet m 5 t y)-
    12*m*(J.scalarClockJet m 2 t y*(J.scalarClockJet m 3 t y)^2)-
    6*m*((J.scalarClockJet m 2 t y)^2*J.scalarClockJet m 4 t y)
noncomputable def HeatJet.gapTimeTest (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  2*(J.scalarClockJet m 3 t y*(J.scalarClockJet m 5 t y/2+
    m*(3*(J.scalarClockJet m 2 t y*J.scalarClockJet m 3 t y)+J.scalarClockJet m 1 t y*J.scalarClockJet m 4 t y)))-
    6*m*((J.scalarClockJet m 2 t y)^2*(J.scalarClockJet m 4 t y/2+
      m*((J.scalarClockJet m 2 t y)^2+J.scalarClockJet m 1 t y*J.scalarClockJet m 3 t y)))
noncomputable def HeatJet.scalarGapThird (J : HeatJet 0) (m T s : ℝ) (x : Fin 1 → ℝ) : ℝ :=
  clockTest m (clockContinuation m J.F (T-s))
    (fun y => (J.scalarClockJet m 4 (T-s) y)^2-
      12*m*(J.scalarClockJet m 2 (T-s) y*(J.scalarClockJet m 3 (T-s) y)^2)+
      6*m^2*(J.scalarClockJet m 2 (T-s) y)^4) s x

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m)
include hG hm

private theorem ScalarGapThird_gap_smooth0 (t : ℝ) : BddSmooth 0 (J.gapTest0 m t) :=
  ((J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 2 t).pow 2).sub
    (((J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 1 t).pow 3).const_mul (2*m))
private theorem ScalarGapThird_gap_smooth1 (t : ℝ) : BddSmooth 0 (J.gapTest1 m t) := by
  have h (k) := J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 k t
  exact (((h 2).mul (h 3)).const_mul 2).sub ((((h 1).pow 2).mul (h 2)).const_mul (6*m))
private theorem ScalarGapThird_gap_smooth2 (t : ℝ) : BddSmooth 0 (J.gapTest2 m t) := by
  have h (k) := J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 k t
  exact (((((h 3).pow 2).add ((h 2).mul (h 4))).const_mul 2).sub
    (((h 1).mul ((h 2).pow 2)).const_mul (12*m))).sub ((((h 1).pow 2).mul (h 3)).const_mul (6*m))

noncomputable def HeatJet.gapJet (t : ℝ) : HeatJet 0 :=
  { J.evolve hm t with
    A := J.gapTest0 m t
    A₁ := fun _ => J.gapTest1 m t
    A₂ := fun _ => J.gapTest2 m t
    smoothA := ScalarGapThird_gap_smooth0 J hG hm t
    smoothA₁ := fun _ => ScalarGapThird_gap_smooth1 J hG hm t
    smoothA₂ := fun _ => ScalarGapThird_gap_smooth2 J hG hm t
    derivA := by
      intro x v s
      have h (k) := J.scalarClockJet_line hG hm k t x v s
      apply (((h 3).pow 2).sub (((h 2).pow 3).const_mul (2*m))).congr_deriv
      simp only [HeatJet.gapTest1,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,Nat.reduceAdd]
      ring
    derivA₁ := by
      intro i x s
      have h (k) := J.scalarClockJet_coord hG hm k t i x s
      apply ((((h 3).mul (h 4)).const_mul 2).sub ((((h 2).pow 2).mul (h 3)).const_mul (6*m))).congr_deriv
      simp only [Pi.pow_apply,HeatJet.gapTest2,Nat.cast_ofNat,Nat.reduceSub,pow_one,Nat.reduceAdd]
      ring }

noncomputable def HeatJet.gapFamily : HeatJetFamily 0 :=
  { J.family hm with
    J := J.gapJet hG hm
    continuousA := by
      have h (k) := J.scalarClockJet_continuous hG hm k
      exact ((h 3).pow 2).sub (((h 2).pow 3).const_mul (2*m))
    continuousA₁ := by
      intro i
      have h (k) := J.scalarClockJet_continuous hG hm k
      exact (((h 3).mul (h 4)).const_mul 2).sub ((((h 2).pow 2).mul (h 3)).const_mul (6*m))
    continuousA₂ := by
      intro i
      have h (k) := J.scalarClockJet_continuous hG hm k
      exact (((((h 4).pow 2).add ((h 3).mul (h 5))).const_mul 2).sub
        (((h 2).mul ((h 3).pow 2)).const_mul (12*m))).sub ((((h 2).pow 2).mul (h 4)).const_mul (6*m))
    boundedA := by
      have h (k) := J.scalarClockJet_bound hG hm k
      exact ((h 2).pow 2).sub (((h 1).pow 3).const_mul (2*m))
    boundedA₁ := by
      intro i
      have h (k) := J.scalarClockJet_bound hG hm k
      exact (((h 2).mul (h 3)).const_mul 2).sub ((((h 1).pow 2).mul (h 2)).const_mul (6*m))
    boundedA₂ := by
      intro i
      have h (k) := J.scalarClockJet_bound hG hm k
      exact (((((h 3).pow 2).add ((h 2).mul (h 4))).const_mul 2).sub
        (((h 1).mul ((h 2).pow 2)).const_mul (12*m))).sub ((((h 1).pow 2).mul (h 3)).const_mul (6*m)) }

private theorem ScalarGapThird_gap_time_smooth (t : ℝ) : BddSmooth 0 (J.gapTimeTest m t) := by
  have h (k) := J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 k t
  convert
    (((h 2).mul (((h 4).mul_const (2:ℝ)⁻¹).add
      ((((h 1).mul (h 2)).const_mul 3).add ((h 0).mul (h 3)) |>.const_mul m))).const_mul 2).sub
      ((((h 1).pow 2).mul (((h 3).mul_const (2:ℝ)⁻¹).add
        (((h 1).pow 2).add ((h 0).mul (h 2)) |>.const_mul m))).const_mul (6*m)) using 1
  ext x
  dsimp only [HeatJet.gapTimeTest,HeatJet.scalarClockJet]
  ring

private theorem ScalarGapThird_gap_time_continuous : Continuous (fun p : ℝ × (Fin 1 → ℝ) => J.gapTimeTest m p.1 p.2) := by
  have h (k) := J.scalarClockJet_continuous hG hm k
  exact (((h 3).mul (((h 5).div_const 2).add
    ((((h 2).mul (h 3)).const_mul 3).add ((h 1).mul (h 4)) |>.const_mul m))).const_mul 2).sub
      ((((h 2).pow 2).mul (((h 4).div_const 2).add
        (((h 2).pow 2).add ((h 1).mul (h 3)) |>.const_mul m))).const_mul (6*m))

private theorem ScalarGapThird_gap_time_bounded : AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => J.gapTimeTest m p.1 p.2) := by
  have h (k) := J.scalarClockJet_bound hG hm k
  simpa only [HeatJet.gapTimeTest,div_eq_mul_inv,one_mul,mul_comm,Nat.reduceAdd] using
    (((h 2).mul (((h 4).const_mul (2:ℝ)⁻¹).add
      ((((h 1).mul (h 2)).const_mul 3).add ((h 0).mul (h 3)) |>.const_mul m))).const_mul 2).sub
      ((((h 1).pow 2).mul (((h 3).const_mul (2:ℝ)⁻¹).add
        (((h 1).pow 2).add ((h 0).mul (h 2)) |>.const_mul m))).const_mul (6*m))

private theorem ScalarGapThird_gap_third_cancellation (t : ℝ) (y : Fin 1 → ℝ) :
    (J.gapJet hG hm t).testRate m y-J.gapTimeTest m t y =
      (J.scalarClockJet m 4 t y)^2-12*m*(J.scalarClockJet m 2 t y*(J.scalarClockJet m 3 t y)^2)+
        6*m^2*(J.scalarClockJet m 2 t y)^4 := by
  dsimp only [HeatJet.testRate,HeatJet.gapJet]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rw [← J.scalarClockJet_one hm t y]
  unfold HeatJet.gapTest2 HeatJet.gapTest1 HeatJet.gapTimeTest
  ring

theorem HeatJet.hasDerivAt_scalarGapCurvature (hH : ∀ k i, BddSmooth k (J.H i))
    {T s : ℝ} (hs : s ∈ Ioo 0 T) (x : Fin 1 → ℝ) :
    HasDerivAt (fun r => J.scalarGapCurvature m T r x) (J.scalarGapThird m T s x) s := by
  let V := J.gapFamily hG hm
  have hdF : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun q => (V.J q).F y)
      ((V.J r).potentialRate m y) r := by
    intro r hr y
    exact J.evolve_time_F hm hr.1 y
  have hdA : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun q => (V.J q).A y) (J.gapTimeTest m r y) r := by
    intro r hr y
    have h2 := realJet_two_time (J.scalarClockPlane_contDiffOn hG hH hm)
      (fun _ z hz => J.scalarClockPlane_timePDE hG hH hm hz z) (x := y 0) hr.1
    have h3 := realJet_three_time (J.scalarClockPlane_contDiffOn hG hH hm)
      (fun _ z hz => J.scalarClockPlane_timePDE hG hH hm hz z) (x := y 0) hr.1
    apply ((h3.pow 2).sub ((h2.pow 3).const_mul (2*m))).congr_deriv
    dsimp only [HeatJet.gapTimeTest,HeatJet.scalarClockJet]
    simp only [Nat.reduceSub,Nat.cast_ofNat,pow_one]
    ring
  have hd := V.hasDerivAt_backwardTest (ScalarGapThird_gap_time_continuous J hG hm)
    (ScalarGapThird_gap_time_bounded J hG hm) (ScalarGapThird_gap_time_smooth J hG hm) hdF hdA hs x
  apply hd.congr_deriv
  change clockTest m _ (fun y => (J.gapJet hG hm (T-s)).testRate m y-J.gapTimeTest m (T-s) y) s x = _
  simp_rw [ScalarGapThird_gap_third_cancellation J hG hm]
  rfl

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology

section
variable {ρ : ℝ → ℝ} (hρ : Integrable ρ)
include hρ

 theorem weighted_bounded_integrable {f : ℝ → ℝ} (hc : Continuous f) (hb : AbsBounded f) :
    Integrable (fun x => ρ x*f x) := by
  obtain ⟨K,_,hK⟩ := hb
  exact hρ.mul_bdd hc.aestronglyMeasurable (ae_of_all _ fun x => hK x)

 theorem weighted_bounded_continuous {f : ℝ → ℝ → ℝ}
    (hc : ∀ s, Continuous (f s)) (ht : ∀ x, Continuous (fun s => f s x))
    (hb : AbsBounded (fun p : ℝ × ℝ => f p.1 p.2)) :
    Continuous (fun s => ∫ x, ρ x*f s x) := by
  obtain ⟨K,_,hK⟩ := hb
  apply continuous_of_dominated (bound := fun x => |ρ x| *K)
  · intro s
    exact hρ.aestronglyMeasurable.mul (hc s).aestronglyMeasurable
  · intro s
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,abs_mul] using
      mul_le_mul_of_nonneg_left (hK (s,x)) (abs_nonneg (ρ x))
  · exact hρ.abs.mul_const K
  · exact ae_of_all _ fun x => continuous_const.mul (ht x)

 theorem weighted_bounded_hasDerivAt {f g : ℝ → ℝ → ℝ} {a b s : ℝ}
    (hs : s ∈ Ioo a b) (hf : ∀ t, Continuous (f t)) (hg : ∀ t, Continuous (g t))
    (hfb : AbsBounded (f s)) (hgb : AbsBounded (fun p : ℝ × ℝ => g p.1 p.2))
    (hd : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r => f r x) (g t x) t) :
    HasDerivAt (fun t => ∫ x, ρ x*f t x) (∫ x, ρ x*g s x) s := by
  obtain ⟨K,_,hK⟩ := hgb
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo a b) (bound := fun x => |ρ x| *K) (Ioo_mem_nhds hs.1 hs.2)
    _ (weighted_bounded_integrable hρ (hf s) hfb) _ _ (hρ.abs.mul_const K) _).2
  · exact Eventually.of_forall fun t => hρ.aestronglyMeasurable.mul (hf t).aestronglyMeasurable
  · exact hρ.aestronglyMeasurable.mul (hg s).aestronglyMeasurable
  · filter_upwards [] with x t ht
    simpa only [Real.norm_eq_abs,abs_mul] using
      mul_le_mul_of_nonneg_left (hK (t,x)) (abs_nonneg (ρ x))
  · exact ae_of_all _ fun x t ht => (hd t ht x).const_mul (ρ x)
end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Set

theorem realSpatialJet_parity {u : ℝ × ℝ → ℝ} (hu : ∀ k, SpatialRegular k u)
    (he : ∀ t x, u (t,-x) = u (t,x)) (k : ℕ) (t x : ℝ) :
    realSpatialJet u k (t,-x) = (-1:ℝ)^k*realSpatialJet u k (t,x) := by
  induction k generalizing x with
  | zero => simpa only [realSpatialJet,pow_zero,one_mul] using he t x
  | succ k ih =>
    have hf : (fun y => realSpatialJet u k (t,-y)) =
        fun y => (-1:ℝ)^k*realSpatialJet u k (t,y) := funext ih
    have hd := (realSpatialJet_hasDerivAt hu k t (-x)).comp x (hasDerivAt_neg x)
    have hr := (realSpatialJet_hasDerivAt hu k t x).const_mul ((-1:ℝ)^k)
    change HasDerivAt (fun y => realSpatialJet u k (t,-y)) _ x at hd
    rw [hf] at hd
    have hh := hd.unique hr
    simp only [mul_neg_one] at hh
    rw [pow_succ]
    nlinarith
end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem HeatJet.filledEnergy_eq_scalarGapEnergy (J : HeatJet 0)
    (hA : J.A = J.G 0) (hA₁ : J.A₁ 0 = J.H 0) {m : ℝ} (hm : 0 < m)
    (T s : ℝ) (x : Fin 1 → ℝ) :
    J.filledEnergy hm T s x = J.scalarGapEnergy m T s x := by
  unfold HeatJet.filledEnergy HeatJet.scalarGapEnergy HeatJet.energy
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,J.scalarClockJet_two hm]
  congr 2
  funext y
  change (clockGradient m J.F (J.G 0) J.A (J.A₁ 0) (T-s) y)^2 = _
  rw [hA,hA₁]
  rfl

theorem HeatJet.hasDerivWithinAt_scalarGapEnergy_zero (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m T : ℝ} (hm : 0 < m) (hT : 0 < T) (x : Fin 1 → ℝ) :
    HasDerivWithinAt (fun s => J.scalarGapEnergy m T s x)
      (J.scalarGapCurvature m T 0 x) (Ici 0) 0 := by
  have hn : Ioo (0:ℝ) T ∈ nhdsWithin 0 (Ioi 0) :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hT))
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 T)
  · intro s hs
    exact (J.hasDerivAt_scalarGapEnergy hG hH hm hs x).differentiableAt.differentiableWithinAt
  · exact (J.continuous_scalarGapEnergy hG hm T x).continuousAt.continuousWithinAt
  · exact hn
  · apply ((J.continuous_scalarGapCurvature hG hm T x).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr'
    filter_upwards [hn] with s hs
    exact (J.hasDerivAt_scalarGapEnergy hG hH hm hs x).deriv.symm

theorem HeatJet.scalarGapCurvature_zero (J : HeatJet 0) (m T : ℝ) (x : Fin 1 → ℝ) :
    J.scalarGapCurvature m T 0 x = (J.scalarClockJet m 3 T x)^2-2*m*(J.scalarClockJet m 2 T x)^3 := by
  simp only [HeatJet.scalarGapCurvature,sub_zero,clockTest_zero]

theorem HeatJet.scalarClockJet_odd_zero (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (he : ∀ x, J.F (-x) = J.F x)
    {m : ℝ} (hm : 0 < m) (t : ℝ) : J.scalarClockJet m 3 t 0 = 0 := by
  have hf : ∀ r x, J.scalarClockPlane m (r,-x) = J.scalarClockPlane m (r,x) := by
    intro r x
    exact clockContinuation_even he m r (fun _ => x)
  have hh := realSpatialJet_parity (J.scalarClockPlane_spatialRegular hG hm) hf 3 t 0
  norm_num at hh
  change realSpatialJet (J.scalarClockPlane m) 3 (t,0) = 0
  linarith

section Profile
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)

private theorem ScalarGapEndpoint_profG (k : ℕ) (i : Fin 1) : BddSmooth k ((scalarProfileHeatJet α hα l t).G i) :=
  scalarProfileJet_bddSmooth_all α hα l t k 0
private theorem ScalarGapEndpoint_profH (k : ℕ) (i : Fin 1) : BddSmooth k ((scalarProfileHeatJet α hα l t).H i) :=
  scalarProfileJet_bddSmooth_all α hα l t k 1

theorem scalarProfileGap_hasDerivAt {m T s : ℝ} (hm : 0 < m) (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => (scalarProfileHeatJet α hα l t).filledSquare hm T r 0)
      ((scalarProfileHeatJet α hα l t).scalarGapEnergy m T s 0) s := by
  rw [← (scalarProfileHeatJet α hα l t).filledEnergy_eq_scalarGapEnergy rfl rfl hm]
  exact (scalarProfileHeatJet α hα l t).hasDerivAt_filledSquare hm hs 0

theorem scalarProfileGapEnergy_hasDerivAt {m T s : ℝ} (hm : 0 < m) (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => (scalarProfileHeatJet α hα l t).scalarGapEnergy m T r 0)
      ((scalarProfileHeatJet α hα l t).scalarGapCurvature m T s 0) s :=
  (scalarProfileHeatJet α hα l t).hasDerivAt_scalarGapEnergy (ScalarGapEndpoint_profG α hα l t) (ScalarGapEndpoint_profH α hα l t) hm hs 0

theorem scalarProfileGap_initial_curvature {m T : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hT : 0 ≤ T) :
    (scalarProfileHeatJet α hα l t).scalarGapCurvature m T 0 0 < 0 := by
  let J := scalarProfileHeatJet α hα l t
  have he : ∀ x, J.F (-x) = J.F x := fun x => scalarProfileJet_zero_even α hα l t (x 0)
  have hodd := J.scalarClockJet_odd_zero (ScalarGapEndpoint_profG α hα l t) he hm T
  have had : J.ScalarAdmissible := fun x => scalarProfileJet_admissible α hα l t (x 0)
  have hl : ∀ x, Real.exp (-4*(t:ℝ))*Scalar.curvature (x 0) ≤ J.H 0 x :=
    fun x => scalarProfileJet_curvature_lower α hα l t (x 0)
  have hb := HeatJet.evolve_curvature_lower had hm hm1 (Real.exp_pos _).le hl hT (0 : Fin 1 → ℝ)
  have hp : 0 < J.scalarClockJet m 2 T 0 := by
    rw [J.scalarClockJet_two hm]
    exact lt_of_lt_of_le (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Scalar.curvature_pos 0)) hb
  rw [J.scalarGapCurvature_zero,hodd,zero_pow (by norm_num : 2 ≠ 0)]
  nlinarith [pow_pos hp 3]

end Profile
end SKFluctuations.Hierarchy

end

end OAI
