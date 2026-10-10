import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.TreeCenter2
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphPerp2

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

noncomputable def classConditional (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (P : CellPath d) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (ρ (treeCell P)).toNNReal⁻¹ • ρ.restrict (treeCell P)

instance classConditional_finite (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) : IsFiniteMeasure (classConditional ρ P) := by
  unfold classConditional
  infer_instance

lemma classConditional_probability (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) (hP : 0 < ρ (treeCell P)) :
    IsProbabilityMeasure (classConditional ρ P) := by
  constructor
  simp only [classConditional, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, Measure.restrict_apply_univ]
  rw [ENNReal.coe_inv (ENNReal.toNNReal_ne_zero.mpr ⟨ne_of_gt hP,measure_ne_top ρ _⟩),
    ENNReal.coe_toNNReal (measure_ne_top ρ _),
    ENNReal.inv_mul_cancel (ne_of_gt hP) (measure_ne_top ρ _)]

noncomputable def adjustedProfile (m : ℝ → ℝ) (N : ℕ) (n : ℕ) : ℝ :=
  m n-(d:ℝ)/2*(n:ℝ)/N

noncomputable def testWidth (N J i n : ℕ) (sig : ℝ) : ℝ :=
  (2-(i:ℝ)/J)*(2:ℝ)^(-(n:ℝ))*((2:ℝ)^N)^(500*sig)

noncomputable def fullParallelCount (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℕ :=
  ((dyadicPaths p).filter fun Q => 0 < ρ (treeCell Q) ∧
    dist (treeCenter Q) (treeCenter P) < 10*(d+1)/(2:ℝ)^g ∧
    ‖graphPerpND w (treeCenter Q-treeCenter P)‖ ≤ W).card

lemma fullParallelCount_actual_line (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖=1) :
    fullParallelCount ρ g p P W w =
      ((dyadicPaths p).filter fun Q => 0 < ρ (treeCell Q) ∧
        dist (treeCenter Q) (treeCenter P) < 10*(d+1)/(2:ℝ)^g ∧
        infDist (treeCenter Q) (graphAffineLineND w (treeCenter P)) ≤ W).card := by
  simp only [fullParallelCount,infDist_graphAffineLineND w _ _ hw]

lemma measurable_fullParallelCount (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) (W : ℝ) : Measurable (fullParallelCount ρ g p P W) := by
  classical
  have he : fullParallelCount ρ g p P W = fun w =>
      ∑ Q ∈ dyadicPaths p, if 0 < ρ (treeCell Q) ∧
        dist (treeCenter Q) (treeCenter P) < 10*(d+1)/(2:ℝ)^g ∧
        ‖graphPerpND w (treeCenter Q-treeCenter P)‖ ≤ W then (1:ℕ) else 0 := by
    funext w
    simp only [fullParallelCount,Finset.card_filter]
  rw [he]
  apply Finset.measurable_sum
  intro Q hQ
  apply Measurable.ite _ measurable_const measurable_const
  unfold graphPerpND
  by_cases h₁ : 0 < ρ (treeCell Q)
  · by_cases h₂ : dist (treeCenter Q) (treeCenter P) < 10*(d+1)/(2:ℝ)^g
    · simp only [h₁,h₂,true_and]
      exact measurableSet_le (by fun_prop) measurable_const
    · simp [h₂]
  · simp [h₁]

noncomputable def fullProjectionCollision (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (P : CellPath d) (W : ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ((classConditional ρ P).prod (classConditional ρ P))
    {xy | |inner ℝ (xy.1-xy.2) w| ≤ W}

lemma measurable_fullProjectionCollision (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) (W : ℝ) :
    Measurable (fullProjectionCollision ρ P W) := by
  exact measurable_measure_prodMk_left (show MeasurableSet
    {z : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) |
      |inner ℝ (z.2.1-z.2.2) z.1| ≤ W} from by measurability)

noncomputable def descriptorGood (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d) :
    PolicyDescriptor → Set (EuclideanSpace ℝ (Fin d))
  | .parallel g p => {w | ‖w‖=1 ∧
      (fullParallelCount ρ g p P (testWidth N J i p sig) w:ℝ) ≤
        ((2:ℝ)^N)^(height (adjustedProfile (d := d) m N) g p+C*sig)}
  | .projection p t => {w | ‖w‖=1 ∧
      fullProjectionCollision ρ P (testWidth N J i t sig) w ≤
        ENNReal.ofReal ((2:ℝ)^(-((t:ℝ)-p))*
          ((2:ℝ)^N)^((adjustedProfile (d := d) m N) p-
            intervalMin (adjustedProfile (d := d) m N) p t+C*sig))}

lemma measurable_descriptorGood (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ)
    (P : CellPath d) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGood ρ m N sig C J i P b) := by
  cases b with
  | parallel g p =>
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_le ((measurable_of_countable (fun a : ℕ => (a:ℝ))).comp
        (measurable_fullParallelCount ρ g p P _)) measurable_const)
  | projection p t =>
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_le (measurable_fullProjectionCollision ρ P _) measurable_const)

noncomputable def radialVector (x y : EuclideanSpace ℝ (Fin d)) := ‖x-y‖⁻¹ • (x-y)

lemma norm_radialVector {x y : EuclideanSpace ℝ (Fin d)} (hxy : x ≠ y) :
    ‖radialVector x y‖=1 := by
  rw [radialVector,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]

@[fun_prop] lemma measurable_radialVector : Measurable
    (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => radialVector z.1 z.2) := by
  unfold radialVector
  fun_prop

noncomputable def endpointGood (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {z | ∀ P ∈ dyadicPaths (descriptorAnchor b), z.1 ∈ treeCell P →
    z.2 ∈ descriptorGood ρ m N sig C J i P b}

lemma measurable_endpointGood (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    MeasurableSet (endpointGood ρ m N sig C J i b) := by
  simp only [endpointGood,ofPred_forall]
  apply MeasurableSet.iInter
  intro P
  apply MeasurableSet.iInter
  intro hP
  exact ((measurableSet_treeCell P).preimage measurable_fst).himp
    ((measurable_descriptorGood ρ m N sig C J i P b).preimage measurable_snd)

noncomputable def distanceGood (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N q a t : ℕ) (sig C : ℝ) (J i : ℕ) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {z | ∀ b ∈ policyDescriptorList (adjustedProfile (d := d) m N) N q a t,
    (z.1,radialVector z.1 z.2) ∈ endpointGood ρ m N sig C J i b ∧
    (z.2,radialVector z.1 z.2) ∈ endpointGood ρ m N sig C J i b}

lemma measurable_distanceGood (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N q a t : ℕ) (sig C : ℝ) (J i : ℕ) :
    MeasurableSet (distanceGood ρ m N q a t sig C J i) := by
  simp only [distanceGood,ofPred_forall]
  apply Finset.measurableSet_biInter
  intro b hb
  exact ((measurable_endpointGood ρ m N sig C J i b).preimage
      (measurable_fst.prodMk measurable_radialVector)).inter
    ((measurable_endpointGood ρ m N sig C J i b).preimage
      (measurable_snd.prodMk measurable_radialVector))

structure PositiveDistanceState (d : ℕ) where
  ρ : Measure (EuclideanSpace ℝ (Fin d))
  mass : ℝ → ℝ
  (N q a t J i : ℕ)
  (sig C : ℝ)
  (X Y : CellPath d)

namespace PositiveDistanceState
variable (e : PositiveDistanceState d)

noncomputable def good := distanceGood e.ρ e.mass e.N e.q e.a e.t e.sig e.C e.J e.i
noncomputable def cellPair := (e.ρ.restrict (treeCell e.X)).prod (e.ρ.restrict (treeCell e.Y))
noncomputable def pair := e.cellPair.restrict e.good
noncomputable def distance : Measure ℝ := Measure.map (fun z => dist z.1 z.2) e.pair
noncomputable def levelMass : ℝ := ((2:ℝ)^e.N)^(-e.mass e.a)
noncomputable def normalization : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^((e.t:ℝ)-e.a)/e.levelMass^4)
noncomputable def width : ℝ := (2:ℝ)^(-(e.t:ℝ))
noncomputable def coincidence : ℝ≥0∞ := e.normalization*(e.pair.prod e.pair)
  {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*(d+1)*e.width}

instance cellPair_finite [IsFiniteMeasure e.ρ] : IsFiniteMeasure e.cellPair := by
  unfold cellPair; infer_instance
instance pair_finite [IsFiniteMeasure e.ρ] : IsFiniteMeasure e.pair := by
  unfold pair; infer_instance
instance distance_finite [IsFiniteMeasure e.ρ] : IsFiniteMeasure e.distance := by
  unfold distance; infer_instance

lemma measurable_good [IsFiniteMeasure e.ρ] : MeasurableSet e.good :=
  measurable_distanceGood _ _ _ _ _ _ _ _ _ _

lemma distance_apply [IsFiniteMeasure e.ρ] {S : Set ℝ} (hS : MeasurableSet S) :
    e.distance S = e.cellPair {z | dist z.1 z.2 ∈ S ∧ z ∈ e.good} := by
  rw [distance,Measure.map_apply (continuous_fst.dist continuous_snd).measurable hS,
    pair,Measure.restrict_apply ((continuous_fst.dist continuous_snd).measurable hS)]
  rfl

lemma distance_collision [IsFiniteMeasure e.ρ] (w : ℝ) :
    (e.distance.prod e.distance) {z : ℝ × ℝ | |z.1-z.2| ≤ w} =
      (e.pair.prod e.pair) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} := by
  rw [distance,Measure.map_prod_map _ _ (continuous_fst.dist continuous_snd).measurable
    (continuous_fst.dist continuous_snd).measurable,
    Measure.map_apply (by fun_prop) (by measurability)]
  rfl

lemma coincidence_four_point [IsFiniteMeasure e.ρ] :
    e.coincidence = e.normalization*(e.cellPair.prod e.cellPair)
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*(d+1)*e.width ∧
        z.1 ∈ e.good ∧ z.2 ∈ e.good} := by
  rw [coincidence,pair,Measure.prod_restrict,Measure.restrict_apply (by measurability)]
  rfl

lemma coincidence_ne_top [IsFiniteMeasure e.ρ] : e.coincidence ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

end PositiveDistanceState

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

lemma RegularizedProfileData.normalized_cell_mass_le
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} {N B : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (hd : RegularizedProfileData ρ N B s lam m) {a : ℕ} (ha : a ≤ N)
    {P : CellPath d} (hP : P.length = a) :
    (ρ (treeCell P)).toReal/((2:ℝ)^N)^(-m a) ≤ ((2:ℝ)^N)^((d+1:ℝ)*lam) := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
  by_cases hp : 0 < ρ (treeCell P)
  · exact (hd.cells a ha P hP hp).2
  · have hz : ρ (treeCell P) = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz,ENNReal.toReal_zero]
    positivity

namespace PositiveDistanceState
variable (e : PositiveDistanceState d)

lemma normalized_cellPair_mass [IsFiniteMeasure e.ρ] :
    e.levelMass^(-2:ℤ)*e.cellPair.real univ =
      ((e.ρ (treeCell e.X)).toReal/e.levelMass)*
      ((e.ρ (treeCell e.Y)).toReal/e.levelMass) := by
  have hp : e.cellPair univ = e.ρ (treeCell e.X)*e.ρ (treeCell e.Y) := by
    unfold cellPair
    rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
  rw [measureReal_def,hp,ENNReal.toReal_mul]
  simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
  ring

lemma normalized_cellPair_profile_mass {B : ℕ} {s lam : ℝ}
    (hd : RegularizedProfileData e.ρ e.N B s lam e.mass)
    (ha : e.a ≤ e.N) (hX : e.X.length=e.a) (hY : e.Y.length=e.a) :
    e.levelMass^(-2:ℤ)*e.cellPair.real univ ≤ ((2:ℝ)^e.N)^(2*(d+1:ℝ)*lam) := by
  let := hd.probability
  rw [e.normalized_cellPair_mass]
  have h := mul_le_mul (hd.normalized_cell_mass_le ha hX)
    (hd.normalized_cell_mass_le ha hY) (by positivity) (by positivity)
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^e.N)] at h
  convert h using 1 <;> congr 1
  ring

lemma coincidence_trivial_profile_bound {B : ℕ} {s lam : ℝ}
    (hd : RegularizedProfileData e.ρ e.N B s lam e.mass)
    (ha : e.a ≤ e.N) (hX : e.X.length=e.a) (hY : e.Y.length=e.a) :
    e.coincidence.toReal ≤ (2:ℝ)^((e.t:ℝ)-e.a)*((2:ℝ)^e.N)^(4*(d+1:ℝ)*lam) := by
  let := hd.probability
  have hmass := e.normalized_cellPair_profile_mass hd ha hX hY
  have hquad : (e.cellPair.prod e.cellPair) univ = e.cellPair univ*e.cellPair univ := by
    rw [← univ_prod_univ,Measure.prod_prod]
  have hc : e.coincidence.toReal ≤ e.normalization.toReal*(e.cellPair.real univ)^2 := by
    rw [e.coincidence_four_point,ENNReal.toReal_mul]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc
      _ ≤ ((e.cellPair.prod e.cellPair) univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
      _ = _ := by rw [hquad,ENNReal.toReal_mul]; simp only [pow_two,measureReal_def]
  have he : e.normalization.toReal*(e.cellPair.real univ)^2 =
      (2:ℝ)^((e.t:ℝ)-e.a)*(e.levelMass^(-2:ℤ)*e.cellPair.real univ)^2 := by
    rw [normalization,ENNReal.toReal_ofReal (by positivity)]
    simp only [zpow_neg,zpow_ofNat]
    field_simp
  have hp := pow_le_pow_left₀ (show 0 ≤ e.levelMass^(-2:ℤ)*e.cellPair.real univ by positivity) hmass 2
  have hr : (((2:ℝ)^e.N)^(2*(d+1:ℝ)*lam))^2 = ((2:ℝ)^e.N)^(4*(d+1:ℝ)*lam) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (2:ℝ)^e.N)]
    congr 1
    norm_num
    ring
  rw [hr] at hp
  exact hc.trans (he.trans_le (mul_le_mul_of_nonneg_left hp (by positivity)))

lemma actual_distance_terminal {B : ℕ} {s lam : ℝ}
    (hd : RegularizedProfileData e.ρ e.N B s lam e.mass)
    (ha : e.a ≤ e.N) (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (ht : e.t ≤ e.a+100*e.q) :
    e.coincidence.toReal ≤ (2:ℝ)^(100*(e.q:ℝ))*((2:ℝ)^e.N)^(4*(d+1:ℝ)*lam) := by
  have htR : (e.t:ℝ) ≤ (e.a:ℝ)+100*e.q := by exact_mod_cast ht
  have he : (2:ℝ)^((e.t:ℝ)-e.a) ≤ (2:ℝ)^(100*(e.q:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact (e.coincidence_trivial_profile_bound hd ha hX hY).trans
    (mul_le_mul_of_nonneg_right he (by positivity))

lemma actual_distance_terminal_rpow {B : ℕ} {s lam : ℝ}
    (hd : RegularizedProfileData e.ρ e.N B s lam e.mass)
    (hN : 0 < e.N) (ha : e.a ≤ e.N) (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (ht : e.t ≤ e.a+100*e.q) :
    e.coincidence.toReal ≤ ((2:ℝ)^e.N)^(100*(e.q:ℝ)/e.N+4*(d+1:ℝ)*lam) := by
  apply (e.actual_distance_terminal hd ha hX hY ht).trans_eq
  rw [Real.rpow_add (by positivity)]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  have hn : (e.N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp

end PositiveDistanceState

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
