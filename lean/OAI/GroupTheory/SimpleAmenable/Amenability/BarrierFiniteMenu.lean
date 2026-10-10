import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.JointBitField
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierSignalSystem
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ChartBoundaryEndpoints

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierFiniteMenu
open Classical Set

noncomputable def barrierChartCuts {a m : ℕ} (g : polygonFullGroup a m) (i : Fin m) : Finset PlaneCut :=
  (fullGroupAffineData_arrangement g i).choose

theorem barrierChartCuts_spec {a m : ℕ} (g : polygonFullGroup a m) (i : Fin m) :
    ∀p q,(∀l ∈ barrierChartCuts g i,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q :=
  (fullGroupAffineData_arrangement g i).choose_spec

theorem barrier_uniform_constants {a m : ℕ} (F : Finset (polygonFullGroup a m)) :
    ∃Q B : ℝ,0 ≤ Q ∧ 0 ≤ B ∧ ∀g ∈ F,∀i (p : GenericSquare a),
      (∀j,|conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| ≤ Q) ∧
      (∀l ∈ barrierChartCuts g i ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
        |conjugate (l.2+integralCutForm a l.1 (fullGroupAffineData g i p).2)| ≤ B) := by
  let R (g : polygonFullGroup a m) (i : Fin m) :=
    (squareArrangement_finite_range (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i)).toFinset
  let C (g : polygonFullGroup a m) (i : Fin m) : ℝ := ∑d ∈ R g i,∑j : Fin 4,|conjugate (integralCutForm a j d.2)|
  have hC (g : polygonFullGroup a m) (i : Fin m) : 0 ≤ C g i :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  let Q : ℝ := ∑g ∈ F,∑i,C g i
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun g _ => Finset.sum_nonneg (fun i _ => hC g i))
  have hshift (g : polygonFullGroup a m) (hg : g ∈ F) (i : Fin m) (p : GenericSquare a) (j : Fin 4) :
      |conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| ≤ Q := by
    have hd : fullGroupAffineData g i p ∈ R g i := (Set.Finite.mem_toFinset _).mpr ⟨p,rfl⟩
    calc
      _ ≤ ∑j : Fin 4,|conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| :=
        Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ C g i := by
        dsimp [C]
        exact Finset.single_le_sum (s := R g i) (f := fun d : Fin m × (CutRing × CutRing) => ∑j : Fin 4, |conjugate (integralCutForm a j d.2)|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hd
      _ ≤ ∑i,C g i := Finset.single_le_sum (fun i _ => hC g i) (Finset.mem_univ i)
      _ ≤ Q := Finset.single_le_sum (fun g _ => Finset.sum_nonneg (fun i _ => hC g i)) hg
  let D (g : polygonFullGroup a m) (i : Fin m) : ℝ := ∑l ∈ barrierChartCuts g i ∪ squareBoundaryCuts,|conjugate l.2|
  have hD (g : polygonFullGroup a m) (i : Fin m) : 0 ≤ D g i := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let L : ℝ := ∑g ∈ F,∑i,D g i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun g _ => Finset.sum_nonneg (fun i _ => hD g i))
  have hlevel (g : polygonFullGroup a m) (hg : g ∈ F) (i : Fin m)
      (l : PlaneCut) (hl : l ∈ barrierChartCuts g i ∪ squareBoundaryCuts) : |conjugate l.2| ≤ L := by
    calc
      _ ≤ D g i := Finset.single_le_sum (fun _ _ => abs_nonneg _) hl
      _ ≤ ∑i,D g i := Finset.single_le_sum (fun i _ => hD g i) (Finset.mem_univ i)
      _ ≤ L := Finset.single_le_sum (fun g _ => Finset.sum_nonneg (fun i _ => hD g i)) hg
  refine ⟨Q,L+Q,hQ,add_nonneg hL hQ,?_⟩
  intro g hg i p
  refine ⟨hshift g hg i p,?_⟩
  intro l hl
  refine ⟨by linarith [hlevel g hg i l hl],?_⟩
  rw [map_add]
  exact (abs_add_le _ _).trans (add_le_add (hlevel g hg i l hl) (hshift g hg i p l.1))

structure BarrierMenu (a m : ℕ) (ha : 0 < a) (F : Finset (polygonFullGroup a m)) where
  Q : ℝ
  B : ℝ
  Q_nonneg : 0 ≤ Q
  B_nonneg : 0 ≤ B
  signals : BarrierSignalSystem a ha Q B
  shift_bound : ∀g ∈ F,∀i (p : GenericSquare a),∀j,
    |conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| ≤ Q
  chart_bound : ∀g ∈ F,∀i (p : GenericSquare a),∀l ∈ barrierChartCuts g i ∪ squareBoundaryCuts,
    |conjugate l.2| ≤ B ∧ |conjugate (l.2+integralCutForm a l.1 (fullGroupAffineData g i p).2)| ≤ B

theorem exists_barrierMenu {a m : ℕ} (ha : 0 < a) (F : Finset (polygonFullGroup a m)) :
    Nonempty (BarrierMenu a m ha F) := by
  obtain ⟨Q,B,hQ,hB,hall⟩ := barrier_uniform_constants F
  obtain ⟨S⟩ := exists_barrierSignalSystem ha Q B
  exact ⟨⟨Q,B,hQ,hB,S,fun g hg i p => (hall g hg i p).1,fun g hg i p => (hall g hg i p).2⟩⟩

end BarrierFiniteMenu

section EightBarrierFields
open Classical MeasureTheory Filter Set
open scoped Topology

noncomputable def barrierEightDirections {a : ℕ} (ha : 0 < a) : Fin (4+4) → ℝ×ℝ :=
  Fin.addCases (barrierFlagDirection ha) (barrierFlagDirection ha)

noncomputable def BarrierSignalSystem.eight {a : ℕ} {ha : 0 < a} {Q B : ℝ}
    (S : BarrierSignalSystem a ha Q B) : Fin (4+4) → FieldSignalData :=
  Fin.addCases (fun _ => S.first) S.second

abbrev BarrierBits (a m : ℕ) (ha : 0 < a) :=
  ∀j : Fin (4+4),FlagSite a m (commonVertexDenominator a) (barrierEightDirections ha j) → Bool

def castFlagBits {a m D : ℕ} {v w : ℝ×ℝ} (e : v=w)
    (b : FlagSite a m D v → Bool) : FlagSite a m D w → Bool := fun z => b (e.symm ▸ z)

theorem castFlagBits_success {a m D : ℕ} {v w : ℝ×ℝ} (e : v=w)
    (b : FlagSite a m D v → Bool) (f : (ℝ×ℝ) → ℝ) (N : ℝ)
    (h : signalSuccess (flagMeanSignal f N) b) :
    signalSuccess (flagMeanSignal f N) (castFlagBits e b) := by cases e; exact h

theorem castFlagBits_transport {a m D : ℕ} {v w : ℝ×ℝ} (e : v=w) (hD : 0 < D)
    (b : FlagSite a m D v → Bool) (g : polygonFullGroup a m) (z : FlagSite a m D w) :
    castFlagBits e (bitReindex (flagSitePermutation hD g) b) (flagSiteAction hD g z)=castFlagBits e b z := by
  cases e
  exact congrArg b ((flagSitePermutation hD g).symm_apply_apply z)

noncomputable def barrierFirstBits {a m : ℕ} {ha : 0 < a} (b : BarrierBits a m ha)
    (j : Fin 4) : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool :=
  castFlagBits (Fin.addCases_left j) (b (j.castAdd 4))

noncomputable def barrierSecondBits {a m : ℕ} {ha : 0 < a} (b : BarrierBits a m ha)
    (j : Fin 4) : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool :=
  castFlagBits (Fin.addCases_right j) (b (j.natAdd 4))

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem eight_q (j : Fin (4+4)) : (S.eight j).q = -3 := by
  induction j using Fin.addCases with
  | left j => simpa only [eight,Fin.addCases_left] using S.first_q
  | right j => simpa only [eight,Fin.addCases_right] using S.second_q j

theorem eight_success {m n : ℕ} {b : BarrierBits a m ha}
    (h : jointFieldSuccess (barrierEightDirections ha) S.eight n b) :
    (∀j,signalSuccess (flagMeanSignal S.first.signal (sourceDyadicN n)) (barrierFirstBits b j)) ∧
    (∀j,signalSuccess (flagMeanSignal (S.second j).signal (sourceDyadicN n)) (barrierSecondBits b j)) := by
  constructor
  · intro j
    apply castFlagBits_success
    simpa only [eight,Fin.addCases_left] using h (j.castAdd 4)
  · intro j
    apply castFlagBits_success
    simpa only [eight,Fin.addCases_right] using h (j.natAdd 4)

end BarrierSignalSystem

noncomputable def barrierBitsTransport {a m : ℕ} {ha : 0 < a} (g : polygonFullGroup a m)
    (b : BarrierBits a m ha) : BarrierBits a m ha :=
  jointBitReindex (barrierEightDirections ha) (commonVertexDenominator_pos ha) g b

theorem barrierBitsTransport_first {a m : ℕ} {ha : 0 < a} (g : polygonFullGroup a m)
    (b : BarrierBits a m ha) (j : Fin 4) (z) :
    barrierFirstBits (barrierBitsTransport g b) j
      (flagSiteAction (commonVertexDenominator_pos ha) g z)=barrierFirstBits b j z := by
  exact castFlagBits_transport (Fin.addCases_left j) (commonVertexDenominator_pos ha)
    (b (j.castAdd 4)) g z

theorem barrierBitsTransport_second {a m : ℕ} {ha : 0 < a} (g : polygonFullGroup a m)
    (b : BarrierBits a m ha) (j : Fin 4) (z) :
    barrierSecondBits (barrierBitsTransport g b) j
      (flagSiteAction (commonVertexDenominator_pos ha) g z)=barrierSecondBits b j z := by
  exact castFlagBits_transport (Fin.addCases_right j) (commonVertexDenominator_pos ha)
    (b (j.natAdd 4)) g z

end EightBarrierFields

end SimpleAmenable
end
end

end OAI
