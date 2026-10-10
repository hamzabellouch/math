import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanFarKernelRegionPartition
import OAI.MeasureTheory.FalconerCompletion.Graphs.AmbientDescendants
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormIteratedFDerivSmoothStar
import OAI.MeasureTheory.FalconerCompletion.Recursion.ExistsFarSeparationPower2

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal Topology Classical
variable {n : ℕ}

lemma actualPairAmbientGood_radial_iff_distanceGood
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ)
    (N q a t : ℕ) (sig C : ℝ) (J i : ℕ)
    (z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))
    (hz : z.1≠z.2) :
    euclideanPairDirectionND z ∈ actualPairAmbientGood
      (adjustedProfile (d := n+1) m N) N q a t ρ m sig C J i z ↔
      z ∈ distanceGood ρ m N q a t sig C J i := by
  have hn : ‖euclideanPairDirectionND z‖=1 := euclideanPairDirectionND_norm z (dist_pos.mpr hz)
  simp only [actualPairAmbientGood, Set.mem_inter_iff, actualPolicyAmbientGood,
    Set.mem_ofPred_eq,hn,ne_eq,not_true_eq_false,false_or,distanceGood]
  constructor
  · intro h b hb
    exact ⟨h.1 b hb,h.2 b hb⟩
  · intro h
    exact ⟨fun b hb => (h b hb).1,fun b hb => (h b hb).2⟩

lemma actualGridPair_restrict_good
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (m : ℝ → ℝ) (N q a t : ℕ) (sig C : ℝ) (J i : ℕ)
    {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (p : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ))
    (hp : farSeparatedGridND a K p.1 p.2) :
    (gridPairMeasureND ρ a p).restrict
        {z | euclideanPairDirectionND z ∈ actualPairAmbientGood
          (adjustedProfile (d := n+1) m N) N q a t ρ m sig C J i z} =
      (gridPairMeasureND ρ a p).restrict (distanceGood ρ m N q a t sig C J i) := by
  apply Measure.restrict_congr_set
  filter_upwards [ae_restrict_mem (μ := ρ.prod ρ) (gridPairSetND_measurable a p)] with z hz
  have hK' : 32*((↑(n+1):ℝ)+1)≤K := by
    push_cast
    linarith
  have hlo := (farSeparatedGridND_all_lengths hK' hp hz.1 hz.2).1
  have hkpos : 0<K := by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
  have hpos : 0<dist z.1 z.2 := lt_of_lt_of_le (div_pos hkpos (by positivity)) hlo
  exact propext (actualPairAmbientGood_radial_iff_distanceGood ρ m N q a t sig C J i z (dist_pos.mp hpos))

lemma gridPairMeasureND_eq_stateCellPair
    (e : PositiveDistanceState (n+1)) [IsFiniteMeasure e.ρ]
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a) :
    gridPairMeasureND e.ρ e.a
      ((fun j => (pathIndex e.X j:ℤ)),fun j => (pathIndex e.Y j:ℤ)) = e.cellPair := by
  rw [gridPairMeasureND_eq_prod]
  unfold PositiveDistanceState.cellPair treeCell
  rw [hX,hY]
  rfl

lemma actualFar_count_eq_coincidence
    (e : PositiveDistanceState (n+1)) [IsFiniteMeasure e.ρ]
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hsep : farSeparatedGridND e.a K
      (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    positiveDistanceCountND
      ((gridPairMeasureND e.ρ e.a
        ((fun j => (pathIndex e.X j:ℤ)),fun j => (pathIndex e.Y j:ℤ))).restrict
        {z | euclideanPairDirectionND z ∈ actualPairAmbientGood
            (adjustedProfile (d := n+1) e.mass e.N)
            e.N e.q e.a e.t e.ρ e.mass e.sig e.C e.J e.i z})
       (n+1) e.t e.a e.levelMass = e.coincidence := by
  let p : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) :=
    ((fun j => (pathIndex e.X j:ℤ)),fun j => (pathIndex e.Y j:ℤ))
  have hg := actualGridPair_restrict_good e.ρ e.mass e.N e.q e.a e.t e.sig e.C e.J e.i hK p hsep
  have hc := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) =>
      μ.restrict (distanceGood e.ρ e.mass e.N e.q e.a e.t e.sig e.C e.J e.i))
    (gridPairMeasureND_eq_stateCellPair e hX hY)
  have he := hg.trans hc
  exact congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) =>
    positiveDistanceCountND μ (n+1) e.t e.a e.levelMass) he

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
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal Topology Classical
variable {n : ℕ}

lemma exists_treePath_of_ambientDescendant
    (P : CellPath (n+1)) {b : ℕ} (hab : P.length≤b)
    (Z : Fin (n+1) → ℤ)
    (hZ : Z∈ambientDescendantsND P.length b (fun j => (pathIndex P j:ℤ))) :
    ∃ Q : CellPath (n+1), Q.length=b ∧
      (fun j => (pathIndex Q j:ℤ))=Z ∧ Q.take P.length=P := by
  let x := Attempt4FullFar.ambientGridCenter b Z
  have hxZ : x∈Attempt4FullFar.ambientGridCell b Z := Attempt4FullFar.ambientGridCenter_mem b Z
  have hxP : x∈treeCell P := ambientDescendantsND_subset hab hZ hxZ
  have hxroot : x∈treeCell [] := by
    simpa only [List.take_zero] using treeCell_subset_take P 0 hxP
  rw [← treeCell_cover_root b] at hxroot
  obtain ⟨Q,hQ,hxQ⟩ := Set.mem_iUnion₂.mp hxroot
  have hlen : Q.length=b := (mem_dyadicPaths b Q).mp hQ
  have hxQ' : x∈Attempt4FullFar.ambientGridCell b (fun j => (pathIndex Q j:ℤ)) := by
    change x∈Attempt4FullFar.ambientGridCell Q.length (fun j => (pathIndex Q j:ℤ)) at hxQ
    simpa only [hlen] using hxQ
  have hlabel : (fun j => (pathIndex Q j:ℤ))=Z := by
    by_contra hne
    exact Set.disjoint_left.mp (Attempt4FullFar.ambientGridCell_disjoint hne) hxQ' hxZ
  refine ⟨Q,hlen,hlabel,?_⟩
  have hlen' : (Q.take P.length).length=P.length := by
    rw [List.length_take,hlen,Nat.min_eq_left hab]
  by_contra hne
  exact Set.disjoint_left.mp (treeCell_disjoint hlen' hne) (treeCell_subset_take Q P.length hxQ) hxP

noncomputable def actualChildState
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ)
    (N q b t : ℕ) (sig C : ℝ) (J i : ℕ) (X Y : CellPath (n+1)) : PositiveDistanceState (n+1) :=
  ⟨ρ,m,N,q,b,t,J,i,sig,C,X,Y⟩

theorem occupiedFarPair_actual_state
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (N q b t : ℕ) (sig C : ℝ) (J i : ℕ)
    (P : CellPath (n+1)) (hab : P.length≤b)
    {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (p : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ))
    (hp : p∈occupiedFarPairsND ρ P.length b K (fun j => (pathIndex P j:ℤ))) :
    ∃ X Y : CellPath (n+1), X.length=b ∧ Y.length=b ∧
      X.take P.length=P ∧ Y.take P.length=P ∧
      (fun j => (pathIndex X j:ℤ))=p.1 ∧ (fun j => (pathIndex Y j:ℤ))=p.2 ∧
      ρ (treeCell X)≠0 ∧ ρ (treeCell Y)≠0 ∧
      let e := actualChildState ρ m N q b t sig C J i X Y
      positiveDistanceCountND
        ((gridPairMeasureND ρ b p).restrict {z | euclideanPairDirectionND z ∈ actualPairAmbientGood
          (adjustedProfile (d := n+1) m N) N q b t ρ m sig C J i z})
        (n+1) t b (((2:ℝ)^N)^(-m b)) = e.coincidence := by
  have hh := Finset.mem_filter.mp hp
  have hk := mem_farParentPairsND_iff.mp hh.1
  obtain ⟨X,hX,hXp,hXa⟩ := exists_treePath_of_ambientDescendant P hab p.1 hk.1
  obtain ⟨Y,hY,hYp,hYa⟩ := exists_treePath_of_ambientDescendant P hab p.2 hk.2.1
  have hcx : treeCell X=Attempt4FullFar.ambientGridCell b p.1 := by
    unfold treeCell
    rw [hX,hXp]
    rfl
  have hcy : treeCell Y=Attempt4FullFar.ambientGridCell b p.2 := by
    unfold treeCell
    rw [hY,hYp]
    rfl
  refine ⟨X,Y,hX,hY,hXa,hYa,hXp,hYp,by rw [hcx]; exact hh.2.1,
    by rw [hcy]; exact hh.2.2,?_⟩
  let e := actualChildState ρ m N q b t sig C J i X Y
  have hsep : farSeparatedGridND e.a K
      (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) := by
    change farSeparatedGridND b K (fun j => (pathIndex X j:ℤ)) (fun j => (pathIndex Y j:ℤ))
    rw [hXp,hYp]
    exact hk.2.2
  let : IsFiniteMeasure e.ρ := by change IsFiniteMeasure ρ; infer_instance
  have he := actualFar_count_eq_coincidence e hX hY hK hsep
  have hpair : ((fun j => (pathIndex X j:ℤ)),fun j => (pathIndex Y j:ℤ))=p := Prod.ext hXp hYp
  change positiveDistanceCountND
        ((gridPairMeasureND ρ b ((fun j => (pathIndex X j:ℤ)),fun j => (pathIndex Y j:ℤ))).restrict
          {z | euclideanPairDirectionND z∈actualPairAmbientGood
            (adjustedProfile (d := n+1) m N) N q b t ρ m sig C J i z})
        (n+1) t b (((2:ℝ)^N)^(-m b))=e.coincidence at he
  rwa [hpair] at he

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
