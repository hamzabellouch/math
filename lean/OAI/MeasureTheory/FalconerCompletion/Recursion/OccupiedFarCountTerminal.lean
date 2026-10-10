import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.PairAmbientGoodRadialIffDistanceGood

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

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

theorem occupiedFar_count_terminal
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (N q b t : ℕ) (sig C : ℝ) (J i : ℕ)
    {B : ℕ} {s lam : ℝ} (hd : RegularizedProfileData ρ N B s lam m)
    (hN : 0<N) (hb : b≤N) (ht : t≤b+100*q)
    (P : CellPath (n+1)) (hab : P.length≤b)
    {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (p : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ))
    (hp : p∈occupiedFarPairsND ρ P.length b K (fun j => (pathIndex P j:ℤ))) :
    (positiveDistanceCountND
        ((gridPairMeasureND ρ b p).restrict {z | euclideanPairDirectionND z ∈ actualPairAmbientGood
          (adjustedProfile (d := n+1) m N) N q b t ρ m sig C J i z})
        (n+1) t b (((2:ℝ)^N)^(-m b))).toReal ≤
      ((2:ℝ)^N)^(100*(q:ℝ)/N+4*(n+2:ℝ)*lam) := by
  obtain ⟨X,Y,hX,hY,hXa,hYa,hXp,hYp,hμX,hμY,he⟩ :=
    occupiedFarPair_actual_state ρ m N q b t sig C J i P hab hK p hp
  rw [he]
  have hh := PositiveDistanceState.actual_distance_terminal_rpow
    (actualChildState ρ m N q b t sig C J i X Y) hd hN hb hX hY ht
  simpa only [actualChildState,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hh

theorem actualFarChildMaximum_terminal
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (m : ℝ → ℝ) (N q a b t : ℕ) (sig C : ℝ) (J i : ℕ)
    {Bρ Bκ : ℕ} {sρ sκ lam : ℝ}
    (hdρ : RegularizedProfileData ρ N Bρ sρ lam m)
    (hdκ : RegularizedProfileData κ N Bκ sκ lam m)
    (hN : 0<N) (hab : a≤b) (hb : b≤N) (ht : t≤b+100*q)
    (X Y : CellPath (n+1)) (hX : X.length=a) (hY : Y.length=a)
    {K : ℝ} (hK : 32*(n+2:ℝ)≤K) :
    (farChildMaximumND ρ κ b
      (occupiedFarPairsND ρ a b K (fun j => (pathIndex X j:ℤ)))
      (occupiedFarPairsND κ a b K (fun j => (pathIndex Y j:ℤ)))
      t (((2:ℝ)^N)^(-m b))
      (actualPairAmbientGood (adjustedProfile (d := n+1) m N) N q b t ρ m sig C J i)
      (actualPairAmbientGood (adjustedProfile (d := n+1) m N) N q b t κ m sig C J i)).toReal ≤
      ((2:ℝ)^N)^(100*(q:ℝ)/N+4*(n+2:ℝ)*lam) := by
  let U := ((2:ℝ)^N)^(100*(q:ℝ)/N+4*(n+2:ℝ)*lam)
  have hU : 0≤U := by positivity
  have one (μ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure μ]
      {B : ℕ} {s : ℝ} (hd : RegularizedProfileData μ N B s lam m)
      (P : CellPath (n+1)) (hP : P.length=a) :
      (occupiedFarPairsND μ a b K (fun j => (pathIndex P j:ℤ))).sup
        (fun p => positiveDistanceCountND
        ((gridPairMeasureND μ b p).restrict {z | euclideanPairDirectionND z ∈ actualPairAmbientGood
          (adjustedProfile (d := n+1) m N) N q b t μ m sig C J i z})
        (n+1) t b (((2:ℝ)^N)^(-m b))) ≤ ENNReal.ofReal U := by
    apply Finset.sup_le
    intro p hp
    have ht' := occupiedFar_count_terminal μ m N q b t sig C J i hd hN hb ht P
      (hP ▸ hab) hK p (by rwa [hP])
    apply (ENNReal.toReal_le_toReal (positiveDistanceCountND_ne_top _ _ _ _ _)
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hU] using ht'
  have hh : farChildMaximumND ρ κ b
      (occupiedFarPairsND ρ a b K (fun j => (pathIndex X j:ℤ)))
      (occupiedFarPairsND κ a b K (fun j => (pathIndex Y j:ℤ)))
      t (((2:ℝ)^N)^(-m b))
      (actualPairAmbientGood (adjustedProfile (d := n+1) m N) N q b t ρ m sig C J i)
      (actualPairAmbientGood (adjustedProfile (d := n+1) m N) N q b t κ m sig C J i) ≤
        ENNReal.ofReal U := sup_le (one ρ hdρ X hX) (one κ hdκ Y hY)
  simpa only [ENNReal.toReal_ofReal hU] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hh

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
