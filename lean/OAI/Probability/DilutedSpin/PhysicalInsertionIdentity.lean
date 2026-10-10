import OAI.Probability.DilutedSpin.CompoundPhysicalMean
import OAI.Probability.DilutedSpin.PhysicalInsertionComparison

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower PhysicalRoot ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i,Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootInsertion_eq_difference (T : KernelTower Ω (L+1))
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin) (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) (i : Fin a → Site N) :
    rootInsertion T Q m base old V a F (z,i) =
      root T Q m (fun y => base z.1 z.2.1.1 z.2.1.2 y+F (fun j => V y (i j)))
        (rootArray z.2.2.1 z.2.2.2) old -
      root T Q m (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old := by
  exact (root_energy_insertion T Q m (base z.1 z.2.1.1 z.2.1.2)
    (fun y => F (fun j => V y (i j))) _ old).symm

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_eq_difference (T : KernelTower Ω (L+1))
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin) (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) :
    sameInsertionAverage T Q m base old V a F z =
      (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
        root T Q m (fun y => base z.1 z.2.1.1 z.2.1.2 y+F (fun j => V y (i j)))
          (rootArray z.2.2.1 z.2.2.2) old) -
      root T Q m (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old := by
  unfold sameInsertionAverage
  simp only [rootInsertion_eq_difference,FiniteLaw.expect_sub,FiniteLaw.expect_const]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
