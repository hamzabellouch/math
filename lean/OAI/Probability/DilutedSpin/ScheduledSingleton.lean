import OAI.Probability.DilutedSpin.PhysicalSingleton
import OAI.Probability.DilutedSpin.ScheduledRootMultileaf

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

omit [Fintype Ω] in
lemma leafProduct_singleton (C : PrescribedTree n) [Subsingleton C.Leaf] (a : C.Leaf)
    (f : FinitePath Ω n → ℝ) (z : Sample Ω C) : leafProduct C f z=f (C.pathAt a z) := by
  rw [leafProduct_eq_prod,Fintype.prod_subsingleton _ a]

lemma childEnergy_singleton (C : PrescribedTree n) (hC : Fintype.card C.Leaf=1)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ) :
    childEnergy C T f=(KernelTower.law (n+1) T).covarianceEnergy f := by
  let : Subsingleton C.Leaf := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨a⟩ := leaf_nonempty C
  rcases T with ⟨μ,K⟩
  unfold childEnergy FiniteLaw.covarianceEnergy FiniteLaw.covariance
  simp_rw [leafProduct_singleton C a]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  erw [branch_leaf_marginal C μ K a (fun w => f w i * f w j),
    branch_leaf_marginal C μ K a (fun w => f w i),
    branch_leaf_marginal C μ K a (fun w => f w j)]

lemma shapeEnergyAt_singleton (C : PrescribedTree n) (hC : Fintype.card C.Leaf=1)
    (d : ℕ) (T : KernelTower Ω (n+1+d)) (f : FinitePath Ω (n+1+d) → Fin N → ℝ) :
    shapeEnergyAt C d T f=KernelTower.prefixEnergyAt (n+1+d) T d f := by
  induction d with
  | zero => exact childEnergy_singleton C hC T f
  | succ d ih => exact T.1.expect_congr (fun z => ih (T.2 z) (fun y => f (z,y)))

lemma prefixEnergyAt_heightCast {m n : ℕ} (h : n=m) (d : ℕ)
    (T : KernelTower Ω n) (f : FinitePath Ω n → Fin N → ℝ) :
    KernelTower.prefixEnergyAt m (kernelHeightCast h T) d (vectorHeightCast h f)=
      KernelTower.prefixEnergyAt n T d f := by
  cases h
  rfl

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

/-- The base topology in the SAME scheduled covariance family is exactly the
conditional singleton covariance controlled by joint_grid_selection. -/
lemma scheduledShapeEnergy_leaf (d : ℕ) (hd : d<L) (q : ReducedTopology.leaf.Vertex → ℕ)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    scheduledShapeEnergy L d .leaf q T f=KernelTower.prefixEnergyAt L T d f := by
  rw [scheduledShapeEnergy_eq_realize (L-(d+1)) d .leaf q (by omega)]
  have hcard : Fintype.card (realize (L-(d+1)) (d+1) .leaf q).Leaf=1 := by
    rw [card_leaf,realize_leaves _ _ .leaf q trivial]
    rfl
  rw [shapeEnergyAt_singleton _ hcard,prefixEnergyAt_heightCast]

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
