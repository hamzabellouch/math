import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcEncoding
import OAI.Combinatorics.PolynomialVacuum.Pairing.OpenPartition

namespace OAI

namespace PolynomialVacuumCylinder
open Classical Filter
open scoped Topology
variable {M : ℕ} [NeZero M]
namespace ArcChoice
def length : ArcChoice M → ℕ
  | .inl _ => 0
  | .inr A => A.word.length
end ArcChoice
noncomputable def arcChoiceLength (s : Bool × ZMod M → ArcChoice M) : ℕ := Finset.univ.sup (fun p => (s p).length)
noncomputable def arcChoiceMass (M : ℕ) [NeZero M] : ℝ := ∑'s,arcChoiceMajorant (M:=M) s
noncomputable def arcChoiceTail (M : ℕ) [NeZero M] (K : ℕ) : ℝ :=
  ∑'s,if K≤arcChoiceLength s then arcChoiceMajorant (M:=M) s else 0

theorem arcChoiceMajorant_nonneg (s : Bool × ZMod M → ArcChoice M) : 0≤arcChoiceMajorant s :=
  Finset.prod_nonneg (fun _ _ => ArcChoice.mass_nonneg _)

theorem arcChoice_tail_tendsto : Tendsto (arcChoiceTail M) atTop (nhds 0) :=
  PolynomialVacuumBridge.Corridor.summable_height_tail_tendsto arcChoiceLength arcChoiceMajorant
    (arcChoice_summable M) arcChoiceMajorant_nonneg

theorem arcChoice_tail_summable (K : ℕ) :
    Summable (fun s : Bool × ZMod M → ArcChoice M => if K≤arcChoiceLength s then arcChoiceMajorant s else 0) := by
  apply (arcChoice_summable M).of_nonneg_of_le
  · intro s; split_ifs <;> first | exact arcChoiceMajorant_nonneg s | rfl
  · intro s; split_ifs <;> first | exact arcChoiceMajorant_nonneg s | rfl

namespace ArcSystem
variable {H : ℕ}
theorem word_le_code_length (S : ArcSystem (bandSites M H)) (A : BoundaryArc (bandSites M H)) (hA : A∈S.val) :
    A.word.length≤arcChoiceLength S.code := by
  have hh:=Finset.le_sup (f:=fun p => (S.code p).length) (Finset.mem_univ A.port)
  simpa only [S.code_member A hA,ArcChoice.length,BoundaryArc.shape_word,arcChoiceLength] using hh

theorem sum_norm_le : (∑S : ArcSystem (bandSites M H),‖S.weight‖)≤arcChoiceMass M := by
  simp_rw [norm_weight_code]
  rw [← Finset.sum_image (fun A _ B _ he => code_injective he)]
  apply Summable.sum_le_tsum
  · intro s _; exact arcChoiceMajorant_nonneg s
  · exact arcChoice_summable M

theorem sum_norm_large_le (K : ℕ) :
    (∑S : ArcSystem (bandSites M H),if K≤arcChoiceLength S.code then ‖S.weight‖ else 0)≤arcChoiceTail M K := by
  simp_rw [norm_weight_code]
  let f : (Bool × ZMod M → ArcChoice M) → ℝ := fun s => if K≤arcChoiceLength s then arcChoiceMajorant s else 0
  change (∑S : ArcSystem (bandSites M H), f S.code) ≤ _
  rw [← Finset.sum_image (fun A _ B _ he => code_injective he)]
  apply Summable.sum_le_tsum
  · intro s _; dsimp [f]; split_ifs <;> first | exact arcChoiceMajorant_nonneg s | rfl
  · exact arcChoice_tail_summable K
end ArcSystem
end PolynomialVacuumCylinder
namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder
 

theorem physicalTransfer_powers_bounded (N H : ℕ) (hH : 0<H) (out inp : Fin (N+1) → Spin) :
    ‖(physicalTransfer (N+1) zeta^H) out inp‖≤arcChoiceMass (N+1) := by
  rw [physicalTransfer_pow_arcs N H hH]
  calc
    _ ≤ ∑S : ArcSystem (bandSites (N+1) H), ‖if matchesBoundary (recoverVertical H S.current)
        (cylinderState N inp) (cylinderState N out) then S.weight else 0‖ := norm_sum_le _ _
    _ ≤ ∑S : ArcSystem (bandSites (N+1) H), ‖S.weight‖ := by
      apply Finset.sum_le_sum
      intro S _
      split_ifs <;> simp
    _ ≤ _ := ArcSystem.sum_norm_le
end PolynomialVacuumAlgebra

end OAI
