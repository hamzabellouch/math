import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTProjection
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverageBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorProduct
open ResidueHaar HistoryCRTIntegration HistoryCRTProjection
open scoped BigOperators

abbrev JointUnits (α : Type*) (M : ℕ) := UnitPair M × (α → (ZMod M)ˣ)

def unitProjection {α : Type*} {M n : ℕ} (hd : n ∣ M) (z : JointUnits α M) : JointUnits α n :=
  ((ZMod.unitsMap hd z.1.1,ZMod.unitsMap hd z.1.2),fun u => ZMod.unitsMap hd (z.2 u))

def jointUnitsEquiv {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    JointUnits α (∏i,p i) ≃ (∀i,JointUnits α (p i)) :=
  ((unitPairEquiv p hc).prodCongr
    ((Equiv.piCongrRight (fun _ : α => (Supply.crtUnitsEquiv p hc).toEquiv)).trans
      (Equiv.piComm (fun (_ : α) (i : ι) => (ZMod (p i))ˣ)))).trans
        (DiagonalSmallResidueNorm.pairPiEquiv _ _)

@[simp] theorem jointUnitsEquiv_apply {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (z : JointUnits α (∏i,p i)) (i : ι) :
    jointUnitsEquiv p hc z i = unitProjection (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) z := by
  apply Prod.ext
  · apply Prod.ext <;> apply Units.ext
    · exact unitPairEquiv_fst_coe p hc z.1 i
    · exact unitPairEquiv_snd_coe p hc z.1 i
  · funext u
    apply Units.ext
    exact Supply.crtUnitsEquiv_apply p hc (z.2 u) i

theorem average_prod {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℂ) :
    average (fun z : α × β => f z.1 z.2) = average (fun x => average (f x)) := by
  simp only [average,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem unit_projected_product_average {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) {M : ℕ} [NeZero M]
    (heq : (∏i,p i) = M) (f : ∀i,JointUnits α (p i) → ℂ) :
    average (fun z : JointUnits α M => ∏i,f i
      (unitProjection ((Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans heq.dvd) z)) =
      ∏i,average (f i) := by
  subst M
  have he := (average_equiv (jointUnitsEquiv (α:=α) p hc)
    (fun z => ∏i,f i (z i))).trans (average_pi_product f)
  simpa only [jointUnitsEquiv_apply] using he

theorem norm_average_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℂ) (B : ℝ) (h : ∀a, ‖f a‖ ≤ B) : ‖average f‖ ≤ B := by
  have hc : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [average,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card α : ℝ)⁻¹ * ∑a,‖f a‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ ≤ (Fintype.card α : ℝ)⁻¹ * ∑_a : α,B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (inv_nonneg.mpr hc.le)
    _ = B := by simp [hc.ne']

end Ostmann.Arithmetic.HistoryBulkSpectatorProduct

end

end OAI
