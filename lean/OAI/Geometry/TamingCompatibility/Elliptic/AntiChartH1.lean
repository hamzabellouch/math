import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.DirectionH1
import OAI.Geometry.TamingCompatibility.Hodge.ClosureLinear

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma antiGraph_norm_sq (a : antiPre A J α hs ht) :
    ‖antiGraph A J α hs ht a‖^2 =
      (∫ x, GeometricAdjoint.pairing J α ht a.val.val a.val.val x ∂ManifoldVolume.geometricVolume A J α) +
      (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val.val)
        (codifferential J α ht a.val.val) x ∂ManifoldVolume.geometricVolume A J α) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖smoothL2 A J α hs ht true a.val‖^2 +
    ‖smoothL2 A J α hs ht false (antiDelta A J α hs ht a)‖^2 = _
  rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht false).norm_map,
    preL2_norm_sq,preL2_norm_sq]
  rfl

def antiToEnergy : antiPre A J α hs ht →ₗ[ℝ] antiEnergy A J α hs ht :=
  ClosureLinear.toClosure (antiGraph A J α hs ht)

lemma antiToEnergy_dense : DenseRange (antiToEnergy A J α hs ht) :=
  ClosureLinear.toClosure_dense (antiGraph A J α hs ht)

def antiToH1 : antiPre A J α hs ht →ₗ[ℝ] globalH1 A 2 :=
  (ClosureLinear.toClosure (localizeH1 A 2)).comp (antiPre A J α hs ht).subtype

include hD in
lemma antiToH1_bound : ∃ C : ℝ, ∀ a : antiPre A J α hs ht,
    ‖antiToH1 A J α hs ht a‖ ≤ C * ‖antiToEnergy A J α hs ht a‖ := by
  classical
  choose C hC hb using localized_jet_bound A J α hs ht D hD
  let B : ℝ := 1 + ∑ p : A.centers, C p
  have hB : 0 < B := by
    have hsum : 0 ≤ ∑ p : A.centers, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hcB (p : A.centers) : C p ≤ B :=
    (Finset.single_le_sum (fun p _ => (hC p).le) (Finset.mem_univ p)).trans
      (by change (∑ p : A.centers, C p) ≤ 1 + (∑ p : A.centers, C p); linarith)
  let N : ℝ := Fintype.card DerivativeIndex * Fintype.card A.centers
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨Real.sqrt (N*B),fun a => ?_⟩
  have hsq : ‖antiToH1 A J α hs ht a‖^2 ≤ N*B*‖antiToEnergy A J α hs ht a‖^2 := by
    change ‖localizeH1 A 2 a.val‖^2 ≤ N*B*‖antiGraph A J α hs ht a‖^2
    simp only [PiLp.norm_sq_eq_of_L2]
    have hlocal (j : DerivativeIndex) (p : A.centers) :
        ‖localizeH1 A 2 a.val j p‖^2 ≤ B*‖antiGraph A J α hs ht a‖^2 := by
      have h := hb p a.val a.property j
      rw [← antiGraph_norm_sq A J α hs ht a] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hcB p) (sq_nonneg _))
    calc
      _ ≤ ∑ j : DerivativeIndex, ∑ p : A.centers, B*‖antiGraph A J α hs ht a‖^2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun p _ => hlocal j p
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [N]; ring
  have hroot : (Real.sqrt (N*B)*‖antiToEnergy A J α hs ht a‖)^2 =
      N*B*‖antiToEnergy A J α hs ht a‖^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hN hB.le)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp (hsq.trans_eq hroot.symm)

def energyToH1 : antiEnergy A J α hs ht →L[ℝ] globalH1 A 2 :=
  (antiToH1 A J α hs ht).extendOfNorm (antiToEnergy A J α hs ht)

include hD in
lemma energyToH1_smooth (a : antiPre A J α hs ht) :
    energyToH1 A J α hs ht (antiToEnergy A J α hs ht a) = antiToH1 A J α hs ht a :=
  LinearMap.extendOfNorm_eq (antiToEnergy_dense A J α hs ht) (antiToH1_bound A J α hs ht D hD) a
end TamingCompatibility.GeometricHilbert

end

end OAI
