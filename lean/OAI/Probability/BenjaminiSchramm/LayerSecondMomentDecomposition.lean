import OAI.Probability.BenjaminiSchramm.LayerMaximumDecomposition
import OAI.Probability.BenjaminiSchramm.SlabSecondMoment

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjusted_full_layer_second_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (x : V) (u : ℝ) (k l : ℤ) :
    (∫⁻ ω, restrictedLayerCount G.ends Set.univ
        {y | G.adjustedLayerIndex a R u x y=k} ω x *
      restrictedLayerCount G.ends Set.univ
        {y | G.adjustedLayerIndex a R u x y=l} ω x ∂G.law p) ≤
      ∑' i : ℤ, G.supAdjustedFullLayerMoment a R p i *
        G.supAdjustedFullLayerMoment a R p (k-i) * G.supAdjustedFullLayerMoment a R p (l-i) := by
  let f := G.adjustedLayerIndex a R u x
  let T (z : V) := G.law p {ω | Percolation.Conn G.ends (ω ∩ Set.univ) x z}
  have hcont (z : V) (j : ℤ) :
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=j} ω z ∂G.law p) ≤
        G.supAdjustedFullLayerMoment a R p (j-f z) := by
    let v := G.orbitAdjustedHeight a x z/R+u
    have hidx (y : V) : f y=f z+G.adjustedLayerIndex a R v z y :=
      G.adjustedLayerIndex_change_base hc hl a R u x z y
    have htar : {y : V | f y=j}={y | G.adjustedLayerIndex a R v z y=j-f z} := by
      ext y
      change f y=j ↔ G.adjustedLayerIndex a R v z y=j-f z
      rw [hidx]
      omega
    rw [htar]
    exact G.adjustedFullLayerMoment_le_sup a R p _ z v
  have hrow (i : ℤ) : (∑' z, if f z=i then T z else 0) ≤ G.supAdjustedFullLayerMoment a R p i := by
    apply le_trans _ (G.adjustedFullLayerMoment_le_sup a R p i x u)
    rw [adjustedFullLayerMoment]
    change _ ≤ ∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=i} ω x ∂Percolation.law p
    rw [lintegral_restrictedLayerCount]
    apply ENNReal.tsum_le_tsum
    intro z
    by_cases hz : f z=i <;>
      simp only [Set.mem_ofPred_eq,hz,ite_true,ite_false,T,law,Percolation.law,le_refl]
  calc
    _ ≤ ∑' z, T z *
        (∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=k} ω z ∂G.law p) *
          (∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=l} ω z ∂G.law p) :=
      restricted_layer_second_moment G.ends Set.univ _ _ p x
    _ ≤ ∑' z, T z*G.supAdjustedFullLayerMoment a R p (k-f z)*
        G.supAdjustedFullLayerMoment a R p (l-f z) := by
      apply ENNReal.tsum_le_tsum
      intro z
      exact mul_le_mul' (mul_le_mul' le_rfl (hcont z k)) (hcont z l)
    _ ≤ ∑' z, ∑' i : ℤ, if f z=i then
        T z*G.supAdjustedFullLayerMoment a R p (k-i)*G.supAdjustedFullLayerMoment a R p (l-i)
        else 0 := by
      apply ENNReal.tsum_le_tsum
      intro z
      have ht := ENNReal.le_tsum (f := fun i : ℤ => if f z=i then
        T z*G.supAdjustedFullLayerMoment a R p (k-i)*G.supAdjustedFullLayerMoment a R p (l-i)
        else 0) (f z)
      rwa [ite_eq_left (rfl : f z=f z)] at ht
    _ = ∑' i : ℤ, (∑' z, if f z=i then T z else 0)*
        G.supAdjustedFullLayerMoment a R p (k-i)*G.supAdjustedFullLayerMoment a R p (l-i) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro i
      rw [←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_right]
      apply tsum_congr
      intro z
      by_cases hz : f z=i <;> simp only [hz,ite_true,ite_false,zero_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact mul_le_mul' (mul_le_mul' (hrow i) le_rfl) le_rfl

end CriticalPercolation.BondGraph

end

end OAI
