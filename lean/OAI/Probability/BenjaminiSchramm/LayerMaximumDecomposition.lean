import OAI.Probability.BenjaminiSchramm.LayerFirstMoments
import OAI.Probability.BenjaminiSchramm.SlabLastMaximum

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem max_height_layer_moment_bound (f : V → ℝ) (I : Set E)
    (p : unitInterval) (x : V) (i : ℝ) :
    (∫⁻ ω, restrictedLayerCount G I {y | f y=i} ω x ∂law p) ≤
      ∑' z, if f x ≤ f z ∧ i ≤ f z then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ f z})) x z} *
          (∫⁻ ω, restrictedLayerCount G (I ∩ internalEdges G {v | f v ≤ f z})
            {y | f y=i} ω z ∂law p) else 0 := by
  simp_rw [lintegral_restrictedLayerCount]
  calc
    _ ≤ ∑' y, ∑' z, if f y=i ∧ f x ≤ f z ∧ i ≤ f z then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ f z})) x z} *
          law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ f z})) z y} else 0 := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : f y=i
      · simp only [Set.mem_ofPred_eq,hy,ite_true]
        have hh := max_height_connection_bound G f I p x y
        refine hh.trans_eq (tsum_congr fun z => ?_)
        rw [hy]
        by_cases hz : f x ≤ f z ∧ i ≤ f z
        · simp only [hz,true_and,ite_true]
        · simp only [hz,true_and,ite_false]
      · simp only [Set.mem_ofPred_eq,hy,false_and,ite_false,tsum_zero,le_refl]
    _ = _ := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro z
      by_cases hz : f x ≤ f z ∧ i ≤ f z
      · rw [ite_eq_left hz,←ENNReal.tsum_mul_left]
        apply tsum_congr
        intro y
        by_cases hy : f y=i <;>
          simp only [Set.mem_ofPred_eq,hy,hz,true_and,false_and,ite_true,ite_false,mul_zero]
      · rw [ite_eq_right hz]
        apply ENNReal.tsum_eq_zero.mpr
        intro y
        exact ite_eq_right (by tauto)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def adjustedFullLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (i : ℤ) (x : V) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R u x y=i} ω x ∂G.law p

def supAdjustedFullLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval) (i : ℤ) : ℝ≥0∞ :=
  ⨆ x, ⨆ u, G.adjustedFullLayerMoment a R p i x u

omit [Countable V] [Countable E] in
lemma adjustedFullLayerMoment_le_sup (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (i : ℤ) (x : V) (u : ℝ) :
    G.adjustedFullLayerMoment a R p i x u ≤ G.supAdjustedFullLayerMoment a R p i :=
  le_iSup_of_le x (le_iSup_of_le u le_rfl)

theorem adjusted_full_layer_moment_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (x : V) (u : ℝ) (i : ℤ) :
    (∫⁻ ω, restrictedLayerCount G.ends Set.univ
      {y | G.adjustedLayerIndex a R u x y=i} ω x ∂G.law p) ≤
      ∑' j : ℕ, if i ≤ (j : ℤ) then
        G.supAdjustedUpLayerMoment a R p j *
          G.supAdjustedDownLayerMoment a R p ((j : ℤ)-i).toNat else 0 := by
  let f := G.adjustedLayerIndex a R u x
  let J (z : V) := Percolation.internalEdges G.ends {v | f v ≤ f z}
  let T (z : V) := G.law p {ω | Percolation.Conn G.ends (ω ∩ J z) x z}
  let D (z : V) := ∫⁻ ω, restrictedLayerCount G.ends (J z) {y | f y=i} ω z ∂G.law p
  have hbase : (∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=i} ω x ∂G.law p) ≤
      ∑' z, if 0 ≤ f z ∧ i ≤ f z then T z*D z else 0 := by
    have hh := max_height_layer_moment_bound G.ends (fun v => (f v : ℝ)) Set.univ p x i
    have htar : {y : V | (f y : ℝ)=(i : ℝ)}={y | f y=i} := by ext y; simp
    have hdom (z : V) : {v : V | (f v : ℝ) ≤ (f z : ℝ)}={v | f v ≤ f z} := by ext v; simp
    simp only [htar,hdom,Set.univ_inter] at hh
    change _ ≤ _
    refine hh.trans_eq (tsum_congr fun z => ?_)
    have hx : f x=0 := G.adjustedLayerIndex_self a R u x
    have he : ((f x : ℝ) ≤ (f z : ℝ) ∧ (i : ℝ) ≤ (f z : ℝ)) ↔ (0 ≤ f z ∧ i ≤ f z) := by
      rw [hx]
      exact_mod_cast (Iff.rfl : (0 ≤ f z ∧ i ≤ f z) ↔ (0 ≤ f z ∧ i ≤ f z))
    simp only [he,T,D,J,law,Percolation.law]
  have hcont (z : V) (j : ℕ) (hz : f z=(j : ℤ)) (hi : i ≤ (j : ℤ)) :
      D z ≤ G.supAdjustedDownLayerMoment a R p ((j : ℤ)-i).toNat := by
    let v := G.orbitAdjustedHeight a x z/R+u
    have hidx (y : V) : f y=(j : ℤ)+G.adjustedLayerIndex a R v z y := by
      simpa only [f,hz] using G.adjustedLayerIndex_change_base hc hl a R u x z y
    have hdom : {y : V | f y ≤ f z}={y | G.adjustedLayerIndex a R v z y ≤ 0} := by
      ext y
      change f y ≤ f z ↔ G.adjustedLayerIndex a R v z y ≤ 0
      rw [hz,hidx]
      omega
    have htar : {y : V | f y=i}=
        {y | G.adjustedLayerIndex a R v z y = -(((j : ℤ)-i).toNat : ℤ)} := by
      ext y
      change f y=i ↔ G.adjustedLayerIndex a R v z y = -(((j : ℤ)-i).toNat : ℤ)
      rw [hidx,Int.toNat_of_nonneg (sub_nonneg.mpr hi)]
      omega
    change (∫⁻ ω, restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {y | f y ≤ f z}) {y | f y=i} ω z ∂G.law p) ≤ _
    rw [hdom,htar]
    exact G.adjustedDownLayerMoment_le_sup a R p _ z v
  have hrow (j : ℕ) : (∑' z, if f z=(j : ℤ) then T z else 0) ≤
      G.supAdjustedUpLayerMoment a R p j := by
    apply le_trans _ (G.adjustedUpLayerMoment_le_sup a R p j x u)
    rw [adjustedUpLayerMoment]
    change _ ≤ ∫⁻ ω, restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | f v ≤ (j : ℤ)}) {v | f v=(j : ℤ)} ω x ∂Percolation.law p
    rw [lintegral_restrictedLayerCount]
    apply ENNReal.tsum_le_tsum
    intro z
    by_cases hz : f z=(j : ℤ)
    · simp only [Set.mem_ofPred_eq,hz,ite_true,T,J,law,Percolation.law,le_refl]
    · simp only [Set.mem_ofPred_eq,hz,ite_false,le_refl]
  calc
    _ ≤ ∑' z, if 0 ≤ f z ∧ i ≤ f z then T z*D z else 0 := hbase
    _ ≤ ∑' z, ∑' j : ℕ, if f z=(j : ℤ) ∧ i ≤ (j : ℤ) then
        T z*G.supAdjustedDownLayerMoment a R p ((j : ℤ)-i).toNat else 0 := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : 0 ≤ f z ∧ i ≤ f z
      · rw [ite_eq_left hz]
        have hj : f z=((f z).toNat : ℤ) := (Int.toNat_of_nonneg hz.1).symm
        apply le_trans (mul_le_mul' le_rfl (hcont z _ hj (hz.2.trans_eq hj)))
        have hband : f z=((f z).toNat : ℤ) ∧ i ≤ ((f z).toNat : ℤ) := ⟨hj,hz.2.trans_eq hj⟩
        have ht := ENNReal.le_tsum (f := fun j : ℕ => if f z=(j : ℤ) ∧ i ≤ (j : ℤ) then
          T z*G.supAdjustedDownLayerMoment a R p ((j : ℤ)-i).toNat else 0) (f z).toNat
        rwa [ite_eq_left hband] at ht
      · rw [ite_eq_right hz]
        exact bot_le
    _ = ∑' j : ℕ, if i ≤ (j : ℤ) then
        (∑' z, if f z=(j : ℤ) then T z else 0)*
          G.supAdjustedDownLayerMoment a R p ((j : ℤ)-i).toNat else 0 := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro j
      by_cases hi : i ≤ (j : ℤ)
      · rw [ite_eq_left hi,←ENNReal.tsum_mul_right]
        apply tsum_congr
        intro z
        by_cases hz : f z=(j : ℤ) <;>
          simp only [hi,hz,true_and,false_and,ite_true,ite_false,zero_mul]
      · simp only [hi,and_false,ite_false,tsum_zero]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro j
      by_cases hi : i ≤ (j : ℤ)
      · simp only [hi,ite_true]
        exact mul_le_mul' (hrow j) le_rfl
      · simp only [hi,ite_false,le_refl]

end CriticalPercolation.BondGraph

end

end OAI
