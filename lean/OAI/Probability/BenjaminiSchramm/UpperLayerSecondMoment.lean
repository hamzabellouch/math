import OAI.Probability.BenjaminiSchramm.LayerSecondMomentDecomposition

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjusted_upper_layer_second_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (x : V) (u : ℝ) (n : ℕ) :
    (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {y | G.adjustedLayerIndex a R u x y ≤ (n : ℤ)})
      {y | G.adjustedLayerIndex a R u x y=(n : ℤ)} ω x)^2 ∂G.law p) ≤
      ∑' i : ℤ, if i ≤ (n : ℤ) then G.supAdjustedFullLayerMoment a R p i *
        (G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0 := by
  let f := G.adjustedLayerIndex a R u x
  let I := Percolation.internalEdges G.ends {y | f y ≤ (n : ℤ)}
  let A := {y | f y=(n : ℤ)}
  let T (z : V) := G.law p {ω | Percolation.Conn G.ends (ω ∩ I) x z}
  let M (z : V) := ∫⁻ ω, restrictedLayerCount G.ends I A ω z ∂G.law p
  have hcont (z : V) (hz : f z ≤ (n : ℤ)) :
      M z ≤ G.supAdjustedUpLayerMoment a R p ((n : ℤ)-f z).toNat := by
    let v := G.orbitAdjustedHeight a x z/R+u
    have hidx (y : V) : f y=f z+G.adjustedLayerIndex a R v z y :=
      G.adjustedLayerIndex_change_base hc hl a R u x z y
    have hdom : {y : V | f y ≤ (n : ℤ)}=
        {y | G.adjustedLayerIndex a R v z y ≤ (((n : ℤ)-f z).toNat : ℤ)} := by
      ext y
      change f y ≤ (n : ℤ) ↔ G.adjustedLayerIndex a R v z y ≤ (((n : ℤ)-f z).toNat : ℤ)
      rw [hidx,Int.toNat_of_nonneg (sub_nonneg.mpr hz)]
      omega
    have htar : A={y | G.adjustedLayerIndex a R v z y = (((n : ℤ)-f z).toNat : ℤ)} := by
      ext y
      change f y=(n : ℤ) ↔ G.adjustedLayerIndex a R v z y = (((n : ℤ)-f z).toNat : ℤ)
      rw [hidx,Int.toNat_of_nonneg (sub_nonneg.mpr hz)]
      omega
    change (∫⁻ ω, restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {y | f y ≤ (n : ℤ)}) A ω z ∂G.law p) ≤ _
    rw [hdom,htar]
    exact G.adjustedUpLayerMoment_le_sup a R p _ z v
  have hzero (z : V) (hz : ¬f z ≤ (n : ℤ)) : T z=0 := by
    have hx : x ∈ {y | f y ≤ (n : ℤ)} := by
      change f x ≤ (n : ℤ)
      simp only [f,G.adjustedLayerIndex_self,Nat.cast_nonneg]
    have he : {ω : Set E | Percolation.Conn G.ends (ω ∩ I) x z}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hz (Percolation.conn_internal_endpoint G.ends {y | f y ≤ (n : ℤ)} hx hω)
    change G.law p {ω | Percolation.Conn G.ends (ω ∩ I) x z}=0
    rw [he,measure_empty]
  have hrow (i : ℤ) : (∑' z, if f z=i then T z else 0) ≤ G.supAdjustedFullLayerMoment a R p i := by
    apply le_trans _ (G.adjustedFullLayerMoment_le_sup a R p i x u)
    rw [adjustedFullLayerMoment]
    change _ ≤ ∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=i} ω x ∂Percolation.law p
    rw [lintegral_restrictedLayerCount]
    apply ENNReal.tsum_le_tsum
    intro z
    by_cases hz : f z=i
    · simp only [Set.mem_ofPred_eq,hz,ite_true,T]
      exact measure_mono fun ω hω => Percolation.conn_mono G.ends
        (show ω ∩ I ⊆ ω ∩ Set.univ from fun e he => ⟨he.1,Set.mem_univ e⟩) hω
    · simp only [Set.mem_ofPred_eq,hz,ite_false,le_refl]
  calc
    _ ≤ ∑' z, T z*(M z)^2 := by
      simpa only [pow_two,mul_assoc,T,M,I,A,f,law,Percolation.law] using
        restricted_layer_second_moment G.ends I A A p x
    _ ≤ ∑' z, if f z ≤ (n : ℤ) then
        T z*(G.supAdjustedUpLayerMoment a R p ((n : ℤ)-f z).toNat)^2 else 0 := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ (n : ℤ)
      · rw [ite_eq_left hz]
        exact mul_le_mul' le_rfl (pow_le_pow_left' (hcont z hz) 2)
      · rw [ite_eq_right hz,hzero z hz,zero_mul]
    _ ≤ ∑' z, ∑' i : ℤ, if f z=i ∧ i ≤ (n : ℤ) then
        T z*(G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0 := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ (n : ℤ)
      · rw [ite_eq_left hz]
        have hband : f z=f z ∧ f z ≤ (n : ℤ) := ⟨rfl,hz⟩
        have ht := ENNReal.le_tsum (f := fun i : ℤ => if f z=i ∧ i ≤ (n : ℤ) then
          T z*(G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0) (f z)
        rwa [ite_eq_left hband] at ht
      · rw [ite_eq_right hz]
        exact bot_le
    _ = ∑' i : ℤ, if i ≤ (n : ℤ) then (∑' z, if f z=i then T z else 0)*
        (G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0 := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro i
      by_cases hi : i ≤ (n : ℤ)
      · rw [ite_eq_left hi,←ENNReal.tsum_mul_right]
        apply tsum_congr
        intro z
        by_cases hz : f z=i <;>
          simp only [hz,hi,true_and,false_and,ite_true,ite_false,zero_mul]
      · simp only [hi,and_false,ite_false,tsum_zero]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : i ≤ (n : ℤ)
      · rw [ite_eq_left hi,ite_eq_left hi]
        exact mul_le_mul' (hrow i) le_rfl
      · simp only [hi,ite_false,le_refl]

end CriticalPercolation.BondGraph

end

end OAI
