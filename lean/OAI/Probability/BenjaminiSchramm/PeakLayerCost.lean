import OAI.Probability.BenjaminiSchramm.SubcriticalPeakConditional

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma integer_downward_layer_cost {V : Type*} (f : V → ℤ) (P : V → Prop) (g : ℕ → ℝ≥0∞) :
    (∑' l : ℕ, g l*(∑' y, if f y= -(l : ℤ) ∧ P y then (1 : ℝ≥0∞) else 0))=
      ∑' y, if f y ≤ 0 ∧ P y then g (-f y).toNat else 0 := by
  simp_rw [←ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  by_cases hP : P y
  · by_cases hf : f y ≤ 0
    · have hd : f y= -(((-f y).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (neg_nonneg.mpr hf)]
        ring
      rw [ite_eq_left ⟨hf,hP⟩,tsum_eq_single (-f y).toNat]
      · rw [ite_eq_left (show f y= -(((-f y).toNat : ℕ) : ℤ) ∧ P y from ⟨hd,hP⟩),mul_one]
      · intro l hl
        have hne : f y ≠ -(l : ℤ) := by
          intro hh
          have hcast : (((-f y).toNat : ℕ) : ℤ)=(l : ℤ) := by omega
          exact hl (Int.ofNat_inj.mp hcast).symm
        rw [ite_eq_right (fun h => hne h.1),mul_zero]
    · rw [ite_eq_right (fun h => hf h.1)]
      apply ENNReal.tsum_eq_zero.mpr
      intro l
      have hne : f y ≠ -(l : ℤ) := by omega
      rw [ite_eq_right (fun h => hne h.1),mul_zero]
  · rw [ite_eq_right (fun h => hP h.2)]
    apply ENNReal.tsum_eq_zero.mpr
    intro l
    rw [ite_eq_right (fun h => hP h.2),mul_zero]

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def downwardLayerCost (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' l : ℕ, ENNReal.ofReal (g l)*restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} ω x

lemma downwardLayerCost_eq_vertex_sum (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ) (ω : Set E) (x : V) :
    G.downwardLayerCost a R g ω x=
      ∑' y, if G.adjustedLayerIndex a R 0 x y ≤ 0 ∧ Percolation.Conn G.ends ω x y then
        ENNReal.ofReal (g (-G.adjustedLayerIndex a R 0 x y).toNat) else 0 := by
  unfold downwardLayerCost restrictedLayerCount
  calc
    _ = ∑' l : ℕ, ENNReal.ofReal (g l)*(∑' y, if G.adjustedLayerIndex a R 0 x y= -(l : ℤ) ∧
        Percolation.Conn G.ends ω x y then (1 : ℝ≥0∞) else 0) := by
      apply tsum_congr
      intro l
      apply congrArg (fun b => ENNReal.ofReal (g l)*b)
      apply tsum_congr
      intro y
      by_cases hh : G.adjustedLayerIndex a R 0 x y= -(l : ℤ) ∧ Percolation.Conn G.ends ω x y
      · have hh' : y ∈ {z | G.adjustedLayerIndex a R 0 x z= -(l : ℤ)} ∧ Percolation.Conn G.ends ω x y := hh
        simp only [Set.inter_univ]
        rw [ite_eq_left hh',ite_eq_left hh]
      · have hh' : ¬(y ∈ {z | G.adjustedLayerIndex a R 0 x z= -(l : ℤ)} ∧ Percolation.Conn G.ends ω x y) := hh
        simp only [Set.inter_univ]
        rw [ite_eq_right hh',ite_eq_right hh]
    _ = _ := integer_downward_layer_cost _ _ _

lemma downwardLayerCost_of_exact_cluster (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ)
    (ω : Set E) (x : V) (S : Finset V) (hS : Percolation.cluster G.ends ω x=(S : Set V))
    (hbelow : ∀ y ∈ S, G.adjustedLayerIndex a R 0 x y ≤ 0) :
    G.downwardLayerCost a R g ω x=
      ∑ y ∈ S, ENNReal.ofReal (g (-G.adjustedLayerIndex a R 0 x y).toNat) := by
  rw [G.downwardLayerCost_eq_vertex_sum]
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro y hy
    have hxy : Percolation.Conn G.ends ω x y := by
      change y ∈ Percolation.cluster G.ends ω x
      rw [hS]
      exact hy
    exact ite_eq_left ⟨hbelow y hy,hxy⟩
  · intro y hy
    apply ite_eq_right
    intro hh
    have hys : y ∈ Percolation.cluster G.ends ω x := hh.2
    rw [hS] at hys
    exact hy hys

variable [Countable V] [Countable E]

lemma measurable_downwardLayerCost (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ) (x : V) :
    Measurable (fun ω => G.downwardLayerCost a R g ω x) :=
  Measurable.tsum fun _l => measurable_const.mul (measurable_restrictedLayerCount G.ends _ _ x)

theorem peakSurvivalCostMoment_eq (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (g : ℕ → ℝ) (n : ℕ) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω ∂G.law p))=
      ∑' l, ENNReal.ofReal (g l)*G.peakSurvivalLayerMoment O a R p n l := by
  have he (x : V) :
      (fun ω => {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω)=
      (fun ω => ∑' l, ENNReal.ofReal (g l)*
        {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
          (fun η => restrictedLayerCount G.ends Set.univ
            {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} η x) ω) := by
    funext ω
    by_cases hω : ω ∈ {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}
    · simp only [Set.indicator_of_mem hω,downwardLayerCost]
    · simp only [Set.indicator_of_notMem hω,mul_zero,tsum_zero]
  have hroot (x : V) :
      (∫⁻ ω, {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω ∂G.law p)=
      ∑' l, ENNReal.ofReal (g l)*(∫⁻ ω,
        {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
          (fun η => restrictedLayerCount G.ends Set.univ
            {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} η x) ω ∂G.law p) := by
    have hmA : MeasurableSet {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x} :=
      measurableSet_lt measurable_const (G.measurable_peakDownBandCount a _ _ x)
    rw [he]
    rw [lintegral_tsum (f := fun j ω => ENNReal.ofReal (g j)*
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y= -(j : ℤ)} η x) ω)
      (fun j => (measurable_const.mul
        ((measurable_restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y= -(j : ℤ)} x).indicator hmA)).aemeasurable)]
    apply tsum_congr
    intro l
    exact lintegral_const_mul _ ((measurable_restrictedLayerCount G.ends Set.univ
      {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} x).indicator hmA)
  simp_rw [hroot,←ENNReal.tsum_mul_left]
  rw [←Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro l
  unfold peakSurvivalLayerMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CriticalPercolation.BondGraph

end

end OAI
