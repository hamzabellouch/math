import OAI.Probability.BenjaminiSchramm.SubcriticalPeakSurvival

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma one_le_tsum_ite_one_of_pos {ι : Type*} (P : ι → Prop)
    (h : 0 < ∑' i, if P i then (1 : ℝ≥0∞) else 0) :
    1 ≤ ∑' i, if P i then (1 : ℝ≥0∞) else 0 := by
  have he : ∃ i, P i := by
    by_contra! hn
    have hz : (∑' i, if P i then (1 : ℝ≥0∞) else 0)=0 :=
      ENNReal.tsum_eq_zero.mpr fun i => ite_eq_right (hn i)
    rw [hz] at h
    exact lt_irrefl _ h
  obtain ⟨i,hi⟩ := he
  have hh := ENNReal.le_tsum (f := fun j => if P j then (1 : ℝ≥0∞) else 0) i
  simpa only [ite_eq_left hi] using hh

lemma one_le_tsum_of_zero_or_one {ι : Type*} (f : ι → ℝ≥0∞)
    (hf : ∀ i, f i=0 ∨ f i=1) (h : 0 < ∑' i, f i) : 1 ≤ ∑' i, f i := by
  have he : ∃ i, f i ≠ 0 := by
    by_contra! hn
    rw [ENNReal.tsum_eq_zero.mpr hn] at h
    exact lt_irrefl _ h
  obtain ⟨i,hi⟩ := he
  have hh := ENNReal.le_tsum (f := f) i
  rwa [(hf i).resolve_left hi] at hh

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def peakSurvivalProbability (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
    G.law p {ω | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x}

def peakSurvivalLayerMoment (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n l : ℕ) : ℝ≥0∞ :=
  ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
    {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
      (fun η => restrictedLayerCount G.ends Set.univ {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} η x) ω ∂G.law p)

variable [Countable V] [Countable E]

theorem peak_survival_layer_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (β : ℝ) (hβ : R < β)
    (K : ℝ≥0∞)
    (hsecond : ∀ (k l : ℕ) (x : V),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ)))) (n l : ℕ) (x : V) :
    (∫⁻ ω,
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => restrictedLayerCount G.ends Set.univ {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} η x) ω ∂G.law p) ≤
      4*K*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) := by
  let F (ω : Set E) := restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x
  let N (j : ℕ) (ω : Set E) := restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ)} ω x
  have hmF : Measurable F := measurable_restrictedLayerCount G.ends _ _ x
  have hmN (j : ℕ) : Measurable (N j) := measurable_restrictedLayerCount G.ends _ _ x
  have hpoint (ω : Set E) :
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator F ω ≤
        F ω*(∑ j ∈ Finset.range 4, N j ω) := by
    by_cases hω : 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x
    · rw [Set.indicator_of_mem (show ω ∈ {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x} from hω)]
      have hone : 1 ≤ G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x :=
        by
          unfold peakDownBandCount peakUpBandTransport at hω ⊢
          exact one_le_tsum_of_zero_or_one _ (fun y => by split_ifs <;> simp) hω
      exact (show F ω ≤ F ω*G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x by
        simpa only [mul_one] using mul_le_mul' (le_refl (F ω)) hone).trans
          (mul_le_mul' le_rfl (G.peakDownBandCount_le_four_layers hc hl a R hR n ω x))
    · rw [Set.indicator_of_notMem (show ω ∉ {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x} from hω)]
      exact bot_le
  calc
    _ ≤ ∫⁻ ω, F ω*(∑ j ∈ Finset.range 4, N j ω) ∂G.law p := lintegral_mono hpoint
    _ = ∑ j ∈ Finset.range 4, ∫⁻ ω, F ω*N j ω ∂G.law p := by
      simp_rw [Finset.mul_sum]
      exact lintegral_finsetSum (f := fun j ω => F ω*N j ω) _ (fun j _ => hmF.mul (hmN j))
    _ ≤ ∑ _j ∈ Finset.range 4, K*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro j _
      apply (hsecond l (n+j+1) x).trans
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hh : ((max n l : ℕ) : ℝ) ≤ ((max l (n+j+1) : ℕ) : ℝ) := by
        exact_mod_cast (show max n l ≤ max l (n+j+1) by omega)
      nlinarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

theorem peakSurvivalLayerMoment_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (β : ℝ) (hβ : R < β)
    (K : ℝ≥0∞)
    (hsecond : ∀ (k l : ℕ) (x : V),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ)))) (n l : ℕ) :
    G.peakSurvivalLayerMoment O a R p n l ≤
      (∑ x ∈ O.roots, ENNReal.ofReal (a x))*(4*K)*
        ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) := by
  apply (Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl
    (G.peak_survival_layer_moment_bound hc hl a R hR p β hβ K hsecond n l x)).trans_eq
  rw [←Finset.sum_mul]
  ring

end CriticalPercolation.BondGraph

end

end OAI
