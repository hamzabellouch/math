import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexCollar_mono {S T : Set V} (hST : S⊆T) (R : ℕ) :
    G.vertexCollar S R⊆G.vertexCollar T R := by
  intro y hy
  obtain ⟨v,hv,hy⟩ := Set.mem_iUnion₂.mp hy
  exact Set.mem_iUnion₂.mpr ⟨v,hST hv,hy⟩

lemma initial_mark_subset_relay (t z : V → ℝ) (σ e ρ : ℝ) (hρ : ρ ≤ e) :
    relayMark t z 0 σ ρ⊆relayRegion t z σ e 0 := by
  intro v hv
  obtain ⟨ht₀,ht₁,hz⟩ := hv
  change |t v-(0:ℕ)| ≤ ((0:ℕ)+1)*e ∧ |z v-σ*(0:ℕ)/4| ≤ Relay.width 0
  norm_num [Relay.width] at ht₀ ht₁ hz ⊢
  exact ⟨by rw [abs_of_nonneg ht₀]; linarith,hz⟩

lemma relay_coordinate_scale (L R m : ℕ) (e ρ : ℝ) (he : 0<e) (hρ : 0 ≤ ρ)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) :
    ρ ≤ e ∧ (L+1)*e+R*ρ<1 ∧ R*ρ+e/4 ≤ 1/4 ∧ R*ρ+e/4 ≤ e ∧
      (L+1)*e+(R+m)*ρ+e/4<1/2 := by
  have hR : 0 ≤ (R:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hm : 0 ≤ (m:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hL : 0 ≤ (L:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he.le
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma relay_collar_in_domain (t z : V → ℝ) (σ e ρ J : ℝ) (L R i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i ≤ L) (hsmall : (L+1)*e+R*ρ<1)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ) :
    G.vertexCollar (relayRegion t z σ e i) R⊆relayDomain t z J (L+1/2) σ := by
  intro y hy
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  apply Relay.move_path_contained J L i hi hJ (t y,z y) (t y,z y)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 <;> norm_num

lemma forceOutside_induced (S : Set V) (ω : Set E) :
    BernoulliProduct.forceOn (G.inducedEdges S)ᶜ ∅ ω=ω∩G.inducedEdges S := by
  ext b
  by_cases hb : b∈G.inducedEdges S <;> simp [hb]

def corridorRelay (t z : V → ℝ) (σ e ρ : ℝ) (L i : ℕ) : Set V :=
  if i=0 then relayMark t z 0 σ ρ
  else if i ≤ L then relayRegion t z σ e i else relayMark t z (L+1/2) σ ρ

lemma corridorRelay_subset (t z : V → ℝ) (σ e ρ : ℝ) (hρe : ρ ≤ e)
    (L i : ℕ) (hi : i ≤ L) : corridorRelay t z σ e ρ L i⊆relayRegion t z σ e i := by
  by_cases h0 : i=0
  · subst i
    simpa [corridorRelay] using initial_mark_subset_relay t z σ e ρ hρe
  · simp only [corridorRelay,ite_eq_right h0,ite_eq_left hi,Subset.rfl]

theorem coordinate_moves_relay_estimates (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (p : unitInterval) (η : ℝ)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
      (G.coordinateMove t z m e y s)) :
    ∀ i ≤ L,
      G.vertexCollar (corridorRelay t z σ e ρ L i) R⊆relayDomain t z J (L+1/2) σ ∧
      ∀ y∈G.vertexCollar (corridorRelay t z σ e ρ L i) R,
        1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
          ((BernoulliProduct.forceOn (G.inducedEdges (relayDomain t z J (L+1/2) σ))ᶜ ∅) ⁻¹'
            G.seedHitEvent (G.vertexBall y m) (corridorRelay t z σ e ρ L (i+1))) := by
  obtain ⟨hρe,hsmall,hheight,htime,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  intro i hi
  have hsub := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R
  refine ⟨hsub.trans (G.relay_collar_in_domain t z σ e ρ J L R i hσ he.le hρ hJ hi hsmall ht hz),?_⟩
  intro y hy
  apply (hmove y (Relay.selectedSign (z y-σ*(i:ℝ)/4)) (Relay.selectedSign_abs _)).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  rw [Set.mem_preimage,G.forceOutside_induced]
  by_cases hiL : i<L
  · have hh := G.full_relay_move t z σ e ρ J L R m i hσ he.le hρ hJ hiL hsmall
      hheight htime ht hz (hsub hy) hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1)) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false,ite_eq_left (by omega : i+1 ≤ L)] using hh
  · have hiEq : i=L := by omega
    subst i
    have hh := G.last_relay_move t z σ e ρ J L R m hσ he.le hρ hJ hL hlast ht hz
      (hsub hy) _ hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false,ite_eq_right (by omega : ¬L+1 ≤ L)] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
