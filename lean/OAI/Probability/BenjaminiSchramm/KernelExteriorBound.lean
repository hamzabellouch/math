import OAI.Probability.BenjaminiSchramm.ExteriorContact
import OAI.Probability.BenjaminiSchramm.BoundaryMultiplicity

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem adjacencyKernel_le_indexed (G : BondGraph V E) (a b : V) :
    (if Adj G a b then (1 : ℝ≥0∞) else 0) ≤ indexedEdgeKernel G a b := by
  by_cases h : Adj G a b
  · obtain ⟨e,he⟩ := h
    rw [ite_eq_left ⟨e,he⟩]
    change (1 : ℝ≥0∞) ≤ ∑' e, if G e = s(a,b) then 1 else 0
    simpa only [ite_eq_left he] using
      (ENNReal.le_tsum (f := fun e => if G e = s(a,b) then (1 : ℝ≥0∞) else 0) e)
  · simp only [ite_eq_right h,zero_le]

theorem neighborSusceptibility_le_edge_action (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (a : V) :
    ENNReal.ofReal (∑ b ∈ neighbors G hloc a, inducedSusceptibility G D p b) ≤
      ∑' b, indexedEdgeKernel G a b * ENNReal.ofReal (inducedSusceptibility G D p b) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => inducedSusceptibility_nonneg G D p b)]
  have he : (∑ b ∈ neighbors G hloc a, ENNReal.ofReal (inducedSusceptibility G D p b)) =
      ∑' b, (if Adj G a b then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (inducedSusceptibility G D p b) := by
    rw [tsum_eq_sum (s := neighbors G hloc a) (fun b hb => by
      rw [ite_eq_right (fun h => hb ((mem_neighbors G hloc a b).mpr h)),zero_mul])]
    apply Finset.sum_congr rfl
    intro b hb
    rw [ite_eq_left ((mem_neighbors G hloc a b).mp hb),one_mul]
  rw [he]
  exact ENNReal.tsum_le_tsum (fun b => mul_le_mul' (adjacencyKernel_le_indexed G a b) le_rfl)

theorem finite_kernel_exterior_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0)
    (W : Finset V) :
    (∑ a ∈ W, ∑' b, K a b * ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b)) ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        ∑ a ∈ W, ∑' b, indexedEdgeKernel G a b *
          ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b) := by
  have hb (a : V) (ha : a ∈ W) :
      (∑' b, K a b * ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b)) ≤
        ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) *
          ENNReal.ofReal (deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) := by
    calc
      _ ≤ ∑' b, K a b *
          (ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) *
            ENNReal.ofReal (deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M)) := by
        apply ENNReal.tsum_le_tsum
        intro b
        by_cases hball : b ∈ reachBall G a M
        · apply mul_le_mul' le_rfl
          rw [←ENNReal.ofReal_mul (zpow_nonneg p.2.1 _)]
          apply ENNReal.ofReal_le_ofReal
          exact inducedSusceptibility_ball_bound G hloc (W : Set V)ᶜ p hp0 a b M
            (by simpa only [Set.mem_compl_iff,Finset.mem_coe,not_not] using ha) hball
            (fun c => summable_restrictedTwoPoint G hloc hqt p hp _ c)
        · rw [hsupport a b hball,zero_mul,zero_mul]
      _ = _ := by rw [ENNReal.tsum_mul_right,hrow,one_mul]
  calc
    _ ≤ ∑ a ∈ W, ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) *
        ENNReal.ofReal (deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) :=
      Finset.sum_le_sum hb
    _ = ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ENNReal.ofReal
        (∑ a ∈ W, deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) := by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun a _ => deletedBoundaryPotential_nonneg G hloc _ p a M),Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ENNReal.ofReal
        (((d+1)^M : ℕ) * ∑ a ∈ W, ∑ b ∈ neighbors G hloc a,
          inducedSusceptibility G (W : Set V)ᶜ p b) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (deletedBoundaryPotential_sum_bound G hloc d hd M W p))
    _ = ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        ∑ a ∈ W, ENNReal.ofReal (∑ b ∈ neighbors G hloc a,
          inducedSusceptibility G (W : Set V)ᶜ p b) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg
          (fun b _ => inducedSusceptibility_nonneg G _ p b)),mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum (fun a _ =>
      neighborSusceptibility_le_edge_action G hloc _ p a))

theorem kernelExteriorPotential_eq_lintegral [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (x : V) :
    kernelExteriorPotential G p K x =
      ∫⁻ ω, ∑' a, ∑' b, K a b *
        (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0) ∂law p := by
  have hm (a b : V) : Measurable (fun ω => K a b *
      (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) :=
    measurable_const.mul (Measurable.ite (measurableSet_conn G x a)
      (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
      measurable_const)
  rw [lintegral_tsum (fun a => (Measurable.tsum (hm a)).aemeasurable)]
  apply tsum_congr
  intro a
  rw [lintegral_tsum (fun b => (hm a b).aemeasurable)]
  apply tsum_congr
  intro b
  exact (lintegral_const_mul _ (Measurable.ite (measurableSet_conn G x a)
    (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
    measurable_const)).symm

theorem kernel_exterior_sample_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0)
    (x : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    (∑' a, ∑' b, K a b *
      (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        ∑' a, ∑' b, indexedEdgeKernel G a b *
          (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0) := by
  let W := hf.toFinset
  have hW : cluster G ω x = (W : Set V) := hf.coe_toFinset.symm
  have hc (a : V) : Conn G ω x a ↔ a ∈ W := by
    change a ∈ cluster G ω x ↔ a ∈ W
    rw [hW]
    rfl
  have he (J : V → V → ℝ≥0∞) :
      (∑' a, ∑' b, J a b *
        (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) =
        ∑ a ∈ W, ∑' b, J a b * ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b) := by
    rw [tsum_eq_sum (s := W) (fun a ha => by
      simp only [ite_eq_right (fun h => ha ((hc a).mp h)),mul_zero,tsum_zero])]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [ite_eq_left ((hc a).mpr ha),exteriorSusceptibility_eq G p x _ ω hf,hW]
  rw [he K,he (indexedEdgeKernel G)]
  exact finite_kernel_exterior_bound G hloc hqt p hp0 hp d hd M K hrow hsupport W

theorem kernelExteriorPotential_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0) (x : V) :
    kernelExteriorPotential G p K x ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        kernelExteriorPotential G p (indexedEdgeKernel G) x := by
  rw [kernelExteriorPotential_eq_lintegral G hloc p K x,
    kernelExteriorPotential_eq_lintegral G hloc p (indexedEdgeKernel G) x]
  have hm (a b : V) : Measurable (fun ω => indexedEdgeKernel G a b *
      (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) :=
    measurable_const.mul (Measurable.ite (measurableSet_conn G x a)
      (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
      measurable_const)
  rw [←lintegral_const_mul _ (Measurable.tsum (fun a => Measurable.tsum (hm a)))]
  apply lintegral_mono_ae
  filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hf
  exact kernel_exterior_sample_bound G hloc hqt p hp0 hp d hd M K hrow hsupport x ω hf

theorem kernelExteriorPotential_le_derivative [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0) (x : V) :
    kernelExteriorPotential G p K x ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        (ENNReal.ofReal (1 - (p : ℝ)) * ENNReal.ofReal (deriv (realSusceptibility G x) p)) := by
  have hh := kernelExteriorPotential_upper G hloc hqt p hp0 hp d hd M K hrow hsupport x
  rwa [kernelExteriorPotential_edge_eq_derivative G hloc hqt p hp0 hp x] at hh

end Percolation.BenjaminiSchramm

end OAI
