import OAI.Probability.BenjaminiSchramm.KernelDeletionOperator

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def exteriorSusceptibility (G : BondGraph V E) (p : unitInterval)
    (x b : V) (ω : Set E) : ℝ :=
  freshExteriorMoment G p x b ω / (cluster G ω x).ncard

theorem measurable_exteriorSusceptibility [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x b : V) :
    Measurable (exteriorSusceptibility G p x b) :=
  (measurable_freshExteriorMoment G p x b).div
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_cluster_ncard G hloc x))

theorem exteriorSusceptibility_nonneg (G : BondGraph V E) (p : unitInterval)
    (x b : V) (ω : Set E) : 0 ≤ exteriorSusceptibility G p x b ω :=
  div_nonneg (freshExteriorMoment_nonneg G p x b ω) (Nat.cast_nonneg _)

theorem exteriorSusceptibility_eq (G : BondGraph V E) (p : unitInterval)
    (x b : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    exteriorSusceptibility G p x b ω = inducedSusceptibility G (cluster G ω x)ᶜ p b := by
  have hn : ((cluster G ω x).ncard : ℝ) ≠ 0 := by
    exact_mod_cast (cluster_ncard_pos G ω x hf).ne'
  exact mul_div_cancel_left₀ _ hn

noncomputable def exteriorConnectionMoment (G : BondGraph V E) (p : unitInterval)
    (x a b : V) : ℝ≥0∞ :=
  ∫⁻ ω, if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω)
    else 0 ∂law p

theorem connection_exterior_comparison [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (C : ℝ≥0∞)
    (hC : ∀ z, ENNReal.ofReal (susceptibility G p z) ≤ C) (x a b : V) :
    law p {ω | Conn G ω x a} * ENNReal.ofReal (susceptibility G p b) ≤
      exteriorConnectionMoment G p x a b + C *
        ∑' z, law p {ω | Conn G ω x a ∧ Conn G ω x z} *
          law p {ω | Conn G ω b z} := by
  let F (ω : Set E) : ℝ≥0∞ := if Conn G ω x a then
    ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0
  let H (z : V) (ω : Set E) : ℝ≥0∞ := if Conn G ω x a ∧ Conn G ω x z then
    law p {η | Conn G η b z} else 0
  have hF : Measurable F := Measurable.ite (measurableSet_conn G x a)
    (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
    measurable_const
  have hH (z : V) : Measurable (H z) := Measurable.ite
    ((measurableSet_conn G x a).inter (measurableSet_conn G x z))
    measurable_const measurable_const
  have hd : (fun ω => if Conn G ω x a then ENNReal.ofReal (susceptibility G p b) else 0)
      ≤ᵐ[law p] fun ω => F ω + C * ∑' z, H z ω := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hf
    by_cases ha : Conn G ω x a
    · simp only [ite_eq_left ha,F]
      rw [exteriorSusceptibility_eq G p x b ω hf]
      have hh := susceptibility_deletion_ennreal G hloc hqt p hp (cluster G ω x)ᶜ C hC b
      simpa only [Set.mem_compl_iff,cluster,Set.mem_ofPred_eq,ite_not,H,
        ha,true_and,mul_comm] using hh
    · simp only [ite_eq_right ha,F,H,ha,false_and,ite_false,tsum_zero,mul_zero,
        add_zero,le_refl]
  have hi := lintegral_mono_ae hd
  have hleft : (∫⁻ ω, if Conn G ω x a then ENNReal.ofReal (susceptibility G p b)
      else 0 ∂law p) = law p {ω | Conn G ω x a} * ENNReal.ofReal (susceptibility G p b) := by
    simpa only [Set.indicator,Set.mem_ofPred_eq,mul_comm] using
      lintegral_indicator_const (measurableSet_conn G x a) (ENNReal.ofReal (susceptibility G p b))
  have hr : (∫⁻ ω, F ω + C * ∑' z, H z ω ∂law p) =
      exteriorConnectionMoment G p x a b + C *
        ∑' z, law p {ω | Conn G ω x a ∧ Conn G ω x z} * law p {ω | Conn G ω b z} := by
    rw [lintegral_add_left hF,lintegral_const_mul _ (Measurable.tsum hH),
      lintegral_tsum (fun z => (hH z).aemeasurable)]
    congr 2
    apply tsum_congr
    intro z
    have hs : MeasurableSet {ω | Conn G ω x a ∧ Conn G ω x z} :=
      (measurableSet_conn G x a).inter (measurableSet_conn G x z)
    simpa only [H,Set.indicator,Set.mem_ofPred_eq,mul_comm] using
      lintegral_indicator_const hs (law p {ω | Conn G ω b z})
  rwa [hleft,hr] at hi

end Percolation.BenjaminiSchramm

end OAI
