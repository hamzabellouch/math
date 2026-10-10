import OAI.Probability.BenjaminiSchramm.ExteriorExposure

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinct_exterior_event (G : BondGraph V E) (x a b y : V) :
    {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y} =
      {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} := by
  ext ω
  constructor
  · rintro ⟨⟨ha,hb⟩,hby⟩
    exact ⟨fun hxy => hb (conn_trans G ω hxy (conn_symm G ω hby)),
      ha,conn_symm G ω hby⟩
  · rintro ⟨hxy,ha,hyb⟩
    exact ⟨⟨ha,fun hb => hxy (conn_trans G ω hb (conn_symm G ω hyb))⟩,
      conn_symm G ω hyb⟩

theorem lintegral_distinctClusterPair [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) =
      ∑' a, ∑' b, J a b *
        law p {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} := by
  let F (a b : V) (ω : Set E) : ℝ≥0∞ :=
    if ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b) then J a b else 0
  have hF (a b : V) : Measurable (F a b) := Measurable.ite
    ((measurableSet_conn G x y).compl.inter
      ((measurableSet_conn G x a).inter (measurableSet_conn G y b)))
    measurable_const measurable_const
  have he (ω : Set E) : (if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0) =
      ∑' a, ∑' b, F a b ω := by
    by_cases hxy : Conn G ω x y
    · simp only [hxy,not_true_eq_false,ite_false,F,false_and,tsum_zero]
    · simp only [hxy,not_false_eq_true,ite_true,F,true_and,clusterPairKernel]
  simp_rw [he]
  rw [lintegral_tsum (fun a => (Measurable.tsum (hF a)).aemeasurable)]
  apply tsum_congr
  intro a
  rw [lintegral_tsum (fun b => (hF a b).aemeasurable)]
  apply tsum_congr
  intro b
  have hs : MeasurableSet {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} :=
    (measurableSet_conn G x y).compl.inter
      ((measurableSet_conn G x a).inter (measurableSet_conn G y b))
  simpa only [F,Set.indicator,Set.mem_ofPred_eq] using lintegral_indicator_const hs (J a b)

theorem kernelExteriorPotential_eq_distinctClusterPair [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (J : V → V → ℝ≥0∞) (x : V) :
    kernelExteriorPotential G p J x =
      ∑' y, ∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p := by
  unfold kernelExteriorPotential
  simp_rw [exteriorConnectionMoment_eq_tsum G hloc hqt p hp,
    distinct_exterior_event G,lintegral_distinctClusterPair G p J x,
    ←ENNReal.tsum_mul_left]
  calc
    _ = ∑' a, ∑' y, ∑' b, J a b *
        law p {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} :=
      tsum_congr (fun _ => ENNReal.tsum_comm)
    _ = _ := ENNReal.tsum_comm

theorem kernelExteriorPotential_edge_eq_contact [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    kernelExteriorPotential G p (indexedEdgeKernel G) x =
      ∑' y, ENNReal.ofReal (∫ ω, fullLargeContact G x y 0 ω ∂law p) := by
  rw [kernelExteriorPotential_eq_distinctClusterPair G hloc hqt p hp]
  apply tsum_congr
  intro y
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_fullContact_subcritical G hloc hqt p hp x y)
    (Filter.Eventually.of_forall (fullLargeContact_nonneg G x y 0)),
    fullContact_lintegral_eq_kernel G hloc p x y (subcritical_cluster_finite_ae G p hp x)]

theorem kernelExteriorPotential_edge_eq_derivative [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (x : V) :
    kernelExteriorPotential G p (indexedEdgeKernel G) x =
      ENNReal.ofReal (1 - (p : ℝ)) * ENNReal.ofReal (deriv (realSusceptibility G x) p) := by
  rw [kernelExteriorPotential_edge_eq_contact G hloc hqt p hp,
    (hasDerivAt_realSusceptibility G hloc hqt p hp0 hp x).deriv,
    ENNReal.ofReal_tsum_of_nonneg (fun y => russoSlope_nonneg G x y p p.2.2)
      (summable_russoSlope G hloc hqt p hp x),←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  have hp1 : 0 < 1 - (p : ℝ) := sub_pos.mpr ((show (p : ℝ) < (pc G : ℝ) from hp).trans_le (pc G).2.2)
  have he : (∫ ω, fullLargeContact G x y 0 ω ∂law p) =
      (1 - (p : ℝ)) * russoSlope G x y p := by
    rw [russoSlope,realContactExpectation_coe]
    field_simp
  rw [he,ENNReal.ofReal_mul hp1.le]

end Percolation.BenjaminiSchramm

end OAI
