import Mathlib
import OAI.Probability.UnimodularPercolation.Deformation.Calibration

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CountedCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem preimage_diff_singleton (b : E ≃ E) (ω : Set E) (e : E) :
    (b ⁻¹' ω) \ {e} = b ⁻¹' (ω \ {b e}) := by
  ext f
  simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]

theorem corridorCounted_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set E) (D : Set V) (ω : Set E) (x y : V) :
    corridorCounted G (b ⁻¹' S) (b ⁻¹' B) (a ⁻¹' D) (b ⁻¹' ω) x y ↔
      corridorCounted G S B D ω (a x) (a y) := by
  have he : (b ⁻¹' ω) ∩ internalEdges G (a ⁻¹' D) = b ⁻¹' (ω ∩ internalEdges G D) := by
    rw [internalEdges_aut_preimage G hab,Set.preimage_inter]
  simp only [corridorCounted,he,conn_aut_iff G hab,preimage_diff_singleton,
    Set.mem_preimage]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hp,hB⟩
    constructor
    · intro e he
      obtain ⟨f,rfl⟩ := b.surjective e
      exact hp f he
    · apply Set.disjoint_left.mpr
      intro e he hw
      obtain ⟨f,rfl⟩ := b.surjective e
      exact Set.disjoint_left.mp hB he hw
  · rintro ⟨hp,hB⟩
    exact ⟨fun e he => hp (b e) he,Set.disjoint_left.mpr (fun e he hw => Set.disjoint_left.mp hB he hw)⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_counted {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted (a ⁻¹' D) (b ⁻¹' ω) x y ↔ (autEquiv hab w).counted D ω (a x) (a y) := by
  have hr : w.retained = b ⁻¹' (autEquiv hab w).retained := by
    ext e
    exact (aut_retained hab w e).symm
  have hb : w.blockers = b ⁻¹' (autEquiv hab w).blockers := by
    ext e
    exact (aut_blockers hab w e).symm
  rw [counted_iff,counted_iff,aut_path_length,hr,hb,corridorCounted_aut G hab]

end RawCorridor

theorem corridorPenaltyTerm_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) {k : ℕ} (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenaltyTerm G P p (a ⁻¹' D) (b ⁻¹' ω) x y w =
      corridorPenaltyTerm G P p D ω (a x) (a y) (RawCorridor.autEquiv hab w) := by
  simp only [corridorPenaltyTerm,w.aut_counted hab D ω x y,RawCorridor.aut_weight hab P hP]

theorem corridorPenalty_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenalty G P p k (a ⁻¹' D) (b ⁻¹' ω) x y =
      corridorPenalty G P p k D ω (a x) (a y) := by
  unfold corridorPenalty
  rw [←(RawCorridor.autEquiv hab).tsum_eq (corridorPenaltyTerm G P p D ω (a x) (a y))]
  exact tsum_congr (fun w => corridorPenaltyTerm_aut G hab P hP p w D ω x y)

end CountedCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t (a ⁻¹' D) (b ⁻¹' ω) x y =
      deformedConnection G P p k t D ω (a x) (a y) := by
  simp only [deformedConnection,corridorPenalty_aut G hab P hP,Set.mem_preimage,
    internalEdges_aut_preimage G hab,←Set.preimage_inter,conn_aut_iff G hab]

theorem deformedKernel_aut [Countable V] [Countable E]
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) :
    deformedKernel G P p k t D (a x) (a y) = deformedKernel G P p k t (a ⁻¹' D) x y := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (measurable_deformedConnection G P p k t (a ⁻¹' D) x y).aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [deformedKernel,deformedConnection_aut G hab P hP] using h.symm

theorem deformedSusceptibility_aut [Countable V] [Countable E]
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D (a x) = deformedSusceptibility G P p k t (a ⁻¹' D) x := by
  unfold deformedSusceptibility
  rw [←a.tsum_eq (deformedKernel G P p k t D (a x))]
  exact tsum_congr (fun y => deformedKernel_aut G hab P hP p k t D x y)

 

noncomputable def corridorDerivativeContribution (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (x y : V) : ℝ :=
  ∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
    deformedConnection G P p k t Set.univ ω x y ∂law p

theorem corridorDerivativeContribution_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (x y : V) :
    0 ≤ corridorDerivativeContribution G P p t w x y :=
  integral_corridorDerivativeTerm_nonneg G P hP p k t w x y

theorem corridorDerivativeContribution_aut [Countable V] [Countable E]
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (x y : V) :
    corridorDerivativeContribution G P p t (RawCorridor.autEquiv hab w) (a x) (a y) =
      corridorDerivativeContribution G P p t w x y := by
  have hm := ((measurable_corridorPenaltyTerm G P p (a ⁻¹' Set.univ) x y w).mul
    (measurable_deformedConnection G P p k t (a ⁻¹' Set.univ) x y))
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  have hc (ω : Set E) := corridorPenaltyTerm_aut G hab P hP p w Set.univ ω x y
  have hd (ω : Set E) := deformedConnection_aut G hab P hP p k t Set.univ ω x y
  simp only [Set.preimage_univ] at hc hd
  simpa only [Pi.mul_apply,corridorDerivativeContribution,Set.preimage_univ,hc,hd] using h.symm

end DeformationCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DerivativeTonelli
attribute [local instance] Classical.propDecidable Classical.decEq

theorem derivative_field_summable (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    Summable (fun yw : V × RawCorridor G k => corridorPenaltyTerm G P p Set.univ ω x yw.1 yw.2 *
      deformedConnection G P p k t Set.univ ω x yw.1) := by
  have hs (y : V) : Summable (fun w : RawCorridor G k =>
      corridorPenaltyTerm G P p Set.univ ω x y w * deformedConnection G P p k t Set.univ ω x y) :=
    (corridorPenalty_summable G hloc P p k Set.univ ω x y).mul_right
      (deformedConnection G P p k t Set.univ ω x y)
  have hr : Summable (fun y => corridorPenalty G P p k Set.univ ω x y *
      deformedConnection G P p k t Set.univ ω x y) := by
    apply summable_of_hasFiniteSupport
    apply hf.subset
    intro y hy
    by_contra hn
    apply hy
    change corridorPenalty G P p k Set.univ ω x y * deformedConnection G P p k t Set.univ ω x y = 0
    rw [deformedConnection_eq_zero_of_not_conn G P p k t Set.univ ω x y hn,mul_zero]
  have hn : 0 ≤ (fun yw : V × RawCorridor G k =>
      corridorPenaltyTerm G P p Set.univ ω x yw.1 yw.2 * deformedConnection G P p k t Set.univ ω x yw.1) :=
    fun yw => mul_nonneg (corridorPenaltyTerm_nonneg G P hP p Set.univ ω x yw.1 yw.2)
      (deformedConnection_nonneg G P p k t Set.univ ω x yw.1)
  apply (summable_prod_of_nonneg hn).mpr
  refine ⟨hs,?_⟩
  simpa only [tsum_mul_right,corridorPenalty] using hr

theorem derivative_field_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    (∑' yw : V × RawCorridor G k, corridorPenaltyTerm G P p Set.univ ω x yw.1 yw.2 *
      deformedConnection G P p k t Set.univ ω x yw.1) =
        deformedDerivativeMass G P p k t Set.univ ω x := by
  rw [(derivative_field_summable G hloc P hP p k t ω x hf).tsum_prod]
  simp only [tsum_mul_right,corridorPenalty,deformedDerivativeMass]

 

theorem derivative_contribution_sum [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : V) :
    Summable (fun yw : V × RawCorridor G k => corridorDerivativeContribution G (walkKernel G hloc a) p t yw.2 x yw.1) ∧
    (∑' yw : V × RawCorridor G k, corridorDerivativeContribution G (walkKernel G hloc a) p t yw.2 x yw.1) =
      ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω x ∂law p := by
  let F := fun yw : V × RawCorridor G k => fun ω =>
    corridorPenaltyTerm G (walkKernel G hloc a) p Set.univ ω x yw.1 yw.2 *
      deformedConnection G (walkKernel G hloc a) p k t Set.univ ω x yw.1
  have hs : ∀ᵐ ω ∂law p, Summable (fun yw => F yw ω) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    exact derivative_field_summable G hloc _ hP p k t ω x hω
  have he : (fun ω => ∑' yw, F yw ω) =ᵐ[law p]
      fun ω => deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω x := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    exact derivative_field_sum G hloc _ hP p k t ω x hω
  have hh := real_tonelli_of_integrable_sum (law p) F
    (fun yw => integrable_corridorDerivativeTerm G _ hP p k t ht Set.univ x yw.1 yw.2)
    (fun yw ω => mul_nonneg (corridorPenaltyTerm_nonneg G _ hP p Set.univ ω x yw.1 yw.2)
      (deformedConnection_nonneg G _ p k t Set.univ ω x yw.1)) hs
    ((integrable_deformedDerivativeMass G hloc hqt d hd a hP p hp0 hp k t ht Set.univ x).congr he.symm)
  exact ⟨hh.1,hh.2.trans (integral_congr_ae he)⟩

end DerivativeTonelli
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DerivativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem raw_from_sum_eq_masked (G : BondGraph V E) (hloc : LocallyFinite G)
    (k : ℕ) (u : V) (f : RawCorridor G k → ℝ) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) k u, f ⟨u,w⟩) =
      ∑' w : RawCorridor G k, if w.base = u then f w else 0 := by
  have hs := summable_raw_selection G hloc k {u} (Set.finite_singleton u)
    (fun w : RawCorridor G k => w.base = u) (fun _ h => h) f
  rw [hs.tsum_sigma]
  have he (x : V) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k x,
      if (RawCorridor.base ⟨x,w⟩) = u then f ⟨x,w⟩ else 0) =
      if x = u then (∑' w : RawFrom (openSimpleGraph G Set.univ) k u, f ⟨u,w⟩) else 0 := by
    by_cases hx : x = u
    · subst x; simp only [RawCorridor.base,ite_true]
    · simp only [RawCorridor.base,hx,ite_false,tsum_zero]
  simp only [he,tsum_ite_eq]

noncomputable def derivativeTransportMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (x u : V) : ℝ :=
  ∑' w : RawFrom (openSimpleGraph G Set.univ) k u,
    ∑' y, corridorDerivativeContribution G P p t ⟨u,w⟩ x y

theorem derivativeTransportMass_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (x u : V) :
    0 ≤ derivativeTransportMass G P p k t x u :=
  tsum_nonneg (fun w => tsum_nonneg (fun y => corridorDerivativeContribution_nonneg G P hP p t ⟨u,w⟩ x y))

theorem derivativeTransportMass_aut [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (x u : V) :
    derivativeTransportMass G P p k t (a x) (a u) = derivativeTransportMass G P p k t x u := by
  unfold derivativeTransportMass
  rw [raw_from_sum_eq_masked G hloc k (a u) (fun w => ∑' y, corridorDerivativeContribution G P p t w (a x) y),
    raw_from_sum_eq_masked G hloc k u (fun w => ∑' y, corridorDerivativeContribution G P p t w x y)]
  rw [←(RawCorridor.autEquiv hab).tsum_eq]
  apply tsum_congr
  intro w
  simp only [RawCorridor.aut_base,a.injective.eq_iff]
  by_cases hw : w.base = u
  · simp only [hw,ite_true]
    rw [←a.tsum_eq]
    exact tsum_congr (fun y => corridorDerivativeContribution_aut G hab P hP p t w x y)
  · simp only [hw,ite_false]

end DerivativeTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DerivativeTransportSums
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_swapped_real {α β : Type*} (f : α → β → ℝ)
    (hs : Summable (fun ab : α × β => f ab.1 ab.2)) :
    Summable (fun ba : β × α => f ba.2 ba.1) := by
  exact hs.comp_injective (Equiv.prodComm β α).injective

theorem derivativeTransportMass_row (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : V) :
    Summable (derivativeTransportMass G (walkKernel G hloc a) p k t x) ∧
    (∑' u, derivativeTransportMass G (walkKernel G hloc a) p k t x u) =
      ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω x ∂law p := by
  obtain ⟨hs,he⟩ := derivative_contribution_sum G hloc hqt d hd a hP p hp0 hp k t ht x
  have hs' : Summable (fun wy : RawCorridor G k × V =>
      corridorDerivativeContribution G (walkKernel G hloc a) p t wy.1 x wy.2) := by
    exact summable_swapped_real (fun y w => corridorDerivativeContribution G (walkKernel G hloc a) p t w x y) hs
  have hr := hs'.prod.sigma
  refine ⟨hr,?_⟩
  change (∑' u, ∑' w : RawFrom (openSimpleGraph G Set.univ) k u, ∑' y,
    corridorDerivativeContribution G (walkKernel G hloc a) p t ⟨u,w⟩ x y) = _
  rw [←hs'.prod.tsum_sigma,←hs'.tsum_prod]
  exact ((Equiv.prodComm (RawCorridor G k) V).tsum_eq
    (fun yw : V × RawCorridor G k => corridorDerivativeContribution G (walkKernel G hloc a) p t yw.2 x yw.1)).trans he

theorem derivativeTransportMass_column (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (u : V) :
    Summable (fun x => derivativeTransportMass G P p k t x u) ∧
    (∑' x, derivativeTransportMass G P p k t x u) =
      ∑' w : RawFrom (openSimpleGraph G Set.univ) k u,
        ∑' xy : V × V, corridorDerivativeContribution G P p t ⟨u,w⟩ xy.1 xy.2 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k u)
  have hs (w : RawFrom (openSimpleGraph G Set.univ) k u) :
      Summable (fun xy : V × V => corridorDerivativeContribution G P p t ⟨u,w⟩ xy.1 xy.2) :=
    summable_corridorDerivativeTerm_pairs G hG hloc hqt P hP p hp0 hp t ht ⟨u,w⟩
  have hh : Summable (fun x => ∑ w : RawFrom (openSimpleGraph G Set.univ) k u,
      ∑' y, corridorDerivativeContribution G P p t ⟨u,w⟩ x y) :=
    summable_sum (fun w _ => (hs w).prod)
  refine ⟨by simpa only [derivativeTransportMass,tsum_fintype] using hh,?_⟩
  simp only [derivativeTransportMass,tsum_fintype]
  rw [Summable.tsum_finsetSum (fun w _ => (hs w).prod)]
  exact Finset.sum_congr rfl (fun w _ => (hs w).tsum_prod.symm)

end DerivativeTransportSums
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedDerivative
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

 

theorem averaged_derivative_transport (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p) =
      ∑ i, weight i * ∑' w : RawFrom (openSimpleGraph G Set.univ) k (root i),
        ∑' xy : V × V, corridorDerivativeContribution G (walkKernel G hloc a) p t ⟨root i,w⟩ xy.1 xy.2 := by
  have hh := htr.real root weight Γ (derivativeTransportMass G (walkKernel G hloc a) p k t)
    (fun g hg x u => by
      obtain ⟨b,hb⟩ := hΓ hg
      exact derivativeTransportMass_aut G hloc hb _ (walkKernel_covariant G hloc a hb) p k t x u)
    (fun x => (derivativeTransportMass_row G hloc hqt d hd a hP p hp0 hp k t ht x).1)
    (fun u => (derivativeTransportMass_column G hG hloc hqt _ hP p hp0 hp k t ht u).1)
  simpa only [(derivativeTransportMass_row G hloc hqt d hd a hP p hp0 hp k t ht _).2,
    (derivativeTransportMass_column G hG hloc hqt _ hP p hp0 hp k t ht _).2] using hh

noncomputable def averagedDeformedSusceptibility (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * deformedSusceptibility G P p k t Set.univ (root i)

theorem hasDerivAt_averagedDeformedSusceptibility (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight)
      (-(∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p)) t := by
  have he : -(∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p) =
      ∑ i, weight i * (-(∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p)) := by
    simp only [mul_neg,Finset.sum_neg_distrib]
  rw [he]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_deformedSusceptibility G hloc hqt d hd a hP p hp0 hp k t ht Set.univ (root i)).const_mul (weight i))

end AveragedDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PathAverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

noncomputable def rawPathAverage (G : BondGraph V E) (P : V → V → ℝ) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (f : RawCorridor G k → ℝ) : ℝ :=
  ∑ i, weight i * ∑' w : RawFrom (openSimpleGraph G Set.univ) k (root i),
    w.2.mass P * f ⟨root i,w⟩

theorem rawPathAverage_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (f g : RawCorridor G k → ℝ) (hfg : ∀ w, f w ≤ g w) :
    rawPathAverage G P k root weight f ≤ rawPathAverage G P k root weight g := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  unfold rawPathAverage
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k (root i))
  simp only [tsum_fintype]
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hfg _) (w.2.mass_nonneg P hP))

theorem rawPathAverage_sub (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (k : ℕ) (root : ι → V) (weight : ι → ℝ)
    (f g : RawCorridor G k → ℝ) :
    rawPathAverage G P k root weight (fun w => f w-g w) =
      rawPathAverage G P k root weight f - rawPathAverage G P k root weight g := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  have he (i : ι) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k (root i),
      w.2.mass P * (f ⟨root i,w⟩-g ⟨root i,w⟩)) =
      (∑' w : RawFrom (openSimpleGraph G Set.univ) k (root i), w.2.mass P*f ⟨root i,w⟩) -
      (∑' w : RawFrom (openSimpleGraph G Set.univ) k (root i), w.2.mass P*g ⟨root i,w⟩) := by
    let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k (root i))
    simp only [tsum_fintype,mul_sub,Finset.sum_sub_distrib]
  simp only [rawPathAverage]
  simp only [he]
  simp only [mul_sub,Finset.sum_sub_distrib]

theorem rawPathAverage_const_mul (G : BondGraph V E) (P : V → V → ℝ) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (c : ℝ) (f : RawCorridor G k → ℝ) :
    rawPathAverage G P k root weight (fun w => c*f w) = c*rawPathAverage G P k root weight f := by
  unfold rawPathAverage
  simp only [←mul_left_comm c,tsum_mul_left,Finset.mul_sum]

noncomputable def retainedSusceptibilityProduct (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) : ℝ :=
  if 3 ≤ w.path.length then
    deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.base *
      deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.endpoint
  else 0

end PathAverage
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedCalibratedDecrease
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

theorem raw_derivative_template_row_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (w : RawCorridor G k)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t*c) * (w.probability P *
      (retainedSusceptibilityProduct G P p t w -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2*(matrixCoeff (T^3) w.base w.endpoint).re)) ≤
      ∑' xy : V × V, corridorDerivativeContribution G P p t w xy.1 xy.2 := by
  by_cases hlen : 3 ≤ w.path.length
  · have hh := calibrated_derivative_template_row_lower G hG hloc hqt d
      (fun x => (neighbors_card_le_degree G hloc x).trans (hd x)) P hP hpcrit p hp hpnear T hT k w hlen c hc t ht
    simpa only [retainedSusceptibilityProduct,hlen,ite_true,corridorDerivativeContribution,
      mul_assoc,mul_left_comm (Real.exp (-t*c))] using hh
  · have hC : 0 ≤ 1+2*(d:ℝ)/(pc G:ℝ) := by positivity
    have hA := (((hT.positiveRealMatrix G p T).pow 3) w.base w.endpoint).2
    have hpr := w.2.2.mass_nonneg P hP
    have hr : 0 ≤ ∑' xy : V × V, corridorDerivativeContribution G P p t w xy.1 xy.2 :=
      tsum_nonneg (fun xy => corridorDerivativeContribution_nonneg G P hP p t w xy.1 xy.2)
    apply le_trans _ hr
    simp only [retainedSusceptibilityProduct,hlen,ite_false,zero_sub,mul_neg]
    exact neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le (mul_nonneg hpr
      (mul_nonneg (mul_nonneg hC (sq_nonneg _)) hA)))

 
theorem averaged_derivative_raw_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (c : ℝ) (hc : ∀ w : RawCorridor G k,
      (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight (walkKernel G hloc a) p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t*c) *
      (rawPathAverage G (walkKernel G hloc a) k root weight (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) -
       (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
         rawPathAverage G (walkKernel G hloc a) k root weight (fun w => (matrixCoeff (T^3) w.base w.endpoint).re)) ≤
      ∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p := by
  rw [averaged_derivative_transport G hG hloc hqt root weight Γ hΓ htr d hd a hP p
      ((half_pos hpcrit).trans_le hpnear) hp k t ht]
  rw [←rawPathAverage_const_mul G _ k root weight _ (fun w => (matrixCoeff (T^3) w.base w.endpoint).re),
    ←rawPathAverage_sub G hloc]
  unfold rawPathAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (hw i)
  rw [←tsum_mul_left]
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k (root i))
  simp only [tsum_fintype]
  exact Finset.sum_le_sum (fun w _ => raw_derivative_template_row_lower G hG hloc hqt d hd _ hP
    hpcrit p hp hpnear T hT k ⟨root i,w⟩ c (hc _) t ht)

end AveragedCalibratedDecrease
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PathErrorTrace
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem rawPathAverage_operator_trace (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (A : Hilbert V →L[ℂ] Hilbert V) (hAs : IsSelfAdjoint A)
    (k : ℕ) (root : ι → V) (weight : ι → ℝ) :
    rawPathAverage G (walkKernel G hloc a) k root weight
      (fun w => (matrixCoeff A w.base w.endpoint).re) = (rootTrace root weight (P^k*A)).re := by
  have he (u : V) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k u,
      w.2.mass (walkKernel G hloc a) * (matrixCoeff A u w.1).re) = (matrixCoeff (P^k*A) u u).re := by
    change RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k u
      (fun v => (matrixCoeff A u v).re) = _
    rw [raw_integral_operator G hloc a P hpos hP]
    simp only [matrixCoeff_real_symm A hAs u]
    exact ((hpos.pow k).mul_hasSum A u u).tsum_eq
  simp only [rawPathAverage,RawCorridor.base,RawCorridor.endpoint,he,rootTrace,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

open scoped ComplexOrder
attribute [local instance] spectralRealOperatorScalarTower spectralRealOperatorSMulCommClass
local instance averagedDecreasePathNonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)
local instance averagedDecreasePathContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

 

theorem rawPathAverage_operator_le_norm (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (Γ : Set (V ≃ V)) (htr : RootTransport root weight Γ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hPi : KernelInvariant Γ P) (hPs : IsSelfAdjoint P)
    (A : Hilbert V →L[ℂ] Hilbert V) (hAi : KernelInvariant Γ A) (hA : 0 ≤ A) (k : ℕ) :
    rawPathAverage G (walkKernel G hloc a) k root weight
      (fun w => (matrixCoeff A w.base w.endpoint).re) ≤
      ‖P‖^k * (rootTrace root weight A).re := by
  rw [rawPathAverage_operator_trace G hloc a P hpos hP A (IsSelfAdjoint.of_nonneg hA)]
  have hh := rootTrace_positive_mul_le root weight htr hw A (P^k) hAi (hPi.pow k) hA (hPs.pow k)
  have hr := (Complex.le_def.mp hh).1
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  have hn : ‖P^k‖ ≤ ‖P‖^k := by
    cases k with
    | zero =>
      simp only [pow_zero]
      have he : (1 : Hilbert V →L[ℂ] Hilbert V) = ContinuousLinearMap.id ℂ (Hilbert V) := by ext f; rfl
      rw [he]
      exact ContinuousLinearMap.norm_id_le
    | succ j => exact norm_pow_le' P (Nat.succ_pos j)
  exact hr.trans (mul_le_mul_of_nonneg_right hn
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw A hA)).1)

end PathErrorTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ComplexOrder
section UniformAveragedDecrease
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]
attribute [local instance] spectralRealOperatorScalarTower spectralRealOperatorSMulCommClass
local instance averagedDecreaseUniformNonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)
local instance averagedDecreaseUniformContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

 

theorem exists_uniform_averaged_decrease (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hPs : IsSelfAdjoint P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T → ∀ (k : ℕ), 3 ≤ k →
      ∀ (t : ℝ), 0 ≤ t →
      Real.exp (-t*Real.exp (C*(k:ℝ))) *
        (rawPathAverage G (walkKernel G hloc a) k root weight
          (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) -
          (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
            (‖P‖^k * (rootTrace root weight (T^3)).re)) ≤
        ∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p := by
  obtain ⟨C,hC,hcost⟩ := exists_uniform_corridor_leg_cost G hG hloc d hd a hK hpcrit hpcrit₁
  refine ⟨C,hC,?_⟩
  intro p hpnear hp T hT k hk t ht
  have hpositive : 0 ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr (hT.isPositive G p T)
  have hTi : KernelInvariant Γ T := fun g hg => hT.invariant G p T g (hΓ hg)
  have hPi : KernelInvariant Γ P := by
    intro g hg x y
    obtain ⟨b,hb⟩ := hΓ hg
    simp only [hP,walkKernel_covariant G hloc a hb]
  have herr := rawPathAverage_operator_le_norm G hloc a root weight hw Γ htr P hpos hP hPi hPs
    (T^3) (hTi.pow 3) (CStarAlgebra.pow_nonneg T 3 hpositive) k
  have hCnonneg : 0 ≤ (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 := by positivity
  apply le_trans _ (averaged_derivative_raw_lower G hG hloc hqt root weight hw Γ hΓ htr
    d hd a hK hpcrit p hp hpnear T hT k (Real.exp (C*(k:ℝ))) (hcost p hpnear hp k hk) t ht)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (mul_le_mul_of_nonneg_left herr hCnonneg) _)
    (Real.exp_pos _).le

end UniformAveragedDecrease
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeformedRowComparison
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

 

theorem exists_uniform_deformed_row_comparison (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C cf : ℝ, 0 < C ∧ 0 < cf ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G → ∀ (k : ℕ), 3 ≤ k → ∀ (t : ℝ),
      0 ≤ t → t*Real.exp (C*(k:ℝ)) ≤ 1 → ∀ x,
      cf*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x := by
  obtain ⟨C,hC,hmove⟩ := exists_uniform_deformed_endpoint_comparison G hloc hqt d hd a hP hpcrit hpcrit₁
  have hex (ij : ι × ι) : ∃ l : List E, Along G (root ij.1) l (root ij.2) := by
    obtain ⟨l,hl,_,_⟩ := conn_exists_bond_trail G (conn_univ_of_connected G hconn (root ij.1) (root ij.2))
    exact ⟨l,hl⟩
  choose path hpath using hex
  let N := ∑ ij : ι × ι, (path ij).length
  have hlen (i j : ι) : (path (i,j)).length ≤ N :=
    Finset.single_le_sum (f := fun ij : ι × ι => (path ij).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
  refine ⟨C,Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N,hC,mul_pos (Real.exp_pos _) (pow_pos (half_pos hpcrit) N),?_⟩
  intro p hpnear hp k hk t ht htc x
  obtain ⟨j,g,b,hgb,hgx⟩ := hcover x
  have hb (i : ι) : (Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N)*
      deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root i) ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root j) := by
    have hh := hmove p hpnear hp k hk t ht Set.univ (root j) (root i) (path (j,i))
      (Set.mem_univ _) (hpath (j,i)) (fun _ _ _ _ => Set.mem_univ _)
    have hpow : ((pc G:ℝ)/2)^N ≤ (p:ℝ)^(path (j,i)).length :=
      (pow_le_pow_left₀ (half_pos hpcrit).le hpnear N).trans
        (pow_le_pow_of_le_one p.2.1 p.2.2 (hlen j i))
    have he : Real.exp (-(N:ℝ)) ≤ Real.exp (-t*((path (j,i)).length*Real.exp (C*(k:ℝ)))) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right htc (Nat.cast_nonneg (path (j,i)).length : (0:ℝ) ≤ _)
      have hn : ((path (j,i)).length:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr (hlen j i)
      nlinarith
    exact (mul_le_mul_of_nonneg_right (mul_le_mul he hpow (pow_nonneg (half_pos hpcrit).le _) (Real.exp_pos _).le)
      (deformedSusceptibility_nonneg G _ p k t Set.univ (root i))).trans hh
  rw [←hgx,deformedSusceptibility_aut G hgb _ (walkKernel_covariant G hloc a hgb)]
  simp only [Set.preimage_univ]
  calc
    _ = ∑ i, weight i*((Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N)*
        deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root i)) := by
      simp only [averagedDeformedSusceptibility,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ i, weight i*deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root j) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = _ := by rw [←Finset.sum_mul,hw1,one_mul]

end DeformedRowComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredSegments
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 
def segmentOrbit (G : BondGraph V E) (γ : I → V) : Set (I → V) :=
  {s | ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ s = a ∘ γ}

omit [Fintype I] in
theorem segmentOrbit_aut_iff (G : BondGraph V E) (γ s : I → V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    a ∘ s ∈ segmentOrbit G γ ↔ s ∈ segmentOrbit G γ := by
  constructor
  · rintro ⟨c,d,hcd,he⟩
    refine ⟨c.trans a.symm,d.trans b.symm,isAut_trans G hcd (isAut_symm G h),?_⟩
    funext i
    have hh := congrFun he i
    simpa only [Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply] using congrArg a.symm hh
  · rintro ⟨c,d,hcd,rfl⟩
    exact ⟨c.trans a,d.trans b,isAut_trans G hcd h,rfl⟩

theorem finite_segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    {s ∈ segmentOrbit G γ | s i = x}.Finite := by
  apply (Set.Finite.pi' (fun _ : I => finite_reachBall hloc x n)).subset
  rintro s ⟨⟨a,b,hab,rfl⟩,hx⟩ j
  have hh := mem_reachBall_aut G hab (hdiam i j)
  change a (γ i) = x at hx
  simpa only [hx,Function.comp_apply] using hh

noncomputable def segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) : Finset (I → V) :=
  (finite_segmentAnchors G hloc γ n hdiam i x).toFinset

theorem mem_segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) (s : I → V) :
    s ∈ segmentAnchors G hloc γ n hdiam i x ↔ s ∈ segmentOrbit G γ ∧ s i = x := by
  exact Set.Finite.mem_toFinset _

theorem segmentAnchors_nonempty_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    (segmentAnchors G hloc γ n hdiam i x).Nonempty ↔ x ∈ vertexOrbit G (γ i) := by
  constructor
  · rintro ⟨s,hs⟩
    obtain ⟨⟨a,b,h,rfl⟩,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
    exact ⟨a,b,h,hx⟩
  · rintro ⟨a,b,h,hx⟩
    exact ⟨a ∘ γ,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨⟨a,b,h,rfl⟩,hx⟩⟩

end AnchoredSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

def segmentAut (a : V ≃ V) : (I → V) ≃ (I → V) where
  toFun s := a ∘ s
  invFun s := a.symm ∘ s
  left_inv s := by funext i; exact a.symm_apply_apply (s i)
  right_inv s := by funext i; exact a.apply_symm_apply (s i)

theorem segmentAnchors_map (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    segmentAnchors G hloc γ n hdiam i (a x) =
      (segmentAnchors G hloc γ n hdiam i x).map (segmentAut a).toEmbedding := by
  ext s
  rw [Finset.mem_map,mem_segmentAnchors]
  constructor
  · rintro ⟨hs,hx⟩
    refine ⟨a.symm ∘ s,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨?_,?_⟩,?_⟩
    · exact (segmentOrbit_aut_iff G γ s (isAut_symm G h)).mpr hs
    · simp only [Function.comp_apply,hx,Equiv.symm_apply_apply]
    · funext j; exact a.apply_symm_apply (s j)
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨ht,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x t).mp ht
    exact ⟨(segmentOrbit_aut_iff G γ t h).mpr ht,congrArg a hx⟩

theorem segmentAnchors_card_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    (segmentAnchors G hloc γ n hdiam i (a x)).card = (segmentAnchors G hloc γ n hdiam i x).card := by
  rw [segmentAnchors_map G hloc γ n hdiam i x h,Finset.card_map]

 

noncomputable def anchoredPositionKernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V) : ℝ :=
  ∑ s ∈ segmentAnchors G hloc γ n hdiam i x,
    if y = s j then ((segmentAnchors G hloc γ n hdiam i x).card : ℝ)⁻¹ else 0

theorem anchoredPositionKernel_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V) :
    0 ≤ anchoredPositionKernel G hloc γ n hdiam i j x y := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs <;> positivity

theorem anchoredPositionKernel_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    anchoredPositionKernel G hloc γ n hdiam i j (a x) (a y) =
      anchoredPositionKernel G hloc γ n hdiam i j x y := by
  simp only [anchoredPositionKernel,segmentAnchors_map G hloc γ n hdiam i x h,
    Finset.card_map,Finset.sum_map,Equiv.toEmbedding_apply,
    segmentAut,Equiv.coe_fn_mk,Function.comp_apply,Equiv.apply_eq_iff_eq]

end AnchoredPositionKernels
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionRows
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem anchoredPositionKernel_hasSum (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x : V) :
    HasSum (anchoredPositionKernel G hloc γ n hdiam i j x)
      (if x ∈ vertexOrbit G (γ i) then (1:ℝ) else 0) := by
  have hh := hasSum_sum (s := segmentAnchors G hloc γ n hdiam i x)
    (fun s _ => hasSum_ite_eq (s j) (((segmentAnchors G hloc γ n hdiam i x).card:ℝ)⁻¹))
  have he : (∑ s ∈ segmentAnchors G hloc γ n hdiam i x,
      ((segmentAnchors G hloc γ n hdiam i x).card:ℝ)⁻¹) =
      if x ∈ vertexOrbit G (γ i) then (1:ℝ) else 0 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    by_cases hx : x ∈ vertexOrbit G (γ i)
    · have hn := Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i x).mpr hx)
      rw [ite_eq_left hx,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
    · have he : segmentAnchors G hloc γ n hdiam i x = ∅ := Finset.not_nonempty_iff_eq_empty.mp
        (fun h => hx ((segmentAnchors_nonempty_iff G hloc γ n hdiam i x).mp h))
      simp only [he,Finset.card_empty,Nat.cast_zero,zero_mul,ite_eq_right hx]
  rw [he] at hh
  exact hh

theorem anchoredPositionKernel_eq_zero_off_ball (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V)
    (hxy : y ∉ reachBall G x n) : anchoredPositionKernel G hloc γ n hdiam i j x y = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  apply ite_eq_right
  intro hy
  obtain ⟨⟨a,b,hab,rfl⟩,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
  change a (γ i) = x at hx
  change y = a (γ j) at hy
  exact hxy (by simpa only [hx,←hy] using mem_reachBall_aut G hab (hdiam i j))

theorem anchoredPositionKernel_eq_zero_off_orbits (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V) :
    x ∉ vertexOrbit G (γ i) ∨ y ∉ vertexOrbit G (γ j) →
      anchoredPositionKernel G hloc γ n hdiam i j x y = 0 := by
  intro h
  apply Finset.sum_eq_zero
  intro s hs
  apply ite_eq_right
  intro hy
  obtain ⟨⟨a,b,hab,rfl⟩,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
  rcases h with h | h
  · exact h ⟨a,b,hab,hx⟩
  · exact h ⟨a,b,hab,hy.symm⟩

end AnchoredPositionRows
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionColumns
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem anchoredPositionKernel_columnSummable (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (y : V) :
    Summable (fun x => anchoredPositionKernel G hloc γ n hdiam i j x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
  intro x hx
  simp only [Set.Finite.mem_toFinset] at hx
  apply Finset.sum_eq_zero
  intro s hs
  apply ite_eq_right
  intro hy
  obtain ⟨⟨a,b,hab,rfl⟩,he⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
  change a (γ i) = x at he
  change y = a (γ j) at hy
  exact hx (by simpa only [he,←hy] using mem_reachBall_aut G hab (hdiam j i))

theorem anchoredPositionKernel_column_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (y : V) :
    (∑' x, anchoredPositionKernel G hloc γ n hdiam i j x y) =
      if y ∈ vertexOrbit G (γ j) then
        ∑' x, anchoredPositionKernel G hloc γ n hdiam i j x (γ j) else 0 := by
  by_cases hy : y ∈ vertexOrbit G (γ j)
  · rw [ite_eq_left hy]
    obtain ⟨a,b,hab,rfl⟩ := hy
    rw [←a.tsum_eq]
    exact tsum_congr (fun x => anchoredPositionKernel_aut G hloc γ n hdiam i j x (γ j) hab)
  · rw [ite_eq_right hy]
    calc
      _ = ∑' _ : V, (0:ℝ) := tsum_congr (fun x =>
        anchoredPositionKernel_eq_zero_off_orbits G hloc γ n hdiam i j x y (Or.inr hy))
      _ = 0 := tsum_zero

 

theorem anchoredPositionKernel_column_mass {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) :
    (∑ r, if root r ∈ vertexOrbit G (γ i) then weight r else 0) =
      (∑ r, if root r ∈ vertexOrbit G (γ j) then weight r else 0) *
      ∑' x, anchoredPositionKernel G hloc γ n hdiam i j x (γ j) := by
  have ht := htr.real root weight Γ (anchoredPositionKernel G hloc γ n hdiam i j)
    (fun a ha x y => by
      obtain ⟨b,hb⟩ := hΓ ha
      exact anchoredPositionKernel_aut G hloc γ n hdiam i j x y hb)
    (fun x => (anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).summable)
    (anchoredPositionKernel_columnSummable G hloc γ n hdiam i j)
  calc
    _ = ∑ r, weight r * ∑' y, anchoredPositionKernel G hloc γ n hdiam i j (root r) y := by
      apply Finset.sum_congr rfl
      intro r _
      rw [(anchoredPositionKernel_hasSum G hloc γ n hdiam i j (root r)).tsum_eq]
      split_ifs <;> simp only [mul_one,mul_zero]
    _ = _ := ht
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [anchoredPositionKernel_column_orbit]
      split_ifs <;> simp only [mul_zero,zero_mul]

theorem anchoredPositionKernel_column_ratio {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I)
    (hj : 0 < ∑ r, if root r ∈ vertexOrbit G (γ j) then weight r else 0) (y : V) :
    (∑' x, anchoredPositionKernel G hloc γ n hdiam i j x y) =
      if y ∈ vertexOrbit G (γ j) then
        (∑ r, if root r ∈ vertexOrbit G (γ i) then weight r else 0) /
        (∑ r, if root r ∈ vertexOrbit G (γ j) then weight r else 0) else 0 := by
  have he := anchoredPositionKernel_column_mass G hloc root weight Γ hΓ htr γ n hdiam i j
  rw [anchoredPositionKernel_column_orbit]
  congr 1
  exact (eq_div_iff (ne_of_gt hj)).mpr (by simpa only [mul_comm] using he.symm)

end AnchoredPositionColumns
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section AsymmetricSchur
open scoped ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_operator_of_unit_row_column_bound (U : V → V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hU : ∀ x y, 0 ≤ U x y)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, U x y ≤ 1)
    (hcol : ∀ y (s : Finset V), ∑ x ∈ s, U x y ≤ D) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ Real.sqrt D ∧
      ∀ x y, matrixCoeff A x y = (U x y : ℂ) := by
  have hentry (x y : V) : U x y ≤ 1 := by simpa only [Finset.sum_singleton] using hrow x {y}
  have hcm (y : V) : Memℓp (fun x => (U x y : ℂ)) 2 := by
    apply (memℓp_gen_iff'' (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    refine ⟨D,hD,fun s => ?_⟩
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact (Finset.sum_le_sum (fun x _ => by nlinarith [hentry x y,hU x y])).trans (hcol y s)
  let col (y : V) : Hilbert V := ⟨fun x => (U x y : ℂ),hcm y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hn (f : V →₀ ℂ) : ‖L f‖ ≤ Real.sqrt D * ‖finiteEmbedding f‖ := by
    apply lp.norm_le_of_forall_sum_le (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    intro s
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    have hpoint (x : V) : ‖L f x‖^2 ≤ ∑ y ∈ f.support, ‖f y‖^2 * U x y := by
      have hn0 : 0 ≤ ∑ y ∈ f.support, ‖f y‖*U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (hU x y))
      have hn1 : ‖L f x‖ ≤ ∑ y ∈ f.support, ‖f y‖*U x y := by
        simp only [L,Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,
          Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro y _
        simp [col,abs_of_nonneg (hU x y)]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul f.support
        (f := fun y => U x y) (g := fun y => ‖f y‖^2*U x y)
        (r := fun y => ‖f y‖*U x y)
        (fun y _ => hU x y)
        (fun y _ => mul_nonneg (sq_nonneg _) (hU x y)) (fun y _ => by nlinarith)
      have hn2 : 0 ≤ ∑ y ∈ f.support, ‖f y‖^2*U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (sq_nonneg _) (hU x y))
      have hr := mul_le_mul_of_nonneg_right (hrow x f.support) hn2
      rw [one_mul] at hr
      exact (sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn1).trans (hcs.trans hr)
    calc
      ∑ x ∈ s, ‖L f x‖^2 ≤ ∑ x ∈ s, ∑ y ∈ f.support, ‖f y‖^2*U x y :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = ∑ y ∈ f.support, ‖f y‖^2*∑ x ∈ s, U x y := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ f.support, ‖f y‖^2*D :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hcol y s) (sq_nonneg _))
      _ = D*∑ y ∈ f.support, ‖finiteEmbedding f y‖^2 := by
        simp only [finiteEmbedding_apply]
        rw [←Finset.sum_mul,mul_comm]
      _ ≤ D*‖finiteEmbedding f‖^2 := by
        apply mul_le_mul_of_nonneg_left _ hD
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) (finiteEmbedding f) f.support
      _ = (Real.sqrt D*‖finiteEmbedding f‖)^2 := by rw [mul_pow,Real.sq_sqrt hD]
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense (Real.sqrt_nonneg _) hn,?_⟩
  intro x y
  have he := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨Real.sqrt D,hn⟩
    (Finsupp.single y (1:ℂ))
  simp only [finiteEmbedding_single] at he
  change (L.extendOfNorm finiteEmbedding) (lp.single 2 y (1:ℂ)) x = _
  rw [he]
  simp [L,col]

end AsymmetricSchur
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem exists_anchoredPositionOperator (G : BondGraph V E) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I)
    (hj : 0 < ∑ r, if root r ∈ vertexOrbit G (γ j) then weight r else 0) :
    ∃ H : Hilbert V →L[ℂ] Hilbert V,
      (∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam i j x y : ℂ)) ∧
      ‖H‖ ≤ Real.sqrt ((∑ r, if root r ∈ vertexOrbit G (γ i) then weight r else 0) /
        (∑ r, if root r ∈ vertexOrbit G (γ j) then weight r else 0)) := by
  have hnum : 0 ≤ ∑ r, if root r ∈ vertexOrbit G (γ i) then weight r else 0 :=
    Finset.sum_nonneg (fun r _ => by split_ifs; exact hw r; exact le_refl 0)
  have hratio := div_nonneg hnum hj.le
  obtain ⟨H,hn,hH⟩ := exists_operator_of_unit_row_column_bound
    (anchoredPositionKernel G hloc γ n hdiam i j) _ hratio
    (anchoredPositionKernel_nonneg G hloc γ n hdiam i j)
    (fun x s => ((anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).summable.sum_le_tsum s
      (fun y _ => anchoredPositionKernel_nonneg G hloc γ n hdiam i j x y)).trans (by
        rw [(anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).tsum_eq]
        split_ifs <;> norm_num))
    (fun y s => ((anchoredPositionKernel_columnSummable G hloc γ n hdiam i j y).sum_le_tsum s
      (fun x _ => anchoredPositionKernel_nonneg G hloc γ n hdiam i j x y)).trans (by
        rw [anchoredPositionKernel_column_ratio G hloc root weight Γ hΓ htr γ n hdiam i j hj y]
        split_ifs; exact le_refl _; exact hratio))
  exact ⟨H,hH,hn⟩

 
theorem exists_anchoredPositionOperator_uniform (G : BondGraph V E) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ a ∈ Γ, a (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) :
    ∃ H : Hilbert V →L[ℂ] Hilbert V,
      (∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam i j x y : ℂ)) ∧
      ‖H‖ ≤ Real.sqrt c := by
  let U := anchoredPositionKernel G hloc γ n hdiam i j
  have hn : ∀ x y, 0 ≤ U x y := anchoredPositionKernel_nonneg G hloc γ n hdiam i j
  have hr : ∀ x, Summable (U x) := fun x => (anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).summable
  have hcol := anchoredPositionKernel_columnSummable G hloc γ n hdiam i j
  have hb (x : V) : (∑' y, U x y) ≤ 1 := by
    rw [(anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).tsum_eq]
    split_ifs <;> norm_num
  have hi : ∀ a ∈ Γ, ∀ x y, U (a x) (a y) = U x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    exact anchoredPositionKernel_aut G hloc γ n hdiam i j x y hb
  have hbcol (y : V) : (∑' x, U x y) ≤ c := by
    simpa only [mul_one] using transported_column_le root weight Γ htr hcov hw hw1 c hc hmin U hn hi hr hcol 1 hb y
  obtain ⟨H,hHn,hH⟩ := exists_operator_of_unit_row_column_bound U c hc hn
    (fun x s => ((hr x).sum_le_tsum s (fun y _ => hn x y)).trans (hb x))
    (fun y s => ((hcol y).sum_le_tsum s (fun x _ => hn x y)).trans (hbcol y))
  exact ⟨H,hH,hHn⟩

end AnchoredPositionOperators
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section RawReversal
namespace HoldingWalk
variable {H : SimpleGraph V}

 
def snocHold : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H (k+1) x y
  | _,_,_,.nil x => .hold (.nil x)
  | _,_,_,.hold w => .hold (snocHold w)
  | _,_,_,.step h w => .step h (snocHold w)

 
def snocStep : {k : ℕ} → {x y z : V} → HoldingWalk H k x y → H.Adj y z → HoldingWalk H (k+1) x z
  | _,_,_,z,.nil _,h => .step h (.nil z)
  | _,_,_,_,.hold w,h => .hold (snocStep w h)
  | _,_,_,_,.step h' w,h => .step h' (snocStep w h)

 

def reverse : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H k y x
  | _,_,_,.nil x => .nil x
  | _,_,_,.hold w => snocHold (reverse w)
  | _,_,_,.step h w => snocStep (reverse w) h.symm

theorem reverse_snocHold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.reverse = w.reverse.hold := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocHold,reverse,ih]
  | step h w ih => simp only [snocHold,reverse,ih,snocStep]

theorem reverse_snocStep {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).reverse = .step h.symm w.reverse := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocStep,reverse,ih,snocHold]
  | step h' w ih => simp only [snocStep,reverse,ih]

theorem reverse_reverse {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.reverse.reverse = w := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,reverse_snocHold,ih]
  | step h w ih => simp only [reverse,reverse_snocStep,ih]

def reverseEquiv (k : ℕ) (x y : V) : HoldingWalk H k x y ≃ HoldingWalk H k y x where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

theorem mass_snocHold (P : V → V → ℝ) {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.mass P = w.mass P * P y y := by
  induction w with
  | nil => simp only [snocHold,mass,mul_one,one_mul]
  | hold w ih => simp only [snocHold,mass,ih,mul_assoc]
  | step h w ih => simp only [snocHold,mass,ih,mul_assoc]

theorem mass_snocStep (P : V → V → ℝ) {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).mass P = w.mass P * P y z := by
  induction w with
  | nil => simp only [snocStep,mass,mul_one,one_mul]
  | hold w ih => simp only [snocStep,mass,ih,mul_assoc]
  | step h' w ih => simp only [snocStep,mass,ih,mul_assoc]

theorem mass_reverse (P : V → V → ℝ) (hP : ∀ x y, P x y = P y x)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.reverse.mass P = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,mass_snocHold,mass,ih,mul_comm]
  | step h w ih => simp only [reverse,mass_snocStep,mass,ih,hP,mul_comm]

theorem vertices_snocHold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.vertices = w.vertices ++ [y] := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocHold,vertices,ih,List.cons_append]
  | step h w ih => simp only [snocHold,vertices,ih,List.cons_append]

theorem vertices_snocStep {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).vertices = w.vertices ++ [z] := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocStep,vertices,ih,List.cons_append]
  | step h' w ih => simp only [snocStep,vertices,ih,List.cons_append]

theorem vertices_reverse {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.reverse.vertices = w.vertices.reverse := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,vertices_snocHold,vertices,ih,List.reverse_cons]
  | step h w ih => simp only [reverse,vertices_snocStep,vertices,ih,List.reverse_cons]

end HoldingWalk
end RawReversal
end Percolation

end OAI
