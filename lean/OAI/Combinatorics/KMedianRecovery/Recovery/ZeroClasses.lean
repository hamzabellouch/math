import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Cap
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricCost

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

noncomputable def zeroClasses (D : Finset V) : Finset (SeparationQuotient V) := by
  classical
  exact D.image SeparationQuotient.mk

lemma zero_class_eq (x y : V) : SeparationQuotient.mk x = SeparationQuotient.mk y ↔ dist x y = 0 :=
  SeparationQuotient.mk_eq_mk.trans Metric.inseparable_iff

lemma zero_cost_connection (D S : Finset V) (hc : cost D S = 0) :
    ∀ p ∈ D, connection S p = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => connection_nonneg S p)).mp hc

lemma zero_cost_classes (D S : Finset V) (hS : S.Nonempty) (hc : cost D S = 0) :
    zeroClasses D ⊆ zeroClasses S := by
  classical
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have he : SeparationQuotient.mk (nearest S hS p) = SeparationQuotient.mk p := by
    apply (zero_class_eq _ _).mpr
    rw [dist_comm,nearest_distance,zero_cost_connection D S hc p hp]
  exact Finset.mem_image.mpr ⟨nearest S hS p,nearest_mem S hS p,he⟩

theorem zero_classes_solution (F D : Finset V) (hD : D.Nonempty)
    (hc : zeroClasses D ⊆ zeroClasses F) :
    ∃ S ⊆ F, S.Nonempty ∧ S.card ≤ (zeroClasses D).card ∧ cost D S = 0 := by
  classical
  let Q := zeroClasses D
  have hQ : Q.Nonempty := Finset.image_nonempty.mpr hD
  have hex (q : Q) : ∃ f ∈ F, SeparationQuotient.mk f = q.val := Finset.mem_image.mp (hc q.property)
  let f : Q → V := fun q => Classical.choose (hex q)
  have hf (q : Q) : f q ∈ F ∧ SeparationQuotient.mk (f q) = q.val := Classical.choose_spec (hex q)
  let S := Finset.univ.image f
  have hSF : S ⊆ F := by
    intro s hs
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hs
    exact (hf q).1
  have hS : S.Nonempty := by
    obtain ⟨q,hq⟩ := hQ
    exact ⟨f ⟨q,hq⟩,Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,rfl⟩⟩
  refine ⟨S,hSF,hS,?_,?_⟩
  · have hh := Finset.card_image_le (s := (Finset.univ : Finset Q)) (f := f)
    simpa only [Finset.card_univ,Fintype.card_coe] using hh
  · apply le_antisymm _ (cost_nonneg D S)
    apply Finset.sum_nonpos
    intro p hp
    have hq : SeparationQuotient.mk p ∈ Q := Finset.mem_image.mpr ⟨p,hp,rfl⟩
    let q : Q := ⟨SeparationQuotient.mk p,hq⟩
    have hs : f q ∈ S := Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
    have hd : dist p (f q) = 0 := (zero_class_eq p (f q)).mp (hf q).2.symm
    exact (connection_le hs).trans_eq hd

theorem optimum_zero_iff (F D : Finset V) (hF : F.Nonempty) (hD : D.Nonempty)
    (k : ℕ) (hk : 0 < k) :
    optimum F D k = 0 ↔ zeroClasses D ⊆ zeroClasses F ∧ (zeroClasses D).card ≤ k := by
  classical
  constructor
  · intro hzero
    obtain ⟨S,hSF,hS,hSk,hcost⟩ := optimum_attained F D hF k hk
    have hc : cost D S = 0 := hcost.trans hzero
    have hclass := zero_cost_classes D S hS hc
    refine ⟨hclass.trans (Finset.image_subset_image hSF),?_⟩
    exact (Finset.card_le_card hclass).trans ((Finset.card_image_le).trans hSk)
  · rintro ⟨hc,hcard⟩
    obtain ⟨S,hSF,hS,hSQ,hcost⟩ := zero_classes_solution F D hD hc
    exact le_antisymm ((optimum_le F D S k hSF hS (hSQ.trans hcard)).trans_eq hcost)
      (optimum_nonneg F D k)

end MetricKMedianRecovery.LocalSearch

namespace MetricKMedianRecovery.RoundedAssembly
open LocalSearch Sampling FiniteSampling IntegralAssembly
variable {V : Type*} [PseudoMetricSpace V] [LinearOrder V] [Fintype V]

lemma successful_factor_nonneg : 0 ≤ (2-gamma)*(1+gamma/16) := by
  have hg := gamma_lt_one
  have hp := gamma_pos
  apply mul_nonneg <;> linarith
lemma successful_factor_le_five : (2-gamma)*(1+gamma/16) ≤ 5 := by
  have hg := gamma_lt_one
  have hp := gamma_pos
  nlinarith
lemma rounded_successful_factor : (2-gamma)*(1+gamma/16)*(1+gamma/16) ≤ 2-gamma/2 := by
  have hg := gamma_pos
  have hsq : 0 ≤ gamma^2 := sq_nonneg _
  have hcube : 0 ≤ gamma^3 := pow_nonneg hg.le _
  nlinarith
lemma rounded_fallback_factor : 5*(1+gamma/16) ≤ 6 := by
  linarith [gamma_lt_one]

theorem rounded_calls : ∃ v : ℚ, 0 < v ∧ ∃ Nstar : ℕ, 1 ≤ Nstar ∧
    ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [PseudoMetricSpace V] [LinearOrder V] [Fintype V],
    ∀ (F D : Finset V) (k : ℕ) (ζ M : ℝ),
    D.Nonempty → 0 < k → k ≤ F.card → Disjoint D F → 0 < ζ → 0 < M →
    let eps := gamma/16
    let C := Rounding.cap D.card eps
    let u := eps*M/D.card
    let L0 := countBound (commonL v Nstar D.card C)
    let n := repetitions c L0 ζ
    ∃ run : RecoverySeed D F C L0 (D.card*C) n → Finset V,
      (∀ seed, run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k) ∧
      ∀ O ⊆ F, O.Nonempty → O.card ≤ k →
      (∀ seed, (Rounding.cost u C D (run seed):ℝ) ≤ 5*(Rounding.cost u C D O:ℝ)) ∧
      1-ζ ≤ probability (fun seed => (Rounding.cost u C D (run seed):ℝ) ≤
        (2-gamma)*(1+gamma/16)*(Rounding.cost u C D O:ℝ)) := by
  obtain ⟨v,hv,Nstar,hNstar,c,hc,H⟩ := uniform_finite_experiment
  refine ⟨v,hv,Nstar,hNstar,c,hc,?_⟩
  intro V instMetric instOrder instFinite F D k ζ M hD hk hkF hDF hζ hM
  let eps := gamma/16
  let C := Rounding.cap D.card eps
  let u := eps*M/D.card
  have heps : 0 < eps := div_pos gamma_pos (by norm_num)
  have hn : (0:ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hu : 0 < u := div_pos (mul_pos heps hM) hn
  have hC : 0 < C := Rounding.cap_pos _ _
  let rm : MetricSpace V := Rounding.metric u hu C hC
  have hint (p : V) (_hp : p ∈ D) (i : V) (_hi : i ∈ F) :
      (Rounding.edge u C p i:ℝ) = @dist V rm.toDist p i := rfl
  have hbound (x i : V) (_hi : i ∈ F) : @dist V rm.toDist x i ≤ C := by
    change (Rounding.edge u C x i:ℝ) ≤ C
    exact_mod_cast Rounding.edge_le_cap u C x i
  have hfar (i : V) (hi : i ∈ F) (p : V) (hp : p ∈ D) :
      (1:ℝ) ≤ @dist V rm.toDist i p := by
    change (1:ℝ) ≤ (Rounding.edge u C i p:ℝ)
    have hne : i ≠ p := fun he => (Finset.disjoint_left.mp hDF hp (he ▸ hi)).elim
    exact_mod_cast (Nat.succ_le_iff.mpr (Rounding.edge_pos u hC hne))
  obtain ⟨run,hfeas,hprob,_⟩ := @H V rm instOrder instFinite (Rounding.edge u C) F D k C ζ
    hD hk hkF hC hint hbound hfar hζ
  refine ⟨run,fun seed => ⟨(hfeas seed).1,(hfeas seed).2.1,(hfeas seed).2.2.1⟩,?_⟩
  intro O hOF hO hOk
  have hopt := @LocalSearch.optimum_le V rm.toPseudoMetricSpace F D O k hOF hO hOk
  have heq (S : Finset V) : @LocalSearch.cost V rm.toPseudoMetricSpace D S = (Rounding.cost u C D S:ℝ) :=
    Rounding.metric_cost u hu C hC D S
  refine ⟨?_,?_⟩
  · intro seed
    have hh := (hfeas seed).2.2.2.trans (mul_le_mul_of_nonneg_left hopt (by norm_num : (0:ℝ) ≤ 5))
    simpa only [heq] using hh
  · refine hprob.trans (probability_mono (fun seed hs => ?_))
    have hh := hs.trans (mul_le_mul_of_nonneg_left hopt successful_factor_nonneg)
    simpa only [heq] using hh

end MetricKMedianRecovery.RoundedAssembly

end OAI
