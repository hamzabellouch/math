import Mathlib
import OAI.Probability.Ballisticity.Estimates.OutwardCapL1
import OAI.Probability.Ballisticity.Entropy.EntropyDecorrelation

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

section SampledSites

variable {D I A J : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
variable [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

omit [Encodable I] in
lemma measurable_countable_sample {Z : J → (I → A) → ℝ}
    (hZ : ∀ j, Measurable (Z j)) {j : D → J} (hj : Measurable j) :
    Measurable (fun x : D × (I → A) => Z (j x.1) x.2) := by
  have hm : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  exact hm.comp ((hj.comp measurable_fst).prodMk measurable_snd)

omit [Encodable I] in
lemma sampled_exponential_integrable {Z : J → (I → A) → ℝ} {s Q : ℝ}
    (hZ : ∀ j, Measurable (Z j))
    (he : ∀ j, Integrable (fun ω => Real.exp (s * Z j ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ j, (∫ ω, Real.exp (s * Z j ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    {j : D → J} (hj : Measurable j) :
    Integrable (fun x : D × (I → A) => Real.exp (s * Z (j x.1) x.2))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))) ∧
    (∫ x : D × (I → A), Real.exp (s * Z (j x.1) x.2)
      ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ Q := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let F : D × (I → A) → ℝ := fun x => Real.exp (s * Z (j x.1) x.2)
  have hF : Measurable F := Real.measurable_exp.comp
    (measurable_const.mul (measurable_countable_sample hZ hj))
  have hFm : Measurable (fun d => ∫ ω, F (d, ω) ∂P) := hF.stronglyMeasurable.integral_prod_right.measurable
  have hFi : Integrable (fun d => ∫ ω, F (d, ω) ∂P) δ :=
    integrable_bounded_nonneg hFm (fun d => integral_nonneg fun ω => (Real.exp_pos _).le)
      (fun d => heQ (j d))
  have hi : Integrable F (δ.prod P) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun d => he (j d)), ?_⟩
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hFi
  refine ⟨hi, ?_⟩
  change (∫ x, F x ∂δ.prod P) ≤ Q
  rw [integral_prod _ hi]
  calc
    (∫ d, ∫ ω, F (d, ω) ∂P ∂δ) ≤ (∫ _ : D, Q ∂δ) := integral_mono hFi (integrable_const Q) (fun d => heQ (j d))
    _ = Q := by simp

omit [Encodable I] [IsProbabilityMeasure δ] [IsProbabilityMeasure ν] in
lemma sampled_locality {Z : J → (I → A) → ℝ}
    (N : ℕ → J → Set I) (j : ℕ → D → J) (hj : ∀ r, Measurable (j r))
    (hloc : ∀ K η : ℝ, 0 < K → 0 < η → ∃ n : ℕ, ∃ F : J → (I → A) → ℝ,
      (∀ a, @Measurable _ _ (rows (N n a)) _ (F a)) ∧
      (∀ a ω, 0 ≤ F a ω ∧ F a ω ≤ K) ∧
      (∀ a, (∫ ω, |min K (Z a ω) - F a ω| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η))
    (hescape : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ,
      ∀ᶠ r in atTop, Disjoint S (N n (j r d))) :
    ∀ K > 0, EscapingLocalApproximation δ ν
      (fun r x => min K (Z (j r x.1) x.2)) K := by
  intro K hK η hη
  obtain ⟨n, F, hFm, hFb, hFerr⟩ := hloc K η hK hη
  refine ⟨fun r x => F (j r x.1) x.2, fun r d => N n (j r d), ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact measurable_countable_sample (fun a => (hFm a).mono (rows_le _) le_rfl) (hj r)
  · exact fun r x => hFb _ _
  · exact fun r d => hFm _
  · exact fun r d => hFerr (j r d)
  · exact fun S hS => hescape n S hS

lemma sampled_entropy_decorrelation {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hf1 : (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) = 1)
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp ((2 * c) * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp ((2 * c) * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (hZi : ∀ a, Integrable (Z a) (Measure.infinitePi (fun _ : I => ν)))
    (hZC : ∀ a, (∫ ω, Z a ω ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (N : ℕ → J → Set I) (j : ℕ → D → J) (hj : ∀ r, Measurable (j r))
    (hloc : ∀ K η : ℝ, 0 < K → 0 < η → ∃ n : ℕ, ∃ F : J → (I → A) → ℝ,
      (∀ a, @Measurable _ _ (rows (N n a)) _ (F a)) ∧
      (∀ a ω, 0 ≤ F a ω ∧ F a ω ≤ K) ∧
      (∀ a, (∫ ω, |min K (Z a ω) - F a ω| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η))
    (hescape : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ,
      ∀ᶠ r in atTop, Disjoint S (N n (j r d))) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      (∫ x : D × (I → A), f x * Z (j r x.1) x.2
        ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ C + ε := by
  exact entropy_decorrelation δ ν hc hC hf hf0 hfi hf1 hH
    (fun r => measurable_countable_sample hZ (hj r)) (fun r x => hZ0 _ _)
    (fun r => (sampled_exponential_integrable δ ν hZ he heQ (hj r)).1)
    (fun r => (sampled_exponential_integrable δ ν hZ he heQ (hj r)).2)
    (fun r d => hZi (j r d)) (fun r d => hZC (j r d))
    (sampled_locality δ ν N j hj hloc hescape)

end SampledSites

lemma limsup_le_of_nonneg_eventual {a : ℕ → ℝ} {C : ℝ}
    (h0 : ∀ r, 0 ≤ a r) (h : ∀ ε > 0, ∀ᶠ r in atTop, a r ≤ C + ε) :
    Filter.limsup a atTop ≤ C := by
  apply (Filter.limsup_le_iff' (isCoboundedUnder_le_of_le atTop h0)
    (isBoundedUnder_of_eventually_le (h 1 zero_lt_one))).mpr
  intro y hy
  simpa only [add_sub_cancel] using h (y - C) (sub_pos.mpr hy)

end TailDecorrelation

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma analytic_rows_eq {d : ℕ} (S : Set (Lattice d)) :
    TailDecorrelation.rows (A := Row d) S = rowSigma S :=
  TailDecorrelation.rows_eq_iSup_two S

lemma pair_neighborhoods_escape {d : ℕ} (e : Direction d) (a : ℝ)
    (k : Fin d) (x : ℕ → Lattice d × Lattice d)
    (hx : Tendsto (fun r => (x r).1 k) atTop atBot)
    (hy : Tendsto (fun r => (x r).2 k) atTop atTop)
    (N : ℕ) (S : Set (Lattice d)) (hS : S.Finite) :
    ∀ᶠ r in atTop, Disjoint S (upperPairNeighborhood e a (x r) N) := by
  have hz : ∀ z ∈ S, ∀ᶠ r in atTop,
      z ∉ LatticeBall (x r).1 N ∪ LatticeBall (x r).2 N := by
    intro z _
    filter_upwards [(tendsto_atBot.mp hx) (z k - (N : ℤ) - 1),
      (tendsto_atTop.mp hy) (z k + (N : ℤ) + 1)] with r hrx hry
    intro hz
    rcases hz with hz | hz
    · have hh := (abs_le.mp (hz k)).2
      omega
    · have hh := (abs_le.mp (hz k)).1
      omega
  filter_upwards [hS.eventually_all.mpr hz] with r hr
  exact Set.disjoint_left.mpr fun z hz hz' => hr z hz hz'.1

lemma integrable_and_mean_le_of_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Z : Ω → ℝ} {c B : ℝ} (hc : 0 < c)
    (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hi : Integrable (fun ω => Real.exp (c * Z ω)) μ)
    (hB : (∫ ω, Real.exp (c * Z ω) ∂μ) ≤ B) :
    Integrable Z μ ∧ (∫ ω, Z ω ∂μ) ≤ B / c := by
  have hb : ∀ ω, Z ω ≤ Real.exp (c * Z ω) / c := by
    intro ω
    apply (le_div_iff₀ hc).mpr
    have h := Real.add_one_le_exp (c * Z ω)
    nlinarith
  have hz : Integrable Z μ := (hi.div_const c).mono' hZ.aestronglyMeasurable
    (Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]
      exact hb ω))
  refine ⟨hz, ?_⟩
  calc
    (∫ ω, Z ω ∂μ) ≤ (∫ ω, Real.exp (c * Z ω) / c ∂μ) := integral_mono hz (hi.div_const c) hb
    _ = (∫ ω, Real.exp (c * Z ω) ∂μ) / c := integral_div _ _
    _ ≤ B / c := div_le_div_of_nonneg_right hB hc.le

end DirectionalTransience

namespace DirectionalTransience

theorem actual_sampled_tail_decorrelation {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A M : ℝ, 0 < A ∧ 0 ≤ M ∧
      ∀ (D : Type) [MeasurableSpace D] (δ : Measure D) [IsProbabilityMeasure δ]
        (g : D × Environment d → ℝ),
        Measurable g → (∀ x, 0 ≤ g x) → Integrable g (δ.prod (environmentLaw ν)) →
        (∫ x, g x ∂δ.prod (environmentLaw ν)) = 1 →
        Integrable (fun x => TailDecorrelation.entropyPlus (g x)) (δ.prod (environmentLaw ν)) →
        ∀ (x : ℕ → D → {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}),
          (∀ r, Measurable (x r)) →
          (∀ᵐ z ∂δ, Tendsto (fun r => (x r z).1.1 f.1) atTop atBot ∧
            Tendsto (fun r => (x r z).1.2 f.1) atTop atTop) →
          Filter.limsup (fun r => ∫ z, g z * outwardCanonicalExcess e f A (x r z.1).1 z.2
            ∂δ.prod (environmentLaw ν)) atTop ≤ M := by
  classical
  obtain ⟨A,c,B,hA,hc,hB,hbound,hloc⟩ := actual_outward_order ν hue e f hef htrans
  let J := {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}
  let Z : J → Environment d → ℝ := fun p => outwardCanonicalExcess e f A p.1
  have hZm : ∀ p : J, Measurable (Z p) := fun p =>
    ((hbound 0 p.1 p.2).2.1).mono (rowSigma_le _) le_rfl
  have hZ0 : ∀ p : J, ∀ ω, 0 ≤ Z p ω := fun p => (hbound 0 p.1 p.2).1
  have he : ∀ p : J, Integrable (fun ω => Real.exp (c * Z p ω)) (environmentLaw ν) :=
    fun p => (hbound 0 p.1 p.2).2.2.1
  have heB : ∀ p : J, (∫ ω, Real.exp (c * Z p ω) ∂environmentLaw ν) ≤ B :=
    fun p => (hbound 0 p.1 p.2).2.2.2.1
  have hZi : ∀ p : J, Integrable (Z p) (environmentLaw ν) := fun p =>
    (integrable_and_mean_le_of_exp (environmentLaw ν) hc (hZm p) (hZ0 p) (he p) (heB p)).1
  have hZB : ∀ p : J, (∫ ω, Z p ω ∂environmentLaw ν) ≤ B / c := fun p =>
    (integrable_and_mean_le_of_exp (environmentLaw ν) hc (hZm p) (hZ0 p) (he p) (heB p)).2
  refine ⟨A,B/c,hA,div_nonneg hB.le hc.le,?_⟩
  intro D mD δ hδ g hgm hg0 hgi hg1 hgH x hxm hxe
  have hcap : ∀ K η : ℝ, 0 < K → 0 < η → ∃ N : ℕ,
      ∃ F : J → Environment d → ℝ,
      (∀ p, @Measurable _ _ (TailDecorrelation.rows (upperPairNeighborhood e 0 p.1 N)) _ (F p)) ∧
      (∀ p ω, 0 ≤ F p ω ∧ F p ω ≤ K) ∧
      (∀ p, (∫ ω, |min K (Z p ω) - F p ω| ∂environmentLaw ν) ≤ η) := by
    intro K η hK hη
    obtain ⟨N,hN⟩ := outward_cap_locality_L1 ν e f A hloc hK hη
    have hh : ∀ p : J, ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e 0 p.1 N)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ K) ∧
        (∫ ω, |min (Z p ω) K - F ω| ∂environmentLaw ν) < η :=
      fun p => hN 0 p.1 p.2
    choose F hFm hFb hFe using hh
    refine ⟨N,F,?_,hFb,?_⟩
    · intro p
      rw [analytic_rows_eq]
      exact hFm p
    · intro p
      simpa only [min_comm] using (hFe p).le
  have hesc : ∀ N (S : Set (Lattice d)), S.Finite → ∀ᵐ z ∂δ,
      ∀ᶠ r in atTop, Disjoint S (upperPairNeighborhood e 0 (x r z).1 N) := by
    intro N S hS
    filter_upwards [hxe] with z hz
    exact pair_neighborhoods_escape e 0 f.1 (fun r => (x r z).1) hz.1 hz.2 N S hS
  have he' : ∀ p : J, Integrable (fun ω => Real.exp ((2*(c/2)) * Z p ω)) (environmentLaw ν) := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using he
  have heB' : ∀ p : J, (∫ ω, Real.exp ((2*(c/2)) * Z p ω) ∂environmentLaw ν) ≤ B := by
    simpa only [show 2*(c/2) = c by ring] using heB
  apply TailDecorrelation.limsup_le_of_nonneg_eventual
  · exact fun r => integral_nonneg fun z => mul_nonneg (hg0 z) (hZ0 _ _)
  · exact TailDecorrelation.sampled_entropy_decorrelation δ ν (by linarith) (div_nonneg hB.le hc.le)
      hgm hg0 hgi hg1 hgH hZm hZ0 he' heB' hZi hZB
      (fun N p => upperPairNeighborhood e 0 p.1 N) x hxm hcap hesc

end DirectionalTransience

end

end OAI
