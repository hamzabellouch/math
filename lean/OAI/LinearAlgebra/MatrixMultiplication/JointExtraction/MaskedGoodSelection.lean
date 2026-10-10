import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MaskedRates

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointMaskedGoodSelection

open Filter JointCoarseHashing JointExtractionRates JointMaskedSelection
open JointOrdinarySelection (hashLevel hashSet)
open JointMaskedRates
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem eventually_exists_good_selection
    {P E O V : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
    (d : ∀ N, OrbitData (P N) (E N) (O N) (V N))
    (hinj : ∀ N, Function.Injective (d N).coarse)
    (degree : ℕ → ℕ) (B p : ℕ)
    (heligibility : ∀ N e, ((d N).eligibilityCompetitors e).card ≤ degree N)
    (hdegree : ∀ N e, ∀ o ∈ (d N).orbits e, ∀ v ∈ (d N).passing e o,
      ((d N).competitors e o v).card ≤ degree N)
    (horbits : ∀ N e, ((d N).orbits e).card ≤ B * (N + 1) ^ p)
    {A D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ)) atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
      G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
      (∀ e ∈ G, (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s) ∧
      (∀ e ∈ G, ∀ f ∈ G, e ≠ f → ((d N).coarse e).1 ≠ ((d N).coarse f).1) := by
  classical
  have huniform := eventually_errorBound_le_half degree B p hH hgap hdegreeRate
  have hsmall : ∀ᶠ N in atTop, ∀ e,
      (((d N).eligibilityCompetitors e).card : ℝ) / (hashModulus H N : ℝ) +
        (((d N).orbits e).card : ℝ) * (N : ℝ) *
          ((degree N : ℝ) / (hashModulus H N : ℝ)) ≤ 1 / 2 := by
    filter_upwards [huniform] with N hN e
    exact (count_error_le_envelope (d N) e (degree N) B p N (hashModulus H N)
      (heligibility N e) (horbits N e)).trans hN
  have hpositive : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact_mod_cast hN
  let good := fun N (s : Sample (P N) (hashLevel H N)) (e : E N) =>
    (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s
  have hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample (P N) (hashLevel H N)) : ℝ) ≤
          (goodIncidence (good N) e : ℝ) := by
    filter_upwards [hsmall, hpositive] with N hN hNpos e
    rw [show goodIncidence (good N) e =
        ((d N).goodEvent (hashLevel H N) (hashSet H N) (N : ℝ) e).card from
      (d N).goodIncidence_eq _ _ _ _]
    exact (d N).goodEvent_card_lower (hashLevel H N) (hashSet H N) (N : ℝ) hNpos e
      (degree N) (hdegree N e) (hN e)
  have hyield := eventually_exists_many_good_explicit good hH hpos hinc hE hε
  have hselection := eventually_exists_good_subfamily good
    (fun N => ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊) hyield
  filter_upwards [hselection] with N hN
  obtain ⟨s, G, hcard, hgood⟩ := hN
  refine ⟨s, G, hcard, hgood, ?_⟩
  intro e he f hf hne
  exact (d N).good_no_shared_x (hashLevel H N) (hashSet H N) (N : ℝ) f e s
    (hgood f hf) (hgood e he) (fun h => hne ((hinj N) h))

end MatrixMultiplication.JointMaskedGoodSelection

namespace MatrixMultiplication.JointMaskedSelection.OrbitData

open JointCoarseHashing
attribute [local instance] Classical.propDecidable

variable {P E O V : Type*} [Fintype P] [Fintype E]

omit [Fintype E] in
theorem good_randomLossFraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k)
    (hg : d.Good k U N e s) (o : O) (ho : o ∈ d.orbits e) :
    JointLossCounts.randomLossFraction (d.full e o) (d.passing e o)
      (d.variableBad k U e o) s ≤ 1 / N := by
  exact le_of_not_gt (fun h => hg.2 (Or.inr ⟨o, ho, h⟩))

theorem passing_actual_failure_subset_bad (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v) :
    (d.passing e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e)) ⊆ (d.passing e o).filter (fun v => d.variableBad k U e o v s) := by
  intro v hv
  obtain ⟨hpass, hfail⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_filter.mpr ⟨hpass, ?_⟩
  by_contra hnotbad
  have hret : v ∈ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s :=
    Finset.mem_filter.mpr ⟨hpass, hnotbad⟩
  exact hfail (d.model_retained_assigned k U hAP N e o ho s hg
    compatible useful keep v hret (hc v hpass) (hu v hpass) (hk v hpass) (hcover v hpass))

theorem good_passing_actual_failure_fraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v) :
    (((d.passing e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e))).card : ℝ) / ((d.full e o).card : ℝ) ≤ 1 / N := by
  have hcard := Finset.card_le_card
    (d.passing_actual_failure_subset_bad k U hAP N e o ho s hg
      compatible useful keep hc hu hk hcover)
  have hR : (((d.passing e o).filter (fun v =>
      d.actualAssignment k U compatible useful keep s v ≠ some (d.coarse e))).card : ℝ) ≤
      (((d.passing e o).filter (fun v => d.variableBad k U e o v s)).card : ℝ) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)).trans
    (d.good_randomLossFraction_le k U N e s hg o ho)

end MatrixMultiplication.JointMaskedSelection.OrbitData

end

end OAI
