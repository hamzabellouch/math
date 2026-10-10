import OAI.Probability.CriticalZ3.SeedQuality

namespace OAI

universe uOmega

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
theorem finite_measureReal_mono_ae {A B : Set Ω} (h : A ≤ᵐ[μ] B) :
    μ.real A ≤ μ.real B :=
  ENNReal.toReal_le_toReal (_root_.MeasureTheory.measure_ne_top μ A) (_root_.MeasureTheory.measure_ne_top μ B) |>.mpr (_root_.MeasureTheory.measure_mono_ae h)
end MeasureTheory

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem entrant_exterior {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : C.Exterior y :=
  (Finset.mem_filter.mp hy).2.choose_spec.1

theorem entrant_node {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : y ∈ G.vertices := (Finset.mem_filter.mp hy).1

/-- Actual separated seed trials under an arbitrary fixed outside pattern. -/
theorem fixed_large_entrants_failure (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (C : Box) (r K : ℕ) (hK : 0 < K)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    (o : G.Node) (T : Set Vertex) (ξ : m.Config)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q) {γ τ : ℝ} (hτ : 0 < τ)
    (hqual : ∀ y, C.Exterior y → (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ)
    (hlarge : K*(8*r+5)^3 ≤ (G.entrants m C ξ o).card) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real
      {ω | ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)} ≤
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ := by
  let pf := fixedParameter p (G.outsideBits m C) ξ
  let μ := ProductCylinder.law pf
  let c := (q : ℝ)^Box.successCard m r
  obtain ⟨t,ht,hcard,hsep⟩ := Box.separated_subset (G.entrants m C ξ o) r K hlarge
  let v (y : t) := G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y.1
  let F (y : t) := {ω | conditionalProbability p (C.bits m) {ω | G.Meets m ω (v y) T} ω ≤ 1-τ}
  let A (y : t) := allValue (C.successBits r m y.1) true
  let B (y : t) := A y ∩ F y
  have hy (y : t) : C.Exterior y.1 := G.entrant_exterior m (ht y.2)
  have hF (y : t) : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F y) := by
    intro ω ω' h
    simp only [F,Set.mem_ofPred_eq,conditionalProbability_determined p (C.bits m) _ ω ω' h]
  have hfresh (y : t) : ∀ e ∈ C.successBits r m y.1, pf e = q := by
    intro e he
    change fixedParameter p (G.outsideBits m C) ξ e = q
    rw [fixedParameter,ite_eq_right (Finset.disjoint_left.mp (G.successBits_disjoint_outside m C r hw (hy y)) he)]
    exact hp e (C.successBits_contained r m hw (hy y) he)
  have hmass (y : t) : μ.real (A y) = c := by
    rw [allValue_probability_constant pf _ q (hfresh y)]
    simp only [bitProbability,ite_true,C.successBits_card r m hw (hy y)]
    rfl
  have hpair (y z : t) (hyz : y ≠ z) : μ.real (A y ∩ A z) ≤ c*c := by
    have hd := C.successBits_disjoint r m hw (hy y) (hy z)
      (hsep y y.2 z z.2 (fun h => hyz (Subtype.ext h)))
    have hind := indepSet_determined pf _ _ hd (A y) (A z)
      (allValue_determined _ _) (allValue_determined _ _)
    have hh : μ.real (A y ∩ A z) = μ.real (A y)*μ.real (A z) := by
      simp only [Measure.real_def,μ,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
    rw [hh,hmass y,hmass z]
  have hbad (y : t) : μ.real (B y) ≤ c*γ/τ :=
    G.fixed_bad_success_mass m p q C r hw (hy y) ξ hp (F y) (hF y) (hqual y (hy y))
  have hbound := TrialCounts.no_good_probability μ A B
    (fun _ => measurableSet_allValue _ _)
    (fun y => (measurableSet_allValue _ _).inter (measurableSet_conditional_test _ _ _ _))
    (c := c) (γ := γ) (τ := τ)
    (by rw [Fintype.card_coe,hcard]; exact mul_pos (Nat.cast_pos.mpr hK) (pow_pos hq _))
    hτ hmass hpair hbad
  rw [Fintype.card_coe,hcard] at hbound
  apply (finite_measureReal_mono_ae (μ := μ) ?_).trans hbound
  filter_upwards [ae_fixed_determined p (G.outsideBits m C) ξ
    (fun ω => G.entrants m C ω o) (G.entrants_determined m C o)] with ω hω
  intro hfail y hAy
  refine ⟨hAy,?_⟩
  by_contra hnot
  have hg : 1-τ < conditionalProbability p (C.bits m) {ω | G.Meets m ω (v y) T} ω :=
    lt_of_not_ge hnot
  have hyω : y.1 ∈ G.entrants m C ω o := hω.symm ▸ ht y.2
  let yn : G.Node := ⟨y.1,G.entrant_node m hyω⟩
  obtain ⟨u,hu,hconn⟩ := G.success_reaches_center m C r hw hC (y := yn) hyω hAy
  have huv : u = v y := Subtype.ext hu
  apply hfail
  refine ⟨u,?_,hconn⟩
  exact ⟨v y,congrArg Subtype.val huv.symm,hg⟩

end CriticalZ3.LatticeGraph

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem measurableSet_large_entrants (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | L ≤ (G.entrants m C ω o).card} := by
  apply ProductCylinder.measurableSet_determined (G.outsideBits m C)
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,G.entrants_determined m C o ω ω' h]

/-- Integrating the exact separated-trial estimate, including histories with
fewer than L entries. -/
theorem large_entrants_failure (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (C : Box) (r K : ℕ) (hK : 0 < K)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    (o : G.Node) (T : Set Vertex)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hqual : ∀ y, C.Exterior y → (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law p).real
      {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
        ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)} ≤
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ := by
  let E : Set m.Config := {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
    ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)}
  have hm : MeasurableSet E := (G.measurableSet_large_entrants m C o _).inter
    (G.measurableSet_meets_goodRelays m p (C.bits m) o T τ).compl
  have hr := select_probability_le p (G.outsideBits m C) (fun _ => E) (fun _ => hm)
    (b := 4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ) ?_
  · exact hr
  · intro a
    let ξ := ProductCylinder.extend (G.outsideBits m C) a
    by_cases hlarge : K*(8*r+5)^3 ≤ (G.entrants m C ξ o).card
    · exact (measureReal_mono (fun _ h => h.2)).trans
        (G.fixed_large_entrants_failure m p q hq C r K hK hw hC o T ξ hp hτ hqual hlarge)
    · have he : (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real E = 0 := by
        have hz : (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)) E = 0 := by
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [ae_fixed_determined p (G.outsideBits m C) ξ
            (fun ω => G.entrants m C ω o) (G.entrants_determined m C o)] with ω hω
          intro h
          exact hlarge (hω ▸ h.1)
        simp only [Measure.real_def,hz,ENNReal.toReal_zero]
      rw [he]
      positivity

end CriticalZ3.LatticeGraph

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

theorem entryBit_internal_expand {C : Box} {y : Vertex} (hy : C.Exterior y) (m : Model) :
    C.entryBit m y ∈ (C.expand 1).bits m := by
  cases m
  · exact LatticeGraph.incidence_internal (exterior_expand hy)
      (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
  · exact (mem_vertices _ _).mpr (C.contains_expand 1 (entry_spec hy).1)
end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

/-- The shell + separated-seed + interior-quality extension, with all probability
terms explicit. The input seed events are the exact cube-restricted events. -/
theorem extension_bound (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ)) {p₀ : ℝ} (hqp : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1)
    (B : Box) (r K R : ℕ) (hK : 0 < K) (hrR : r < R)
    (hG : G.ContainsBox (B.expand R)) (o : G.Node) (T : Set Vertex)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ e ∈ (B.expand R).bits m, p e = q)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hreach : ∀ c, (B.expand R).Contains c → ∃ ℓ : ℕ,
      r ≤ ℓ ∧ G.ContainsBox (Box.cube c ℓ) ∧
      1-γ ≤ (ProductCylinder.law p).real (m.SeedReaches c r ℓ T)) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ ¬G.Meets m ω o T} ≤
      1/((1-p₀)^(K*(8*r+5)^3)*(R-r : ℕ)) +
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ+τ := by
  have hsub (j : ℕ) (hj : j < R) : ∀ x, ((B.expand j).expand 1).Contains x →
      (B.expand R).Contains x := by
    intro x hx
    rw [Box.expand_expand] at hx
    exact B.expand_mono (by omega) hx
  obtain ⟨j,hj,hlayer⟩ := G.exists_shell m p B o q hqp hp₀ (K*(8*r+5)^3) r R hrR ho (by
    intro j hj y hy
    exact hp _ (Box.bits_mono m (hsub j (Finset.mem_Ico.mp hj).2) (Box.entryBit_internal_expand hy m)))
  let C := B.expand j
  have hjR : j < R := (Finset.mem_Ico.mp hj).2
  have hw : ∀ i, C.lower i+r ≤ C.upper i-r := B.expanded_seed_width (Finset.mem_Ico.mp hj).1
  have hC : G.ContainsBox (C.expand 1) := hG.mono G (hsub j hjR)
  have hpC : ∀ e ∈ (C.expand 1).bits m, p e = q := fun e he =>
    hp e (Box.bits_mono m (hsub j hjR) he)
  have hqual (y : Vertex) (_hy : C.Exterior y) : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ := by
    let c := C.relayCenter r y
    have hc : C.Contains c := C.seedBox_contained r hw y _ (Box.center_mem_cube _ _)
    obtain ⟨ℓ,hrℓ,hcube,hprob⟩ := hreach c (B.expand_mono hjR.le hc)
    have hmass : (ProductCylinder.law p).real (allValue ((C.seedBox r y).bits m) true) =
        (q : ℝ)^Box.seedCard m r := by
      rw [allValue_probability_constant p _ q (by
        intro e he
        exact hpC e (Box.bits_mono m (fun x hx => C.contains_expand 1
          (C.seedBox_contained r hw y x hx)) he))]
      simp only [bitProbability,ite_true,Box.seedBox,Box.cube_bits_card,Box.seedCard]
    have hh := G.seed_conditional_quality m p C T hrℓ (C.seedBox_contained r hw y)
      hcube (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) rfl hτ hprob
    change (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ _) ≤
      (ProductCylinder.law p).real (allValue ((C.seedBox r y).bits m) true)*γ/τ at hh
    rwa [hmass] at hh
  have hlarge := G.large_entrants_failure m p q hq C r K hK hw hC o T hpC hγ hτ hqual
  have hrelay := G.random_relay_failure m p (C.bits m) o T hτ.le
  let E₁ : Set m.Config := {ω | G.Meets m ω o {x | B.Contains x} ∧
    (G.entrants m C ω o).card < K*(8*r+5)^3}
  let E₂ : Set m.Config := {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
    ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)}
  let E₃ : Set m.Config := {ω | G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω) ∧
    ¬G.Meets m ω o T}
  have hcontain : {ω | G.Meets m ω o {x | B.Contains x} ∧ ¬G.Meets m ω o T} ⊆ (E₁ ∪ E₂) ∪ E₃ := by
    intro ω hω
    by_cases hn : (G.entrants m C ω o).card < K*(8*r+5)^3
    · exact Or.inl (Or.inl ⟨hω.1,hn⟩)
    · by_cases hg : G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)
      · exact Or.inr ⟨hg,hω.2⟩
      · exact Or.inl (Or.inr ⟨le_of_not_gt hn,hg⟩)
  have hh := (measureReal_mono (μ := ProductCylinder.law p) hcontain).trans
    ((measureReal_union_le (E₁ ∪ E₂) E₃).trans
      (add_le_add (measureReal_union_le E₁ E₂) le_rfl))
  have := hh.trans (add_le_add (add_le_add hlayer hlarge) hrelay)
  simpa only [add_assoc] using this

end LatticeGraph
end CriticalZ3

end OAI
