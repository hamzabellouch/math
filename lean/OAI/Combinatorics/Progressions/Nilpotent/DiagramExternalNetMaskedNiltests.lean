import OAI.Combinatorics.Progressions.Estimates.DiagramNativeExternalNetMonotone

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {L σ Ω G X : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype Ω] [Fintype G] [Nonempty X] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (Q : RationalFilteredNilmanifold L s d)

theorem exists_externalNet_masked_niltests
    {cost : ℝ} (hcost : 0 ≤ cost) (hQ : Q.GeometryComplexityLE cost)
    (K : ℝ≥0) (hK : (K : ℝ) ≤ Real.exp cost)
    (n : ℕ) (hn : (n : ℝ) ≤ Real.exp cost)
    (centers : Fin n → Q.Space → ℂ)
    (hcap : ∀ i y, ‖centers i y‖ ≤ 1)
    (hLip : letI := Q.metricSpace; ∀ i, LipschitzWith K (centers i))
    (hpositive : ∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1)
    (F : X → Q.Space → ℂ) {B ε δ : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights G)
    (physical : Ω → G → X) (globalWeight : X → ℝ)
    {w : σ → ℕ} (localOrbits : Ω → Q.filtration.realification.PolynomialOrbit w)
    (point : Ω → G → σ → ℤ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hweight : ∀ x, |globalWeight x| ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ (localLaw a).mean (fun z =>
      globalWeight (physical a z) *
        (F (physical a z) (QuotientGroup.mk
          (Q.filtration.realification.polynomialOrbitEval w (point a z) (localOrbits a)))).re)) :
    ∃ (i : Fin n) (reference : Q.Niltest w) (localTests : Ω → Q.Niltest w)
      (masked : X → ℝ) (H' : Finset Ω),
      reference.orbit = 1 ∧ reference.observable = centers i ∧
      reference.normBound = 1 ∧ reference.lipBound = K ∧
      reference.UnitIntervalValued ∧ reference.ComplexityLE (cost + 3) ∧
      (∀ a, (localTests a).orbit = localOrbits a ∧
        (localTests a).observable = reference.observable ∧
        (localTests a).normBound = 1 ∧ (localTests a).lipBound = K ∧
        (localTests a).UnitIntervalValued ∧ (localTests a).ComplexityLE (cost + 3) ∧
        ∀ x, (localTests a).eval x = centers i (QuotientGroup.mk
          (Q.filtration.realification.polynomialOrbitEval w x (localOrbits a)))) ∧
      (∀ x, masked x = if externalNetIndex F centers hnet x = i then globalWeight x else 0) ∧
      (∀ x, |masked x| ≤ B) ∧ H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / Real.exp cost ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / (2 * Real.exp cost) ≤ (localLaw a).mean
        (fun z => masked (physical a z) * ((localTests a).eval (point a z)).re) := by
  classical
  let : Nonempty (Fin n) := ⟨Classical.choose (hnet (Classical.choice inferInstance))⟩
  let lowerPoint : Ω → G → Q.Space := fun a z => QuotientGroup.mk
    (Q.filtration.realification.polynomialOrbitEval w (point a z) (localOrbits a))
  obtain ⟨i, masked, H', hmask, hmaskcap, hsub, hpos, hmass, hretained⟩ :=
    exists_externalNet_common_mask F centers hnet outer H hH localLaw physical lowerPoint
      globalWeight hB hδ herror hweight hscore
  let reference := Q.externalNetNiltest (centers i) K (hcap i) (hLip i)
    (1 : Q.filtration.realification.PolynomialOrbit w)
  let localTests := fun a => Q.externalNetNiltest (centers i) K (hcap i) (hLip i) (localOrbits a)
  have hnNat : 0 < n := by simpa only [Fintype.card_fin] using Fintype.card_pos (α := Fin n)
  have hnp : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hmass' : outer.mass H / Real.exp cost ≤ outer.mass H' := by
    apply le_trans _ hmass
    simp only [Fintype.card_fin]
    exact div_le_div_of_nonneg_left hH.le hnp hn
  refine ⟨i, reference, localTests, masked, H', rfl, rfl, rfl, rfl, hpositive i,
    Q.externalNetNiltest_complexity _ K (hcap i) (hLip i) 1 hcost hQ hK,
    ?_, ?_, hmaskcap, hsub, hpos, hmass', ?_⟩
  · intro a
    exact ⟨rfl, rfl, rfl, rfl, hpositive i,
      Q.externalNetNiltest_complexity _ K (hcap i) (hLip i) (localOrbits a) hcost hQ hK,
      fun _ => rfl⟩
  · intro x
    rw [hmask]
    split_ifs <;> rfl
  · intro a ha
    apply le_trans _ (hretained a ha)
    simp only [Fintype.card_fin]
    exact div_le_div_of_nonneg_left hδ.le (by positivity)
      (mul_le_mul_of_nonneg_left hn (by norm_num))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u uO uR uIO uX uΩ uG uσ

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem DiagramNativeExternalNetConclusion.exists_masked_niltests (s t k : ℕ)
{H M L₀ ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {e f d₀ : ℕ} {d : ι → ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀)
      (F : ∀ i, RationalFilteredNilmanifold (L i) t (d i))
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) (p cost : ℝ) (q : ℕ)
    (h : DiagramNativeExternalNetConclusion.{u, uO, uR, uIO} s t k E D Q F φ ψ₀ ψ p cost q)
    (hcost : 0 ≤ cost) :
      let Z₀ := pi F
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := realification_moduleTopology_t2 Z₀.basis
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE cost ∧
        ∃ Z : RationalFilteredNilmanifold (∀ i, L i) t (Fintype.card (Σ i, Fin (d i))),
          Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
          Z.GeometryComplexityLE cost ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp cost ∧
          letI := Q'.metricSpace
          letI := Z.metricSpace
          let diagram := fun x : E.RealGroup =>
            ((QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x) : Q'.Space),
              (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Z.filtration.lowerCentralSeries_eq_bot) (liePiMap ψ) x) : Z.Space))
          ∀ {O : Type uO} {R : Type uR} {IO : Type uIO} [Fintype R] [Fintype IO]
            (S : O → D.Space → ℂ) (oc : IO → O) (r : R → D.RealGroup)
            (ℓ B : ℝ≥0) {ε : ℝ},
            (ℓ : ℝ) ≤ Real.exp p → 1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ k) →
            0 < ε → 1 / ε ≤ Real.exp p →
            (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
            (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
            (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
            (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
            (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid q) →
            let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
              (D.basis.baseChange ℝ) B
            let frozen := fun o (a : A) j (x : E.RealGroup) =>
              S o (QuotientGroup.mk (a.val * realificationMap
                (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r j))
            ∃ n : ℕ, (n : ℝ) ≤ Real.exp cost ∧
              ∃ centers : Fin n → Q'.Space → ℂ,
                (∀ i, LipschitzWith K (centers i)) ∧
                (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
                (∀ i y, ‖centers i y‖ ≤ 1) ∧
                (∀ o a j x, positiveImageSlice diagram K (frozen o a j)
                  (diagram x).2 (diagram x).1 = frozen o a j x) ∧
                (∀ o a j z, ∃ i, ∀ y,
                  ‖positiveImageSlice diagram K (frozen o a j) z y - centers i y‖ ≤ ε) ∧
                ∀ {X : Type uX} [Nonempty X]
                  (observableAt : X → O) (leftAt : X → A) (rightAt : X → R)
                  (externalAt : X → Z.Space),
                  let physicalFunction := fun x y => positiveImageSlice diagram K
                    (frozen (observableAt x) (leftAt x) (rightAt x)) (externalAt x) y
                  ∀ {Ω : Type uΩ} {G : Type uG} {σ : Type uσ} [Fintype Ω] [Fintype G]
                    (outer : FiniteProbabilityWeights Ω) (retained : Finset Ω),
                    0 < outer.mass retained →
                    ∀ (localLaw : Ω → FiniteProbabilityWeights G)
                      (physical : Ω → G → X) (globalWeight : X → ℝ)
                      (site : Ω → G → E.RealGroup) {w : σ → ℕ}
                      (localOrbits : Ω → Q'.filtration.realification.PolynomialOrbit w)
                      (point : Ω → G → σ → ℤ) {Bscore δ : ℝ},
                      0 ≤ Bscore → 0 < δ → Bscore * ε ≤ δ / 2 →
                      (∀ x, |globalWeight x| ≤ Bscore) →
                      (∀ a ∈ retained, ∀ z, (diagram (site a z)).1 =
                        QuotientGroup.mk (Q'.filtration.realification.polynomialOrbitEval w
                          (point a z) (localOrbits a))) →
                      (∀ a ∈ retained, ∀ z, (diagram (site a z)).2 = externalAt (physical a z)) →
                      (∀ a ∈ retained, δ ≤ (localLaw a).mean (fun z =>
                        globalWeight (physical a z) *
                          (frozen (observableAt (physical a z)) (leftAt (physical a z))
                            (rightAt (physical a z)) (site a z)).re)) →
                      ∃ (i : Fin n) (idx : X → Fin n) (reference : Q'.Niltest w)
                        (localTests : Ω → Q'.Niltest w) (masked : X → ℝ) (retained' : Finset Ω),
                        (∀ x y, ‖physicalFunction x y - centers (idx x) y‖ ≤ ε) ∧
                        reference.orbit = 1 ∧ reference.observable = centers i ∧
                        reference.normBound = 1 ∧ reference.lipBound = K ∧
                        reference.UnitIntervalValued ∧ reference.ComplexityLE (cost + 3) ∧
                        (∀ a, (localTests a).orbit = localOrbits a ∧
                          (localTests a).observable = reference.observable ∧
                          (localTests a).normBound = 1 ∧ (localTests a).lipBound = K ∧
                          (localTests a).UnitIntervalValued ∧ (localTests a).ComplexityLE (cost + 3) ∧
                          ∀ x, (localTests a).eval x = centers i (QuotientGroup.mk
                            (Q'.filtration.realification.polynomialOrbitEval w x (localOrbits a)))) ∧
                        (∀ x, masked x = if idx x = i then globalWeight x else 0) ∧
                        (∀ x, |masked x| ≤ Bscore) ∧ retained' ⊆ retained ∧
                        0 < outer.mass retained' ∧
                        outer.mass retained / Real.exp cost ≤ outer.mass retained' ∧
                        ∀ a ∈ retained', δ / (2 * Real.exp cost) ≤ (localLaw a).mean
                          (fun z => masked (physical a z) * ((localTests a).eval (point a z)).re) := by
  let Z₀ := pi F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom,
    K, hK, hnet⟩ := h
  refine ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom, K, hK, ?_⟩
  let := Q'.metricSpace
  let := Z.metricSpace
  intro diagram O J IO _ _ S oc r ℓ Bbox ε hℓ hB hBbound hε hεinv hIO hJ hS hpositive hO hr
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover⟩ :=
    hnet (O := O) (R := J) (IO := IO) S oc r ℓ Bbox hℓ hB hBbound hε hεinv hIO hJ
      hS hpositive hO hr
  refine ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover, ?_⟩
  intro X _ observableAt leftAt rightAt externalAt physicalFunction Ω G σ _ _
    outer retained hretained localLaw physical globalWeight site w localOrbits point Bscore δ
    hBscore hδ herror hweight hlower hexternal hscore
  have hnetPhysical : ∀ x, ∃ i, ∀ y, ‖physicalFunction x y - centers i y‖ ≤ ε :=
    fun x => hcover (observableAt x) (leftAt x) (rightAt x) (externalAt x)
  have hpoint (a : Ω) (ha : a ∈ retained) (z : G) :
      physicalFunction (physical a z) (QuotientGroup.mk
        (Q'.filtration.realification.polynomialOrbitEval w (point a z) (localOrbits a))) =
      S (observableAt (physical a z)) (QuotientGroup.mk
        ((leftAt (physical a z)).val * realificationMap
          (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot) φ (site a z) * r (rightAt (physical a z)))) := by
    change positiveImageSlice diagram K _ (externalAt (physical a z)) _ = _
    rw [← hlower a ha z, ← hexternal a ha z]
    exact heval (observableAt (physical a z)) (leftAt (physical a z))
      (rightAt (physical a z)) (site a z)
  have hs : ∀ a ∈ retained, δ ≤ (localLaw a).mean (fun z =>
      globalWeight (physical a z) * (physicalFunction (physical a z) (QuotientGroup.mk
        (Q'.filtration.realification.polynomialOrbitEval w (point a z) (localOrbits a)))).re) := by
    intro a ha
    simpa only [hpoint a ha] using hscore a ha
  obtain ⟨i, reference, localTests, masked, retained', href, hobs, hnorm, hlip,
    hunitref, hcomplex, hlocal, hmask, hmaskcap, hsub, hpos, hmass, hretainedScore⟩ :=
    Q'.exists_externalNet_masked_niltests hcost hQgeom K hK n hn centers hcap hLip hunit
      physicalFunction hnetPhysical outer retained hretained localLaw physical globalWeight
      localOrbits point hBscore hδ herror hweight hs
  exact ⟨i, externalNetIndex physicalFunction centers hnetPhysical, reference, localTests,
    masked, retained', externalNetIndex_approx physicalFunction centers hnetPhysical,
    href, hobs, hnorm, hlip, hunitref, hcomplex, hlocal,
    hmask, hmaskcap, hsub, hpos, hmass, hretainedScore⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
