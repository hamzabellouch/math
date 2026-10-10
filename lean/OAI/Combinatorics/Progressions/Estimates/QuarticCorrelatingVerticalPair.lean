import OAI.Combinatorics.Progressions.Estimates.QuarticPreciseSampledExchange

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem unit_vertical_frequency_integral_on_lattice {L I : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s : ℕ}
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (eta : L →ₗ[ℚ] ℚ) (v : I → F.realification.Group ⧸ Γ → ℂ)
    (hunit : ∀ x, ∑ i, ‖v i x‖ ^ 2 = 1)
    (hv : ∀ i (z : F.realification.Group), z ∈ F.realification.subgroup s → ∀ x,
      v i (z • x) = CircleFourier.character
        ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * v i x)
    (z : F.realification.Group) (hz : z ∈ F.realification.subgroup s) (hlat : z ∈ Γ) :
    ∃ n : ℤ, realifyFunctional eta z.coord = n := by
  let x : F.realification.Group ⧸ Γ := QuotientGroup.mk 1
  obtain ⟨i, hi⟩ := exists_large_unit_coordinate (fun i => v i x) (hunit x)
  have hnonzero : v i x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt ((by positivity : (0 : ℝ) < 1 / (Fintype.card I + 1 : ℝ)).trans_le hi)
  exact vertical_frequency_integral_on_lattice F Γ eta (v i) (hv i) ⟨x, hnonzero⟩ z hz hlat

def cubicPairMiddleVerticalBudget (p q b : ℝ) : ℝ :=
  productNiltestBudget (cubicPairBudget p q) + b + 4 + (p + b + 2) ^ 4

namespace NativePolynomialOrbitFactors

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

noncomputable def cubicPairMiddleFrequency :
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra →ₗ[ℚ] ℚ :=
  (W.vertical.frequency.comp (V.cubicPairProjection 0).toLinearMap).comp
    ((pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl.toLinearMap

theorem cubicPairMiddleFrequency_real
    (x : ℝ ⊗[ℚ] (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra) :
    realifyFunctional R.cubicPairMiddleFrequency x = realifyFunctional W.vertical.frequency
      (realificationLieHom (V.cubicPairProjection 0)
        (realificationLieHom
          ((pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl x)) := by
  rw [cubicPairMiddleFrequency, realifyFunctional_comp, realifyFunctional_comp]
  rfl

variable {R}
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.cubicPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

theorem FrozenMiddleRealization.cubicPairMiddleFrequency_height (hb : 0 ≤ b)
    (l : Fin (Module.finrank ℚ
      ((pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra))) :
    rationalLogHeight (R.cubicPairMiddleFrequency (M.model.basis l)) ≤ (p + b + 2) ^ 4 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  change rationalLogHeight (W.vertical.frequency
    (V.cubicPairProjection 0 (M.model.basis l : V.CubicPairAlgebra))) ≤ _
  apply rational_functional_value_logHeight W.model.basis W.vertical.frequency
    (add_nonneg hp hb)
    (by simpa only [Fintype.card_fin] using W.complexity.1.1.trans (le_add_of_nonneg_right hb))
    (fun k => (W.vertical.height k).trans (le_add_of_nonneg_right hb))
  intro k
  exact (congrArg rationalLogHeight
    (productFinBasis_repr_component V.cubicPairModels
      (M.model.basis l : V.CubicPairAlgebra) (some 0) k)).trans_le
      ((M.inclusion_height l _).trans (le_add_of_nonneg_left hp))

theorem FrozenMiddleRealization.cubicPairMiddleFrequency_integral (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (hlat : z ∈ M.model.realLattice) :
    ∃ n : ℤ, realifyFunctional R.cubicPairMiddleFrequency z.coord = n := by
  apply unit_vertical_frequency_integral_on_lattice M.model.filtration M.model.realLattice
    R.cubicPairMiddleFrequency (fun out => (M.cubicPairMiddleTest 0 out).observable)
    (M.cubicPairMiddleTest_unit 0) ?_ z hz hlat
  intro out a ha y
  rw [R.cubicPairMiddleFrequency_real]
  exact M.cubicPairMiddleTest_common_vertical 0 out a ha y

noncomputable def FrozenMiddleRealization.cubicPairMiddleVertical (hb : 0 ≤ b) (k : Fin 2) :
    M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
      (Fin W.outputDim) (cubicPairMiddleVerticalBudget p q b) where
  observable out := (M.cubicPairMiddleTest k out).observable
  unit := M.cubicPairMiddleTest_unit k
  norm out x := (M.cubicPairMiddleTest k out).norm_le x
  lipBound := productExpBound (productNiltestBudget (cubicPairBudget p q) + b + 4)
  lip_bound := by
    apply Real.exp_le_exp.mpr
    exact le_add_of_nonneg_right (by positivity)
  lipschitz := by
    let := M.model.metricSpace
    intro out
    apply (M.cubicPairMiddleTest k out).lipschitz.weaken
    change ((M.cubicPairMiddleTest k out).lipBound : ℝ) ≤
      Real.exp (productNiltestBudget (cubicPairBudget p q) + b + 4)
    have h := (M.cubicPairMiddleTest k out).observable_budget
      (M.cubicPairMiddleTest_complexity hb k out)
    linarith [(M.cubicPairMiddleTest k out).normBound.coe_nonneg]
  frequency := R.cubicPairMiddleFrequency
  height l := by
    have hB : 0 ≤ cubicPairBudget p q :=
      (by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
    have hT : 0 ≤ productNiltestBudget (cubicPairBudget p q) + b + 4 := by
      unfold productNiltestBudget productObservableLipBudget
      positivity
    exact (M.cubicPairMiddleFrequency_height hb l).trans (le_add_of_nonneg_left hT)
  vertical out z hz x := by
    rw [R.cubicPairMiddleFrequency_real]
    exact M.cubicPairMiddleTest_common_vertical k out z hz x
  integral := M.cubicPairMiddleFrequency_integral

theorem FrozenMiddleRealization.cubicPairMiddleVertical_eval (hb : 0 ≤ b)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ℤ) :
    (M.cubicPairMiddleVertical hb k).observable out (QuotientGroup.mk
      (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M.orbit)) =
      R.cubicPairFrozenVector k a c out x := M.cubicPairMiddleTest_eval k out x

end NativePolynomialOrbitFactors
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

noncomputable def quarticPairMiddleVerticalBudget (p q b : ℝ) : ℝ :=
  productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) + b + 4 + (p + b + 2) ^ 4

namespace NativePolynomialOrbitFactors

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

noncomputable def quarticPairMiddleFrequency :
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra →ₗ[ℚ] ℚ :=
  (W.vertical.frequency.comp (V.quarticOriginalPairProjection 0).toLinearMap).comp
    ((pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl.toLinearMap

theorem quarticPairMiddleFrequency_real
    (x : ℝ ⊗[ℚ] (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra) :
    realifyFunctional R.quarticPairMiddleFrequency x = realifyFunctional W.vertical.frequency
      (realificationLieHom (V.quarticOriginalPairProjection 0)
        (realificationLieHom
          ((pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl x)) := by
  rw [quarticPairMiddleFrequency, realifyFunctional_comp, realifyFunctional_comp]
  rfl

variable {R}
  [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.quarticPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

theorem FrozenMiddleRealization.quarticPairMiddleFrequency_height (hb : 0 ≤ b)
    (l : Fin (Module.finrank ℚ
      ((pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra))) :
    rationalLogHeight (R.quarticPairMiddleFrequency (M.model.basis l)) ≤ (p + b + 2) ^ 4 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  change rationalLogHeight (W.vertical.frequency
    (V.quarticOriginalPairProjection 0 (M.model.basis l : V.QuarticPairAlgebra))) ≤ _
  apply rational_functional_value_logHeight W.model.basis W.vertical.frequency
    (add_nonneg hp hb)
    (by simpa only [Fintype.card_fin] using W.complexity.1.1.trans (le_add_of_nonneg_right hb))
    (fun k => (W.vertical.height k).trans (le_add_of_nonneg_right hb))
  intro k
  exact (congrArg rationalLogHeight
    (productFinBasis_repr_component V.quarticPairModels
      (M.model.basis l : V.QuarticPairAlgebra) (some 0) k)).trans_le
      ((M.inclusion_height l _).trans (le_add_of_nonneg_left hp))

theorem FrozenMiddleRealization.quarticPairMiddleTest_vertical (k : Fin 2) (out : Fin W.outputDim)
    (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : M.model.Space) :
    (M.quarticPairMiddleTest k out).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional R.quarticPairMiddleFrequency z.coord : ℝ) : CircleFourier.Circle) *
        (M.quarticPairMiddleTest k out).observable x := by
  rw [R.quarticPairMiddleFrequency_real]
  exact M.quarticPairMiddleTest_common_vertical k out z hz x

theorem FrozenMiddleRealization.quarticPairMiddleFrequency_integral (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (hlat : z ∈ M.model.realLattice) :
    ∃ n : ℤ, realifyFunctional R.quarticPairMiddleFrequency z.coord = n := by
  exact unit_vertical_frequency_integral_on_lattice M.model.filtration M.model.realLattice
    R.quarticPairMiddleFrequency (fun out => (M.quarticPairMiddleTest 0 out).observable)
    (M.quarticPairMiddleTest_unit 0) (M.quarticPairMiddleTest_vertical 0) z hz hlat

noncomputable def FrozenMiddleRealization.quarticPairMiddleVertical (hb : 0 ≤ b) (k : Fin 2) :
    M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
      (Fin W.outputDim) (quarticPairMiddleVerticalBudget p q b) where
  observable out := (M.quarticPairMiddleTest k out).observable
  unit := M.quarticPairMiddleTest_unit k
  norm out x := (M.quarticPairMiddleTest k out).norm_le x
  lipBound := productExpBound (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) + b + 4)
  lip_bound := by
    apply Real.exp_le_exp.mpr
    exact le_add_of_nonneg_right (by positivity)
  lipschitz := by
    let := M.model.metricSpace
    intro out
    apply (M.quarticPairMiddleTest k out).lipschitz.weaken
    change ((M.quarticPairMiddleTest k out).lipBound : ℝ) ≤
      Real.exp (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) + b + 4)
    have h := (M.quarticPairMiddleTest k out).observable_budget
      (M.quarticPairMiddleTest_complexity hb k out)
    linarith [(M.quarticPairMiddleTest k out).normBound.coe_nonneg]
  frequency := R.quarticPairMiddleFrequency
  height l := by
    have hB : 0 ≤ quarticPairBudget (tensorPowerBudget 6 p) q :=
      (by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
    have hT : 0 ≤ productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) + b + 4 := by
      unfold productNiltestBudget productObservableLipBudget
      positivity
    exact (M.quarticPairMiddleFrequency_height hb l).trans (le_add_of_nonneg_left hT)
  vertical := M.quarticPairMiddleTest_vertical k
  integral := M.quarticPairMiddleFrequency_integral

theorem FrozenMiddleRealization.quarticPairMiddleVertical_eval (hb : 0 ≤ b)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin 4 → ℤ) :
    (M.quarticPairMiddleVertical hb k).observable out (QuotientGroup.mk
      (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M.orbit)) =
      R.quarticPairFrozenVector k a c out x := M.quarticPairMiddleTest_eval k out x

end NativePolynomialOrbitFactors
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]

def HasQuarticVerticalCorrelatingAnchor (row : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N))
    (out : Fin W.outputDim) (b : ℝ) : Prop :=
  ∃ y : Fin 4 → ZMod N, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
    Real.exp (-b) * N ≤ (S.card : ℝ) ∧ ∃ w : ZMod N → ℝ,
      PositiveCyclicNiltest.{0} 1 N b w ∧
      ∃ M : R.FrozenMiddleRealization
          (R.slowValue (fun k => ((y k).val : ℤ)))
          (R.rationalValue (fun k => ((y k).val : ℤ))) b,
        ∃ U : Fin 2 → M.model.UnitVerticalObservable
            (M.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
            (Fin W.outputDim) b,
          (∀ k, (U k).frequency = R.quarticPairMiddleFrequency) ∧
          (∀ k l x, (U k).observable l (QuotientGroup.mk
            (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M.orbit)) =
              R.quarticPairAnchoredVector (fun k => ((y k).val : ℤ)) k l x) ∧
          NativeIntegerVectorEquivalence 3 b
            (R.quarticPairAnchoredVector (fun k => ((y k).val : ℤ)) 0)
            (R.quarticPairAnchoredVector (fun k => ((y k).val : ℤ)) 1) ∧
          ∀ h ∈ S, Real.exp (-b) ≤
            ‖𝔼 n : ZMod N, row h n *
              star ((w n : ℂ) * (U 0).observable out (QuotientGroup.mk
                (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1)
                  ![(h.val : ℤ), (n.val : ℤ), (n.val : ℤ), (n.val : ℤ)] M.orbit)))‖

theorem hasQuarticVerticalCorrelatingAnchor_mono
    {row : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)} {out : Fin W.outputDim}
    {a b : ℝ} (h : R.HasQuarticVerticalCorrelatingAnchor row H out a) (hab : a ≤ b) :
    R.HasQuarticVerticalCorrelatingAnchor row H out b := by
  obtain ⟨y, S, hSH, hS, hsize, w, hw, M, U, hfreq, heval, hequiv, hcorr⟩ := h
  have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (neg_le_neg hab)
  exact ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hsize,
    w, hw.mono le_rfl hab, M.mono hab, fun k => (U k).mono hab, hfreq, heval,
    hequiv.mono hab, fun h hh => he.trans (hcorr h hh)⟩

end NativePolynomialOrbitFactors

theorem exists_quartic_correlating_vertical_pair :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      0 ≤ r → 0 ≤ b → R.HasQuarticPairFrozenReduction b →
      ∀ (row : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N)) (out : Fin W.outputDim),
        R.HasQuarticCorrelatingAnchor row H out b →
        R.HasQuarticVerticalCorrelatingAnchor row H out ((tensorPowerBudget 6 p + q + r + b + C) ^ C) := by
  obtain ⟨A, _, hmodel⟩ := exists_quartic_pair_middle_model
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let D := (X + Polynomial.C A) ^ A
  let P := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + D + (P + D + 4 + (X + D + 2) ^ 4))
  refine ⟨C, hC, ?_⟩
  intro p q r b W N _ i j V R _ _ _ _ _ _ _ _ hr hb hred row H out hanchor
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpk : p ≤ tensorPowerBudget 6 p := (tensorPowerBudget_bounds 6 hp).1
  have hk : 0 ≤ tensorPowerBudget 6 p := hp.trans hpk
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget 6 p + q + r + b
  let B₀ := 4 * (v + 1) + raisedNiltestBudget v + 6
  let d := (v + A) ^ A
  let z := productNiltestBudget B₀ + d + 4 + (v + d + 2) ^ 4
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hB : 0 ≤ B₀ := by dsimp [B₀, raisedNiltestBudget]; positivity
  have hz : 0 ≤ z := by
    dsimp [z]
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hsum : v + d + z ≤ (tensorPowerBudget 6 p + q + r + b + C) ^ C := by
    simpa [X, B, D, P, v, B₀, d, z, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have hbC : b ≤ (tensorPowerBudget 6 p + q + r + b + C) ^ C := by dsimp [v] at hsum; linarith
  have hdC : d ≤ (tensorPowerBudget 6 p + q + r + b + C) ^ C := by linarith
  have hzC : z ≤ (tensorPowerBudget 6 p + q + r + b + C) ^ C := by linarith
  obtain ⟨u, hu, hub, houter, _hfreeze⟩ := hred
  obtain ⟨y, S, hSH, hS, hdensity, w, hw, hequiv, hcorr⟩ := hanchor
  have hy : ∀ k : Fin 4, |(((y k).val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    intro k
    change |((y k).val : ℝ)| ≤ (N : ℝ)
    rw [abs_of_nonneg (Nat.cast_nonneg ((y k).val))]
    exact Nat.cast_le.mpr (y k).val_lt.le
  obtain ⟨M, _hMc, _hMe⟩ := hmodel R hr hu houter (fun k => ((y k).val : ℤ)) hy
  let c := (tensorPowerBudget 6 p + q + r + u + A) ^ A
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcd : c ≤ d := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hpqv : tensorPowerBudget 6 p + q ≤ v := by dsimp [v]; linarith
  have hpv : p ≤ v := by dsimp [v]; linarith
  have hpair : quarticPairBudget (tensorPowerBudget 6 p) q ≤ B₀ := by
    dsimp [quarticPairBudget, B₀, raisedNiltestBudget]
    gcongr
  have hpair0 : 0 ≤ quarticPairBudget (tensorPowerBudget 6 p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
  have hprod : productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) ≤ productNiltestBudget B₀ :=
    productNiltestBudget_mono hpair0 hpair
  have hvcost : quarticPairMiddleVerticalBudget p q c ≤ z := by
    dsimp [quarticPairMiddleVerticalBudget, z]
    gcongr
  let M' := M.mono (hcd.trans hdC)
  let U : Fin 2 → M'.model.UnitVerticalObservable
      (M'.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
      (Fin W.outputDim) ((tensorPowerBudget 6 p + q + r + b + C) ^ C) :=
    fun k => (M.quarticPairMiddleVertical hc k).mono (hvcost.trans hzC)
  have heval (k l x) : (U k).observable l (QuotientGroup.mk
      (M'.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M'.orbit)) =
      R.quarticPairAnchoredVector (fun k => ((y k).val : ℤ)) k l x :=
    M.quarticPairMiddleVertical_eval hc k l x
  have hexp : Real.exp (-((tensorPowerBudget 6 p + q + r + b + C) ^ C)) ≤ Real.exp (-b) :=
    Real.exp_le_exp.mpr (neg_le_neg hbC)
  refine ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg N)).trans hdensity,
    w, hw.mono le_rfl hbC, M', U, fun _ => rfl, heval, hequiv.mono hbC, ?_⟩
  intro h hh
  apply hexp.trans
  simpa only [heval] using hcorr h hh

end Erdos3

end

end OAI
