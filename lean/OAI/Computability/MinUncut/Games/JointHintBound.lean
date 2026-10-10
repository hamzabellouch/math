import Mathlib
import OAI.Computability.MinUncut.Games.JointHintSampling
import OAI.Computability.MinUncut.Estimates.PatchDensity

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

lemma raw_background_expect (U : I → Equation Name) {d : ℕ} (H : Finset I)
    (f : (Fin d → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 pos : I → Fin 3,
      𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H) pos)),
        f (fun k => formPullback (projection U (hiddenSet H) pos) (L k))) =
    (𝔼 z : (Fin d → F₂) × (I → JointForms.Raw d),
      f (firstHints U (hiddenSet H) (rawPositions z.2) (rawCoefficients z.1 z.2))) := by
  classical
  have hpos (pos : I → Fin 3) :
      (𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H) pos)),
        f (fun k => formPullback (projection U (hiddenSet H) pos) (L k))) =
      (𝔼 c : HintCoefficients I d, f (firstHints U (hiddenSet H) pos c)) :=
    (uniform_hintTupleGenerator _ d (fun L =>
      f (fun k => formPullback (projection U (hiddenSet H) pos) (L k)))).symm
  simp_rw [hpos]
  rw [← expect_pair (fun z : (I → Fin 3) × HintCoefficients I d =>
    f (firstHints U (hiddenSet H) z.1 z.2))]
  exact Fintype.expect_equiv (hintRawEquiv (I := I) d) _ _ (fun z => rfl)

lemma actual_joint_law (U : I → Equation Name) {d k : ℕ} (hk : k≤Fintype.card I)
    (f : (Fin d → Forms (FirstAlphabet U)) → ℝ) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    (𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) =
    (𝔼 sample : (Fin d → F₂) × (FixedSets I k × (I → JointForms.Raw d)),
      f (tupleCoordinateGenerator U d
        (JointForms.affineOutput (fun i => directionEmbedding (U i))
          (fun i => (origin (U i)).val) sample))) := by
  classical
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  simp_rw [raw_background_expect]
  rw [expect_pair]
  simp_rw [expect_pair]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro κ _
  apply Finset.expect_congr rfl
  intro H _
  apply Finset.expect_congr rfl
  intro w _
  exact congrArg f (raw_joint_identity U H κ w)

theorem actual_joint_smoothness [Nonempty I] (U : I → Equation Name) {d k : ℕ}
    (hk : k≤Fintype.card I) (f : (Fin d → Forms (FirstAlphabet U)) → ℝ)
    {M : ℝ} (hM : 0≤M) (hf : ∀ L, |f L|≤M) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    |(𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) -
      (𝔼 L : Fin d → Forms (FirstAlphabet U), f L)| ≤
    Real.sqrt (((2 : ℝ)^(4*d*k)-1)*(k : ℝ)^2/Fintype.card I)*M := by
  classical
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  rw [actual_joint_law U hk]
  let output := JointForms.affineOutput (fun i => directionEmbedding (U i))
    (fun i => (origin (U i)).val) (d := d) (k := k)
  have h := Density.expect_difference (Density.ofMap output)
    (fun z => f (tupleCoordinateGenerator U d z)) hM (fun z => hf _)
  rw [Density.expect_ofMap,uniform_tupleCoordinateGenerator] at h
  have htv := JointForms.joint_smoothness hk (fun i => alphabet_dimension_le (U i))
    (fun i => directionEmbedding (U i)) (fun i => directionEmbedding_injective (U i))
    (fun i => (origin (U i)).val) (d := d)
  refine h.trans ?_
  calc
    _ ≤ 2 * (Real.sqrt (((2 : ℝ)^(4*d*k)-1)*(k : ℝ)^2/Fintype.card I)/2)*M := by
      gcongr
      convert htv using 1
      exact Density.tv_ofMap_instances _ _ _ _ _ _ _ _ output
    _ = _ := by ring

end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

lemma expect_reindex {J K A : Type*} [Fintype J] [Fintype K] [Fintype A] [DecidableEq J] [DecidableEq K]
    (e : J ≃ K) (f : (J → A) → ℝ) :
    (𝔼 L : K → A, f (fun j => L (e j))) = 𝔼 L : J → A, f L := by
  exact Fintype.expect_equiv (Equiv.arrowCongr e.symm (Equiv.refl A)) _ _ (fun _ => rfl)

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

lemma pulled_background_reindex {K : Type*} [Fintype K] [DecidableEq K]
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (e : J ≃ K) (f : (J → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 L : K → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      f (fun j => formPullback (projection U hidden pos) (L (e j)))) =
    𝔼 L : J → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      f (fun j => formPullback (projection U hidden pos) (L j)) :=
  expect_reindex e (fun L => f (fun j => formPullback (projection U hidden pos) (L j)))

lemma actual_background_reindex {K : Type*} [Fintype K] [DecidableEq K]
    (U : I → Equation Name) (k : ℕ) (e : J ≃ K)
    (f : (J → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 H : FixedSets I k, 𝔼 pos : I → Fin 3,
      𝔼 L : K → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L (e j)))) =
      𝔼 H : FixedSets I k, 𝔼 pos : I → Fin 3,
      𝔼 L : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j)) := by
  apply Finset.expect_congr rfl
  intro H _
  exact Finset.expect_congr rfl (fun pos _ => pulled_background_reindex U _ pos e f)

theorem actual_joint_smoothness_index [Nonempty I] (U : I → Equation Name) {k : ℕ}
    (hk : k≤Fintype.card I) (f : (J → Forms (FirstAlphabet U)) → ℝ)
    {M : ℝ} (hM : 0≤M) (hf : ∀ L, |f L|≤M) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    |(𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 L : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) -
      (𝔼 L : J → Forms (FirstAlphabet U), f L)| ≤
    Real.sqrt (((2 : ℝ)^(4*Fintype.card J*k)-1)*(k : ℝ)^2/Fintype.card I)*M := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  let e := Fintype.equivFin J
  have h := actual_joint_smoothness (d := Fintype.card J) U hk (fun L => f (fun j => L (e j))) hM
    (fun L => hf _)
  dsimp only at h
  rw [actual_background_reindex U k e f,expect_reindex e f] at h
  exact h

end MinUncut.Outer

end

end OAI
