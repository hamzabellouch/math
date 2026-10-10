import Mathlib
import OAI.Computability.MinUncut.Estimates.IndexedLists
import OAI.Computability.MinUncut.Estimates.FourthTest
import OAI.Computability.MinUncut.Games.AdaptiveKernel

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [DecidableEq J]

theorem actual_remainder_fourth (U : I → Equation Name) {k : ℕ} (hk : k≤Fintype.card I)
    (f : (J → Forms (FirstAlphabet U)) → Forms (FirstAlphabet U) → ℝ)
    {M u : ℝ} (hM : 0≤M) (hu : 0<u) (hf : ∀ D z, |f D z|≤M) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    (𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 D : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        restrictedFourth (projection U (hiddenSet H.val) pos)
          (f (fun j => formPullback (projection U (hiddenSet H.val) pos) (D j))) u) ≤
      u^2*M^2+Real.sqrt (((2 : ℝ)^(4*(Fintype.card J+3)*k)-1)*(k : ℝ)^2/Fintype.card I)*
        (M+M^2/u)^4 := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  have h := actual_joint_smoothness_index U hk (adaptiveKernel f u)
    (by positivity : 0≤(M+M^2/u)^4) (adaptiveKernel_abs f hM hu hf)
  rw [TripleIndex.card] at h
  have he (H : FixedSets I k) (pos : I → Fin 3) :
      (𝔼 L : TripleIndex J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        adaptiveKernel f u (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) =
      𝔼 D : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        restrictedFourth (projection U (hiddenSet H.val) pos)
          (f (fun j => formPullback (projection U (hiddenSet H.val) pos) (D j))) u :=
    adaptiveKernel_pullback_mean _ f u
  simp_rw [he] at h
  have hm := adaptiveKernel_uniform f hM hu hf
  have hh := (le_abs_self _).trans h
  linarith


open scoped BigOperators
open MinUncut.Inner OuterSmoothness MinUncut.Composition
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

structure LocalRows (Name I J : Type*) [Fintype I] where
  first : (U : I → Equation Name) → (J → Forms (FirstAlphabet U)) → Forms (FirstAlphabet U) → ℝ
  second : (V : I → SecondQuestion Name) → (J → Forms (SecondAlphabet V)) → Forms (SecondAlphabet V) → ℝ

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

def LocalRows.lists (rows : LocalRows Name I J) (u θ : ℝ) : IndexedLists Name I J where
  first U D := labelList (rows.first U D) u
  second V D := labelList (rows.second V D) θ

def LocalRows.atom (rows : LocalRows Name I J) (θ : ℝ) : BackgroundStatistic Name I J :=
  fun U hidden pos B => if (labelList (rows.second (secondQuestion U hidden pos) B) θ).Nonempty
    then 1 else 0

def LocalRows.distance (rows : LocalRows Name I J) : BackgroundStatistic Name I J :=
  fun U hidden pos B => rowDistance (projection U hidden pos)
    (rows.first U (fun j => formPullback (projection U hidden pos) (B j)))
    (rows.second (secondQuestion U hidden pos) B)

def LocalRows.fourth (rows : LocalRows Name I J) (u : ℝ) : BackgroundStatistic Name I J :=
  fun U hidden pos B => restrictedFourth (projection U hidden pos)
    (rows.first U (fun j => formPullback (projection U hidden pos) (B j))) u

omit [Fintype J] [DecidableEq J] in
lemma LocalRows.card_first (rows : LocalRows Name I J) {M u θ : ℝ}
    (hM : 0≤M) (hu : 0<u) (hf : ∀ U D z, |rows.first U D z|≤M)
    (U : I → Equation Name) (D : J → Forms (FirstAlphabet U)) :
    ((rows.lists u θ).first U D).card≤⌈M^2/u^2⌉₊ := by
  exact_mod_cast (labelList_card _ hM hu (hf U D)).trans (Nat.le_ceil _)

omit [Fintype J] [DecidableEq J] in
lemma LocalRows.card_second (rows : LocalRows Name I J) {M u θ : ℝ}
    (hM : 0≤M) (hθ : 0<θ) (hg : ∀ V D z, |rows.second V D z|≤M)
    (V : I → SecondQuestion Name) (D : J → Forms (SecondAlphabet V)) :
    ((rows.lists u θ).second V D).card≤⌈M^2/θ^2⌉₊ := by
  exact_mod_cast (labelList_card _ hM hθ (hg V D)).trans (Nat.le_ceil _)

lemma LocalRows.mean_fourth [Nonempty I] (rows : LocalRows Name I J)
    (equations : S → Equation Name) {k : ℕ} (hk : k≤Fintype.card I)
    {M u : ℝ} (hM : 0≤M) (hu : 0<u) (hf : ∀ U D z, |rows.first U D z|≤M) :
    backgroundMean equations k (rows.fourth u) ≤
      u^2*M^2+Real.sqrt (((2 : ℝ)^(4*(Fintype.card J+3)*k)-1)*(k : ℝ)^2/Fintype.card I)*
        (M+M^2/u)^4 := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  unfold backgroundMean
  rw [Finset.expect_comm]
  exact (Finset.expect_le_expect (fun a _ =>
    actual_remainder_fourth (fun i => equations (a i)) hk (rows.first _) hM hu (hf _))).trans_eq
      (Fintype.expect_const _)

theorem LocalRows.atom_bound [Fintype Name] [Nonempty I]
    (rows : LocalRows Name I J) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {k : ℕ} (hk : k≤Fintype.card I) {M u θ : ℝ} (hM : 0≤M) (hu : 0<u) (hθ : 0<θ)
    (hf : ∀ U D z, |rows.first U D z|≤M) (hg : ∀ V D z, |rows.second V D z|≤M) :
    backgroundMean equations k (rows.atom θ) ≤
      (⌈M^2/u^2⌉₊ : ℝ)*(⌈M^2/θ^2⌉₊ : ℝ)*hintRate (Fintype.card J)^k +
      (16/θ^2)*backgroundMean equations k rows.distance +
      (256/θ^4)*(u^2*M^2+
        Real.sqrt (((2 : ℝ)^(4*(Fintype.card J+3)*k)-1)*(k : ℝ)^2/Fintype.card I)*(M+M^2/u)^4) := by
  have hp := backgroundMean_mono equations k (F := rows.atom θ)
    (G := fun U hidden pos B =>
      (if (rows.lists u θ).matches U hidden pos B then 1 else 0) +
      (16/θ^2)*rows.distance U hidden pos B + (256/θ^4)*rows.fourth u U hidden pos B)
    (fun U hidden pos B => atom_le_matching_charge (projection U hidden pos)
      (rows.first U (fun j => formPullback (projection U hidden pos) (B j)))
      (rows.second (secondQuestion U hidden pos) B) u hθ)
  rw [backgroundMean_add,backgroundMean_add,backgroundMean_mul,backgroundMean_mul] at hp
  have hm := (rows.lists u θ).full_soundness equations hsound hk
    (rows.card_first hM hu hf) (rows.card_second hM hθ hg)
  have hr := rows.mean_fourth equations hk hM hu hf
  have hx := mul_le_mul_of_nonneg_left hr (by positivity : 0≤256/θ^4)
  linarith

end MinUncut.Outer

open scoped BigOperators
namespace MinUncut
open MeasureTheory GaussianHermite
lemma integrable_expect {T Ω : Type*} [Fintype T] [MeasurableSpace Ω] {μ : Measure Ω}
    (f : T → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    Integrable (fun x => 𝔼 t, f t x) μ := by
  simp only [Finset.expect_eq_sum_div_card]
  exact (integrable_finsetSum _ (fun t _ => hf t)).div_const _
end MinUncut
namespace MinUncut.Outer
open MeasureTheory GaussianHermite MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I J S Ω : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [MeasurableSpace Ω] {μ : Measure Ω}

lemma backgroundMean_integrable (equations : S → Equation Name) (k : ℕ)
    (F : Ω → BackgroundStatistic Name I J)
    (hF : ∀ U h pos B, Integrable (fun c => F c U h pos B) μ) :
    Integrable (fun c => backgroundMean equations k (F c)) μ := by
  exact integrable_expect _ (fun H => integrable_expect _ (fun a =>
    integrable_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B))))

lemma integral_backgroundMean (equations : S → Equation Name) (k : ℕ)
    (F : Ω → BackgroundStatistic Name I J)
    (hF : ∀ U h pos B, Integrable (fun c => F c U h pos B) μ) :
    (∫ c, backgroundMean equations k (F c) ∂μ) =
      backgroundMean equations k (fun U h pos B => ∫ c, F c U h pos B ∂μ) := by
  unfold backgroundMean
  rw [integral_expect _ (fun H => integrable_expect _ (fun a =>
    integrable_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B))))]
  congr 1
  funext H
  rw [integral_expect _ (fun a =>
    integrable_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B)))]
  congr 1
  funext a
  rw [integral_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B))]
  congr 1
  funext pos
  exact integral_expect _ (fun B => hF _ _ _ B)
end MinUncut.Outer

end

end OAI
