import OAI.Computability.PerfectCompleteness.Decoding.DecoderContraction
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.PerfectCompleteness.Machines.OwnInputHeavyBounds
import OAI.Computability.PerfectCompleteness.Sampling.BoundedListSamplingLemmas

namespace OAI


namespace PerfectCompleteness.RightDecoder

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)

local instance characterFintype : Fintype (Module.Dual F2 (UpperVector rows upper)) :=
  Fintype.ofInjective
    (fun f : Module.Dual F2 (UpperVector rows upper) =>
      (f : UpperVector rows upper → F2)) DFunLike.coe_injective

local instance scalarFintype : Fintype (Module.Dual F2 (UpperSpace slots upper)) := by
  letI : Fintype (UpperSpace slots upper) := Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun f : Module.Dual F2 (UpperSpace slots upper) =>
      (f : UpperSpace slots upper → F2)) DFunLike.coe_injective

variable (repeats : Nat → Nat) (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a) (threshold : ℝ)

def law : FiniteDistribution (Module.Dual F2 (UpperSpace slots upper)) :=
  BoundedListSampling.outputLaw
    (fun σ => heavyList slots rows upper lower W a repeats cut labeling input σ threshold)
    0 (DecoderContraction.contract W)

theorem probability_law (event : Module.Dual F2 (UpperSpace slots upper) → Bool) :
    (law slots rows upper lower W a repeats cut labeling input threshold).probability event =
      (BoundedListSampling.jointLaw
        (fun σ => heavyList slots rows upper lower W a repeats cut labeling input σ threshold)
        0).probability (fun choice => event
          (DecoderContraction.contract W choice.1 choice.2)) := by
  unfold law BoundedListSampling.outputLaw
  exact FiniteDistribution.probability_pushforward _ _ _

theorem success_lower (M : ℝ) (hM : 0 < M)
    (hcard : ∀ σ : Module.Dual F2 (UpperVector rows upper),
      ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤ M)
    (event : Module.Dual F2 (UpperSpace slots upper) → Bool)
    (witness : ∃ σ Φ,
      Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ∧
      event (DecoderContraction.contract W σ Φ) = true) :
    1 / ((Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) * M) ≤
      (law slots rows upper lower W a repeats cut labeling input threshold).probability event := by
  exact BoundedListSampling.output_success_lower
    (fun σ => heavyList slots rows upper lower W a repeats cut labeling input σ threshold)
    0 (DecoderContraction.contract W) M hM hcard event witness

theorem coset_lower (M : ℝ) (hM : 0 < M)
    (hcard : ∀ σ : Module.Dual F2 (UpperVector rows upper),
      ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤ M)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z : Module.Dual F2 (UpperSpace slots upper))
    (witness : ∃ σ Φ,
      Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ∧
      σ.comp W.subtype ≠ 0 ∧
      Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q) :
    1 / ((Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) * M) ≤
      (law slots rows upper lower W a repeats cut labeling input threshold).probability
        (fun decoded => decide (decoded - z ∈ Q)) := by
  apply success_lower slots rows upper lower W a repeats cut labeling input threshold M hM hcard
  obtain ⟨σ, Φ, hlist, hσ, hΦ⟩ := witness
  exact ⟨σ, Φ, hlist, by
    simpa only [decide_eq_true_eq] using
      DecoderContraction.contract_sub_mem W Q σ Φ z hσ hΦ⟩

theorem coset_lower_of_balanced
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hthreshold : 0 < threshold)
    (hsmall : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ threshold ^ 2 / 2)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z : Module.Dual F2 (UpperSpace slots upper))
    (witness : ∃ σ Φ,
      Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ∧
      σ.comp W.subtype ≠ 0 ∧
      Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q) :
    threshold ^ 2 /
        (2 * (Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ)) ≤
      (law slots rows upper lower W a repeats cut labeling input threshold).probability
        (fun decoded => decide (decoded - z ∈ Q)) := by
  have hsq : 0 < threshold ^ 2 := sq_pos_of_pos hthreshold
  have hcard : ∀ σ : Module.Dual F2 (UpperVector rows upper),
      ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤
        2 / threshold ^ 2 := by
    intro σ
    exact OwnInputHeavyBounds.heavyList_card_le_of_balanced slots rows upper lower W a
      repeats cut hrep labeling input σ threshold hthreshold hsmall
  have h := coset_lower slots rows upper lower W a repeats cut labeling input threshold
    (2 / threshold ^ 2) (div_pos (by norm_num) hsq) hcard Q z witness
  have hcount :
      (Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have heq :
      1 / ((Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) *
        (2 / threshold ^ 2)) =
      threshold ^ 2 / (2 * (Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ)) := by
    field_simp [hcount, ne_of_gt hsq]
  rwa [heq] at h

end
end PerfectCompleteness.RightDecoder



namespace PerfectCompleteness.RightDecoderDescendant

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open PointwiseSpaces TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper lower : Nodes branch n) (cut : Cut upper lower)

def leafEquiv (s : RecursiveSpaces.Slots branch (Nodes.height lower)) :
    cut.path.family (LeafDomain (nodeSlots slots upper)) s ≃
      LeafDomain (nodeSlots slots lower) s :=
  Equiv.cast (congrFun
    (Cut.family_eq (slots := slots) (upper := upper) (lower := lower) cut) s)

def restriction : Domain (nodeSlots slots upper) → Domain (nodeSlots slots lower) :=
  fun x => RecursiveSpaces.project (fun s => leafEquiv slots upper lower cut s)
    (cut.path.restriction (LeafDomain (nodeSlots slots upper)) x)

theorem restriction_restrictNode (x : Domain slots) :
    restriction slots upper lower cut (restrictNode slots upper x) =
      restrictNode slots lower x := by
  have cast_apply :
      ∀ (i j : RecursiveSpaces.Slots branch n) (_ : i = j)
        (hA : LeafDomain slots i = LeafDomain slots j),
        Equiv.cast hA (x i) = x j := by
    intro i j hij hA
    subst j
    rfl
  funext s
  exact cast_apply _ _ (cut.slots_agree s)
    (congrFun (Cut.family_eq (slots := slots) (upper := upper) (lower := lower) cut) s)

variable (hbranch : ∀ k < Nodes.height upper, 0 < branch k)

def squareEmbedding :
    squareSpace (H (nodeSlots slots lower)) →ₗ[F2] UpperSpace slots upper :=
  (DecoderContraction.descendantSquareEmbedding cut.path
    (LeafDomain (nodeSlots slots upper)) hbranch cut.proper).comp
      (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
        (leafEquiv slots upper lower cut)).toLinearMap

@[simp] theorem squareEmbedding_apply
    (f : squareSpace (H (nodeSlots slots lower))) (x : Domain (nodeSlots slots upper)) :
    (squareEmbedding slots upper lower cut hbranch f).val x =
      f.val (restriction slots upper lower cut x) := rfl

theorem squareEmbedding_restrictNode
    (f : squareSpace (H (nodeSlots slots lower))) (x : Domain slots) :
    (squareEmbedding slots upper lower cut hbranch f).val (restrictNode slots upper x) =
      f.val (restrictNode slots lower x) := by
  rw [squareEmbedding_apply, restriction_restrictNode]

theorem squareEmbedding_injective :
    Function.Injective (squareEmbedding slots upper lower cut hbranch) := by
  exact (DecoderContraction.descendantSquareEmbedding_injective cut.path
    (LeafDomain (nodeSlots slots upper)) hbranch cut.proper
    (fun _ => inferInstance)).comp
      (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
        (leafEquiv slots upper lower cut)).injective

def functional (z : Module.Dual F2 (UpperSpace slots upper)) :
    Module.Dual F2 (squareSpace (H (nodeSlots slots lower))) :=
  z.comp (squareEmbedding slots upper lower cut hbranch)

abbrev Form := H (nodeSlots slots lower) →ₗ[F2] H (nodeSlots slots lower) →ₗ[F2] F2

def form (z : Module.Dual F2 (UpperSpace slots upper)) : Form slots lower :=
  OddListExtraction.multiplicationForm (H (nodeSlots slots lower))
    (functional slots upper lower cut hbranch z)

@[simp] theorem form_apply (z : Module.Dual F2 (UpperSpace slots upper))
    (f g : H (nodeSlots slots lower)) :
    form slots upper lower cut hbranch z f g =
      z (squareEmbedding slots upper lower cut hbranch
        (OddListExtraction.productElement (H (nodeSlots slots lower)) f g)) := rfl

theorem form_evaluation (x : Domain (nodeSlots slots upper))
    (f g : H (nodeSlots slots lower)) :
    form slots upper lower cut hbranch
      (EvaluationMatrix.evaluation (UpperSpace slots upper) x) f g =
        f.val (restriction slots upper lower cut x) *
          g.val (restriction slots upper lower cut x) := rfl

theorem form_evaluation_restrictNode (x : Domain slots)
    (f g : H (nodeSlots slots lower)) :
    form slots upper lower cut hbranch
      (EvaluationMatrix.evaluation (UpperSpace slots upper) (restrictNode slots upper x)) f g =
        f.val (restrictNode slots lower x) * g.val (restrictNode slots lower x) := by
  rw [form_evaluation, restriction_restrictNode]

theorem functional_eq_of_sub_mem
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z' z : Module.Dual F2 (UpperSpace slots upper)) (herror : z' - z ∈ Q)
    (hvanish : ∀ q ∈ Q, q.comp (squareEmbedding slots upper lower cut hbranch) = 0) :
    functional slots upper lower cut hbranch z' =
      functional slots upper lower cut hbranch z := by
  have h := hvanish (z' - z) herror
  apply LinearMap.ext
  intro f
  have he := LinearMap.congr_fun h f
  change z' (squareEmbedding slots upper lower cut hbranch f) -
    z (squareEmbedding slots upper lower cut hbranch f) = 0 at he
  exact sub_eq_zero.mp he

theorem form_eq_of_sub_mem
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z' z : Module.Dual F2 (UpperSpace slots upper)) (herror : z' - z ∈ Q)
    (hvanish : ∀ q ∈ Q, q.comp (squareEmbedding slots upper lower cut hbranch) = 0) :
    form slots upper lower cut hbranch z' = form slots upper lower cut hbranch z := by
  unfold form
  rw [functional_eq_of_sub_mem slots upper lower cut hbranch Q z' z herror hvanish]


variable (rows : Nat → Nat)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)
  (repeats : Nat → Nat)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a) (threshold : ℝ)

local instance scalarFintype : Fintype (Module.Dual F2 (UpperSpace slots upper)) :=
  RightDecoder.scalarFintype slots upper

local instance formFintype : Fintype (Form slots lower) := by
  letI : Fintype (H (nodeSlots slots lower)) := Fintype.ofFinite _
  letI : Fintype (Module.Dual F2 (H (nodeSlots slots lower))) :=
    Fintype.ofInjective
      (fun f : Module.Dual F2 (H (nodeSlots slots lower)) =>
        (f : H (nodeSlots slots lower) → F2)) DFunLike.coe_injective
  exact Fintype.ofInjective
    (fun f : Form slots lower =>
      (f : H (nodeSlots slots lower) → Module.Dual F2 (H (nodeSlots slots lower))))
    DFunLike.coe_injective

local instance characterFintype : Fintype (Module.Dual F2 (UpperVector rows upper)) :=
  RightDecoder.characterFintype rows upper

def formLaw : FiniteDistribution (Form slots lower) :=
  (RightDecoder.law slots rows upper lower W a repeats cut labeling input threshold).pushforward
    (form slots upper lower cut hbranch)

theorem probability_formLaw (event : Form slots lower → Bool) :
    (formLaw slots upper lower cut hbranch rows W a repeats labeling input threshold).probability
        event =
      (RightDecoder.law slots rows upper lower W a repeats cut labeling input threshold).probability
        (fun z => event (form slots upper lower cut hbranch z)) :=
  FiniteDistribution.probability_pushforward _ _ _

theorem coset_probability_le_form_probability
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z : Module.Dual F2 (UpperSpace slots upper))
    (hvanish : ∀ q ∈ Q, q.comp (squareEmbedding slots upper lower cut hbranch) = 0) :
    (RightDecoder.law slots rows upper lower W a repeats cut labeling input threshold).probability
        (fun decoded => decide (decoded - z ∈ Q)) ≤
      (formLaw slots upper lower cut hbranch rows W a repeats labeling input threshold).probability
        (fun decoded => decide (decoded = form slots upper lower cut hbranch z)) := by
  rw [probability_formLaw]
  apply FiniteDistribution.probability_mono
  intro decoded hdecoded
  have hmem : decoded - z ∈ Q := of_decide_eq_true hdecoded
  simpa only [decide_eq_true_eq] using
    form_eq_of_sub_mem slots upper lower cut hbranch Q decoded z hmem hvanish

theorem form_contract_eq
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (σ : Module.Dual F2 (UpperVector rows upper))
    (Φ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper))
    (z : Module.Dual F2 (UpperSpace slots upper))
    (hσ : σ.comp W.subtype ≠ 0)
    (hΦ : Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q)
    (hvanish : ∀ q ∈ Q, q.comp (squareEmbedding slots upper lower cut hbranch) = 0) :
    form slots upper lower cut hbranch (DecoderContraction.contract W σ Φ) =
      form slots upper lower cut hbranch z :=
  form_eq_of_sub_mem slots upper lower cut hbranch Q _ z
    (DecoderContraction.contract_sub_mem W Q σ Φ z hσ hΦ) hvanish

theorem form_success_lower_of_balanced
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hthreshold : 0 < threshold)
    (hsmall : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ threshold ^ 2 / 2)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z : Module.Dual F2 (UpperSpace slots upper))
    (hvanish : ∀ q ∈ Q, q.comp (squareEmbedding slots upper lower cut hbranch) = 0)
    (witness : ∃ σ Φ,
      Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ∧
      σ.comp W.subtype ≠ 0 ∧
      Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q) :
    threshold ^ 2 /
        (2 * (Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ)) ≤
      (formLaw slots upper lower cut hbranch rows W a repeats labeling input threshold).probability
        (fun decoded => decide (decoded = form slots upper lower cut hbranch z)) :=
  (RightDecoder.coset_lower_of_balanced slots rows upper lower W a repeats cut labeling input
    threshold hrep hthreshold hsmall Q z witness).trans
      (coset_probability_le_form_probability slots upper lower cut hbranch rows W a repeats
        labeling input threshold Q z hvanish)


end
end PerfectCompleteness.RightDecoderDescendant

end OAI
