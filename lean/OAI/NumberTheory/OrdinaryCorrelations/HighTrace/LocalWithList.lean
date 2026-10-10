import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ : ℕ}

def localWithList (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (a : ZMod (p : ℕ)) : ℝ :=
  S.primeFactor w p a * listLocal w 𝔏 p a

def fixedProduct (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (a : S.FixedResidues w) : ℝ := ∏ p, localWithList w 𝔏 p.val (a p)

def freeCoreProduct (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (b : S.FreeCoreResidues w) : ℝ := ∏ p, localWithList w 𝔏 p.val.val (b p)

def freeCenterProduct (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (c : S.FreeCenterResidues w) : ℝ := ∏ p, localWithList w 𝔏 p.val.val (c p)

def splitCutoff (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (a : S.FixedResidues w) (b : S.FreeCoreResidues w) : ℝ :=
  S.cutoffProduct w cut (S.coreFromSplit w a b)

lemma product_merge (w : ClosedLine h ℓ)
    (f : ∀ p : S.Index, ZMod (p : ℕ) → ℝ)
    (a : S.FixedResidues w) (b : S.FreeCoreResidues w) (c : S.FreeCenterResidues w) :
    (∏ p, f p (((S.splitResidues w).symm (a,(b,c))) p)) =
      (∏ p : S.FixedIndex w, f p.val (a p)) *
      ((∏ p : S.FreeCoreIndex w, f p.val.val (b p)) *
       (∏ p : S.FreeCenterIndex w, f p.val.val (c p))) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (S.IsFixed w)]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun p : S.FreeIndex w => S.IsCore p.val)]
  congr 1
  · apply prod_congr rfl
    intro p _
    simp [splitResidues, p.property]
  · congr 1 <;> apply prod_congr rfl <;> intro p _ <;>
      simp [splitResidues, p.val.property, p.property]

theorem kernel_list_split (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w)
    (b : S.FreeCoreResidues w) (c : S.FreeCenterResidues w) :
    S.kernel w cut ((S.splitResidues w).symm (a,(b,c))) *
      listIndicator w 𝔏 ((S.splitResidues w).symm (a,(b,c))) =
    separatedKernel (splitCutoff w cut) (fixedProduct w 𝔏)
      (freeCoreProduct w 𝔏) (freeCenterProduct w 𝔏) a (b,c) := by
  rw [kernel, listIndicator_product]
  rw [mul_assoc, ← prod_mul_distrib]
  change S.cutoffProduct w cut (S.restrictCore _) *
    (∏ p, localWithList w 𝔏 p _) = _
  rw [restrictCore_merge, product_merge]
  simp only [separatedKernel, splitCutoff, fixedProduct, freeCoreProduct, freeCenterProduct]
  ring

lemma freeCoreProduct_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (b : S.FreeCoreResidues w) : 0 ≤ freeCoreProduct w 𝔏 b := by
  apply prod_nonneg
  intro p _
  exact mul_nonneg (S.core_primeFactor_nonneg w p.val.val p.property (b p))
    (listLocal_nonneg w 𝔏 _ _)

def assignedKernelIntegral (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (group : S.FixedResidues w → Prop) : ℝ :=
  avg (fun a => if group a then
    |avg (fun bc : S.FreeCoreResidues w × S.FreeCenterResidues w =>
      S.kernel w cut ((S.splitResidues w).symm (a,bc)) *
      listIndicator w 𝔏 ((S.splitResidues w).symm (a,bc)))| else 0)

lemma kernel_list_function (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) :
    (fun bc : S.FreeCoreResidues w × S.FreeCenterResidues w =>
      S.kernel w cut ((S.splitResidues w).symm (a,bc)) *
        listIndicator w 𝔏 ((S.splitResidues w).symm (a,bc))) =
    separatedKernel (splitCutoff w cut) (fixedProduct w 𝔏)
      (freeCoreProduct w 𝔏) (freeCenterProduct w 𝔏) a := by
  funext bc
  exact kernel_list_split w cut 𝔏 a bc.1 bc.2

lemma assignedKernelIntegral_eq (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (𝔏 : List (AttachedSpec w D L)) (group : S.FixedResidues w → Prop) :
    assignedKernelIntegral w cut 𝔏 group =
      assignedIntegral group (splitCutoff w cut) (fixedProduct w 𝔏)
        (freeCoreProduct w 𝔏) (freeCenterProduct w 𝔏) := by
  unfold assignedKernelIntegral
  simp_rw [kernel_list_function]
  rfl

lemma freeCenter_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :
    avg (freeCenterProduct w 𝔏) =
      ∏ p : S.FreeCenterIndex w, avg (localWithList w 𝔏 p.val.val) := by
  simp only [freeCenterProduct, avg, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_inv_distrib, ← Fintype.prod_sum, prod_mul_distrib]

theorem assignedKernelIntegral_signed (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L))
    (group : S.FixedResidues w → Prop) :
    assignedKernelIntegral w cut 𝔏 group =
      |∏ p : S.FreeCenterIndex w, avg (localWithList w 𝔏 p.val.val)| *
      avg (fun a => if group a then |fixedProduct w 𝔏 a| *
        avg (fun b => splitCutoff w cut a b * freeCoreProduct w 𝔏 b) else 0) := by
  rw [assignedKernelIntegral_eq]
  rw [assignedIntegral_signed group (splitCutoff w cut) (fixedProduct w 𝔏)
    (freeCoreProduct w 𝔏) (freeCenterProduct w 𝔏)
    (fun a b => S.cutoffProduct_nonneg w cut (S.coreFromSplit w a b)) (freeCoreProduct_nonneg w 𝔏)]
  rw [freeCenter_mean]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
