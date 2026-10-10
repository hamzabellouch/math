import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteLabelEntropy
import OAI.NumberTheory.PrimePackets.FutureConditionalEntropy

namespace OAI

/-! # Finite codes for actual future observations -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

def finiteFutureCode {Y : Type*} {M : ℕ} (T : Y → Y) (P : Y → Fin M) (n : ℕ)
    (y : Y) : Fin (Fintype.card (Fin n → Fin M)) :=
  Fintype.equivFin _ (futureName T P n y)

lemma finiteFutureCode_measurable {Y : Type*} [MeasurableSpace Y] {M : ℕ}
    {T : Y → Y} (hT : Measurable T) {P : Y → Fin M} (hP : Measurable P) (n : ℕ) :
    Measurable (finiteFutureCode T P n) := by
  apply (measurable_of_finite (Fintype.equivFin (Fin n → Fin M))).comp
  apply measurable_pi_iff.mpr
  intro i
  exact hP.comp ((hT.iterate i.val).comp hT)

def truncateFutureCode {M m n : ℕ} (hmn : m ≤ n)
    (v : Fin (Fintype.card (Fin n → Fin M))) : Fin (Fintype.card (Fin m → Fin M)) :=
  Fintype.equivFin _ (fun i : Fin m => (Fintype.equivFin (Fin n → Fin M)).symm v
    ⟨i.val,lt_of_lt_of_le i.isLt hmn⟩)

lemma truncate_finiteFutureCode {Y : Type*} {M m n : ℕ} (T : Y → Y) (P : Y → Fin M)
    (hmn : m ≤ n) (y : Y) :
    truncateFutureCode hmn (finiteFutureCode T P n y) = finiteFutureCode T P m y := by
  simp only [truncateFutureCode,finiteFutureCode,Equiv.symm_apply_apply]
  rfl

lemma finiteFutureCode_eq_of_longer {Y : Type*} {M m n : ℕ} (T : Y → Y) (P : Y → Fin M)
    (hmn : m ≤ n) {x y : Y} (h : finiteFutureCode T P n x=finiteFutureCode T P n y) :
    finiteFutureCode T P m x=finiteFutureCode T P m y := by
  have H := congrArg (truncateFutureCode hmn) h
  simpa only [truncate_finiteFutureCode] using H

lemma all_finiteFutureCode_eq_iff {Y : Type*} {M : ℕ}
    (T : Y → Y) (P : Y → Fin M) (x y : Y) :
    (∀ n, finiteFutureCode T P n x=finiteFutureCode T P n y) ↔
      ∀ k : ℕ, P (T^[k+1] x)=P (T^[k+1] y) := by
  constructor
  · intro h k
    have H := (Fintype.equivFin (Fin (k+1) → Fin M)).injective (h (k+1))
    have He := congrFun H ⟨k,Nat.lt_succ_self k⟩
    simpa only [futureName,orbitName,Function.iterate_succ_apply] using He
  · intro h n
    apply congrArg (Fintype.equivFin (Fin n → Fin M))
    funext i
    simpa only [futureName,orbitName,Function.iterate_succ_apply] using h i.val

lemma transverse_finiteFutureCode_monotone
    {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V] {M : ℕ}
    (T : Y → Y) (P : Y → Fin M) (F : S × V → Y) :
    Monotone (fun n => transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) := by
  intro m n hmn A hA
  obtain ⟨B,hB,rfl⟩ := hA
  let f : S × Fin (Fintype.card (Fin n → Fin M)) →
      S × Fin (Fintype.card (Fin m → Fin M)) :=
    fun z => (z.1,truncateFutureCode hmn z.2)
  have hf : Measurable f := measurable_fst.prodMk
    ((measurable_of_finite (truncateFutureCode hmn)).comp measurable_snd)
  refine ⟨f ⁻¹' B,hf hB,?_⟩
  ext z
  simp only [Set.mem_preimage,f,truncate_finiteFutureCode]

lemma finiteFutureCode_fibers_antitone
    {S V Y : Type*} {M : ℕ} (T : Y → Y) (P : Y → Fin M) (F : S × V → Y)
    (z : S × V) :
    Antitone (fun n => {t : V | finiteFutureCode T P n (F (z.1,t)) = finiteFutureCode T P n (F z)}) := by
  intro m n hmn t ht
  exact finiteFutureCode_eq_of_longer T P hmn ht

end DukePrimeDegree

end

end OAI
