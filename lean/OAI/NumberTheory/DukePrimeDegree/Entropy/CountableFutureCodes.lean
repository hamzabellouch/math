import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteFutureCodes
import OAI.NumberTheory.DukePrimeDegree.Entropy.HeightObservationEntropy

namespace OAI

/-! # Finite codes converging to the future of a countable observation

Both the time interval and the clipping level increase. The limiting atom
records every future value of the original countable observation.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

def countableFutureCode {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (m : ℕ)
    (y : Y) : Fin (Fintype.card (Fin m → Fin (m+1))) :=
  Fintype.equivFin _ (fun i : Fin m => heightClip Q m (T^[i.val+1] y))

lemma countableFutureCode_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) (m : ℕ) :
    Measurable (countableFutureCode T Q m) :=
  (measurable_of_finite (Fintype.equivFin (Fin m → Fin (m+1)))).comp
    (measurable_pi_iff.mpr fun i => (heightClip_measurable hQ m).comp (hT.iterate (i.val+1)))

def truncateCountableFutureCode {m n : ℕ} (hmn : m ≤ n)
    (v : Fin (Fintype.card (Fin n → Fin (n+1)))) :
    Fin (Fintype.card (Fin m → Fin (m+1))) :=
  Fintype.equivFin _ (fun i : Fin m =>
    ⟨min ((Fintype.equivFin (Fin n → Fin (n+1))).symm v
      ⟨i.val,lt_of_lt_of_le i.isLt hmn⟩).val m,
      Nat.lt_succ_of_le (min_le_right _ _)⟩)

lemma truncate_countableFutureCode {Y : Type*} {m n : ℕ} (T : Y → Y) (Q : Y → ℕ)
    (hmn : m ≤ n) (y : Y) :
    truncateCountableFutureCode hmn (countableFutureCode T Q n y) =
      countableFutureCode T Q m y := by
  simp only [truncateCountableFutureCode,countableFutureCode,Equiv.symm_apply_apply]
  apply congrArg (Fintype.equivFin (Fin m → Fin (m+1)))
  funext i
  apply Fin.ext
  change min (min (Q (T^[i.val+1] y)) n) m = min (Q (T^[i.val+1] y)) m
  omega

lemma countableFutureCode_eq_of_longer {Y : Type*} {m n : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (hmn : m ≤ n) {x y : Y}
    (h : countableFutureCode T Q n x=countableFutureCode T Q n y) :
    countableFutureCode T Q m x=countableFutureCode T Q m y := by
  have H := congrArg (truncateCountableFutureCode hmn) h
  simpa only [truncate_countableFutureCode] using H

lemma all_countableFutureCode_eq_iff {Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (x y : Y) :
    (∀ m, countableFutureCode T Q m x=countableFutureCode T Q m y) ↔
      ∀ k : ℕ, Q (T^[k+1] x)=Q (T^[k+1] y) := by
  constructor
  · intro h k
    let m := max k (max (Q (T^[k+1] x)) (Q (T^[k+1] y)))+1
    have hk : k < m := by dsimp only [m]; omega
    have hx : Q (T^[k+1] x) < m := by dsimp only [m]; omega
    have hy : Q (T^[k+1] y) < m := by dsimp only [m]; omega
    have he := congrArg (fun v =>
      ((Fintype.equivFin (Fin m → Fin (m+1))).symm v ⟨k,hk⟩).val) (h m)
    simp only [countableFutureCode,Equiv.symm_apply_apply] at he
    change min (Q (T^[k+1] x)) m=min (Q (T^[k+1] y)) m at he
    omega
  · intro h m
    apply congrArg (Fintype.equivFin (Fin m → Fin (m+1)))
    funext i
    apply Fin.ext
    change min (Q (T^[i.val+1] x)) m=min (Q (T^[i.val+1] y)) m
    rw [h i.val]

lemma transverse_countableFutureCode_monotone
    {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) :
    Monotone (fun m => transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) := by
  intro m n hmn A hA
  obtain ⟨B,hB,rfl⟩ := hA
  let f : S × Fin (Fintype.card (Fin n → Fin (n+1))) →
      S × Fin (Fintype.card (Fin m → Fin (m+1))) :=
    fun z => (z.1,truncateCountableFutureCode hmn z.2)
  have hf : Measurable f := measurable_fst.prodMk
    ((measurable_of_finite (truncateCountableFutureCode hmn)).comp measurable_snd)
  refine ⟨f ⁻¹' B,hf hB,?_⟩
  ext z
  simp only [Set.mem_preimage,f,truncate_countableFutureCode]

lemma countableFutureCode_fibers_antitone {S V Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) (z : S × V) :
    Antitone (fun m => labelFiber (fun z => countableFutureCode T Q m (F z)) z) := by
  intro m n hmn t ht
  exact countableFutureCode_eq_of_longer T Q hmn ht

def countableFutureFiber {S V Y : Type*} (T : Y → Y) (Q : Y → ℕ)
    (F : S × V → Y) (z : S × V) : Set V :=
  {t | ∀ k : ℕ, Q (T^[k+1] (F (z.1,t)))=Q (T^[k+1] (F z))}

lemma countableFutureFiber_eq_iInter {S V Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) (z : S × V) :
    countableFutureFiber T Q F z =
      ⋂ m, labelFiber (fun z => countableFutureCode T Q m (F z)) z := by
  ext t
  simp only [countableFutureFiber,labelFiber,mem_iInter,mem_ofPred_eq]
  exact (all_countableFutureCode_eq_iff T Q (F (z.1,t)) (F z)).symm

end DukePrimeDegree

end

end OAI
