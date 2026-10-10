import OAI.NumberTheory.TwoPoint.Walks.WordResampling
import OAI.NumberTheory.TwoPoint.Walks.WordRelations
import OAI.NumberTheory.TwoPoint.Bounds.OrderedPrimeSystems

namespace OAI

/-! One actual nondegenerate relation for each forward prohibited word. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- The last transition of a prohibited word acquires a new prime. Its
contribution to the prohibited suffix is exactly the last step. -/
theorem ForwardProhibited.exists_active {h s J : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : ForwardProhibited h s supply w)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding) :
    ∃ z, ActivePrime h w z := by
  have hlen : 3 ≤ w.length := hw.1
  have hinter : TuplePrimeIntervals w := hw.2.2.2.2.1
  obtain ⟨z, hz, hzprev⟩ := adjacent_tuple_new_prime w J hsq hcard hw.2.2.2.1
    (w.length - 2) (by omega)
  have hlast : w.length - 2 + 1 = w.length - 1 := by omega
  have hzlast : TuplePrimeAt w z (w.length - 1) := hlast ▸ hz
  have hearly : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w z i := by
    intro i hi hzi
    exact hzprev (hinter z i (w.length - 2) (w.length - 1)
      (by omega) (by omega) (by omega) hzi hzlast)
  refine ⟨z, hw.last_new_active hzlast hearly ?_⟩
  intro p i hp hi hnot
  apply word_prime_support hsupport p i ?_ hi hnot
  obtain ⟨j, hj⟩ := hp
  exact ⟨j, hj.index_lt, hj⟩

abbrev BadRelationCode (N : ℕ) (ι : Type*) := ι × ι × Fin (N + 1) × Fin (N + 1)

namespace BadRelationCode

variable {N : ℕ} {ι : Type*} [DecidableEq ι]

def Holds (d : BadRelationCode N ι) (w : LabeledPrimeWord ι) (h : ℕ) (x : ι → ℤ) : Prop :=
  d.2.1 ≠ d.1 ∧ primeRelationEvent (w.intervalRelation h d.2.2.1 d.2.2.2) d.1 d.2.1 x

def toSystem (d : BadRelationCode N ι) (w : LabeledPrimeWord ι) (h : ℕ)
    (hne : d.2.1 ≠ d.1) : OrderedPrimeSystem ι where
  Index := Fin 1
  Term _ := Fin w.word.length
  relation _ := w.intervalRelation h d.2.2.1 d.2.2.2
  selected _ := d.1
  control _ := d.2.1
  control_ne _ := hne
  triangular i j hij := by have hi := i.isLt; have hj := j.isLt; omega

lemma toSystem_size (d : BadRelationCode N ι) (w : LabeledPrimeWord ι) (h : ℕ)
    (hne : d.2.1 ≠ d.1) : (d.toSystem w h hne).size = 1 := by
  change Fintype.card (Fin 1) = 1
  exact Fintype.card_fin 1

end BadRelationCode

/-- The numerical event retains every arithmetic assumption used to get
the last-step coefficient. The reciprocal sum may subsequently enlarge
to coincident numerical assignments. -/
def ResampledProhibitedEvent {ι : Type*} [DecidableEq ι]
    (w : LabeledPrimeWord ι) (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (value : ι → ℕ) : Prop :=
  Function.Injective value ∧ (∀ i, (value i).Prime) ∧
  ForwardProhibited h s supply (w.resample value).word ∧
  (∀ a ∈ (w.resample value).word, Squarefree a.tuple) ∧
  (∀ a ∈ (w.resample value).word, a.tuple.primeFactors.card = J) ∧
  (∀ p j, TuplePrimeAt (w.resample value).word p j →
    ¬p ∣ h ∧ ∀ a ∈ (w.resample value).word, ¬p ∣ a.padding)

theorem resampled_prohibited_relation {ι : Type*} [DecidableEq ι]
    {h s J N : ℕ} {supply : ℕ → ℕ → Prop}
    (w : LabeledPrimeWord ι) (hN : w.word.length ≤ N) (value : ι → ℕ)
    (hevent : ResampledProhibitedEvent w h s J supply value) :
    ∃ d : BadRelationCode N ι, d.Holds w h (fun i => (value i : ℤ)) := by
  rcases hevent with ⟨hinj, hprime, hpro, hsq, hcard, hsupport⟩
  obtain ⟨z, hz⟩ := hpro.exists_active hsq hcard hsupport
  have hzseen : ∃ r, TuplePrimeAt (w.resample value).word z r := by
    by_contra! hn
    rcases hz with ⟨c, a, b, _, _, _, _, hnonzero⟩
    apply hnonzero
    have he : wordPrimeContribution h (w.resample value).word z a b = 0 := by
      unfold wordPrimeContribution
      simp only [hn, ite_false, sum_const_zero]
    rw [he]
    exact dvd_zero _
  obtain ⟨rz, hrz⟩ := hzseen
  obtain ⟨y, _, hy⟩ := (w.resample value).occurrence_has_label value hprime
    (w.resample_realizes value) z ⟨rz, hrz.index_lt⟩ hrz
  have hyactive : ActivePrime h (w.resample value).word (value y) := by simpa only [hy] using hz
  obtain ⟨control, a, b, hne, hab, hb, he⟩ := (w.resample value).active_relation h value
    hinj hprime (w.resample_realizes value) y hyactive
  have hbn : b ≤ N := hb.trans (by simpa only [LabeledPrimeWord.resample_length] using hN)
  refine ⟨⟨y, control, ⟨a, by omega⟩, ⟨b, by omega⟩⟩, hne, ?_⟩
  exact (primeRelationEvent_reindex (w.resamplePattern value).index _ _
    ((w.resamplePattern value).interval h a b) y control _).mp he

theorem bad_relation_reciprocal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N h : ℕ) (w : LabeledPrimeWord ι)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ x : ι → P, if ∃ d : BadRelationCode N ι,
      d.Holds w h (integerPrimeAssignment Subtype.val x)
      then ∏ i, ((x i).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card ι ^ 2 * (N + 1) ^ 2 : ℕ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  let D := {d : BadRelationCode N ι // d.2.1 ≠ d.1}
  have hone (d : D) :
      (∑ x : ι → P, if d.val.Holds w h (integerPrimeAssignment Subtype.val x)
        then ∏ i, ((x i).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
    have hs := (d.val.toSystem w h d.property).reciprocal_sum_bound P hP hV H B hH hB hlo hhi
    rw [BadRelationCode.toSystem_size, pow_one] at hs
    have he (x : ι → ℤ) : d.val.Holds w h x ↔ (d.val.toSystem w h d.property).Holds x := by
      constructor
      · intro hx _
        exact hx.2
      · intro hx
        exact ⟨d.property, hx (0 : Fin 1)⟩
    simpa only [he] using hs
  calc
    _ ≤ ∑ d : D, ∑ x : ι → P,
        if d.val.Holds w h (integerPrimeAssignment Subtype.val x)
          then ∏ i, ((x i).val : ℝ)⁻¹ else 0 := by
      rw [sum_comm]
      apply sum_le_sum
      intro x _
      by_cases hx : ∃ d : BadRelationCode N ι, d.Holds w h (integerPrimeAssignment Subtype.val x)
      · rw [ite_eq_left hx]
        obtain ⟨d, hd⟩ := hx
        have hi := single_le_sum (f := fun d : D =>
          if d.val.Holds w h (integerPrimeAssignment Subtype.val x)
            then ∏ i, ((x i).val : ℝ)⁻¹ else 0)
          (fun _ _ => by split_ifs <;> positivity) (mem_univ (⟨d, hd.1⟩ : D))
        simpa only [ite_eq_left hd] using hi
      · rw [ite_eq_right hx]
        exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    _ ≤ (Fintype.card D : ℝ) * (primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H)) := by
      simpa only [sum_const, card_univ, nsmul_eq_mul] using
        (sum_le_sum (s := (univ : Finset D)) (fun d _ => hone d))
    _ ≤ _ := by
      have hc : Fintype.card D ≤ Fintype.card ι ^ 2 * (N + 1) ^ 2 := by
        apply (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans_eq
        simp only [BadRelationCode, Fintype.card_prod, Fintype.card_fin]
        ring
      have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
      calc
        _ ≤ (Fintype.card ι ^ 2 * (N + 1) ^ 2 : ℕ) *
            (primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
        _ = _ := by ring

/-- The numerical prohibited event enters the fixed metadata union. The
ambient prime assignment may be enlarged after this inclusion is proved. -/
theorem resampled_prohibited_reciprocal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s J : ℕ} {supply : ℕ → ℕ → Prop}
    (N h : ℕ) (w : LabeledPrimeWord ι) (hN : w.word.length ≤ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ x : ι → P, if ResampledProhibitedEvent w h s J supply (fun i => (x i).val)
      then ∏ i, ((x i).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card ι ^ 2 * (N + 1) ^ 2 : ℕ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  apply le_trans _ (bad_relation_reciprocal_bound N h w P hP hV H B hH hB hlo hhi)
  apply sum_le_sum
  intro x _
  by_cases he : ResampledProhibitedEvent w h s J supply (fun i => (x i).val)
  · have hd : ∃ d : BadRelationCode N ι, d.Holds w h (integerPrimeAssignment Subtype.val x) :=
      resampled_prohibited_relation w hN (fun i => (x i).val) he
    rw [ite_eq_left he, ite_eq_left hd]
  · rw [ite_eq_right he]
    split_ifs <;> positivity

end TwoPointCorrelations

end OAI
