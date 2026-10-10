import OAI.NumberTheory.TwoPoint.Bounds.EncodedBadSum

namespace OAI

/-! Covering the manuscript's literal prohibited-word catalog by finite prime codes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma decodeStep_injective {pairs : Finset (ℕ × ℕ)} :
    Function.Injective (decodeStep (pairs := pairs)) := by
  intro a b h
  apply Prod.ext
  · exact congrArg SignedStep.forward h
  · apply Subtype.ext
    exact Prod.ext (congrArg SignedStep.tuple h) (congrArg SignedStep.padding h)

lemma decodeStepWord_injective {pairs : Finset (ℕ × ℕ)} {s : ℕ} :
    Function.Injective (decodeStepWord (pairs := pairs) (s := s)) := by
  rintro ⟨m, a⟩ ⟨n, b⟩ h
  have hm : m = n := by
    apply Fin.ext
    simpa only [decodeStepWord_length] using congrArg List.length h
  subst n
  have hab : a = b := by
    funext i
    apply decodeStep_injective
    exact congrFun (List.ofFn_injective h) i
  cases hab
  rfl

lemma prohibitedCatalog_decode_injective (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    Function.Injective (fun c : ProhibitedCatalog pairs h s => decodeStepWord c.val) := by
  intro a b hab
  exact Subtype.ext (decodeStepWord_injective hab)

/-- The supplied finite pair family discharges every side condition used by
the nondegenerate last-prime relation, including the global padding exclusion. -/
theorem prohibitedCatalog_has_encoding (pairs : Finset (ℕ × ℕ)) (P Q : Finset ℕ)
    (h s J M : ℕ)
    (ht : ∀ dq ∈ pairs, Squarefree dq.1) (hq : ∀ dq ∈ pairs, Squarefree dq.2)
    (hJ : ∀ dq ∈ pairs, dq.1.primeFactors.card = J)
    (hM : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M)
    (hP : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P)
    (hQ : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q)
    (hd : Disjoint P Q) (hh : ∀ p ∈ P, ¬p ∣ h)
    (c : ProhibitedCatalog pairs h s) :
    ∃ e : PrimeWordEncoding c.val.1.val (s * (J + M)) P Q,
      e.Prohibited h s J (fun d q => (d, q) ∈ pairs) ∧
      e.decode = decodeStepWord c.val ∧
      e.weight = ∏ p ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (p : ℝ)⁻¹ := by
  let w : Fin c.val.1.val → SignedStep := fun i => decodeStep (c.val.2 i)
  have hw (i : Fin c.val.1.val) : ((w i).tuple, (w i).padding) ∈ pairs :=
    (c.val.2 i).2.property
  have hpairs (a : SignedStep) (ha : a ∈ List.ofFn w) : (a.tuple, a.padding) ∈ pairs := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hw i
  have hT : Fintype.card (ActualPrimeSlot w) ≤ s * (J + M) := by
    apply (actualPrimeSlot_card_le w J M (fun i => (hJ _ (hw i)).le)
      (fun i => hM _ (hw i))).trans
    exact Nat.mul_le_mul_right (J + M) (Nat.le_of_lt_succ c.val.1.isLt)
  apply PrimeWordEncoding.covers_prohibited w hT
    (fun i => ht _ (hw i)) (fun i => hq _ (hw i))
    (fun i => hP _ (hw i)) (fun i => hQ _ (hw i))
    (fun i j => hd.mono (hP _ (hw i)) (hQ _ (hw j))) h s J _ c.property.1
    (fun i => hJ _ (hw i))
  intro p j hp
  obtain ⟨hpprime, a, ha, hpa⟩ := hp
  have hapairs := hpairs a (List.mem_of_getElem? ha)
  have hpP : p ∈ P := hP _ hapairs (hpprime.mem_primeFactors hpa (ht _ hapairs).ne_zero)
  refine ⟨hh p hpP, ?_⟩
  intro b hb hpb
  have hbpairs := hpairs b hb
  have hpQ : p ∈ Q := hQ _ hbpairs (hpprime.mem_primeFactors hpb (hq _ hbpairs).ne_zero)
  exact disjoint_left.mp hd hpP hpQ

/-- The actual catalog sum is bounded by the finite code sum, with each
numerical prime still carrying exactly one reciprocal. -/
theorem prohibitedCatalog_reciprocal_sum_le_encodings
    (pairs : Finset (ℕ × ℕ)) (P Q : Finset ℕ) (h s J M : ℕ)
    (ht : ∀ dq ∈ pairs, Squarefree dq.1) (hq : ∀ dq ∈ pairs, Squarefree dq.2)
    (hJ : ∀ dq ∈ pairs, dq.1.primeFactors.card = J)
    (hM : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M)
    (hP : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P)
    (hQ : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q)
    (hd : Disjoint P Q) (hh : ∀ p ∈ P, ¬p ∣ h) :
    (∑ c : ProhibitedCatalog pairs h s,
      ∏ p ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (p : ℝ)⁻¹) ≤
      ∑ R : Fin (s + 1), ∑ e : PrimeWordEncoding R.val (s * (J + M)) P Q,
        if e.Prohibited h s J (fun d q => (d, q) ∈ pairs) then e.weight else 0 := by
  let F := (univ : Finset (ProhibitedCatalog pairs h s)).image (fun c => decodeStepWord c.val)
  let C := (R : Fin (s + 1)) × PrimeWordEncoding R.val (s * (J + M)) P Q
  let decode : C → List SignedStep := fun e => e.2.decode
  let weight (w : List SignedStep) : ℝ := ∏ p ∈ wordDivisorPrimeSupport w, (p : ℝ)⁻¹
  let cost (e : C) : ℝ :=
    if e.2.Prohibited h s J (fun d q => (d, q) ∈ pairs) then e.2.weight else 0
  have hsum : (∑ c : ProhibitedCatalog pairs h s, weight (decodeStepWord c.val)) =
      ∑ w ∈ F, weight w := by
    symm
    exact sum_image (fun a _ b _ hab => prohibitedCatalog_decode_injective pairs h s hab)
  have hcost (e : C) : 0 ≤ cost e := by
    dsimp only [cost]
    split_ifs
    · exact e.2.weight_nonneg
    · exact le_rfl
  have hcover (w : List SignedStep) (hw : w ∈ F) :
      ∃ e : C, decode e = w ∧ weight w ≤ cost e := by
    obtain ⟨c, _, rfl⟩ := mem_image.mp hw
    obtain ⟨e, he, hdecode, hweight⟩ :=
      prohibitedCatalog_has_encoding pairs P Q h s J M ht hq hJ hM hP hQ hd hh c
    refine ⟨⟨c.val.1, e⟩, hdecode, ?_⟩
    dsimp only [cost, weight]
    rw [ite_eq_left he, hweight]
  rw [hsum]
  exact (finite_decoding_weight_bound F decode weight cost hcost hcover).trans_eq
    (Fintype.sum_sigma cost)

/-- Full reciprocal estimate for the manuscript's minimal prohibited words. -/
theorem prohibitedCatalog_reciprocal_bound
    (pairs : Finset (ℕ × ℕ)) (P Q : Finset ℕ) (h s J M : ℕ)
    (ht : ∀ dq ∈ pairs, Squarefree dq.1) (hq : ∀ dq ∈ pairs, Squarefree dq.2)
    (hJ : ∀ dq ∈ pairs, dq.1.primeFactors.card = J)
    (hM : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M)
    (hP : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P)
    (hQ : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q)
    (hd : Disjoint P Q) (hh : ∀ p ∈ P, ¬p ∣ h)
    (hprime : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ c : ProhibitedCatalog pairs h s,
      ∏ p ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (p : ℝ)⁻¹) ≤
      badCatalogCost s (s * (J + M)) (primeHarmonicMass P) (primeHarmonicMass Q) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) :=
  (prohibitedCatalog_reciprocal_sum_le_encodings pairs P Q h s J M
    ht hq hJ hM hP hQ hd hh).trans
    (bounded_encoded_prohibited_sum_le (s * (J + M)) h s J P Q
      (fun d q => (d, q) ∈ pairs) hprime hVP H B hH hB hlo hhi)

end TwoPointCorrelations

end OAI
