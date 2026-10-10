import OAI.Combinatorics.ProgressionColoring.FiniteProbability
import OAI.Combinatorics.ProgressionColoring.CyclicBasic
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Sparse perturbations indexed by literal keys

A signature records the original bit and the actual key at every position.
The key is never renamed. All positions with the same key use the same sampled
bit. The finite events below therefore include the correlations caused by
repeated keys, including inconsistent prescriptions.
-/

universe uKey uIndex

namespace QuantitativeVanDerWaerden
namespace SparsePerturbation

open scoped BigOperators

abbrev Signature (Key : Type uKey) (k : ℕ) := Fin k → Bool × Key

variable {Key : Type uKey} [Fintype Key] {k : ℕ}
variable [DecidableEq Key]

/-- The actual key image of a literal signature. -/
noncomputable def usedKeys (σ : Signature Key k) : Finset Key := by
  classical
  exact Finset.univ.image (fun j => (σ j).2)

/-- Positions whose original bit differs from the target bit. -/
def oppositePositions (σ : Signature Key k) (b : Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun j => (σ j).1 ≠ b)

/-- The fixed keys that must flip for the target event. -/
noncomputable def oppositeKeys (σ : Signature Key k) (b : Bool) : Finset Key := by
  classical
  exact (oppositePositions σ b).image (fun j => (σ j).2)

/-- The finite event that this signature becomes monochromatic in bit `b`. -/
noncomputable def targetEvent (σ : Signature Key k) (b : Bool) :
    Finset (Key → Bool) := by
  classical
  exact Finset.univ.filter (fun ω => ∀ j, Bool.xor (σ j).1 (ω (σ j).2) = b)

@[simp] theorem mem_targetEvent (σ : Signature Key k) (b : Bool) (ω : Key → Bool) :
    ω ∈ targetEvent σ b ↔ ∀ j, Bool.xor (σ j).1 (ω (σ j).2) = b := by
  classical
  simp [targetEvent]

theorem xor_right_eq_of_same_target {c x y b : Bool}
    (hx : Bool.xor c x = b) (hy : Bool.xor c y = b) : x = y := by
  cases c <;> cases x <;> cases y <;> cases b <;> simp_all

theorem xor_target_of_opposite {c x b : Bool}
    (hc : c ≠ b) (hx : Bool.xor c x = b) : x = true := by
  cases c <;> cases x <;> cases b <;> simp_all

/-- A key shared by opposite original colors makes each target event empty. -/
theorem targetEvent_eq_empty_of_conflict (σ : Signature Key k) (b : Bool)
    {i j : Fin k} (hkey : (σ i).2 = (σ j).2) (hcolor : (σ i).1 ≠ (σ j).1) :
    targetEvent σ b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  have hi := (mem_targetEvent σ b ω).mp hω i
  have hj := (mem_targetEvent σ b ω).mp hω j
  rw [hkey] at hi
  generalize hc : (σ i).1 = ci at hi hcolor
  generalize hd : (σ j).1 = cj at hj hcolor
  generalize he : ω (σ j).2 = e at hi hj
  cases ci <;> cases cj <;> cases e <;> cases b <;> simp_all

/-- A nonempty target event is exactly the cylinder prescribed by any one of
its members, on the actual used-key set. -/
theorem targetEvent_eq_prescriptions (σ : Signature Key k) (b : Bool)
    {ω₀ : Key → Bool} (hω₀ : ω₀ ∈ targetEvent σ b) :
    targetEvent σ b = Finset.univ.filter (fun ω =>
      ∀ a ∈ usedKeys σ, ω a = ω₀ a) := by
  classical
  ext ω
  simp only [mem_targetEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hω a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact xor_right_eq_of_same_target (hω j) ((mem_targetEvent σ b ω₀).mp hω₀ j)
  · intro hω j
    have hj : (σ j).2 ∈ usedKeys σ := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [hω _ hj]
    exact (mem_targetEvent σ b ω₀).mp hω₀ j

/-- Every target event forces the already determined opposite-key set to flip.
There is no additional choice of a subset of keys. -/
theorem targetEvent_subset_opposite_cylinder (σ : Signature Key k) (b : Bool) :
    targetEvent σ b ⊆ Finset.univ.filter (fun ω =>
      ∀ a ∈ oppositeKeys σ b, ω a = true) := by
  classical
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hc : (σ j).1 ≠ b := (Finset.mem_filter.mp hj).2
  exact xor_target_of_opposite hc ((mem_targetEvent σ b ω).mp hω j)

/-- The same literal signature gives the same event on the same key variables. -/
theorem targetEvent_eq_of_signature_eq {σ τ : Signature Key k} (h : σ = τ)
    (b : Bool) : targetEvent σ b = targetEvent τ b := by rw [h]

/-- A multiplicity cap applies to every subset of positions. -/
theorem card_le_four_mul_card_image {Key : Type uKey} [Fintype Key] {k : ℕ}
    [DecidableEq Key]
    (σ : Signature Key k)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (J : Finset (Fin k)) :
    J.card ≤ 4 * (J.image (fun j => (σ j).2)).card := by
  classical
  calc
    J.card = ∑ a ∈ J.image (fun j => (σ j).2),
        (J.filter (fun j => (σ j).2 = a)).card :=
      Finset.card_eq_sum_card_image _ J
    _ ≤ ∑ _a ∈ J.image (fun j => (σ j).2), 4 := by
      apply Finset.sum_le_sum
      intro a ha
      apply le_trans (Finset.card_le_card ?_) (hmult a)
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    _ = 4 * (J.image (fun j => (σ j).2)).card := by simp [Nat.mul_comm]

/-- Exact integer lower bound on the number of keys in a whole signature. -/
theorem ceil_quarter_le_usedKeys_card (σ : Signature Key k)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4) :
    (k + 3) / 4 ≤ (usedKeys σ).card := by
  have h := card_le_four_mul_card_image σ hmult Finset.univ
  simp only [Finset.card_univ, Fintype.card_fin] at h
  change k ≤ 4 * (usedKeys σ).card at h
  omega

/-- Exact integer lower bound on the predetermined flips in a rich signature.
The richness premise is the integral form of at least `k/100` opposite bits. -/
theorem ceil_four_hundredth_le_oppositeKeys_card (σ : Signature Key k) (b : Bool)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (hrich : k ≤ 100 * (oppositePositions σ b).card) :
    (k + 399) / 400 ≤ (oppositeKeys σ b).card := by
  have h := card_le_four_mul_card_image σ hmult (oppositePositions σ b)
  change (oppositePositions σ b).card ≤ 4 * (oppositeKeys σ b).card at h
  omega

open FiniteProbability

/-- Exact target probability, whenever the prescriptions are consistent. -/
theorem target_probability_eq (p : ℝ) (σ : Signature Key k) (b : Bool)
    {ω₀ : Key → Bool} (hω₀ : ω₀ ∈ targetEvent σ b) :
    prob (bernoulliWeight p) (targetEvent σ b) =
      ∏ a ∈ usedKeys σ, if ω₀ a then p else 1 - p := by
  have heq : targetEvent σ b = cylinder (usedKeys σ) ω₀ :=
    targetEvent_eq_prescriptions σ b hω₀
  rw [heq, prob_bernoulli_cylinder]

/-- Sparse flips preserve a fixed rich signature with high probability. -/
theorem target_probability_le_flip_pow {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Signature Key k) (b : Bool) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ p ^ (oppositeKeys σ b).card := by
  classical
  have hsub : targetEvent σ b ⊆ cylinder (oppositeKeys σ b) (fun _ => true) :=
    targetEvent_subset_opposite_cylinder σ b
  calc
    _ ≤ prob (bernoulliWeight p) (cylinder (oppositeKeys σ b) (fun _ => true)) :=
      prob_mono (bernoulliWeight_nonneg hp hp1) hsub
    _ = p ^ (oppositeKeys σ b).card := by
      rw [prob_bernoulli_cylinder]
      simp

/-- For `p ≤ 1/2`, every prescribed key has probability at most `1-p`. -/
theorem target_probability_le_stay_pow {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (σ : Signature Key k) (b : Bool) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ (1 - p) ^ (usedKeys σ).card := by
  classical
  by_cases h : (targetEvent σ b).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := h
    rw [target_probability_eq p σ b hω₀]
    calc
      _ ≤ ∏ _a ∈ usedKeys σ, (1 - p) := by
        apply Finset.prod_le_prod₀
        · intro a ha
          split_ifs <;> linarith
        · intro a ha
          split_ifs <;> linarith
      _ = (1 - p) ^ (usedKeys σ).card := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, prob_empty]
    exact pow_nonneg (by linarith) _

theorem rich_target_probability_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Signature Key k) (b : Bool)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (hrich : k ≤ 100 * (oppositePositions σ b).card) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ p ^ ((k + 399) / 400) :=
  (target_probability_le_flip_pow hp hp1 σ b).trans
    (pow_le_pow_of_le_one hp hp1 (ceil_four_hundredth_le_oppositeKeys_card σ b hmult hrich))

theorem target_probability_le {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (σ : Signature Key k)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (b : Bool) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ (1 - p) ^ ((k + 3) / 4) :=
  (target_probability_le_stay_pow hp hp2 σ b).trans
    (pow_le_pow_of_le_one (by linarith) (by linarith) (ceil_quarter_le_usedKeys_card σ hmult))

/-- Either target bit is bad. -/
noncomputable def monochromaticEvent (σ : Signature Key k) : Finset (Key → Bool) := by
  classical
  exact targetEvent σ false ∪ targetEvent σ true

@[simp] theorem mem_monochromaticEvent (σ : Signature Key k) (ω : Key → Bool) :
    ω ∈ monochromaticEvent σ ↔ ∃ b, ∀ j, Bool.xor (σ j).1 (ω (σ j).2) = b := by
  classical
  simp only [monochromaticEvent, Finset.mem_union, mem_targetEvent]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

theorem monochromatic_probability_le {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Signature Key k)
    (h : ∀ b, prob (bernoulliWeight p) (targetEvent σ b) ≤ r) :
    prob (bernoulliWeight p) (monochromaticEvent σ) ≤ 2 * r := by
  classical
  calc
    _ ≤ prob (bernoulliWeight p) (targetEvent σ false) +
        prob (bernoulliWeight p) (targetEvent σ true) :=
      prob_union_le (bernoulliWeight_nonneg hp hp1) _ _
    _ ≤ r + r := add_le_add (h false) (h true)
    _ = 2 * r := by ring

/-- Finite sparse-perturbation theorem. The affine family is counted through
its actual literal-signature image; repeated descriptions are not new events.
No independence between different progression events is assumed. -/
theorem exists_avoiding_of_rich_or_signature {ι : Type uIndex} [DecidableEq ι]
    (P A : Finset ι) (σ : ι → Signature Key k) (hA : A ⊆ P)
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hmult : ∀ i ∈ P, ∀ a, (Finset.univ.filter (fun j => (σ i j).2 = a)).card ≤ 4)
    (hcases : ∀ i ∈ P, i ∈ A ∨ ∀ b, k ≤ 100 * (oppositePositions (σ i) b).card)
    (hbudget : 2 * (P.card : ℝ) * p ^ ((k + 399) / 400) +
      2 * ((A.image σ).card : ℝ) * (1 - p) ^ ((k + 3) / 4) < 1) :
    ∃ ω : Key → Bool, ∀ i ∈ P, ∀ b, ∃ j,
      Bool.xor (σ i j).1 (ω (σ i j).2) ≠ b := by
  classical
  let R := P \ A
  let F := A.image σ
  let ER := R.biUnion (fun i => monochromaticEvent (σ i))
  let EF := F.biUnion monochromaticEvent
  have hp1 : p ≤ 1 := by linarith
  have hnonneg := bernoulliWeight_nonneg (Key := Key) hp hp1
  have hR : prob (bernoulliWeight p) ER ≤ 2 * (P.card : ℝ) * p ^ ((k + 399) / 400) := by
    calc
      _ ≤ ∑ i ∈ R, prob (bernoulliWeight p) (monochromaticEvent (σ i)) :=
        prob_biUnion_le hnonneg R _
      _ ≤ ∑ _i ∈ R, 2 * p ^ ((k + 399) / 400) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiP : i ∈ P := (Finset.mem_sdiff.mp hi).1
        have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
        have hrich := (hcases i hiP).resolve_left hiA
        exact monochromatic_probability_le hp hp1 (σ i)
          (fun b => rich_target_probability_le hp hp1 (σ i) b (hmult i hiP) (hrich b))
      _ = 2 * (R.card : ℝ) * p ^ ((k + 399) / 400) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ 2 * (P.card : ℝ) * p ^ ((k + 399) / 400) := by
        have hcard : (R.card : ℝ) ≤ P.card := by
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : R ⊆ P)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num))
          (pow_nonneg hp _)
  have hF : prob (bernoulliWeight p) EF ≤
      2 * (F.card : ℝ) * (1 - p) ^ ((k + 3) / 4) := by
    calc
      _ ≤ ∑ τ ∈ F, prob (bernoulliWeight p) (monochromaticEvent τ) :=
        prob_biUnion_le hnonneg F _
      _ ≤ ∑ _τ ∈ F, 2 * (1 - p) ^ ((k + 3) / 4) := by
        apply Finset.sum_le_sum
        intro τ hτ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hτ
        exact monochromatic_probability_le hp hp1 (σ i)
          (target_probability_le hp hp2 (σ i) (hmult i (hA hi)))
      _ = 2 * (F.card : ℝ) * (1 - p) ^ ((k + 3) / 4) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hbad : prob (bernoulliWeight p) (ER ∪ EF) < 1 :=
    (prob_union_le hnonneg ER EF).trans_lt ((add_le_add hR hF).trans_lt hbudget)
  obtain ⟨ω, hω⟩ := exists_not_mem_of_prob_lt_one (sum_bernoulliWeight p) (ER ∪ EF) hbad
  refine ⟨ω, ?_⟩
  intro i hi b
  by_contra h
  have hmono : ω ∈ monochromaticEvent (σ i) := by
    apply (mem_monochromaticEvent (σ i) ω).mpr
    exact ⟨b, fun j => not_ne_iff.mp (fun hn => h ⟨j, hn⟩)⟩
  apply hω
  by_cases hiA : i ∈ A
  · apply Finset.mem_union.mpr (Or.inr ?_)
    exact Finset.mem_biUnion.mpr ⟨σ i, Finset.mem_image.mpr ⟨i, hiA, rfl⟩, hmono⟩
  · apply Finset.mem_union.mpr (Or.inl ?_)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiA⟩, hmono⟩

/-- Actual ordered nonzero-step progressions in a finite cyclic group. -/
def nonzeroProgressions (N : ℕ) [NeZero N] : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter (fun ad => ad.2 ≠ 0)

@[simp] theorem mem_nonzeroProgressions {N : ℕ} [NeZero N] (ad : ZMod N × ZMod N) :
    ad ∈ nonzeroProgressions N ↔ ad.2 ≠ 0 := by
  simp [nonzeroProgressions]

theorem nonzeroProgressions_card_le (N : ℕ) [NeZero N] :
    (nonzeroProgressions N).card ≤ N ^ 2 := by
  calc
    _ ≤ (Finset.univ : Finset (ZMod N × ZMod N)).card := Finset.card_filter_le _ _
    _ = N ^ 2 := by simp [ZMod.card, pow_two]

/-- Literal signatures of the actual cyclic samples. -/
def cyclicSignature {N : ℕ} (c₀ : ZMod N → Bool) (key : ZMod N → Key)
    (ad : ZMod N × ZMod N) : Signature Key k :=
  fun j => let x := ad.1 + (j.val : ZMod N) * ad.2; (c₀ x, key x)

/-- Apply the finite product construction to the actual cyclic group. This
wrapper constructs the coloring itself from the sampled key bits. -/
theorem exists_cyclicAvoids_of_sparse_data {N : ℕ} [NeZero N]
    (c₀ : ZMod N → Bool) (key : ZMod N → Key)
    (A : Finset (ZMod N × ZMod N)) (hA : A ⊆ nonzeroProgressions N)
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hmult : ∀ ad ∈ nonzeroProgressions N, ∀ a,
      (Finset.univ.filter (fun j : Fin k => (cyclicSignature (k := k) c₀ key ad j).2 = a)).card ≤ 4)
    (hcases : ∀ ad ∈ nonzeroProgressions N, ad ∈ A ∨ ∀ b,
      k ≤ 100 * (oppositePositions (cyclicSignature (k := k) c₀ key ad) b).card)
    (hbudget : 2 * (N : ℝ) ^ 2 * p ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀ key)).card : ℝ) *
        (1 - p) ^ ((k + 3) / 4) < 1) :
    ∃ C : ZMod N → Bool, CyclicAvoids C k := by
  classical
  have hbudget' : 2 * ((nonzeroProgressions N).card : ℝ) * p ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀ key)).card : ℝ) *
        (1 - p) ^ ((k + 3) / 4) < 1 := by
    have hc : ((nonzeroProgressions N).card : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast nonzeroProgressions_card_le N
    apply lt_of_le_of_lt _ hbudget
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
        (pow_nonneg hp _)) le_rfl
  obtain ⟨ω, hω⟩ := exists_avoiding_of_rich_or_signature
    (nonzeroProgressions N) A (cyclicSignature (k := k) c₀ key) hA hp hp2 hmult hcases hbudget'
  refine ⟨fun x => Bool.xor (c₀ x) (ω (key x)), ?_⟩
  intro a d hd hmono
  obtain ⟨j, hj⟩ := hω (a, d) ((mem_nonzeroProgressions (a, d)).mpr hd)
    (Bool.xor (c₀ a) (ω (key a)))
  exact hj (hmono j.val j.isLt)

end SparsePerturbation
end QuantitativeVanDerWaerden

end OAI
