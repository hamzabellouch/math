import OAI.Computability.PerfectCompleteness.Reduction.CanonicalGameLemmas

namespace OAI

section

namespace PerfectCompleteness.LocalCompletionFamily

open scoped Classical
open CompletionProbability

noncomputable section

abbrev Input (q : Nat) := (Fin (2 * q) → Bool) × (Fin (2 * q) → Fin q)

abbrev Result (q : Nat) := Fin (2 * q) × (Fin (2 * q) → Fin (2 * q) → Fin q)

abbrev Legal {q : Nat} (input : Input q) := {a : Fin (2 * q) // input.1 a = true}

def legalEmbedding {q : Nat} (input : Input q) : Legal input ↪ Fin (2 * q) :=
  ⟨Subtype.val, Subtype.val_injective⟩

def legalProjection {q : Nat} (input : Input q) (a : Legal input) : Fin q := input.2 a.val

def Admissible {q : Nat} (input : Input q) : Prop :=
  ∀ b, Fintype.card {a : Legal input // input.2 a.val = b} ≤ 2

def activeCount {q : Nat} (result : Result q) : Nat := result.1.val + 1

theorem activeCount_positive {q : Nat} (result : Result q) : 0 < activeCount result :=
  Nat.succ_pos _

theorem activeCount_le {q : Nat} (result : Result q) : activeCount result ≤ 2 * q :=
  Nat.succ_le_of_lt result.1.isLt

def table {q : Nat} (result : Result q) (seed : Fin (activeCount result)) :
    Fin (2 * q) → Fin q :=
  result.2 ⟨seed.val, lt_of_lt_of_le seed.isLt (activeCount_le result)⟩

structure Correct {q : Nat} (input : Input q) (result : Result q) : Prop where
  agrees : ∀ seed a, input.1 a = true → table result seed a = input.2 a
  exact_two : ∀ seed b, Fintype.card {a : Fin (2 * q) // table result seed a = b} = 2
  illegal_probability : ∀ a, input.1 a ≠ true → ∀ b,
    uniformProbability (fun seed : Fin (activeCount result) => table result seed a = b) ≤
      2 / (2 * q - Fintype.card (Legal input) : Nat)

def packSampler {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) : Result q :=
  (⟨n - 1, by omega⟩,
    fun slot => if h : slot.val < n then sampler ⟨slot.val, h⟩ else sampler ⟨0, hn⟩)

@[simp] theorem activeCount_packSampler {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) :
    activeCount (packSampler hn hbound sampler) = n := by
  change n - 1 + 1 = n
  omega

def packedSeedEquiv {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) :
    Fin (activeCount (packSampler hn hbound sampler)) ≃ Fin n where
  toFun seed := ⟨seed.val, by simpa only [activeCount_packSampler] using seed.isLt⟩
  invFun seed := ⟨seed.val, by simpa only [activeCount_packSampler] using seed.isLt⟩
  left_inv seed := Fin.ext rfl
  right_inv seed := Fin.ext rfl

theorem table_packSampler {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q)
    (seed : Fin (activeCount (packSampler hn hbound sampler))) :
    table (packSampler hn hbound sampler) seed =
      sampler (packedSeedEquiv hn hbound sampler seed) := by
  have hs : seed.val < n := (packedSeedEquiv hn hbound sampler seed).isLt
  change (if h : seed.val < n then sampler ⟨seed.val, h⟩ else sampler ⟨0, hn⟩) =
    sampler ⟨seed.val, hs⟩
  rw [dite_eq_left hs]

private theorem uniformProbability_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (equiv : Ω ≃ Γ) (event : Γ → Prop) :
    uniformProbability (fun seed => event (equiv seed)) = uniformProbability event := by
  let restricted : {seed : Ω // event (equiv seed)} ≃ {seed : Γ // event seed} :=
    equiv.subtypeEquiv (fun _ => Iff.rfl)
  unfold uniformProbability
  rw [Fintype.card_congr restricted, Fintype.card_congr equiv]

private theorem uniformProbability_packSampler {q n : Nat}
    (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) (a : Fin (2 * q)) (b : Fin q) :
    uniformProbability (fun seed : Fin (activeCount (packSampler hn hbound sampler)) =>
      table (packSampler hn hbound sampler) seed a = b) =
    uniformProbability (fun seed : Fin n => sampler seed a = b) := by
  have hevent :
      (fun seed : Fin (activeCount (packSampler hn hbound sampler)) =>
        table (packSampler hn hbound sampler) seed a = b) =
      (fun seed : Fin (activeCount (packSampler hn hbound sampler)) =>
        sampler (packedSeedEquiv hn hbound sampler seed) a = b) := by
    funext seed
    exact congrArg (fun f : Fin (2 * q) → Fin q => f a = b)
      (table_packSampler hn hbound sampler seed)
  exact (congrArg
    (uniformProbability (Ω := Fin (activeCount (packSampler hn hbound sampler))))
    hevent).trans
      (uniformProbability_equiv
        (Ω := Fin (activeCount (packSampler hn hbound sampler))) (Γ := Fin n)
        (packedSeedEquiv hn hbound sampler) (fun seed : Fin n => sampler seed a = b))

private theorem correct_packSampler {q n : Nat} (input : Input q)
    (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q)
    (hext : ∀ seed l, sampler seed (legalEmbedding input l) = legalProjection input l)
    (hexact : ∀ seed b, Fintype.card {a : Fin (2 * q) // sampler seed a = b} = 2)
    (hprob : ∀ (a : Illegal (legalEmbedding input)) (b : Fin q),
      uniformProbability (fun seed : Fin n => sampler seed a.val = b) ≤
        2 / (2 * q - Fintype.card (Legal input) : Nat)) :
    Correct input (packSampler hn hbound sampler) := by
  constructor
  · intro seed a ha
    rw [table_packSampler]
    exact hext (packedSeedEquiv hn hbound sampler seed) ⟨a, ha⟩
  · intro seed b
    rw [table_packSampler]
    have hb := hexact (packedSeedEquiv hn hbound sampler seed) b
    simp only [← Nat.card_eq_fintype_card] at hb ⊢
    exact hb
  · intro a ha b
    rw [uniformProbability_packSampler]
    have hillegal : a ∉ Set.range (legalEmbedding input) := by
      rintro ⟨l, hl⟩
      have hval : l.val = a := hl
      exact ha (hval ▸ l.property)
    exact hprob ⟨a, hillegal⟩ b

theorem exists_correct {q : Nat} (hq : 0 < q) (input : Input q)
    (hadmissible : Admissible input) : ∃ result : Result q, Correct input result := by
  obtain ⟨n, hn, hsize, sampler, hext, hexact, hprob⟩ :=
    exists_completion_sampler_bounded (legalEmbedding input) (legalProjection input)
      (by
        intro b
        rw [Fintype.card_eq_nat_card]
        change Nat.card {l : Legal input // input.2 l.val = b} ≤ 2
        have hb := hadmissible b
        rw [Fintype.card_eq_nat_card] at hb
        exact hb)
      (by simp)
  have hfull : 0 < 2 * q := Nat.mul_pos (by decide) hq
  have hbound : n ≤ 2 * q := by
    have hsize' : n ≤ max 1 (2 * q - Fintype.card (Legal input)) := by
      simpa only [Fintype.card_fin] using hsize
    exact hsize'.trans (max_le (Nat.succ_le_of_lt hfull) (Nat.sub_le _ _))
  refine ⟨packSampler hn hbound sampler,
    correct_packSampler input hn hbound sampler hext ?_ ?_⟩
  · intro seed b
    have hb := hexact seed b
    simp only [← Nat.card_eq_fintype_card] at hb ⊢
    exact hb
  · intro a b
    simpa only [Fintype.card_fin] using (hprob a b).2

def fallback {q : Nat} (hq : 0 < q) : Result q :=
  (⟨0, Nat.mul_pos (by decide) hq⟩, fun _ _ => ⟨0, hq⟩)

def lookup {q : Nat} (hq : 0 < q) (input : Input q) : Result q :=
  if h : Admissible input then Classical.choose (exists_correct hq input h) else fallback hq

theorem lookup_correct {q : Nat} (hq : 0 < q) (input : Input q)
    (hadmissible : Admissible input) : Correct input (lookup hq input) := by
  unfold lookup
  rw [dite_eq_left hadmissible]
  exact Classical.choose_spec (exists_correct hq input hadmissible)

end
end PerfectCompleteness.LocalCompletionFamily

end

end OAI
