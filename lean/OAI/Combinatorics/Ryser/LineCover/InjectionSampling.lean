import OAI.Combinatorics.Ryser.Probability.Product
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

universe u v w

def restrict {I : Type u} {J : Type v} {Ω : Type w}
    (j : I ↪ J) (sample : J ↪ Ω) : I ↪ Ω :=
  j.trans sample

@[simp] theorem restrict_apply {I : Type u} {J : Type v} {Ω : Type w}
    (j : I ↪ J) (sample : J ↪ Ω) (i : I) :
    restrict j sample i = sample (j i) := rfl

theorem restriction_fiber_natCard_eq
    {I : Type u} {J : Type v} {Ω : Type w} [Finite I]
    (j : I ↪ J) (v₀ v₁ : I ↪ Ω) :
    Nat.card {sample : J ↪ Ω // restrict j sample = v₀} =
      Nat.card {sample : J ↪ Ω // restrict j sample = v₁} := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    v₀ v₁ v₀.injective v₁.injective
  let E : (J ↪ Ω) ≃ (J ↪ Ω) :=
    Equiv.embeddingCongr (Equiv.refl J) σ
  refine Nat.card_congr
    (E.subtypeEquiv
      (p := fun sample => restrict j sample = v₀)
      (q := fun sample => restrict j sample = v₁) ?_)
  intro sample
  constructor
  · intro hu
    apply Function.Embedding.ext
    intro i
    change σ (sample (j i)) = v₁ i
    have hi := congrArg (fun b : I ↪ Ω => b i) hu
    change sample (j i) = v₀ i at hi
    exact (congrArg σ hi).trans (hσ i)
  · intro hu
    apply Function.Embedding.ext
    intro i
    change sample (j i) = v₀ i
    apply σ.injective
    have hi := congrArg (fun b : I ↪ Ω => b i) hu
    change σ (sample (j i)) = v₁ i at hi
    exact hi.trans (hσ i).symm

theorem natCard_embeddings
    {A : Type u} {B : Type v} [Finite A] [Finite B] :
    Nat.card (A ↪ B) =
      (Nat.card B).descFactorial (Nat.card A) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_embedding_eq (α := A) (β := B))

theorem restriction_fiber_natCard
    {I : Type u} {J : Type v} {Ω : Type w}
    [Finite I] [Finite J] [Finite Ω]
    (j : I ↪ J) (v₀ : I ↪ Ω) :
    Nat.card {sample : J ↪ Ω // restrict j sample = v₀} =
      (Nat.card Ω - Nat.card I).descFactorial
        (Nat.card J - Nat.card I) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  let : Fintype Ω := Fintype.ofFinite Ω
  have hfactor :
      Nat.card (J ↪ Ω) =
        Nat.card (I ↪ Ω) *
          Nat.card {sample : J ↪ Ω // restrict j sample = v₀} := by
    calc
      Nat.card (J ↪ Ω) =
          ∑ v₁ : I ↪ Ω,
            Nat.card {sample : J ↪ Ω // restrict j sample = v₁} := by
        rw [← Nat.card_congr
          (Equiv.sigmaFiberEquiv (fun sample : J ↪ Ω => restrict j sample))]
        exact Nat.card_sigma
      _ = ∑ _v₁ : I ↪ Ω,
          Nat.card {sample : J ↪ Ω // restrict j sample = v₀} := by
        apply Finset.sum_congr rfl
        intro v₁ _
        exact restriction_fiber_natCard_eq j v₁ v₀
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ,
          Nat.nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [natCard_embeddings (A := J) (B := Ω),
    natCard_embeddings (A := I) (B := Ω)] at hfactor
  have hIJ : Nat.card I ≤ Nat.card J :=
    Nat.card_le_card_of_injective j j.injective
  have hIΩ : Nat.card I ≤ Nat.card Ω :=
    Nat.card_le_card_of_injective v₀ v₀.injective
  have hpos : 0 < (Nat.card Ω).descFactorial (Nat.card I) :=
    Nat.descFactorial_pos.mpr hIΩ
  apply Nat.mul_left_cancel hpos
  calc
    (Nat.card Ω).descFactorial (Nat.card I) *
        Nat.card {sample : J ↪ Ω // restrict j sample = v₀} =
        (Nat.card Ω).descFactorial (Nat.card J) := hfactor.symm
    _ = (Nat.card Ω - Nat.card I).descFactorial
          (Nat.card J - Nat.card I) *
        (Nat.card Ω).descFactorial (Nat.card I) :=
      (Nat.descFactorial_mul_descFactorial
        (n := Nat.card Ω) hIJ).symm
    _ = _ := Nat.mul_comm _ _

section Laws

variable {I : Type u} {J : Type v} {Ω : Type w}
  [Fintype I] [Fintype J] [Fintype Ω]

theorem map_uniform_restrict [Nonempty (J ↪ Ω)] [Nonempty (I ↪ Ω)]
    (j : I ↪ J) :
    (FiniteLaw.uniform (J ↪ Ω)).map (restrict j) =
      FiniteLaw.uniform (I ↪ Ω) :=
  FiniteLaw.map_uniform_of_fiber_card_eq (restrict j)
    (restriction_fiber_natCard_eq j)

theorem prob_restrict [Nonempty (J ↪ Ω)] [Nonempty (I ↪ Ω)]
    (j : I ↪ J) (P : (I ↪ Ω) → Prop) :
    (FiniteLaw.uniform (J ↪ Ω)).prob (fun sample => P (restrict j sample)) =
      (FiniteLaw.uniform (I ↪ Ω)).prob P := by
  calc
    _ = ((FiniteLaw.uniform (J ↪ Ω)).map (restrict j)).prob P :=
      (FiniteLaw.prob_map _ _ _).symm
    _ = _ := by rw [map_uniform_restrict j]

theorem expectation_restrict [Nonempty (J ↪ Ω)] [Nonempty (I ↪ Ω)]
    (j : I ↪ J) (f : (I ↪ Ω) → ℝ) :
    (FiniteLaw.uniform (J ↪ Ω)).expectation (fun sample => f (restrict j sample)) =
      (FiniteLaw.uniform (I ↪ Ω)).expectation f := by
  calc
    _ = ((FiniteLaw.uniform (J ↪ Ω)).map (restrict j)).expectation f :=
      (FiniteLaw.expectation_map _ _ _).symm
    _ = _ := by rw [map_uniform_restrict j]

theorem map_uniform_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω] (i : I) :
    (FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i) =
      FiniteLaw.uniform Ω := by
  classical
  apply FiniteLaw.map_uniform_of_fiber_card_eq
  intro a b
  let E : (I ↪ Ω) ≃ (I ↪ Ω) :=
    Equiv.embeddingCongr (Equiv.refl I) (Equiv.swap a b)
  refine Nat.card_congr
    (E.subtypeEquiv
      (p := fun sample => sample i = a)
      (q := fun sample => sample i = b) ?_)
  intro sample
  change sample i = a ↔ Equiv.swap a b (sample i) = b
  constructor
  · intro hu
    rw [hu, Equiv.swap_apply_left]
  · intro hu
    apply (Equiv.swap a b).injective
    simpa only [Equiv.swap_apply_left] using hu

theorem prob_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω]
    (i : I) (P : Ω → Prop) :
    (FiniteLaw.uniform (I ↪ Ω)).prob (fun sample => P (sample i)) =
      (FiniteLaw.uniform Ω).prob P := by
  calc
    _ = ((FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i)).prob P :=
      (FiniteLaw.prob_map _ _ _).symm
    _ = _ := by rw [map_uniform_coordinate i]

theorem expectation_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω]
    (i : I) (f : Ω → ℝ) :
    (FiniteLaw.uniform (I ↪ Ω)).expectation (fun sample => f (sample i)) =
      (FiniteLaw.uniform Ω).expectation f := by
  calc
    _ = ((FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i)).expectation f :=
      (FiniteLaw.expectation_map _ _ _).symm
    _ = _ := by rw [map_uniform_coordinate i]

end Laws

theorem sample_nonempty (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) : Nonempty (I ↪ Ω) :=
  Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card] using hle)

noncomputable def law (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) : FiniteLaw (I ↪ Ω) := by
  letI : Nonempty (I ↪ Ω) := sample_nonempty I Ω hle
  exact FiniteLaw.uniform (I ↪ Ω)

theorem law_eq_uniform (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    [Nonempty (I ↪ Ω)] (hle : Nat.card I ≤ Nat.card Ω) :
    law I Ω hle = FiniteLaw.uniform (I ↪ Ω) := rfl

theorem law_weight (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) (sample : I ↪ Ω) :
    (law I Ω hle).weight sample =
      ((Nat.card Ω).descFactorial (Nat.card I) : ℝ)⁻¹ := by
  change (Fintype.card (I ↪ Ω) : ℝ)⁻¹ = _
  rw [← Nat.card_eq_fintype_card (α := I ↪ Ω), natCard_embeddings]

theorem law_prob (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) (P : (I ↪ Ω) → Prop) :
    (law I Ω hle).prob P =
      (Nat.card {sample : I ↪ Ω // P sample} : ℝ) /
        ((Nat.card Ω).descFactorial (Nat.card I) : ℝ) := by
  classical
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hle
  simpa only [law_eq_uniform, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_embedding_eq] using
    (FiniteLaw.uniform_prob (I ↪ Ω) P)

variable {I : Type u} {J : Type v} {Ω : Type w}
  [Fintype I] [Fintype J] [Fintype Ω]

theorem map_law_restrict (j : I ↪ J)
    (hJ : Nat.card J ≤ Nat.card Ω) (hI : Nat.card I ≤ Nat.card Ω) :
    (law J Ω hJ).map (restrict j) = law I Ω hI := by
  let : Nonempty (J ↪ Ω) := sample_nonempty J Ω hJ
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hI
  simpa only [law_eq_uniform] using (map_uniform_restrict (Ω := Ω) j)

theorem prob_law_restrict (j : I ↪ J)
    (hJ : Nat.card J ≤ Nat.card Ω) (hI : Nat.card I ≤ Nat.card Ω)
    (P : (I ↪ Ω) → Prop) :
    (law J Ω hJ).prob (fun sample => P (restrict j sample)) =
      (law I Ω hI).prob P := by
  let : Nonempty (J ↪ Ω) := sample_nonempty J Ω hJ
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hI
  simpa only [law_eq_uniform] using (prob_restrict j P)

theorem expectation_law_restrict (j : I ↪ J)
    (hJ : Nat.card J ≤ Nat.card Ω) (hI : Nat.card I ≤ Nat.card Ω)
    (f : (I ↪ Ω) → ℝ) :
    (law J Ω hJ).expectation (fun sample => f (restrict j sample)) =
      (law I Ω hI).expectation f := by
  let : Nonempty (J ↪ Ω) := sample_nonempty J Ω hJ
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hI
  simpa only [law_eq_uniform] using (expectation_restrict j f)

end RyserCoveringCounterexample.InjectionSampling

end OAI
