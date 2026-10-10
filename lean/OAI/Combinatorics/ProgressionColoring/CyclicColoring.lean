import OAI.Combinatorics.ProgressionColoring.Perturbation
import OAI.Combinatorics.ProgressionColoring.KeyMultiplicity
import Mathlib.Data.Set.Finite.Range

namespace OAI

noncomputable section

universe uX uAmbient

namespace QuantitativeVanDerWaerden
namespace CyclicColoring

open SparsePerturbation

variable {X : Type uX} {Ambient : Type uAmbient}

def finiteImageKey (key : X → Ambient) (x : X) : Set.range key :=
  ⟨key x, x, rfl⟩

@[simp] theorem finiteImageKey_val (key : X → Ambient) (x : X) :
    (finiteImageKey key x).val = key x := rfl

@[simp] theorem finiteImageKey_eq_iff (key : X → Ambient) (x : X)
    (a : Set.range key) : finiteImageKey key x = a ↔ key x = a.val :=
  Subtype.ext_iff

/-- Coercion keeps literal key identities and is injective on signature words. -/
def ambientSignature {k : ℕ} (key : X → Ambient)
    (σ : Signature (Set.range key) k) : Signature Ambient k :=
  fun j => ((σ j).1, (σ j).2.val)

theorem ambientSignature_injective {k : ℕ} (key : X → Ambient) :
    Function.Injective (ambientSignature (k := k) key) := by
  intro σ τ h
  funext j
  have hj := congrFun h j
  apply Prod.ext
  · exact congrArg (fun z : Bool × Ambient => z.1) hj
  · apply Subtype.ext
    exact congrArg (fun z : Bool × Ambient => z.2) hj

/-- Passing to the finite image does not rename or merge geometric signatures. -/
theorem cyclic_signature_image_card {N k : ℕ} [NeZero N] [DecidableEq Ambient]
    (c₀ : ZMod N → Bool) (key : ZMod N → Ambient)
    (A : Finset (ZMod N × ZMod N)) :
    (A.image (cyclicSignature (k := k) c₀ (finiteImageKey key))).card =
      (A.image (cyclicSignature (k := k) c₀ key)).card := by
  classical
  calc
    _ = ((A.image (cyclicSignature (k := k) c₀ (finiteImageKey key))).image
        (ambientSignature key)).card :=
      (Finset.card_image_of_injective _ (ambientSignature_injective key)).symm
    _ = (A.image (cyclicSignature (k := k) c₀ key)).card := by
      rw [Finset.image_image]
      rfl

/-- The finite Bernoulli construction also applies to an infinite ambient key
type: only the actual image is used as the probability-space coordinate type. -/
theorem exists_cyclicAvoids_of_ambient_keys {N k : ℕ} [NeZero N]
    [DecidableEq Ambient] (c₀ : ZMod N → Bool) (key : ZMod N → Ambient)
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
  apply exists_cyclicAvoids_of_sparse_data c₀ (finiteImageKey key) A hA hp hp2
  · intro ad had a
    refine (Nat.le_of_eq (congrArg (Finset.card : Finset (Fin k) → ℕ) ?_)).trans
      (hmult ad had a.val)
    apply Finset.ext
    intro j
    constructor
    · intro hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (finiteImageKey_eq_iff key _ a).mp (Finset.mem_filter.mp hj).2
    · intro hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (finiteImageKey_eq_iff key _ a).mpr (Finset.mem_filter.mp hj).2
  · intro ad had
    rcases hcases ad had with hmem | hbound
    · exact Or.inl hmem
    · refine Or.inr ?_
      intro b
      refine (hbound b).trans (Nat.mul_le_mul_left 100
        (Nat.le_of_eq (congrArg (Finset.card : Finset (Fin k) → ℕ) ?_)))
      apply Finset.ext
      intro j
      constructor
      · intro hj
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      · intro hj
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · simpa only [cyclic_signature_image_card] using hbudget

theorem exists_cyclicAvoids_of_geometric_data (mesh : AdaptiveMesh)
    {P e D dilation k : ℕ} [NeZero ((P ^ e) ^ D)] (hP : P.Prime) (hk : k ≤ P)
    (hunit : Nat.Coprime dilation ((P ^ e) ^ D))
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (c₀ : CyclicGroup (P ^ e) D → Bool)
    (A : Finset (CyclicGroup (P ^ e) D × CyclicGroup (P ^ e) D))
    (hA : A ⊆ nonzeroProgressions ((P ^ e) ^ D))
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hcases : ∀ ad ∈ nonzeroProgressions ((P ^ e) ^ D), ad ∈ A ∨ ∀ b,
      k ≤ 100 * (oppositePositions
        (cyclicSignature (k := k) c₀ (perturbationKey mesh (P ^ e) D dilation) ad) b).card)
    (hbudget : 2 * (((P ^ e) ^ D : ℕ) : ℝ) ^ 2 * p ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀
        (perturbationKey mesh (P ^ e) D dilation))).card : ℝ) *
        (1 - p) ^ ((k + 3) / 4) < 1) :
    ∃ C : CyclicGroup (P ^ e) D → Bool, CyclicAvoids C k := by
  classical
  apply exists_cyclicAvoids_of_ambient_keys c₀
    (perturbationKey mesh (P ^ e) D dilation) A hA hp hp2 ?_ hcases hbudget
  intro ad had a
  exact perturbationKey_fin_fiber_card_le_four mesh hP hk hunit hsmall ad.1 ad.2
    ((mem_nonzeroProgressions ad).mp had) a

end CyclicColoring
end QuantitativeVanDerWaerden

end

end OAI
