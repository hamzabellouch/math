import OAI.NumberTheory.TwoPoint.Bounds.ResidueSampling

namespace OAI

/-! Exact selected-modulus intersection estimates on a single fixed
interval or cube. These discharge the arithmetic premise of Bonferroni. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selected_pairwise_coprime {ι : Type*} [DecidableEq ι]
    (s : ι → ℕ) (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (S : Finset ι) :
    Pairwise (fun i j : S => (s i).Coprime (s j)) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))

theorem sieve_one_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) (S : Finset ι) :
    |(uniformFiniteLaw (Fin N)).probability
        (eventIntersection (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i))) S) -
      ∏ i ∈ S, (uniformZModLaw (s i)).probability (E i)| ≤
        (∏ i ∈ S, (s i : ℝ)) / N := by
  let q : S → ℕ := fun i => s i
  have hc := selected_pairwise_coprime s hcop S
  have hmap (j : Fin N) (i : S) :
      ZMod.prodEquivPi q hc ((A : ZMod (∏ i, q i)) + (j.val : ZMod (∏ i, q i))) i =
        ((A + j.val : ℕ) : ZMod (s i)) := by
    rw [← Nat.cast_add]
    simp only [ZMod.prodEquivPi_apply, map_natCast]
  have hh := sieveCRT_one_sample_discrepancy q hc (A : ZMod (∏ i, q i)) N
    (fun i => E i)
  simp_rw [hmap] at hh
  have he : (fun j : Fin N => ∀ i : S, E i ((A + j.val : ℕ) : ZMod (s i))) =
      eventIntersection (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i))) S := by
    funext j
    simp only [eventIntersection, Subtype.forall]
  rw [he, Nat.cast_prod] at hh
  rw [← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (uniformZModLaw (s i)).probability (E i)),
    ← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (s i : ℝ))] at hh
  exact hh

theorem sieve_cube_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ℕ × ℕ × ℕ) (N : ℕ) [NeZero N]
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) (S : Finset ι) :
    |(uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
        (eventIntersection (fun i (j : Fin N × Fin N × Fin N) => E i
          (((A.1 + j.1.val : ℕ) : ZMod (s i)),
            ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
            ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i)))) S) -
      ∏ i ∈ S, (uniformResidueCubeLaw (s i)).probability (E i)| ≤
        3 / (N : ℝ) * ∏ i ∈ S, (s i : ℝ) := by
  let q : S → ℕ := fun i => s i
  have hc := selected_pairwise_coprime s hcop S
  have hmap (j : Fin N × Fin N × Fin N) (i : S) :
      sieveCubeCRT q hc
        ((A.1 : ZMod (∏ i, q i)) + (j.1.val : ZMod (∏ i, q i)),
          (A.2.1 : ZMod (∏ i, q i)) + (j.2.1.val : ZMod (∏ i, q i)),
          (A.2.2 : ZMod (∏ i, q i)) + (j.2.2.val : ZMod (∏ i, q i))) i =
        (((A.1 + j.1.val : ℕ) : ZMod (s i)),
          ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
          ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i))) := by
    simp only [← Nat.cast_add]
    exact sieveCubeCRT_natCast q hc _ _ _ i
  have hh := sieveCRT_cube_sample_discrepancy q hc
    ((A.1 : ZMod (∏ i, q i)), (A.2.1 : ZMod (∏ i, q i)), (A.2.2 : ZMod (∏ i, q i))) N
    (fun i => E i)
  simp_rw [hmap] at hh
  have he : (fun j : Fin N × Fin N × Fin N => ∀ i : S, E i
      (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
        ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i)))) =
      eventIntersection (fun i (j : Fin N × Fin N × Fin N) => E i
        (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
          ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i)))) S := by
    funext j
    simp only [eventIntersection, Subtype.forall]
  rw [he, Nat.cast_prod] at hh
  rw [← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (uniformResidueCubeLaw (s i)).probability (E i)),
    ← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (s i : ℝ))] at hh
  convert hh using 1
  ring

end TwoPointCorrelations

end OAI
