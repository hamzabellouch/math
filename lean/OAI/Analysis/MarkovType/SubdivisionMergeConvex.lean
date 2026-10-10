import OAI.Analysis.MarkovType.SubdivisionProfileExpansion
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem convex_constant_Icc_min {f : ℝ → ℝ} {c : ℝ}
    (hf : ConvexOn ℝ Set.univ f)
    (hc : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = c) :
    ∀ t : ℝ, c ≤ f t := by
  have h0 : f 0 = c := hc 0 ⟨le_rfl, zero_le_one⟩
  have h1 : f 1 = c := hc 1 ⟨zero_le_one, le_rfl⟩
  intro t
  by_cases ht0 : t < 0
  · have h := hf.secant_mono_aux1 (x := t) (y := 0) (z := 1)
      (Set.mem_univ t) (Set.mem_univ 1) ht0 zero_lt_one
    rw [h0, h1] at h
    nlinarith only [h]
  · have h0t : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : t ≤ 1
    · exact (hc t ⟨h0t, ht1⟩).ge
    · have h1t : 1 < t := lt_of_not_ge ht1
      have h := hf.secant_mono_aux1 (x := 0) (y := 1) (z := t)
        (Set.mem_univ 0) (Set.mem_univ t) zero_lt_one h1t
      rw [h0, h1] at h
      nlinarith only [h]

namespace Subdivision

private theorem ofList_singleton (a : ℝ) : ofList [a] = Finsupp.single 0 a := by
  simpa using ofList_replicate 1 a

private theorem ofList_pair (a b : ℝ) :
    ofList [a, b] = Finsupp.single 0 a + Finsupp.single 1 b := by
  change ofList ([a] ++ [b]) = _
  rw [ofList_append, ofList_singleton, ofList_singleton]
  simp only [List.length_singleton, Finsupp.mapDomain_single, Nat.add_zero]

private def pairBase (left right : List ℝ) : C00 :=
  ofList left + Finsupp.mapDomain (fun i => left.length + i)
    (Finsupp.mapDomain (fun i => 2 + i) (ofList right))

private def singleBase (left right : List ℝ) : C00 :=
  ofList left + Finsupp.mapDomain (fun i => left.length + i)
    (Finsupp.mapDomain (fun i => 1 + i) (ofList right))

private theorem pair_context_eq (left right : List ℝ) (a b : ℝ) :
    ofList (left ++ [a, b] ++ right) = pairBase left right +
      Finsupp.single left.length a + Finsupp.single (left.length + 1) b := by
  rw [List.append_assoc, ofList_append, ofList_append, ofList_pair]
  simp only [List.length_cons, List.length_nil, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, Nat.add_zero, pairBase]
  exact ((add_assoc (ofList left)
    (Finsupp.single left.length a + Finsupp.single (left.length + 1) b) _).symm.trans
      (add_right_comm _ _ _)).trans (add_assoc _ _ _).symm

private theorem single_context_eq (left right : List ℝ) (a : ℝ) :
    ofList (left ++ [a] ++ right) = singleBase left right + Finsupp.single left.length a := by
  rw [List.append_assoc, ofList_append, ofList_append, ofList_singleton]
  simp only [List.length_singleton, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, Nat.add_zero, singleBase]
  exact (add_assoc (ofList left) (Finsupp.single left.length a) _).symm.trans
    (add_right_comm _ _ _)

private theorem pair_context_affine (left right : List ℝ)
    (a b c d α β : ℝ) (hαβ : α + β = 1) :
    ofList (left ++ [α * a + β * c, α * b + β * d] ++ right) =
      α • ofList (left ++ [a, b] ++ right) + β • ofList (left ++ [c, d] ++ right) := by
  rw [pair_context_eq, pair_context_eq, pair_context_eq]
  calc
    pairBase left right + Finsupp.single left.length (α * a + β * c) +
        Finsupp.single (left.length + 1) (α * b + β * d) =
      (α + β) • pairBase left right + Finsupp.single left.length (α * a + β * c) +
        Finsupp.single (left.length + 1) (α * b + β * d) := by rw [hαβ, one_smul]
    _ = _ := by
      simp only [add_smul, smul_add, Finsupp.smul_single, smul_eq_mul, Finsupp.single_add]
      abel

private theorem seminorm_single_le (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (k : ℕ) (c : ℝ) : p (Finsupp.single k c) ≤ |c| := by
  classical
  let a : Fin (k + 1) → ℝ := fun i => if i = Fin.last k then c else 0
  have ha : C00.ofArray a = Finsupp.single k c := by
    unfold C00.ofArray C00.place
    rw [Finset.sum_eq_single (Fin.last k)]
    · simp [a]
    · intro i _ hi
      simp [a, hi]
    · simp
  have h := hupper a
  rw [ha] at h
  simpa [a, abs_ite] using h

theorem pair_context_lipschitz (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (left right : List ℝ) (a b a' b' : ℝ) :
    |p (ofList (left ++ [a, b] ++ right)) - p (ofList (left ++ [a', b'] ++ right))| ≤
      |a - a'| + |b - b'| := by
  have hsub : ofList (left ++ [a, b] ++ right) - ofList (left ++ [a', b'] ++ right) =
      Finsupp.single left.length (a - a') + Finsupp.single (left.length + 1) (b - b') := by
    rw [pair_context_eq, pair_context_eq, Finsupp.single_sub, Finsupp.single_sub]
    abel
  calc
    |p (ofList (left ++ [a, b] ++ right)) - p (ofList (left ++ [a', b'] ++ right))|
        ≤ p (ofList (left ++ [a, b] ++ right) - ofList (left ++ [a', b'] ++ right)) :=
      abs_sub_map_le_sub p _ _
    _ = p (Finsupp.single left.length (a - a') +
        Finsupp.single (left.length + 1) (b - b')) := by rw [hsub]
    _ ≤ p (Finsupp.single left.length (a - a')) +
        p (Finsupp.single (left.length + 1) (b - b')) := map_add_le_add p _ _
    _ ≤ |a - a'| + |b - b'| := add_le_add
      (seminorm_single_le p hupper _ _) (seminorm_single_le p hupper _ _)

theorem single_context_lipschitz (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (left right : List ℝ) (a a' : ℝ) :
    |p (ofList (left ++ [a] ++ right)) - p (ofList (left ++ [a'] ++ right))| ≤ |a - a'| := by
  have hsub : ofList (left ++ [a] ++ right) - ofList (left ++ [a'] ++ right) =
      Finsupp.single left.length (a - a') := by
    rw [single_context_eq, single_context_eq, Finsupp.single_sub]
    abel
  calc
    |p (ofList (left ++ [a] ++ right)) - p (ofList (left ++ [a'] ++ right))|
        ≤ p (ofList (left ++ [a] ++ right) - ofList (left ++ [a'] ++ right)) :=
      abs_sub_map_le_sub p _ _
    _ = p (Finsupp.single left.length (a - a')) := by rw [hsub]
    _ ≤ |a - a'| := seminorm_single_le p hupper _ _

private theorem merge_context_le_of_ne_zero (p : Seminorm ℝ C00)
    (left right : List ℝ)
    (hsame : ∀ s θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      p (ofList (left ++ [θ * s, (1 - θ) * s] ++ right)) =
        p (ofList (left ++ [s] ++ right)))
    (a b : ℝ) (hs : a + b ≠ 0) :
    p (ofList (left ++ [a + b] ++ right)) ≤ p (ofList (left ++ [a, b] ++ right)) := by
  let s := a + b
  let f : ℝ → ℝ := fun t => p (ofList (left ++ [t * s, (1 - t) * s] ++ right))
  have hf : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hαβ
    have heq : ofList (left ++ [(α * x + β * y) * s, (1 - (α * x + β * y)) * s] ++ right) =
        α • ofList (left ++ [x * s, (1 - x) * s] ++ right) +
          β • ofList (left ++ [y * s, (1 - y) * s] ++ right) := by
      have hsecond : (1 - (α * x + β * y)) * s = α * ((1 - x) * s) + β * ((1 - y) * s) := by
        calc
          (1 - (α * x + β * y)) * s = ((α + β) - (α * x + β * y)) * s := by rw [hαβ]
          _ = _ := by ring
      rw [show (α * x + β * y) * s = α * (x * s) + β * (y * s) by ring, hsecond]
      exact pair_context_affine left right _ _ _ _ α β hαβ
    change p (ofList (left ++ [(α * x + β * y) * s, (1 - (α * x + β * y)) * s] ++ right)) ≤ _
    rw [heq]
    exact p.convexOn.2 (Set.mem_univ _) (Set.mem_univ _) hα hβ hαβ
  have hmin := convex_constant_Icc_min hf
    (fun t ht => hsame s t ht.1 ht.2) (a / s)
  have hs' : s ≠ 0 := hs
  have hfirst : a / s * s = a := div_mul_cancel₀ a hs'
  have hsecond : (1 - a / s) * s = b := by
    rw [sub_mul, one_mul, hfirst]
    dsimp only [s]
    ring
  simpa only [f, hfirst, hsecond, s] using hmin

theorem merge_context_le (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (left right : List ℝ)
    (hsame : ∀ s θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      p (ofList (left ++ [θ * s, (1 - θ) * s] ++ right)) =
        p (ofList (left ++ [s] ++ right)))
    (a b : ℝ) :
    p (ofList (left ++ [a + b] ++ right)) ≤ p (ofList (left ++ [a, b] ++ right)) := by
  by_cases hs : a + b = 0
  · rw [hs]
    by_contra hbad
    have hgap : p (ofList (left ++ [a, b] ++ right)) < p (ofList (left ++ [0] ++ right)) :=
      lt_of_not_ge hbad
    let δ := (p (ofList (left ++ [0] ++ right)) - p (ofList (left ++ [a, b] ++ right))) / 4
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    have hsum : a + δ + b = δ := by linarith only [hs]
    have hnonzero : a + δ + b ≠ 0 := by rw [hsum]; exact ne_of_gt hδ
    have hmerge := merge_context_le_of_ne_zero p left right hsame (a + δ) b hnonzero
    rw [hsum] at hmerge
    have hsingle := single_context_lipschitz p hupper left right 0 δ
    have hpair := pair_context_lipschitz p hupper left right (a + δ) b a b
    have hsingle' : |p (ofList (left ++ [0] ++ right)) - p (ofList (left ++ [δ] ++ right))| ≤ δ := by
      simpa only [zero_sub, abs_neg, abs_of_pos hδ] using hsingle
    have hpair' : |p (ofList (left ++ [a + δ, b] ++ right)) - p (ofList (left ++ [a, b] ++ right))| ≤ δ := by
      simpa only [add_sub_cancel_left, sub_self, abs_zero, add_zero, abs_of_pos hδ] using hpair
    have h1 := (abs_le.mp hsingle').2
    have h2 := (abs_le.mp hpair').2
    dsimp only [δ] at hδ hmerge h1 h2
    linarith
  · exact merge_context_le_of_ne_zero p left right hsame a b hs

end Subdivision

end MarkovSuperreflexivity

end

end OAI
