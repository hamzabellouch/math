import OAI.Analysis.MutuallyUnbiased.Cubic.CubicSupport

namespace OAI

/-! From cubed row-ratio patterns to the single three-by-three exceptional block. -/

noncomputable section

namespace MUB6

def nonOneSupport (f : Fin 6 → ℂ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => f i ≠ 1)

@[simp] theorem mem_nonOneSupport (f : Fin 6 → ℂ) (i : Fin 6) :
    i ∈ nonOneSupport f ↔ f i ≠ 1 := by
  classical
  simp [nonOneSupport]

theorem twoValuePattern_supported (f : Fin 6 → ℂ) (hf : TwoValuePattern f)
    (hf0 : f 0 = 1) (j : Fin 6) (hj : f j ≠ 1) :
    (nonOneSupport f).card = 3 ∧ (0 : Fin 6) ∉ nonOneSupport f ∧
      ∀ i, f i = supportedValue (nonOneSupport f) (f j) i := by
  classical
  have hd : f 0 ≠ f j := by rw [hf0]; exact Ne.symm hj
  have hv : ∀ i, f i = 1 ∨ f i = f j := by
    simpa only [hf0] using value_pair_exhausts f hf.1 0 j hd
  have hs : nonOneSupport f = Finset.univ.filter (fun i => f i = f j) := by
    ext i
    simp only [mem_nonOneSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => (hv i).resolve_left h
    · intro h
      simpa only [h] using hj
  refine ⟨?_, by simp [hf0], ?_⟩
  · rw [hs]
    exact hf.2 (f j) ⟨j, rfl⟩ ⟨0, hd⟩
  · intro i
    by_cases hi : f i = 1
    · simp [supportedValue, hi]
    · simp [supportedValue, (hv i).resolve_left hi]

theorem dephased_pattern_single_block (F : Fin 6 → Fin 6 → ℂ)
    (h0row : ∀ j, F 0 j = 1) (h0col : ∀ i, F i 0 = 1)
    (hnz : ∀ i j, F i j ≠ 0)
    (hrow : ∀ i, TwoValuePattern (F i))
    (hcol : ∀ j, TwoValuePattern (fun i => F i j))
    (hratio : ∀ i r, i ≠ r → TwoValuePattern (fun j => F i j / F r j))
    (i j : Fin 6) (hij : F i j ≠ 1) :
    ∃ (R S : Finset (Fin 6)) (x : ℂ),
      R.card = 3 ∧ S.card = 3 ∧ (0 : Fin 6) ∉ R ∧ (0 : Fin 6) ∉ S ∧
      x ≠ 0 ∧ x ≠ 1 ∧
      ∀ r c, F r c = if r ∈ R ∧ c ∈ S then x else 1 := by
  classical
  let R := nonOneSupport (fun r => F r j)
  let S := nonOneSupport (F i)
  obtain ⟨hScard, hS0, hSvalue⟩ :=
    twoValuePattern_supported (F i) (hrow i) (h0col i) j hij
  obtain ⟨hRcard, hR0, hRvalue⟩ :=
    twoValuePattern_supported (fun r => F r j) (hcol j) (h0row j) i hij
  have hsamesupport (r c : Fin 6) (hrc : F r c ≠ 1) : nonOneSupport (F r) = S := by
    by_cases hri : r = i
    · subst r
      rfl
    obtain ⟨hUcard, hU0, hUvalue⟩ :=
      twoValuePattern_supported (F r) (hrow r) (h0col r) c hrc
    apply common_support_of_twoValuePattern _ _ hUcard hScard hU0 hS0
      (F r c) (F i j) (hnz r c) hrc hij
    have hq := hratio r i hri
    have heq : (fun k => F r k / F i k) =
        supportedRatio (nonOneSupport (F r)) S (F r c) (F i j) := by
      funext k
      rw [hUvalue k, hSvalue k]
      rfl
    rwa [← heq]
  refine ⟨R, S, F i j, hRcard, hScard, hR0, hS0, hnz i j, hij, ?_⟩
  intro r c
  by_cases hr : r ∈ R
  · have hr' : r ∈ nonOneSupport (fun r => F r j) := hr
    have hrj : F r j ≠ 1 := (mem_nonOneSupport (fun r => F r j) r).mp hr'
    obtain ⟨_, _, hv⟩ :=
      twoValuePattern_supported (F r) (hrow r) (h0col r) j hrj
    have hval : F r j = F i j := by
      simpa only [supportedValue, ite_eq_left hr'] using hRvalue r
    rw [hv c, hsamesupport r j hrj, hval]
    simp [supportedValue, hr]
  · have hrc : F r c = 1 := by
      by_contra hc
      have hs := hsamesupport r c hc
      have hjS : j ∈ S := (mem_nonOneSupport _ _).mpr hij
      have hjU : j ∈ nonOneSupport (F r) := by rwa [hs]
      exact hr ((mem_nonOneSupport (fun r => F r j) r).mpr
        ((mem_nonOneSupport (F r) j).mp hjU))
    simp [hr, hrc]

end MUB6

end

end OAI
