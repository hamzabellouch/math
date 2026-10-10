import OAI.Combinatorics.MatchingPSD.Involutions

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

def lowDegree (x : E → X → ℝ) (d : ℕ) : Submodule ℝ (X → ℝ) :=
  Submodule.span ℝ {f | ∃ l : List E, l.length ≤ d ∧ f = (l.map x).prod}

lemma lowDegree_mono (x : E → X → ℝ) {d e : ℕ} (h : d ≤ e) :
    lowDegree x d ≤ lowDegree x e := by
  apply Submodule.span_mono
  rintro f ⟨l, hl, hf⟩
  exact ⟨l, hl.trans h, hf⟩

lemma one_mem_lowDegree (x : E → X → ℝ) (d : ℕ) : (1 : X → ℝ) ∈ lowDegree x d :=
  Submodule.subset_span ⟨[], Nat.zero_le _, rfl⟩

lemma coord_mem_lowDegree (x : E → X → ℝ) (e : E) : x e ∈ lowDegree x 1 := by
  apply Submodule.subset_span
  exact ⟨[e], by simp, by simp⟩

lemma mul_mem_lowDegree (x : E → X → ℝ) {d e : ℕ} {f g : X → ℝ}
    (hf : f ∈ lowDegree x d) (hg : g ∈ lowDegree x e) :
    f * g ∈ lowDegree x (d + e) := by
  refine Submodule.span_induction₂
    (p := fun f g _ _ => f * g ∈ lowDegree x (d + e)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · rintro f g ⟨l, hl, rfl⟩ ⟨m, hm, rfl⟩
    apply Submodule.subset_span
    exact ⟨l ++ m, by simpa using Nat.add_le_add hl hm, by simp⟩
  · intro g _; simp
  · intro f _; simp
  · intro f g h _ _ _ hf hg
    simpa only [add_mul] using (lowDegree x (d + e)).add_mem hf hg
  · intro f g h _ _ _ hg hh
    simpa only [mul_add] using (lowDegree x (d + e)).add_mem hg hh
  · intro r f g _ _ h
    simpa only [smul_mul_assoc] using (lowDegree x (d + e)).smul_mem r h
  · intro r f g _ _ h
    simpa only [mul_smul_comm] using (lowDegree x (d + e)).smul_mem r h

lemma prod_mem_lowDegree {ι : Type u_3} (x : E → X → ℝ) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i ∈ s, f i ∈ lowDegree x 1) :
    (∏ i ∈ s, f i) ∈ lowDegree x s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_lowDegree x 0
  | @insert i s his ih =>
    rw [Finset.prod_insert his, Finset.card_insert_of_notMem his]
    have hi := hf i (Finset.mem_insert_self i s)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Nat.add_comm] using mul_mem_lowDegree x hi hs

lemma boolean_pattern_mem_lowDegree [DecidableEq E]
    (x : E → X → ℝ) (s t : Finset E) :
    (∏ e ∈ s, if e ∈ t then x e else 1 - x e) ∈ lowDegree x s.card := by
  apply prod_mem_lowDegree
  intro e _
  split_ifs
  · exact coord_mem_lowDegree x e
  · exact (lowDegree x 1).sub_mem (one_mem_lowDegree x 1) (coord_mem_lowDegree x e)

lemma mem_of_fiber_indicators {I : Type u_4} [Fintype I] [DecidableEq I]
    (θ : X → I) (f : X → ℝ) (S : Submodule ℝ (X → ℝ))
    (hf : ∀ a b, θ a = θ b → f a = f b)
    (hind : ∀ a, (fun b => if θ b = θ a then (1 : ℝ) else 0) ∈ S) : f ∈ S := by
  classical
  let g (i : I) : ℝ := if h : ∃ a, θ a = i then f h.choose else 0
  let b (i : I) : X → ℝ := fun a => if θ a = i then 1 else 0
  have hm (i : I) : g i • b i ∈ S := by
    by_cases hi : ∃ a, θ a = i
    · have hb : b i = b (θ hi.choose) := by rw [hi.choose_spec]
      rw [hb]
      exact S.smul_mem _ (hind hi.choose)
    · have hb : b i = 0 := by
        ext a
        have hn : θ a ≠ i := by intro h; exact hi ⟨a, h⟩
        simp [b, hn]
      simp [hb]
  have he : ∑ i, g i • b i = f := by
    ext a
    simp only [Finset.sum_apply, Pi.smul_apply, b, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have ha : ∃ c, θ c = θ a := ⟨a, rfl⟩
    dsimp [g]
    rw [dite_eq_left ha]
    exact hf ha.choose a ha.choose_spec
  rw [← he]
  exact S.sum_mem (fun i _ => hm i)

end MatchingSmoothing

end OAI
