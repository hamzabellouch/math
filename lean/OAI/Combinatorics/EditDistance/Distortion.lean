import OAI.Combinatorics.EditDistance.DirectSums
import OAI.Combinatorics.EditDistance.Metric

namespace OAI

/-!
# Distance-ratio extrema and finite-dimensional embeddings
-/

namespace EditDistortion
universe u v

noncomputable def coordinateEmbedding (X : Type u) [Fintype X] : X ↪ L1 := by
  classical
  let e : X ↪ ℕ := (Fintype.equivFin X).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩
  refine ⟨fun x => lp.single 1 (e x) (1 : ℝ), ?_⟩
  intro x y h
  by_contra hxy
  have hne : e x ≠ e y := fun h => hxy (e.injective h)
  have he := congrArg (fun f : L1 => f (e x)) h
  simp only [lp.single_apply_self,lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 (e y) (1 : ℝ) hne] at he
  norm_num at he

lemma ratios_finite {X : Type u} [Finite X] (ρ : X → X → ℝ) (f : X → L1) :
    {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y}.Finite := by
  refine (Set.finite_range (fun p : X × X => ‖f p.1-f p.2‖/ρ p.1 p.2)).subset ?_
  rintro r ⟨x,y,_,rfl⟩
  exact Set.mem_range.mpr ⟨(x,y),rfl⟩

lemma reverse_ratios_finite {X : Type u} [Finite X] (ρ : X → X → ℝ) (f : X → L1) :
    {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖}.Finite := by
  refine (Set.finite_range (fun p : X × X => ρ p.1 p.2/‖f p.1-f p.2‖)).subset ?_
  rintro r ⟨x,y,_,rfl⟩
  exact Set.mem_range.mpr ⟨(x,y),rfl⟩

lemma distortion_constants {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hd : ∀ x, ρ x x = 0)
    (hp : ∀ x y, x ≠ y → 0 < ρ x y) (f : X ↪ L1) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ distortion ρ f = U*V ∧
      (∀ x y, ‖f x-f y‖ ≤ U*ρ x y) ∧ (∀ x y, ρ x y ≤ V*‖f x-f y‖) := by
  let U := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y}
  let V := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖}
  have hu (x y : X) (hxy : x ≠ y) : ‖f x-f y‖/ρ x y ≤ U :=
    le_csSup (ratios_finite ρ f).bddAbove ⟨x,y,hxy,rfl⟩
  have hv (x y : X) (hxy : x ≠ y) : ρ x y/‖f x-f y‖ ≤ V :=
    le_csSup (reverse_ratios_finite ρ f).bddAbove ⟨x,y,hxy,rfl⟩
  have hn (x y : X) (hxy : x ≠ y) : 0 < ‖f x-f y‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (f.injective h)))
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  refine ⟨U,V,(div_pos (hn x y hxy) (hp x y hxy)).trans_le (hu x y hxy),
    (div_pos (hp x y hxy) (hn x y hxy)).trans_le (hv x y hxy),rfl,?_,?_⟩
  · intro x y
    by_cases hxy : x = y
    · subst y; simp only [sub_self,norm_zero,hd,mul_zero,le_refl]
    · exact (div_le_iff₀ (hp x y hxy)).mp (hu x y hxy)
  · intro x y
    by_cases hxy : x = y
    · subst y; simp only [sub_self,norm_zero,hd,mul_zero,le_refl]
    · exact (div_le_iff₀ (hn x y hxy)).mp (hv x y hxy)

lemma distortion_nonneg {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hd : ∀ x, ρ x x = 0)
    (hp : ∀ x y, x ≠ y → 0 < ρ x y) (f : X ↪ L1) : 0 ≤ distortion ρ f := by
  obtain ⟨U,V,hU,hV,he,_,_⟩ := distortion_constants ρ hd hp f
  rw [he]
  positivity

lemma leastDistortion_lower {X : Type u} [Fintype X] (ρ : X → X → ℝ) (B : ℝ)
    (h : ∀ f : X ↪ L1, B ≤ distortion ρ f) : B ≤ leastDistortion ρ := by
  let : Nonempty (X ↪ L1) := ⟨coordinateEmbedding X⟩
  apply le_csInf (Set.range_nonempty (f := distortion ρ))
  rintro r ⟨f,rfl⟩
  exact h f

lemma finite_words (Alpha : Type u) [Finite Alpha] (d : ℕ) : Finite (Words Alpha d) := by
  let domain := (n : Fin (d+1)) × (Fin n.val → Alpha)
  let F : domain → Words Alpha d := fun ⟨n,v⟩ => ⟨List.ofFn v,by simp only [List.length_ofFn]; omega⟩
  apply Finite.of_surjective F
  intro x
  refine ⟨⟨⟨x.val.length,by have := x.property; omega⟩,x.val.get⟩,?_⟩
  apply Subtype.ext
  exact List.ofFn_get x.val

lemma edit_real_diag {Alpha : Type u} (x : List Alpha) : (edit x x : ℝ) = 0 := by
  exact_mod_cast (cost_refl (s := true) x)

lemma edit_real_pos {Alpha : Type u} (x y : List Alpha) (hxy : x ≠ y) : 0 < (edit x y : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (mt (cost_eq_zero_iff (s := true)).mp hxy)

end EditDistortion

end OAI
