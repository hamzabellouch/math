import OAI.Combinatorics.InfiniteMatroid.Cardinality
import OAI.Combinatorics.InfiniteMatroid.FiniteCounting
import OAI.Combinatorics.InfiniteMatroid.BlockDensity

namespace OAI

section
open Set Filter Finset
open scoped Topology
namespace InfiniteMatroidCounterexample

abbrev ColumnTag := CIndex × Fin 3

noncomputable def columnString (t : ColumnTag) (n : ℕ) : Bool :=
  if n < 2 then decide (t.2.val = n) else cindexBinaryEquiv t.1 (n-2)

lemma columnString_injective : Function.Injective columnString := by
  intro t s h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hk : t.2 = s.2 := by
    rcases t with ⟨t,k⟩
    rcases s with ⟨s,l⟩
    fin_cases k <;> fin_cases l <;> simp_all [columnString]
  have ht : t.1 = s.1 := by
    apply cindexBinaryEquiv.injective
    funext n
    have hn := congrFun h (n+2)
    simpa [columnString] using hn
  exact Prod.ext ht hk

def prefixString (h : ℕ → Bool) (m : ℕ) : Fin m → Bool := fun i ↦ h i

lemma eventually_prefix_injective {A : Type} [Finite A] (h : A → (ℕ → Bool))
    (hh : Function.Injective h) :
    ∀ᶠ m : ℕ in atTop, Function.Injective (fun a ↦ prefixString (h a) m) := by
  have he : ∀ a b : A, ∀ᶠ m : ℕ in atTop,
      prefixString (h a) m = prefixString (h b) m → a = b := by
    intro a b
    by_cases hab : a = b
    · exact Eventually.of_forall (fun _ _ ↦ hab)
    have hn : h a ≠ h b := fun he ↦ hab (hh he)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hn
    filter_upwards [eventually_ge_atTop (k+1)] with m hm heq
    exact (hk (congrFun heq ⟨k, by omega⟩)).elim
  exact eventually_all.mpr (fun a ↦ eventually_all.mpr (fun b ↦ he a b))

def column (t : ColumnTag) : Set D := {x | x.2 (prefixString (columnString t) x.1) = true}

noncomputable def dDensity (X : Set D) (m : ℕ) : ℝ := finiteDensity (dBlock m) X

def DSmall (X : Set D) : Prop := Tendsto (dDensity X) atTop (𝓝 0)

lemma dBlock_trace_card (X : Set D) (m : ℕ) :
    (traceFinset (dBlock m) X).card =
      @Fintype.card {f : (Fin m → Bool) → Bool // (⟨m,f⟩ : D) ∈ X}
        (by classical exact inferInstance) := by
  classical
  let e : ((Fin m → Bool) → Bool) ↪ D := ⟨fun f ↦ ⟨m,f⟩, fun _ _ h ↦ by simpa using h⟩
  have he : traceFinset (dBlock m) X = (univ.filter (fun f ↦ (⟨m,f⟩ : D) ∈ X)).map e := by
    ext x
    rcases x with ⟨k,f⟩
    simp only [mem_traceFinset, mem_dBlock, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨rfl,hf⟩
      exact ⟨f,hf,rfl⟩
    · rintro ⟨g,hg,heq⟩
      change (⟨m,g⟩ : D) = ⟨k,f⟩ at heq
      cases heq
      exact ⟨rfl,hg⟩
  rw [he, card_map]
  exact (Fintype.card_subtype _).symm

lemma dDensity_formula (X : Set D) (m : ℕ) :
    dDensity X m =
      (@Fintype.card {f : (Fin m → Bool) → Bool // (⟨m,f⟩ : D) ∈ X}
        (by classical exact inferInstance) : ℝ) / Fintype.card ((Fin m → Bool) → Bool) := by
  simp only [dDensity, finiteDensity, dBlock_trace_card, card_dBlock, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- All finite marginals are uniform once the chosen prefixes separate. -/
lemma columns_uniform {A : Type} [Fintype A] [DecidableEq A] (e : A ↪ ColumnTag)
    (P : (A → Bool) → Prop) :
    ∀ᶠ m in atTop,
      dDensity {x : D | P (fun a ↦ x.2 (prefixString (columnString (e a)) x.1))} m =
        (Nat.card {v : A → Bool // P v} : ℝ) /
          Fintype.card (A → Bool) := by
  classical
  filter_upwards [eventually_prefix_injective (fun a ↦ columnString (e a))
    (columnString_injective.comp e.injective)] with m hm
  rw [dDensity_formula]
  rw [Nat.card_eq_fintype_card]
  exact function_density_restriction ⟨fun a ↦ prefixString (columnString (e a)) m, hm⟩ P

lemma columns_pattern (F : Finset ColumnTag) (v : F → Bool) :
    ∀ᶠ m in atTop,
      dDensity {x : D | ∀ t : F, x.2 (prefixString (columnString t) x.1) = v t} m =
        1 / (2 : ℝ)^F.card := by
  classical
  have h := columns_uniform (A := F) ⟨Subtype.val, Subtype.val_injective⟩ (fun w ↦ w = v)
  have hc : Nat.card {w : F → Bool // w = v} = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_one_iff.mpr ⟨⟨v,rfl⟩, fun w ↦ Subtype.ext w.property⟩
  rw [hc] at h
  simpa [funext_iff] using h

lemma dSmall_empty : DSmall ∅ := by
  have he : dDensity ∅ = fun _ ↦ 0 := by ext m; simp [dDensity, finiteDensity]
  rw [DSmall, he]
  exact tendsto_const_nhds

lemma dSmall_mono {X Y : Set D} (hY : DSmall Y) (hXY : X ⊆ Y) : DSmall X :=
  squeeze_zero (fun _ ↦ finiteDensity_nonneg _ _) (fun _ ↦ finiteDensity_mono _ hXY) hY

lemma dSmall_union {X Y : Set D} (hX : DSmall X) (hY : DSmall Y) : DSmall (X ∪ Y) := by
  have ht : Tendsto (fun m ↦ dDensity X m + dDensity Y m) atTop (𝓝 0) := by simpa using hX.add hY
  exact squeeze_zero (fun m ↦ finiteDensity_nonneg _ _) (fun m ↦ finiteDensity_union_le _ _ _) ht

lemma dSmall_false_of_eventual {X : Set D} {c : ℝ} (hc : 0 < c)
    (h : dDensity X =ᶠ[atTop] fun _ ↦ c) : ¬ DSmall X := by
  intro hX
  have he := tendsto_nhds_unique ((tendsto_congr' h).mp hX) tendsto_const_nhds
  exact hc.ne he

lemma pattern_positive (F : Finset ColumnTag) (v : F → Bool) :
    ¬ DSmall {x : D | ∀ t : F, x.2 (prefixString (columnString t) x.1) = v t} :=
  dSmall_false_of_eventual (by positivity) (columns_pattern F v)

end InfiniteMatroidCounterexample
end

end OAI
