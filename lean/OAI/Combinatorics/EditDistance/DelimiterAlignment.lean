import OAI.Combinatorics.EditDistance.Metric

namespace OAI

/-!
# Increasing matchings through binary delimiter blocks
-/

namespace EditCode
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Matching
variable {k w n U V : ℕ} {f g : Fin k → ℕ}

def BlockSpan (f g : Fin k → ℕ) (w i : ℕ) : Prop :=
  ∃ t : ℕ, ∀ r : ℕ, r < w → ∃ a : Fin k, f a = w * i + r ∧ g a = t + r

def Missing (f : Fin k → ℕ) (w i : ℕ) : Prop :=
  ∃ r : ℕ, r < w ∧ ∀ a : Fin k, f a ≠ w * i + r

def Gap (f g : Fin k → ℕ) (w i : ℕ) : Prop :=
  ∃ (r : ℕ) (a b : Fin k), r + 1 < w ∧ f a = w * i + r ∧
    f b = w * i + (r+1) ∧ g a + 1 < g b

lemma span_of_no_defect (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w) (i : ℕ)
    (hm : ¬ Missing f w i) (hgap : ¬ Gap f g w i) : BlockSpan f g w i := by
  have hfull : ∀ r : ℕ, r < w → ∃ a : Fin k, f a = w * i + r := by
    intro r hr
    by_contra h
    exact hm ⟨r,hr,by simpa only [not_exists] using h⟩
  obtain ⟨a₀, ha₀⟩ := hfull 0 hw
  refine ⟨g a₀, ?_⟩
  intro r hr
  induction r with
  | zero => exact ⟨a₀,ha₀,by omega⟩
  | succ r ih =>
      obtain ⟨a, ha, hga⟩ := ih (by omega)
      obtain ⟨b, hb⟩ := hfull (r+1) hr
      have hab : a < b := hf.lt_iff_lt.mp (by omega)
      have hgab := hg hab
      have hn : ¬g a + 1 < g b := fun h => hgap ⟨r,a,b,hr,ha,hb,h⟩
      exact ⟨b,hb,by omega⟩

lemma defect_of_not_span (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w) (i : ℕ)
    (h : ¬BlockSpan f g w i) : Missing f w i ∨ Gap f g w i := by
  by_contra h'
  push Not at h'
  exact h (span_of_no_defect hf hg hw i h'.1 h'.2)

def Charge (f g : Fin k → ℕ) (w i : ℕ) : ℕ ⊕ ℕ → Prop
  | Sum.inl x => w * i ≤ x ∧ x < w * i + w ∧ ∀ a : Fin k, f a ≠ x
  | Sum.inr x => (∀ a : Fin k, g a ≠ x) ∧ ∃ a b : Fin k,
      w * i ≤ f a ∧ f a < w * i + w ∧ w * i ≤ f b ∧ f b < w * i + w ∧
        g a < x ∧ x < g b

lemma exists_charge (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w) (i : ℕ)
    (h : ¬BlockSpan f g w i) : ∃ x, Charge f g w i x := by
  rcases defect_of_not_span hf hg hw i h with hm | hgap
  · obtain ⟨r,hr,hm⟩ := hm
    exact ⟨Sum.inl (w*i+r), by exact ⟨by omega,by omega,hm⟩⟩
  · obtain ⟨r,a,b,hr,ha,hb,hgap⟩ := hgap
    refine ⟨Sum.inr (g a+1), ?_⟩
    constructor
    · intro c hc
      have hac : a < c := hg.lt_iff_lt.mp (by omega)
      have hcb : c < b := hg.lt_iff_lt.mp (by omega)
      have hfa := hf hac
      have hfb := hf hcb
      omega
    · exact ⟨a,b,by omega,by omega,by omega,by omega,by omega,hgap⟩

lemma charge_distinct (hf : StrictMono f) (hg : StrictMono g)
    {i j : ℕ} (hij : i ≠ j) {x : ℕ ⊕ ℕ}
    (hi : Charge f g w i x) (hj : Charge f g w j x) : False := by
  wlog h : i < j generalizing i j
  · exact this hij.symm hj hi (lt_of_le_of_ne (Nat.le_of_not_gt h) hij.symm)
  have hwi : w * i + w ≤ w * j := by
    have := Nat.mul_le_mul_left w h
    nlinarith
  cases x with
  | inl x => dsimp [Charge] at hi hj; omega
  | inr x =>
      obtain ⟨_,a,b,ha₁,ha₂,hb₁,hb₂,hax,hxb⟩ := hi
      obtain ⟨_,c,d,hc₁,hc₂,hd₁,hd₂,hcx,hxd⟩ := hj
      have hbc : b < c := hf.lt_iff_lt.mp (by omega)
      have := hg hbc
      omega

lemma missing_card {N : ℕ} (hf : Function.Injective f) (hN : ∀ a, f a < N) :
    (Finset.range N \ Finset.univ.image f).card = N - k := by
  have hs : Finset.univ.image f ⊆ Finset.range N := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hN a)
  rw [Finset.card_sdiff_of_subset hs, Finset.card_range,
    Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

theorem bad_blocks_le_loss
    (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w)
    (hU : ∀ a, f a < U) (hV : ∀ a, g a < V) (hn : w * n ≤ U) :
    (Finset.univ.filter (fun i : Fin n => ¬BlockSpan f g w i.val)).card ≤ (U-k) + (V-k) := by
  classical
  let B := {i : Fin n // ¬BlockSpan f g w i.val}
  let X := Finset.range U \ Finset.univ.image f
  let Y := Finset.range V \ Finset.univ.image g
  have hx (i : B) : ∃ x, Charge f g w i.val.val x := exists_charge hf hg hw i.val i.property
  let c (i : B) : ℕ ⊕ ℕ := (hx i).choose
  have hc (i : B) : Charge f g w i.val.val (c i) := (hx i).choose_spec
  have hcX (i : B) (x : ℕ) (he : c i = Sum.inl x) : x ∈ X := by
    have h := hc i
    rw [he] at h
    rcases h with ⟨h₁,h₂,h₃⟩
    have hwi : w * (i.val.val+1) ≤ w * n := Nat.mul_le_mul_left _ i.val.isLt
    simp only [X, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and, not_exists]
    exact ⟨by nlinarith,fun a => (h₃ a)⟩
  have hcY (i : B) (x : ℕ) (he : c i = Sum.inr x) : x ∈ Y := by
    have h := hc i
    rw [he] at h
    obtain ⟨hx,a,b,_,_,_,_,_,hxb⟩ := h
    simp only [Y, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and, not_exists]
    exact ⟨lt_trans hxb (hV b),hx⟩
  let c' (i : B) : X ⊕ Y := match he : c i with
    | Sum.inl x => Sum.inl ⟨x,hcX i x he⟩
    | Sum.inr x => Sum.inr ⟨x,hcY i x he⟩
  have hval (i : B) : Sum.map Subtype.val Subtype.val (c' i) = c i := by
    dsimp [c']
    split <;> rename_i x he <;> exact he.symm
  have hinj : Function.Injective c' := by
    intro i j he
    have he' : c i = c j := by rw [←hval i,←hval j,he]
    by_contra hij
    have hvalne : i.val.val ≠ j.val.val := by
      intro h
      apply hij
      exact Subtype.ext (Fin.ext h)
    exact charge_distinct hf hg hvalne (hc i) (by rw [he']; exact hc j)
  have hcard := Fintype.card_le_of_injective c' hinj
  simpa only [B, Fintype.card_subtype, Fintype.card_sum, Fintype.card_coe, X, Y,
    missing_card hf.injective hU, missing_card hg.injective hV] using hcard

end Matching
end EditCode

end OAI
