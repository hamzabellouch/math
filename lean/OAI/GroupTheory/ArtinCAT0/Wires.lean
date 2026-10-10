import OAI.GroupTheory.ArtinCAT0.Mirrors

namespace OAI

namespace ArtinCAT0

structure WireSystem (D : Type*) where
  mate : D → D
  mate_inv : Function.Involutive mate
  mate_ne : ∀ d, mate d ≠ d
  pass : D → D
  pass_inv : Function.Involutive pass

namespace WireSystem
variable {D : Type*} (W : WireSystem D)

@[simp] lemma mate_mate (d : D) : W.mate (W.mate d) = d := W.mate_inv d
@[simp] lemma pass_pass (d : D) : W.pass (W.pass d) = d := W.pass_inv d
abbrev Live := {d : D // W.pass d = d}

structure Cut where
  p : D
  moving : W.pass p ≠ p

namespace Cut
variable {W} (K : W.Cut)
abbrev q := W.pass K.p

def Removed (d : D) : Prop := d = K.p ∨ d = K.q
abbrev Kept := {d : D // ¬ K.Removed d}

lemma removed_pass (d : D) : K.Removed (W.pass d) ↔ K.Removed d := by
  constructor <;> intro h <;> rcases h with h | h
  · right
    have := congrArg W.pass h
    simpa using this
  · left
    have := congrArg W.pass h
    simpa using this
  · right
    have := congrArg W.pass h
    simpa using this
  · left
    subst d
    simp [q]

lemma pass_ne (d : D) (hd : K.Removed d) : W.pass d ≠ d := by
  rcases hd with rfl | rfl
  · exact K.moving
  · simpa [q] using K.moving.symm

lemma internal (d : D) (hd : K.Removed d) (hm : K.Removed (W.mate d)) :
    W.mate d = W.pass d := by
  rcases hd with rfl | rfl
  · rcases hm with h | h
    · exact (W.mate_ne K.p h).elim
    · exact h
  · rcases hm with h | h
    · simpa [q] using h
    · exact (W.mate_ne K.q h).elim

lemma mate_pass_outside (d : D) (hd : K.Removed d) (hm : ¬ K.Removed (W.mate d)) :
    ¬ K.Removed (W.mate (W.pass d)) := by
  intro hh
  have h := K.internal (W.pass d) ((K.removed_pass d).2 hd) hh
  simp only [W.pass_pass] at h
  have he := congrArg W.mate h
  simp only [W.mate_mate] at he
  exact hm (he ▸ (K.removed_pass d).2 hd)

noncomputable def splice (d : D) : D := by
  classical
  exact if K.Removed (W.mate d) then W.mate (W.pass (W.mate d)) else W.mate d

lemma splice_inside (d : D) (h : K.Removed (W.mate d)) :
    K.splice d = W.mate (W.pass (W.mate d)) := by simp [splice, h]
lemma splice_outside (d : D) (h : ¬ K.Removed (W.mate d)) :
    K.splice d = W.mate d := by simp [splice, h]

lemma splice_kept (d : D) (hd : ¬ K.Removed d) : ¬ K.Removed (K.splice d) := by
  by_cases hm : K.Removed (W.mate d)
  · rw [K.splice_inside d hm]
    exact K.mate_pass_outside (W.mate d) hm (by simpa using hd)
  · rw [K.splice_outside d hm]
    exact hm

lemma splice_splice (d : D) (hd : ¬ K.Removed d) : K.splice (K.splice d) = d := by
  by_cases hm : K.Removed (W.mate d)
  · rw [K.splice_inside d hm]
    rw [K.splice_inside _ (by simpa using (K.removed_pass (W.mate d)).2 hm)]
    simp
  · rw [K.splice_outside d hm]
    rw [K.splice_outside _ (by simpa using hd)]
    simp

lemma splice_ne (d : D) : K.splice d ≠ d := by
  by_cases hm : K.Removed (W.mate d)
  · rw [K.splice_inside d hm]
    intro h
    have he := congrArg W.mate h
    simp only [W.mate_mate] at he
    exact K.pass_ne (W.mate d) hm he
  · rw [K.splice_outside d hm]
    exact W.mate_ne d

noncomputable def reduced : WireSystem K.Kept where
  mate d := ⟨K.splice d, K.splice_kept d d.property⟩
  mate_inv d := Subtype.ext (K.splice_splice d d.property)
  mate_ne d h := K.splice_ne d (congrArg Subtype.val h)
  pass d := ⟨W.pass d, fun h => d.property ((K.removed_pass d).1 h)⟩
  pass_inv d := Subtype.ext (W.pass_pass d)

lemma live_kept (d : W.Live) : ¬ K.Removed d.val := by
  intro hd
  exact K.pass_ne d hd d.property

def liveEquiv : K.reduced.Live ≃ W.Live where
  toFun d := ⟨d.val.val, congrArg Subtype.val d.property⟩
  invFun d := ⟨⟨d.val,K.live_kept d⟩, Subtype.ext d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def extend (w : K.Kept → ℝ) (d : D) : ℝ := by
  classical
  exact if hd : K.Removed d then
    if hm : K.Removed (W.mate d) then 0 else -w ⟨W.mate d, hm⟩
    else w ⟨d,hd⟩

lemma extend_kept (w : K.Kept → ℝ) (d : K.Kept) : K.extend w d = w d := by
  simp [extend, d.property]

lemma extend_pass_removed (w : K.Kept → ℝ)
    (ha : ∀ d, w (K.reduced.mate d) = -w d) (d : D) (hd : K.Removed d) :
    K.extend w (W.pass d) = -K.extend w d := by
  by_cases hm : K.Removed (W.mate d)
  · have he := K.internal d hd hm
    have he' : W.mate (W.pass d) = d := by rw [← he, W.mate_mate]
    simp [extend, hd, hm, (K.removed_pass d).2 hd, he']
  · have hm' := K.mate_pass_outside d hd hm
    have he : K.reduced.mate ⟨W.mate d,hm⟩ = ⟨W.mate (W.pass d),hm'⟩ := by
      apply Subtype.ext
      change K.splice (W.mate d) = _
      rw [K.splice_inside _ (by simpa using hd), W.mate_mate]
    have hh := ha ⟨W.mate d,hm⟩
    rw [he] at hh
    simp only [extend, dite_eq_left hd, dite_eq_left ((K.removed_pass d).2 hd), dite_eq_right hm,
      dite_eq_right hm', hh, neg_neg]

lemma extend_mate (w : K.Kept → ℝ)
    (ha : ∀ d, w (K.reduced.mate d) = -w d) (d : D) :
    K.extend w (W.mate d) = -K.extend w d := by
  by_cases hd : K.Removed d
  · by_cases hm : K.Removed (W.mate d)
    · simp [extend, hd, hm]
    · simp [extend, hd, hm]
  · by_cases hm : K.Removed (W.mate d)
    · simp [extend, hd, hm]
    · have he : K.reduced.mate ⟨d,hd⟩ = ⟨W.mate d,hm⟩ := by
        exact Subtype.ext (K.splice_outside d hm)
      simpa [extend, hd, hm, he] using ha ⟨d,hd⟩

lemma extend_pass (w : K.Kept → ℝ)
    (ha : ∀ d, w (K.reduced.mate d) = -w d)
    (hb : ∀ d, K.reduced.pass d ≠ d → w (K.reduced.pass d) = -w d)
    (d : D) (hd : W.pass d ≠ d) : K.extend w (W.pass d) = -K.extend w d := by
  by_cases hr : K.Removed d
  · exact K.extend_pass_removed w ha d hr
  · have hr' : ¬ K.Removed (W.pass d) := fun h => hr ((K.removed_pass d).1 h)
    have hb' := hb ⟨d,hr⟩ (fun he => hd (congrArg Subtype.val he))
    simpa [extend, hr, hr', reduced] using hb'

lemma reduced_color {C : Type*} (r : C → C) (hr : Function.Involutive r) (c : D → C)
    (ha : ∀ d, c (W.mate d) = r (c d))
    (hb : ∀ d, W.pass d ≠ d → c (W.pass d) = r (c d)) :
    ∀ d : K.Kept, c (K.reduced.mate d).val = r (c d.val) := by
  intro d
  change c (K.splice d.val) = _
  by_cases hm : K.Removed (W.mate d.val)
  · rw [K.splice_inside _ hm, ha, hb _ (K.pass_ne _ hm), ha, hr]
  · rw [K.splice_outside _ hm, ha]

end Cut

/-- The bivalent parts of a finite graph can be suppressed. In addition to its
boundary matching we retain extension of every antisymmetric edge weight. -/
structure Resolution where
  mate : W.Live → W.Live
  mate_inv : Function.Involutive mate
  mate_ne : ∀ d, mate d ≠ d
  lift : ∀ w : W.Live → ℝ, (∀ d, w (mate d) = -w d) →
    ∃ v : D → ℝ, (∀ d : W.Live, v d.val = w d) ∧
      (∀ d, v (W.mate d) = -v d) ∧
      ∀ d, W.pass d ≠ d → v (W.pass d) = -v d

namespace Resolution
variable {W}

noncomputable def expand (K : W.Cut) (R : K.reduced.Resolution) : W.Resolution where
  mate d := K.liveEquiv (R.mate (K.liveEquiv.symm d))
  mate_inv d := by
    simp only [Equiv.symm_apply_apply]
    rw [R.mate_inv, Equiv.apply_symm_apply]
  mate_ne d h := R.mate_ne (K.liveEquiv.symm d) (by simpa using congrArg K.liveEquiv.symm h)
  lift w hw := by
    let w' : K.reduced.Live → ℝ := fun d => w (K.liveEquiv d)
    have hw' : ∀ d, w' (R.mate d) = -w' d := by
      intro d
      simpa only [w', Equiv.symm_apply_apply] using hw (K.liveEquiv d)
    obtain ⟨v,hv,ha,hb⟩ := R.lift w' hw'
    refine ⟨K.extend v, ?_, K.extend_mate v ha, K.extend_pass v ha hb⟩
    intro d
    have hh := hv (K.liveEquiv.symm d)
    change v ⟨d.val,K.live_kept d⟩ = w' (K.liveEquiv.symm d) at hh
    rw [show K.extend v d.val = v ⟨d.val,K.live_kept d⟩ from K.extend_kept v ⟨d.val,_⟩]
    simpa [w'] using hh

lemma expand_color (K : W.Cut) (R : K.reduced.Resolution)
    {C : Type*} (r : C → C) (c : D → C)
    (hc : ∀ d, c (R.mate d).val.val = r (c d.val.val)) :
    ∀ d, c ((R.expand K).mate d).val = r (c d.val) := by
  intro d
  exact hc (K.liveEquiv.symm d)

noncomputable def of_all_live (h : ∀ d, W.pass d = d) : W.Resolution where
  mate d := ⟨W.mate d.val,h _⟩
  mate_inv d := Subtype.ext (W.mate_mate d.val)
  mate_ne d hd := W.mate_ne d.val (congrArg Subtype.val hd)
  lift w hw := by
    refine ⟨fun d => w ⟨d,h d⟩, fun _ => rfl, fun d => ?_, fun d hd => (hd (h d)).elim⟩
    exact hw ⟨d,h d⟩

end Resolution

universe u

/-- Suppression of all bivalent vertices of a finite matching graph, with
reversal-compatible labels and a cocycle lifting property. A closed component
without live ends receives zero in the lift. -/
theorem resolve {C : Type*} (r : C → C) (hr : Function.Involutive r) :
    ∀ (D : Type u) [Fintype D] (W : WireSystem D) (c : D → C),
      (∀ d, c (W.mate d) = r (c d)) →
      (∀ d, W.pass d ≠ d → c (W.pass d) = r (c d)) →
      ∃ R : W.Resolution, ∀ d, c (R.mate d).val = r (c d.val) := by
  suffices hh : ∀ n : ℕ, ∀ (D : Type u) [Fintype D] (W : WireSystem D) (c : D → C),
      Fintype.card D = n →
      (∀ d, c (W.mate d) = r (c d)) →
      (∀ d, W.pass d ≠ d → c (W.pass d) = r (c d)) →
      ∃ R : W.Resolution, ∀ d, c (R.mate d).val = r (c d.val) by
    intro D _ W c ha hb
    exact hh (Fintype.card D) D W c rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    intro D _ W c hn ha hb
    by_cases hp : ∀ d, W.pass d = d
    · refine ⟨Resolution.of_all_live hp, ?_⟩
      intro d
      exact ha d.val
    push Not at hp
    obtain ⟨p,hp⟩ := hp
    let K : W.Cut := ⟨p,hp⟩
    have hcard : Fintype.card K.Kept < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (fun h => h (Or.inl rfl) : ¬ (¬ K.Removed p))
    obtain ⟨R,hR⟩ := ih (Fintype.card K.Kept) hcard K.Kept K.reduced
      (fun d => c d.val) rfl (K.reduced_color r hr c ha hb)
      (fun d hd => hb d.val (fun h => hd (Subtype.ext h)))
    exact ⟨R.expand K, R.expand_color K r c hR⟩

end WireSystem
end ArtinCAT0

end OAI
