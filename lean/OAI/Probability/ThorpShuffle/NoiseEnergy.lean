import OAI.Probability.ThorpShuffle.HalfHistories

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def insertBit (d : ℕ) (i : Fin (d + 1)) (b : Bool) (x : Position d) : Position (d + 1) :=
  Fin.insertNth i b x

def halfPositionEquiv (d : ℕ) (i : Fin (d + 1)) : Bool × Position d ≃ Position (d + 1) :=
  Fin.insertNthEquiv (fun _ => Bool) i

@[simp] theorem halfPositionEquiv_apply (d : ℕ) (i : Fin (d + 1)) (p : Bool × Position d) :
    halfPositionEquiv d i p = insertBit d i p.1 p.2 := rfl

@[simp] theorem insertBit_zero (d : ℕ) (b : Bool) (x : Position d) :
    insertBit d 0 b x = Fin.cons b x := Fin.insertNth_zero' _ _

@[simp] theorem insertBit_last (d : ℕ) (b : Bool) (x : Position d) :
    insertBit d (Fin.last d) b x = Fin.snoc x b := Fin.insertNth_last' _ _

 theorem insertBit_cons (d : ℕ) (k : Fin (d + 1)) (h b : Bool) (x : Position d) :
    insertBit (d + 1) k.succ h (Fin.cons b x) = Fin.cons b (insertBit d k h x) := by
  change Fin.insertNth (α := fun _ => Bool) k.succ h (Fin.cons b x) = _
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [insertBit]
  · change Fin.cons b x = Fin.cons b (insertBit d k h x) ∘ k.succ.succAbove
    erw [Fin.cons_comp_succ_succAbove]
    simp [insertBit]

 theorem insertBit_snoc (d : ℕ) (k : Fin (d + 1)) (h b : Bool) (x : Position d) :
    insertBit (d + 1) k.castSucc h (Fin.snoc x b) = Fin.snoc (insertBit d k h x) b := by
  change Fin.insertNth (α := fun _ => Bool) k.castSucc h (Fin.snoc x b) = _
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [insertBit]
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Fin.removeNth, Fin.succAbove_ne_last_last, insertBit]
    · simp [Fin.removeNth, Fin.castSucc_succAbove_castSucc, insertBit]

 theorem physicalFree_snoc (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Position d → Bool) (x : Position d) (b : Bool) :
    physicalFree d B c (Fin.snoc x b) = B (Fin.cons (b ^^ c x) x) := by
  erw [← scatterPosition_eq_snoc, physicalFree_scatter]
  rfl

 theorem physicalFlow_snoc (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Position d → Bool) (x : Position d) (b : Bool) :
    physicalFlow d B w c (Fin.snoc x b) =
      if b then (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).2
      else (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).1 := by
  erw [← scatterPosition_eq_snoc, physicalFlow_scatter]
  rfl

@[ext] theorem RawState.ext {d : ℕ} {v u : RawState d}
    (hf : v.free = u.free) (hw : v.weight = u.weight) : v = u := by
  cases v; cases u; simp_all

def halfRaw (d : ℕ) (i : Fin (d + 1)) (h : Bool) (v : RawState (d + 1)) : RawState d where
  free x := v.free (insertBit d i h x)
  weight x := v.weight (insertBit d i h x)

theorem rawNext_half (d : ℕ) (k : Fin (d + 1)) (h : Bool)
    (v : RawState (d + 2)) (c : Position (d + 1) → Bool) :
    halfRaw (d + 1) k.castSucc h (rawNext (d + 1) v c) =
      rawNext d (halfRaw (d + 1) k.succ h v) (fun x => c (insertBit d k h x)) := by
  apply RawState.ext
  · funext x
    obtain ⟨⟨b, y⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (d + 1) => Bool)).surjective x
    change physicalFree (d + 1) v.free c (insertBit (d + 1) k.castSucc h (Fin.snoc y b)) =
      physicalFree d (fun z => v.free (insertBit (d + 1) k.succ h z))
        (fun z => c (insertBit d k h z)) (Fin.snoc y b)
    erw [insertBit_snoc, physicalFree_snoc, physicalFree_snoc, insertBit_cons]
  · funext x
    obtain ⟨⟨b, y⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (d + 1) => Bool)).surjective x
    change physicalFlow (d + 1) v.free v.weight c
      (insertBit (d + 1) k.castSucc h (Fin.snoc y b)) =
      physicalFlow d (fun z => v.free (insertBit (d + 1) k.succ h z))
        (fun z => v.weight (insertBit (d + 1) k.succ h z))
        (fun z => c (insertBit d k h z)) (Fin.snoc y b)
    erw [insertBit_snoc, physicalFlow_snoc, physicalFlow_snoc]
    simp only [insertBit_cons]

end Conditional

namespace Conditional

def halfMarker (d t : ℕ) : Fin (d + 2) := ⟨d + 1 - t, by omega⟩
def coinHalfMarker (d t : ℕ) : Fin (d + 1) := ⟨d - t, by omega⟩

@[simp] theorem halfMarker_zero (d : ℕ) : halfMarker d 0 = Fin.last (d + 1) := rfl
@[simp] theorem halfMarker_end (d : ℕ) : halfMarker d (d + 1) = 0 := by
  apply Fin.ext; simp [halfMarker]

theorem halfMarker_next (d t : ℕ) (ht : t ≤ d) :
    halfMarker d (t + 1) = (coinHalfMarker d t).castSucc := by
  apply Fin.ext; simp only [halfMarker, coinHalfMarker, Fin.val_castSucc]; omega

theorem halfMarker_previous (d t : ℕ) (ht : t ≤ d) :
    halfMarker d t = (coinHalfMarker d t).succ := by
  apply Fin.ext; simp only [halfMarker, coinHalfMarker, Fin.val_succ]; omega

def halfHistory (d t : ℕ) (h : Bool) (ω : History (d + 2) t) : History (d + 1) t :=
  fun i x => ω i (insertBit d (coinHalfMarker d i.val) h x)

@[simp] theorem halfHistory_snoc (d t : ℕ) (h : Bool)
    (ω : History (d + 2) t) (c : Coins (d + 2)) :
    halfHistory d (t + 1) h (Fin.snoc ω c) =
      Fin.snoc (halfHistory d t h ω) (fun x => c (insertBit d (coinHalfMarker d t) h x)) := by
  funext i x
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (Fin.snoc (α := fun _ => Coins (d + 2)) ω c (Fin.last t)) (insertBit d (coinHalfMarker d t) h x) =
      (Fin.snoc (α := fun _ => Coins (d + 1)) (halfHistory d t h ω)
        (fun z => c (insertBit d (coinHalfMarker d t) h z)) (Fin.last t)) x
    erw [Fin.snoc_last, Fin.snoc_last]
  · change (Fin.snoc (α := fun _ => Coins (d + 2)) ω c j.castSucc) (insertBit d (coinHalfMarker d j.val) h x) =
      (Fin.snoc (α := fun _ => Coins (d + 1)) (halfHistory d t h ω)
        (fun z => c (insertBit d (coinHalfMarker d t) h z)) j.castSucc) x
    erw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

theorem rawIterate_half (d t : ℕ) (ht : t ≤ d + 1) (h : Bool)
    (v : RawState (d + 2)) (ω : History (d + 2) t) :
    halfRaw (d + 1) (halfMarker d t) h (rawIterate (d + 1) v t ω) =
      rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) t (halfHistory d t h ω) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change halfRaw (d + 1) (halfMarker d (t + 1)) h
      (rawNext (d + 1) (rawIterate (d + 1) v t (fun i => ω i.castSucc)) (ω (Fin.last t))) = _
    erw [halfMarker_next d t (by omega), rawNext_half,
      ← halfMarker_previous d t (by omega), ih (by omega)]
    rfl

def splitHalfHistory (d t : ℕ) :
    History (d + 2) t ≃ History (d + 1) t × History (d + 1) t where
  toFun ω := (halfHistory d t false ω, halfHistory d t true ω)
  invFun p := fun i y =>
    if y (coinHalfMarker d i.val) then
      p.2 i (Fin.removeNth (coinHalfMarker d i.val) y)
    else p.1 i (Fin.removeNth (coinHalfMarker d i.val) y)
  left_inv ω := by
    funext i y
    obtain ⟨⟨h, x⟩, rfl⟩ := (halfPositionEquiv d (coinHalfMarker d i.val)).surjective y
    simp only [halfPositionEquiv_apply, insertBit, Fin.insertNth_apply_same,
      halfHistory, Fin.removeNth_insertNth]
    cases h <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext i x <;>
      simp [halfHistory, insertBit, Fin.insertNth_apply_same, Fin.removeNth_insertNth]

theorem mean_half_product (d t : ℕ) (f g : History (d + 1) t → ℝ) :
    mean (fun ω : History (d + 2) t => f (halfHistory d t false ω) *
      g (halfHistory d t true ω)) = mean f * mean g := by
  have he := mean_equiv (splitHalfHistory d t) (fun p => f p.1 * g p.2)
  change mean (fun ω : History (d + 2) t => f (halfHistory d t false ω) *
      g (halfHistory d t true ω)) = _ at he
  erw [he, mean_prod]
  simp_rw [mean_const_mul]
  exact mean_mul_const _ _

theorem mean_opposite_half_product (d t : ℕ) (h : Bool)
    (f g : History (d + 1) t → ℝ) :
    mean (fun ω : History (d + 2) t => f (halfHistory d t h ω) *
      g (halfHistory d t (!h) ω)) = mean f * mean g := by
  cases h
  · exact mean_half_product d t f g
  · simp only [Bool.not_true]
    simpa only [mul_comm] using mean_half_product d t g f

end Conditional

end Thorp

end

end OAI
