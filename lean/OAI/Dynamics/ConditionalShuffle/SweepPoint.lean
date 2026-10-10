import OAI.Dynamics.ConditionalShuffle.OverlayModel

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional

abbrev SweepHistory (d t : ℕ) := Fin t → Position d → Bool

lemma mean_function_snoc {Ω : Type*} [Fintype Ω] (t : ℕ)
    (f : (Fin (t+1) → Ω) → ℝ) :
    mean f = mean (fun ω : Fin t → Ω => mean (fun c : Ω => f (Fin.snoc ω c))) := by
  have h := mean_equiv (Fin.snocEquiv (fun _ : Fin (t+1) => Ω)) f
  rw [mean_prod] at h
  rw [← h, mean_comm]
  rfl

def Untouched (d t : ℕ) (tag y : Position (d+1)) : Prop :=
  ∀ (i : Fin (d+1)) (hi : t ≤ i.val), y ⟨i.val-t, by omega⟩ = tag i

lemma untouched_zero (d : ℕ) (tag : Position (d+1)) : Untouched d 0 tag tag := by
  intro i hi; rfl

lemma untouched_drop (d t : ℕ) (tag : Position (d+1)) (x : Position d) (a b : Bool)
    (h : Untouched d t tag (Fin.cons a x)) : Untouched d (t+1) tag (Fin.snoc x b) := by
  intro i hi
  have hj : i.val-t-1 < d := by omega
  have he : (⟨i.val-t, by omega⟩ : Fin (d+1)) = (⟨i.val-t-1,hj⟩ : Fin d).succ := by
    apply Fin.ext; simp; omega
  have he' : (⟨i.val-(t+1), by omega⟩ : Fin (d+1)) = (⟨i.val-t-1,hj⟩ : Fin d).castSucc := by
    apply Fin.ext; simp; omega
  rw [he', Fin.snoc_castSucc]
  have hh := h i (by omega)
  rw [he, Fin.cons_succ] at hh
  exact hh

lemma untouched_step (d t : ℕ) (tag x : Position (d+1)) (c : (Position d → Bool))
    (h : Untouched d t tag x) : Untouched d (t+1) tag (step (d+1) c x) := by
  obtain ⟨⟨b,y⟩, rfl⟩ := (splitPosition d).symm.surjective x
  change Untouched d (t+1) tag (step (d+1) c (Fin.cons b y))
  erw [step_cons, scatterPosition_eq_snoc]
  exact untouched_drop d t tag y b (b ^^ c y) h

lemma untouched_run (d t : ℕ) (tag : Position (d+1)) (ω : SweepHistory d t) :
    Untouched d t tag (run (d+1) t ω tag) := by
  induction t with
  | zero => erw [run_zero]; exact untouched_zero d tag
  | succ t ih =>
      erw [run_succ]
      exact untouched_step d t tag _ _ (ih (fun i => ω i.castSucc))

def rawPoint (d : ℕ) (B : Position d → Bool) (tag : Position d) : RawState d :=
  ⟨B, fun x => if x = tag then 1 else 0⟩

lemma rawPoint_support (d t : ℕ) (B : Position (d+1) → Bool) (tag y : Position (d+1))
    (ω : SweepHistory d t) (h : ¬ Untouched d t tag y) :
    (rawIterate d (rawPoint (d+1) B tag) t ω).weight y = 0 := by
  induction t generalizing y with
  | zero =>
      have hne : y ≠ tag := by intro hy; subst y; exact h (untouched_zero d tag)
      simp [rawIterate, rawPoint, hne]
  | succ t ih =>
      obtain ⟨⟨b,x⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (d+1) => Bool)).surjective y
      have hz (a : Bool) : (rawIterate d (rawPoint (d+1) B tag) t (Fin.init ω)).weight
          (Fin.cons a x) = 0 :=
        ih (Fin.cons a x) (Fin.init ω) (fun hh => h (untouched_drop d t tag x a b hh))
      change physicalFlow d _ _ (ω (Fin.last t)) (Fin.snoc x b) = 0
      erw [physicalFlow_snoc]
      erw [hz false, hz true]
      cases (rawIterate d (rawPoint (d+1) B tag) t (Fin.init ω)).free (Fin.cons false x) <;>
        cases (rawIterate d (rawPoint (d+1) B tag) t (Fin.init ω)).free (Fin.cons true x) <;>
        cases b <;> cases ω (Fin.last t) x <;> norm_num [pairUpdate]

def mate (d : ℕ) (x : Position (d+1)) : Position (d+1) :=
  Fin.cons (!(x 0)) (Fin.tail x)

@[simp] lemma mate_zero (d : ℕ) (x : Position (d+1)) : mate d x 0 = !(x 0) := rfl
@[simp] lemma mate_succ (d : ℕ) (x : Position (d+1)) (i : Fin d) :
    mate d x i.succ = x i.succ := rfl

lemma rawPoint_mate_zero (d t : ℕ) (ht : t < d+1) (B : Position (d+1) → Bool)
    (tag : Position (d+1)) (ω : SweepHistory d t) :
    (rawIterate d (rawPoint (d+1) B tag) t ω).weight (mate d (run (d+1) t ω tag)) = 0 := by
  apply rawPoint_support
  intro h
  have hh := h ⟨t,ht⟩ (Nat.le_refl t)
  have hh' := untouched_run d t tag ω ⟨t,ht⟩ (Nat.le_refl t)
  simp only [Nat.sub_self] at hh hh'
  change (!(run (d+1) t ω tag 0)) = tag ⟨t,ht⟩ at hh
  change run (d+1) t ω tag 0 = tag ⟨t,ht⟩ at hh'
  rw [hh'] at hh
  cases he : tag ⟨t,ht⟩ <;> simp_all

def partnerIndex (d t : ℕ) (tag : Position (d+1)) (ω : SweepHistory d t) : Position (d+1) :=
  (run (d+1) t ω).symm (mate d (run (d+1) t ω tag))

lemma partnerIndex_bit (d t : ℕ) (ht : t < d+1) (tag : Position (d+1))
    (ω : SweepHistory d t) : partnerIndex d t tag ω ⟨t,ht⟩ = !(tag ⟨t,ht⟩) := by
  have hh := untouched_run d t (partnerIndex d t tag ω) ω ⟨t,ht⟩ (Nat.le_refl t)
  have hh' := untouched_run d t tag ω ⟨t,ht⟩ (Nat.le_refl t)
  simp only [partnerIndex, Equiv.apply_symm_apply, Nat.sub_self] at hh
  change (!(run (d+1) t ω tag 0)) = _ at hh
  simp only [Nat.sub_self] at hh'
  change run (d+1) t ω tag 0 = _ at hh'
  rw [hh'] at hh
  exact hh.symm

lemma partnerIndex_later (d t : ℕ) (tag : Position (d+1)) (ω : SweepHistory d t)
    (i : Fin (d+1)) (hi : t < i.val) : partnerIndex d t tag ω i = tag i := by
  have hh := untouched_run d t (partnerIndex d t tag ω) ω i (by omega)
  have hh' := untouched_run d t tag ω i (by omega)
  simp only [partnerIndex, Equiv.apply_symm_apply] at hh
  have hj : i.val-t-1 < d := by omega
  have he : (⟨i.val-t, by omega⟩ : Fin (d+1)) = (⟨i.val-t-1,hj⟩ : Fin d).succ := by
    apply Fin.ext; simp; omega
  rw [he, mate_succ] at hh
  rw [he] at hh'
  exact hh.symm.trans hh'

lemma partnerIndex_ne (d t : ℕ) (ht : t < d+1) (tag : Position (d+1))
    (ω : SweepHistory d t) : partnerIndex d t tag ω ≠ tag := by
  intro h
  have hh := partnerIndex_bit d t ht tag ω
  rw [h] at hh
  cases he : tag ⟨t,ht⟩ <;> simp_all

lemma partnerIndex_distinct (d s t : ℕ) (hst : s < t) (ht : t < d+1)
    (tag : Position (d+1)) (a : SweepHistory d s) (b : SweepHistory d t) :
    partnerIndex d s tag a ≠ partnerIndex d t tag b := by
  intro h
  have hh := partnerIndex_later d s tag a ⟨t,ht⟩ hst
  rw [h, partnerIndex_bit d t ht tag b] at hh
  cases he : tag ⟨t,ht⟩ <;> simp_all

lemma physicalFlow_at_tag (d : ℕ) (B : Position (d+1) → Bool)
    (w : Position (d+1) → ℝ) (x : Position (d+1)) (c : (Position d → Bool))
    (hx : B x = true) (hz : w (mate d x) = 0) :
    physicalFlow d B w c (step (d+1) c x) =
      w x * (if B (mate d x) then (1/2 : ℝ) else 1) := by
  obtain ⟨⟨b,y⟩, rfl⟩ := (splitPosition d).symm.surjective x
  change B (Fin.cons b y) = true at hx
  change w (Fin.cons (!b) y) = 0 at hz
  change physicalFlow d B w c (step (d+1) c (Fin.cons b y)) =
    w (Fin.cons b y) * (if B (Fin.cons (!b) y) then (1/2 : ℝ) else 1)
  erw [step_cons, scatterPosition_eq_snoc, physicalFlow_snoc]
  cases b <;> cases h0 : B (Fin.cons false y) <;> cases h1 : B (Fin.cons true y) <;>
    cases hc : c y <;> simp_all [pairUpdate] <;> ring

lemma rawNext_masked (d : ℕ) (v : RawState (d+1)) (c r : (Position d → Bool)) :
    rawNext d v (maskedCoin (freePairMask d v.free) c r) = rawNext d v c := by
  apply RawState.ext
  · funext z
    obtain ⟨⟨b,x⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (d+1) => Bool)).surjective z
    change physicalFree d v.free _ (Fin.snoc x b) = physicalFree d v.free c (Fin.snoc x b)
    erw [physicalFree_snoc, physicalFree_snoc]
    cases h0 : v.free (Fin.cons false x) <;> cases h1 : v.free (Fin.cons true x) <;>
      cases b <;> cases hc : c x <;> cases hr : r x <;>
      simp [maskedCoin, freePairMask, h0, h1, hc, hr]
  · funext z
    obtain ⟨⟨b,x⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (d+1) => Bool)).surjective z
    change physicalFlow d v.free v.weight _ (Fin.snoc x b) =
      physicalFlow d v.free v.weight c (Fin.snoc x b)
    erw [physicalFlow_snoc, physicalFlow_snoc]
    cases h0 : v.free (Fin.cons false x) <;> cases h1 : v.free (Fin.cons true x) <;>
      cases b <;> cases hc : c x <;> cases hr : r x <;>
      simp [maskedCoin, freePairMask, pairUpdate, h0, h1, hc]

lemma rawNext_joint (d : ℕ) (v : RawState (d+1))
    (F : RawState (d+1) → Position (d+1) → ℝ) :
    mean (fun c : Position d → Bool => ∑ y, (rawNext d v c).weight y * F (rawNext d v c) y) =
      mean (fun c : Position d → Bool => ∑ x, v.weight x * F (rawNext d v c) (step (d+1) c x)) := by
  calc
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ y, v.weight ((step (d+1) (maskedCoin (freePairMask d v.free) c r)).symm y) *
          F (rawNext d v c) y)) := by
      apply mean_congr; intro c
      rw [mean_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [mean_mul_const, ← physicalFlow_resampling]
      rfl
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ x, v.weight x * F (rawNext d v c)
          (step (d+1) (maskedCoin (freePairMask d v.free) c r) x))) := by
      apply mean_congr; intro c
      apply mean_congr; intro r
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp (step (d+1) (maskedCoin (freePairMask d v.free) c r))
          (fun y => v.weight ((step (d+1) (maskedCoin (freePairMask d v.free) c r)).symm y) *
            F (rawNext d v c) y)).symm
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ x, v.weight x * F (rawNext d v (maskedCoin (freePairMask d v.free) c r))
          (step (d+1) (maskedCoin (freePairMask d v.free) c r) x))) := by
      simp only [rawNext_masked]
    _ = _ := mean_maskedCoin (freePairMask d v.free)
      (fun c : Position d → Bool => ∑ x, v.weight x * F (rawNext d v c) (step (d+1) c x))

lemma rawIterate_joint (d : ℕ) (v : RawState (d+1)) (t : ℕ)
    (F : RawState (d+1) → Position (d+1) → ℝ) :
    mean (fun ω : SweepHistory d t => ∑ x, v.weight x *
      F (rawIterate d v t ω) (run (d+1) t ω x)) =
      mean (fun ω : SweepHistory d t => ∑ y, (rawIterate d v t ω).weight y *
        F (rawIterate d v t ω) y) := by
  induction t generalizing F with
  | zero => simp only [rawIterate]; rfl
  | succ t ih =>
    let G (v' : RawState (d+1)) (x : Position (d+1)) : ℝ :=
      mean (fun c : (Position d → Bool) => F (rawNext d v' c) (step (d+1) c x))
    have hl : mean (fun ω : SweepHistory d (t+1) => ∑ x, v.weight x *
        F (rawIterate d v (t+1) ω) (run (d+1) (t+1) ω x)) =
        mean (fun ω : SweepHistory d t => ∑ x, v.weight x *
          G (rawIterate d v t ω) (run (d+1) t ω x)) := by
      rw [mean_function_snoc]
      apply mean_congr; intro ω
      have hp (c : Position d → Bool) :
          (∑ x, v.weight x * F (rawIterate d v (t+1) (Fin.snoc ω c))
            (run (d+1) (t+1) (Fin.snoc ω c) x)) =
          ∑ x, v.weight x * F (rawNext d (rawIterate d v t ω) c)
            (step (d+1) c (run (d+1) t ω x)) := by
        erw [rawIterate_snoc, run_snoc]
        rfl
      trans mean (fun c : Position d → Bool => ∑ x, v.weight x *
        F (rawNext d (rawIterate d v t ω) c) (step (d+1) c (run (d+1) t ω x)))
      · exact mean_congr hp
      · rw [mean_sum]
        simp_rw [mean_const_mul]
        rfl
    have hr : mean (fun ω : SweepHistory d (t+1) => ∑ y,
        (rawIterate d v (t+1) ω).weight y * F (rawIterate d v (t+1) ω) y) =
        mean (fun ω : SweepHistory d t => ∑ x, (rawIterate d v t ω).weight x *
          G (rawIterate d v t ω) x) := by
      rw [mean_function_snoc]
      apply mean_congr; intro ω
      have hp (c : Position d → Bool) :
          (∑ y, (rawIterate d v (t+1) (Fin.snoc ω c)).weight y *
            F (rawIterate d v (t+1) (Fin.snoc ω c)) y) =
          ∑ y, (rawNext d (rawIterate d v t ω) c).weight y *
            F (rawNext d (rawIterate d v t ω) c) y := by
        erw [rawIterate_snoc]
      trans mean (fun c : Position d → Bool => ∑ y, (rawNext d (rawIterate d v t ω) c).weight y *
        F (rawNext d (rawIterate d v t ω) c) y)
      · exact mean_congr hp
      · erw [rawNext_joint, mean_sum]
        simp_rw [mean_const_mul]
        rfl
    exact hl.trans ((ih G).trans hr.symm)

lemma rawPoint_energy_identity (d t : ℕ) (B : Position (d+1) → Bool)
    (tag : Position (d+1)) :
    mean (fun ω : SweepHistory d t => rawEnergy (rawIterate d (rawPoint (d+1) B tag) t ω)) =
      mean (fun ω : SweepHistory d t =>
        (rawIterate d (rawPoint (d+1) B tag) t ω).weight (run (d+1) t ω tag)) := by
  have hh := rawIterate_joint d (rawPoint (d+1) B tag) t (fun v y => v.weight y)
  simpa [rawPoint, rawEnergy, sq] using hh.symm

def encounterList (d t : ℕ) (tag : Position (d+1)) (ω : SweepHistory d t)
    (i : Fin t) : Position (d+1) :=
  partnerIndex d i.val tag (fun j => ω ⟨j.val, by omega⟩)

@[simp] lemma encounterList_snoc_castSucc (d t : ℕ) (tag : Position (d+1))
    (ω : SweepHistory d t) (c : (Position d → Bool)) (i : Fin t) :
    encounterList d (t+1) tag (Fin.snoc ω c) i.castSucc = encounterList d t tag ω i := by
  unfold encounterList
  congr 1
  funext j
  change (Fin.snoc (α := fun _ : Fin (t+1) => Position d → Bool) ω c) (⟨j.val, by omega⟩ : Fin t).castSucc = _
  simp only [Fin.snoc_castSucc]

@[simp] lemma encounterList_snoc_last (d t : ℕ) (tag : Position (d+1))
    (ω : SweepHistory d t) (c : (Position d → Bool)) :
    encounterList d (t+1) tag (Fin.snoc ω c) (Fin.last t) = partnerIndex d t tag ω := by
  unfold encounterList
  congr 1
  funext j
  change (Fin.snoc (α := fun _ : Fin (t+1) => Position d → Bool) ω c) j.castSucc = _
  simp only [Fin.snoc_castSucc]

lemma encounterList_injective (d t : ℕ) (ht : t ≤ d+1) (tag : Position (d+1))
    (ω : SweepHistory d t) : Function.Injective (encounterList d t tag ω) := by
  intro i j h
  by_contra hij
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hh | hh
  · exact partnerIndex_distinct d _ _ hh (by omega) tag _ _ h
  · exact partnerIndex_distinct d _ _ hh (by omega) tag _ _ h.symm

lemma encounterList_ne (d t : ℕ) (ht : t ≤ d+1) (tag : Position (d+1))
    (ω : SweepHistory d t) (i : Fin t) : encounterList d t tag ω i ≠ tag :=
  partnerIndex_ne d _ (by omega) tag _

lemma rawPoint_tag_product (d t : ℕ) (ht : t ≤ d+1) (B : Position (d+1) → Bool)
    (tag : Position (d+1)) (hb : B tag = true) (ω : SweepHistory d t) :
    (rawIterate d (rawPoint (d+1) B tag) t ω).weight (run (d+1) t ω tag) =
      ∏ i : Fin t, (if B (encounterList d t tag ω i) then (1/2 : ℝ) else 1) := by
  induction t with
  | zero => erw [run_zero]; simp [rawIterate, rawPoint]
  | succ t ih =>
    obtain ⟨⟨c,ω⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (t+1) => (Position d → Bool))).surjective ω
    change (rawIterate d (rawPoint (d+1) B tag) (t+1) (Fin.snoc ω c)).weight
      (run (d+1) (t+1) (Fin.snoc ω c) tag) = _
    erw [rawIterate_snoc, run_snoc]
    change physicalFlow d _ _ c (step (d+1) c (run (d+1) t ω tag)) = _
    rw [physicalFlow_at_tag d _ _ _ c
      (by erw [rawIterate_free]; simpa [rawPoint] using hb)
      (rawPoint_mate_zero d t (by omega) B tag ω)]
    erw [ih (by omega) ω, rawIterate_free]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, rawPoint, Fin.prod_univ_castSucc, encounterList_snoc_castSucc,
      encounterList_snoc_last]
    rfl

end Thorp.Conditional

end

end OAI
