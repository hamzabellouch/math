import Mathlib
import OAI.Computability.MinUncut.Estimates.SingleRow
import OAI.Computability.MinUncut.Games.JointInner

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open scoped BigOperators
open OuterSmoothness
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

abbrev Away (x : A) := {a : A // a ≠ x}

lemma card_away (x : A) : Fintype.card (Away x) = Fintype.card A - 1 := by
  simpa only [Away, Fintype.card_unique] using Fintype.card_subtype_compl (fun a : A => a=x)

def pointedSet (x : A) {k : ℕ} (H : FixedSets (Away x) k) : Finset A :=
  insert x (H.val.map ⟨Subtype.val, Subtype.val_injective⟩)

lemma mem_pointedSet_self (x : A) {k : ℕ} (H : FixedSets (Away x) k) : x ∈ pointedSet x H := by
  simp [pointedSet]

lemma mem_pointedSet {x a : A} (h : a ≠ x) {k : ℕ} (H : FixedSets (Away x) k) :
    a ∈ pointedSet x H ↔ (⟨a,h⟩ : Away x) ∈ H.val := by
  simp only [pointedSet, Finset.mem_insert, h, false_or, Finset.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    have : b=⟨a,h⟩ := Subtype.ext he
    simpa [this] using hb
  · intro ha
    exact ⟨⟨a,h⟩,ha,rfl⟩

lemma pointedSet_card (x : A) {k : ℕ} (H : FixedSets (Away x) k) :
    (pointedSet x H).card = k+1 := by
  have hx : x ∉ H.val.map ⟨Subtype.val, Subtype.val_injective⟩ := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro a _ h
    exact a.property h
  simp [pointedSet, hx, H.property]

lemma pointed_membership {x a : A} (ha : a ≠ x) {k : ℕ}
    (hk : k ≤ Fintype.card A-1) :
    (𝔼 H : FixedSets (Away x) k, if a ∈ pointedSet x H then (1:ℝ) else 0) =
      (k:ℝ)/(Fintype.card A-1) := by
  have : Nonempty (Away x) := ⟨⟨a,ha⟩⟩
  simp_rw [mem_pointedSet ha]
  rw [membership_probability (by simpa [card_away] using hk), card_away]
  have hc : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [Nat.cast_sub hc, Nat.cast_one]

lemma expect_coordinate {B : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)]
    (i : ι) (f : B i → ℝ) : (𝔼 x : ∀ j, B j, f (x i)) = 𝔼 b, f b := by
  calc
    _ = 𝔼 p : B i × (∀ j : {j // j ≠ i}, B j), f p.1 := by
      apply Fintype.expect_equiv (Equiv.piSplitAt i B)
      intro x
      rfl
    _ = _ := by rw [expect_pair]; simp

abbrev PointedBox (x : ι → A) (k : ℕ) := ∀ i, FixedSets (Away (x i)) k

def InBox {x : ι → A} {k : ℕ} (H : PointedBox x k) (u : ι → A) : Prop :=
  ∀ i, u i ∈ pointedSet (x i) (H i)

omit [Fintype ι] [DecidableEq ι] in
lemma point_mem (x : ι → A) {k : ℕ} (H : PointedBox x k) : InBox H x :=
  fun _ => mem_pointedSet_self _ _

lemma other_point_probability {x u : ι → A} (hu : u ≠ x) {k : ℕ}
    (hk : k ≤ Fintype.card A-1) :
    (𝔼 H : PointedBox x k, if InBox H u then (1:ℝ) else 0) ≤
      (k:ℝ)/(Fintype.card A-1) := by
  classical
  have (i : ι) : Nonempty (FixedSets (Away (x i)) k) :=
    fixedSets_nonempty (by simpa [card_away] using hk)
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
  calc
    _ ≤ 𝔼 H : PointedBox x k, if u i ∈ pointedSet (x i) (H i) then (1:ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro H _
      by_cases h : InBox H u
      · simp [h, h i]
      · simp only [h, ite_false]; positivity
    _ = _ := by
      rw [expect_coordinate (B := fun i => FixedSets (Away (x i)) k) i (fun H : FixedSets (Away (x i)) k => if u i ∈ pointedSet (x i) H then (1:ℝ) else 0), pointed_membership hi hk]

def FaceInBox {x : ι → A} {k : ℕ} (H : PointedBox x k) (i : ι)
    (u : {j : ι // j ≠ i} → A) : Prop := ∀ j : {j : ι // j ≠ i}, u j ∈ pointedSet (x j.val) (H j.val)

lemma other_face_probability (i : ι) {x : ι → A} (u : {j : ι // j ≠ i} → A)
    (hu : u ≠ fun j : {j : ι // j ≠ i} => x j.val) {k : ℕ} (hk : k ≤ Fintype.card A-1) :
    (𝔼 H : PointedBox x k, if FaceInBox H i u then (1:ℝ) else 0) ≤
      (k:ℝ)/(Fintype.card A-1) := by
  classical
  have (j : ι) : Nonempty (FixedSets (Away (x j)) k) :=
    fixedSets_nonempty (by simpa [card_away] using hk)
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hu
  calc
    _ ≤ 𝔼 H : PointedBox x k, if u j ∈ pointedSet (x j.val) (H j.val) then (1:ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro H _
      by_cases h : FaceInBox H i u
      · simp [h, h j]
      · simp only [h, ite_false]; positivity
    _ = _ := by
      rw [expect_coordinate (B := fun i => FixedSets (Away (x i)) k) j.val (fun H : FixedSets (Away (x j.val)) k => if u j ∈ pointedSet (x j.val) H then (1:ℝ) else 0), pointed_membership hj hk]
lemma exists_indicator_le {T : Type*} (s : Finset T) (p : T → Prop) :
    (if ∃ t ∈ s, p t then (1:ℝ) else 0) ≤ ∑ t ∈ s, if p t then 1 else 0 := by
  classical
  by_cases h : ∃ t ∈ s, p t
  · obtain ⟨t,ht,hp⟩ := h
    have hb := Finset.single_le_sum (s := s) (f := fun t => if p t then (1:ℝ) else 0)
      (fun _ _ => by positivity) ht
    simpa [hp, show ∃ t ∈ s, p t from ⟨t,ht,hp⟩] using hb
  · simp only [h, ite_false]
    exact Finset.sum_nonneg (fun _ _ => by positivity)

abbrev Row (ι A : Type*) := Σ i : ι, ({j : ι // j ≠ i} → A)

def Removed {x : ι → A} {k : ℕ} (H : PointedBox x k)
    (P : Finset (ι → A)) (S : Finset (Row ι A)) : Prop :=
  (∃ u ∈ P, u ≠ x ∧ InBox H u) ∨
    (∃ r ∈ S, r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2)

lemma removal_probability [Nonempty A] {x : ι → A} {k : ℕ} (hk : k ≤ Fintype.card A-1)
    (P : Finset (ι → A)) (S : Finset (Row ι A)) :
    (𝔼 H : PointedBox x k, if Removed H P S then (1:ℝ) else 0) ≤
      (P.card+S.card)*((k:ℝ)/(Fintype.card A-1)) := by
  classical
  have (j : ι) : Nonempty (FixedSets (Away (x j)) k) :=
    fixedSets_nonempty (by simpa [card_away] using hk)
  have hprob : 0 ≤ (k:ℝ)/(Fintype.card A-1) := by
    have hc : 1 ≤ Fintype.card A := Fintype.card_pos
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hc))
  have hp (u : ι → A) :
      (𝔼 H : PointedBox x k, if u ≠ x ∧ InBox H u then (1:ℝ) else 0) ≤
        (k:ℝ)/(Fintype.card A-1) := by
    by_cases hu : u=x
    · simp [hu]; exact hprob
    · simpa only [ne_eq, hu, not_false_eq_true, true_and] using other_point_probability hu hk
  have hs (r : Row ι A) :
      (𝔼 H : PointedBox x k, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0) ≤
        (k:ℝ)/(Fintype.card A-1) := by
    by_cases hr : r.2=(fun j => x j.val)
    · simp [hr]; exact hprob
    · simpa only [ne_eq, hr, not_false_eq_true, true_and] using other_face_probability r.1 r.2 hr hk
  calc
    _ ≤ (𝔼 H : PointedBox x k,
        ((∑ u ∈ P, if u ≠ x ∧ InBox H u then (1:ℝ) else 0) +
        (∑ r ∈ S, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0))) := by
      apply Finset.expect_le_expect
      intro H _
      have hp0 : 0 ≤ ∑ u ∈ P, if u ≠ x ∧ InBox H u then (1:ℝ) else 0 :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have hs0 : 0 ≤ ∑ r ∈ S, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0 :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      by_cases hh : Removed H P S
      · rw [ite_eq_left hh]
        rcases hh with ⟨u,hu,hux,huH⟩ | ⟨r,hr,hrx,hrH⟩
        · have h := Finset.single_le_sum (s := P)
            (f := fun u => if u ≠ x ∧ InBox H u then (1:ℝ) else 0) (fun _ _ => by positivity) hu
          rw [ite_eq_left ⟨hux,huH⟩] at h
          exact h.trans (le_add_of_nonneg_right hs0)
        · have h := Finset.single_le_sum (s := S)
            (f := fun r => if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0) (fun _ _ => by positivity) hr
          rw [ite_eq_left ⟨hrx,hrH⟩] at h
          exact h.trans (le_add_of_nonneg_left hp0)
      · rw [ite_eq_right hh]
        exact add_nonneg hp0 hs0
    _ = (∑ u ∈ P, 𝔼 H : PointedBox x k, if u ≠ x ∧ InBox H u then (1:ℝ) else 0) +
        (∑ r ∈ S, 𝔼 H : PointedBox x k, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0) := by
      rw [Finset.expect_add_distrib, Finset.expect_sum_comm, Finset.expect_sum_comm]
    _ ≤ (∑ _u ∈ P, (k:ℝ)/(Fintype.card A-1)) +
        (∑ _r ∈ S, (k:ℝ)/(Fintype.card A-1)) :=
      add_le_add (Finset.sum_le_sum (fun u _ => hp u)) (Finset.sum_le_sum (fun r _ => hs r))
    _ = _ := by simp; ring
end MinUncut.Subbox
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R W ι Ω : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [Fintype Ω]

lemma selectedProject_filter_loss (J : Finset (Finset R × (ι → ℕ)))
    (p : (Finset R × (ι → ℕ)) → Prop) (u : (R → W) → (ι → ℝ) → ℝ) :
    jointEnergy (fun B c => selectedProject J u B c-selectedProject (J.filter p) u B c) =
      ∑ j ∈ J, if p j then 0 else jointEnergy (maskHermite j.1 j.2 u) := by
  rw [selectedProject_loss_energy J (J.filter p) (Finset.filter_subset _ _)]
  have hs : J\J.filter p = J.filter (fun j => ¬p j) := by ext j; simp; aesop
  rw [hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

lemma selectedProject_average_loss (J : Finset (Finset R × (ι → ℕ)))
    (p : Ω → (Finset R × (ι → ℕ)) → Prop) (u : (R → W) → (ι → ℝ) → ℝ)
    (δ : ℝ) (hp : ∀ j ∈ J, (𝔼 ω, if p ω j then (0:ℝ) else 1) ≤ δ) :
    (𝔼 ω, jointEnergy (fun B c => selectedProject J u B c-selectedProject (J.filter (p ω)) u B c)) ≤
      δ*jointEnergy (selectedProject J u) := by
  simp_rw [selectedProject_filter_loss]
  rw [Finset.expect_sum_comm, selectedProject_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hm (ω) : (if p ω j then (0:ℝ) else jointEnergy (maskHermite j.1 j.2 u)) =
      (if p ω j then (0:ℝ) else 1)*jointEnergy (maskHermite j.1 j.2 u) := by split_ifs <;> simp
  simp_rw [hm, ← Finset.expect_mul]
  exact mul_le_mul_of_nonneg_right (hp j hj) (jointEnergy_nonneg _)

lemma selectedProject_average_contraction [Nonempty Ω]
    (J : Ω → Finset (Finset R × (ι → ℕ))) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    (𝔼 ω, jointEnergy (selectedProject (J ω) u)) ≤ jointEnergy u := by
  calc
    _ ≤ 𝔼 _ω : Ω, jointEnergy u := Finset.expect_le_expect (fun _ _ => selectedProject_energy_le _ _ hu)
    _ = _ := Fintype.expect_const _
end MinUncut.RowNoise
namespace MinUncut.Subbox
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A ι W : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

def positiveSupport (I : (ι → A) → ℕ) : Finset (ι → A) := Finset.univ.filter (fun u => 0 < I u)

omit [DecidableEq A] [Nonempty A] in
lemma positiveSupport_card (I : (ι → A) → ℕ) : (positiveSupport I).card ≤ ∑ u, I u := by
  calc
    _ = ∑ u ∈ positiveSupport I, 1 := by simp
    _ ≤ ∑ u ∈ positiveSupport I, I u := Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2)
    _ ≤ ∑ u, I u := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

def localizedSelection (x : ι → A) {k : ℕ} (H : PointedBox x k)
    (J : Finset (Finset (Row ι A) × ((ι → A) → ℕ))) :=
  J.filter (fun j => ¬Removed H (positiveSupport j.2) j.1)

lemma localization_energy_loss (x : ι → A) {k s r : ℕ} (hk : k ≤ Fintype.card A-1)
    (J : Finset (Finset (Row ι A) × ((ι → A) → ℕ)))
    (hJ : ∀ j ∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ r)
    (u : (Row ι A → W) → ((ι → A) → ℝ) → ℝ) :
    (𝔼 H : PointedBox x k, jointEnergy (fun B c => selectedProject J u B c-
      selectedProject (localizedSelection x H J) u B c)) ≤
        ((s+r:ℕ):ℝ)*((k:ℝ)/(Fintype.card A-1))*jointEnergy (selectedProject J u) := by
  change (𝔼 H : PointedBox x k, jointEnergy (fun B c => selectedProject J u B c-
    selectedProject (J.filter (fun j => ¬Removed H (positiveSupport j.2) j.1)) u B c)) ≤ _
  convert selectedProject_average_loss (R := Row ι A) (W := W) (ι := ι → A)
    (Ω := PointedBox x k) J (fun H j => ¬Removed H (positiveSupport j.2) j.1) u
    (((s+r:ℕ):ℝ)*((k:ℝ)/(Fintype.card A-1))) ?_ using 1
  · apply Finset.expect_congr rfl
    intro H _
    congr 1
    funext B c
    congr 2
    ext j
    simp
  · intro j hj
    have hp := removal_probability (x := x) hk (positiveSupport j.2) j.1
    have hcard : (positiveSupport j.2).card+j.1.card ≤ s+r :=
      Nat.add_le_add ((positiveSupport_card j.2).trans (hJ j hj).1) (hJ j hj).2
    have hc : (0:ℝ) ≤ (k:ℝ)/(Fintype.card A-1) :=
      div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (Fintype.card_pos (α := A))))
    have hmul := mul_le_mul_of_nonneg_right (show ((positiveSupport j.2).card:ℝ)+j.1.card ≤ ((s+r:ℕ):ℝ) by exact_mod_cast hcard) hc
    refine le_trans ?_ (hp.trans hmul)
    apply Finset.expect_le_expect
    intro H _
    split_ifs <;> simp_all

omit [Nonempty A] in
lemma localized_energy_contraction (x : ι → A) {k : ℕ} (hk : k ≤ Fintype.card A-1)
    (J : Finset (Finset (Row ι A) × ((ι → A) → ℕ)))
    (u : (Row ι A → W) → ((ι → A) → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi (ι → A))) :
    (𝔼 H : PointedBox x k, jointEnergy (selectedProject (localizedSelection x H J) u)) ≤ jointEnergy u := by
  have (i : ι) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  exact selectedProject_average_contraction _ u hu
end MinUncut.Subbox
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance awayRowNoiseDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def zeroFree (F : Finset R) (B : R → W) : R → W := fun t => if t ∈ F then 0 else B t

omit [Fintype W] [DecidableEq W] in
lemma dual_local_sum (F : Finset R) (r s : R) (hrs : r ≠ s) (hr : r ∈ F) (hs : s ∈ F)
    (α : Module.Dual F₂ (R → W)) (hm : frequency α r=frequency α s)
    (hz : ∀ t ∈ F, t ≠ r → t ≠ s → frequency α t=0) (B C : R → W)
    (hBC : ∀ t ∉ F, B t=C t) :
    α B = α (zeroFree F C)+frequency α r (B r+B s) := by
  have he (t : R) : frequency α t (B t) = frequency α t (zeroFree F C t)+
      (if t=r then frequency α r (B r) else 0)+(if t=s then frequency α s (B s) else 0) := by
    by_cases htr : t=r
    · subst t; simp [zeroFree, hr, hrs]
    by_cases hts : t=s
    · subst t; simp [zeroFree, hs, hrs.symm]
    by_cases htF : t∈F
    · simp [hz t htF htr hts, htr, hts]
    · simp [zeroFree, htF, htr, hts, hBC t htF]
  calc
    α B = ∑ t, (frequency α t (zeroFree F C t)+
      (if t=r then frequency α r (B r) else 0)+(if t=s then frequency α s (B s) else 0)) := by
        rw [dual_apply]; exact Finset.sum_congr rfl (fun t _ => he t)
    _ = α (zeroFree F C)+frequency α r (B r)+frequency α s (B s) := by
      simp [Finset.sum_add_distrib, ← dual_apply]
    _ = _ := by rw [map_add, hm]; abel

omit [Fintype W] [DecidableEq W] in
lemma character_local_sum (F : Finset R) (r s : R) (hrs : r ≠ s) (hr : r ∈ F) (hs : s ∈ F)
    (α : Module.Dual F₂ (R → W)) (hm : frequency α r=frequency α s)
    (hz : ∀ t ∈ F, t ≠ r → t ≠ s → frequency α t=0) (B C : R → W)
    (hBC : ∀ t ∉ F, B t=C t) :
    character α B = character α (zeroFree F C)*character (frequency α r) (B r+B s) := by
  simp only [character, dual_local_sum F r s hrs hr hs α hm hz B C hBC, sign_add]

omit [Fintype R] [Fintype W] [DecidableEq W] in
lemma character_single (α : Module.Dual F₂ (R → W)) (r : R) (b : W) :
    character α (Pi.single r b)=character (frequency α r) b := rfl

def localSlice (J : Finset (Finset R × (ι → ℕ))) (u : (R → W) → (ι → ℝ) → ℝ)
    (F : Finset R) (r : R) (C : R → W) (c : ι → ℝ) (b : W) : ℝ :=
  selectedProject J u (zeroFree F C+Pi.single r b) c

lemma selectedProject_local_sum (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (F : Finset R) (r s : R)
    (hrs : r ≠ s) (hr : r ∈ F) (hs : s ∈ F)
    (hJ : ∀ j ∈ J, ∀ t ∈ j.1, t ∈ F → t=r ∨ t=s)
    (hm : ∀ j ∈ J, ∀ α : Module.Dual F₂ (R → W), mask α=j.1 →
      coefficient (fun B => coeff (u B) j.2) α ≠ 0 → frequency α r=frequency α s)
    (B C : R → W) (hBC : ∀ t ∉ F, B t=C t) (c : ι → ℝ) :
    selectedProject J u B c = localSlice J u F r C c (B r+B s) := by
  unfold localSlice selectedProject
  apply Finset.sum_congr rfl
  intro j hj
  simp only [maskHermite_eq, maskProject_expansion]
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  by_cases hmask : mask α=j.1
  swap
  · simp [hmask]
  rw [ite_eq_left hmask, ite_eq_left hmask]
  by_cases hc : coefficient (fun B => coeff (u B) j.2) α=0
  · simp [hc]
  have hz (t : R) (htF : t∈F) (htr : t≠r) (hts : t≠s) : frequency α t=0 := by
    by_contra ht
    have htm : t∈j.1 := by rw [← hmask]; simpa [mask] using ht
    exact (hJ j hj t htm htF).elim htr hts
  rw [character_local_sum F r s hrs hr hs α (hm j hj α hmask hc) hz B C hBC]
  simp only [character_add, character_single]

lemma localSlice_odd (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (F : Finset R) (r : R) (e : W)
    (ho : ∀ j ∈ J, ∀ α : Module.Dual F₂ (R → W), mask α=j.1 →
      coefficient (fun B => coeff (u B) j.2) α ≠ 0 → frequency α r e=1)
    (C : R → W) (c : ι → ℝ) (b : W) :
    localSlice J u F r C c (b+e) = -localSlice J u F r C c b := by
  unfold localSlice selectedProject
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [maskHermite_eq, maskProject_expansion]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  by_cases hmask : mask α=j.1
  swap
  · simp [hmask]
  rw [ite_eq_left hmask, ite_eq_left hmask]
  by_cases hc : coefficient (fun B => coeff (u B) j.2) α=0
  · simp [hc]
  have he : character (frequency α r) e = -1 := by simp [character,ho j hj α hmask hc]
  simp only [character_add, character_single, he]
  ring

omit [DecidableEq W] in
lemma odd_coefficient_zero (v : W → ℝ) (e : W) (hv : ∀ b, v (b+e) = -v b)
    (α : Module.Dual F₂ W) (hα : α e≠1) : coefficient v α=0 := by
  have hz : α e=0 := by
    have hh : ∀ a : F₂, a=0 ∨ a=1 := by decide
    exact (hh (α e)).resolve_right hα
  have ht := coefficient_translate v α e
  have hh : (fun b => v (e+b)) = fun b => -v b := by funext b; rw [add_comm, hv]
  rw [hh] at ht
  simp only [coefficient, neg_mul, Finset.expect_neg_distrib, character, hz, BinaryFourier.sign_zero, one_mul] at ht
  change -coefficient v α=coefficient v α at ht
  linarith

lemma localSlice_fourier (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (F : Finset R) (r : R) (e : W)
    (ho : ∀ j ∈ J, ∀ α : Module.Dual F₂ (R → W), mask α=j.1 →
      coefficient (fun B => coeff (u B) j.2) α ≠ 0 → frequency α r e=1)
    (C : R → W) (c : ι → ℝ) (b : W) :
    localSlice J u F r C c b = ∑ α ∈ Finset.univ.filter (fun α : Module.Dual F₂ W => α e=1),
      coefficient (localSlice J u F r C c) α*character α b := by
  rw [← inversion (localSlice J u F r C c) b, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α _
  by_cases ha : α e=1
  · simp [ha]
  · simp [ha, odd_coefficient_zero _ e (localSlice_odd J u F r e ho C c) α ha]
end MinUncut.RowNoise
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

abbrev PairClass (m : ℕ) := {p : Fin m × Fin m // p.1<p.2}

instance pairClassOrder : LinearOrder (PairClass m) :=
  LinearOrder.lift' (fun p : PairClass m => finProdFinEquiv p.val)
    (fun _ _ h => Subtype.ext (finProdFinEquiv.injective h))

def PairAdmissible (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n))
    (p : PairClass m) : Prop :=
  (∀ u, 0 < I u → face u p.val.1 ≠ face x p.val.1 ∧ face u p.val.2 ≠ face x p.val.2) ∧
  (∀ y, (⟨p.val.1,y⟩ : Row m n) ∈ S → doubleMatch p.val.1 p.val.2 x (rowFill x ⟨p.val.1,y⟩) → y=face x p.val.1) ∧
  (∀ y, (⟨p.val.2,y⟩ : Row m n) ∈ S → doubleMatch p.val.2 p.val.1 x (rowFill x ⟨p.val.2,y⟩) → y=face x p.val.2)

lemma pairAdmissible_exists (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n))
    (hx : I x=0) (hsize : S.card < (m-(∑ u, I u)).choose 2) :
    ∃ p : PairClass m, PairAdmissible x I S p := by
  obtain ⟨i,j,hij,hu,hi,hj⟩ := admissible_pair x I S hx hsize
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨⟨(i,j),h⟩,hu,hi,hj⟩
  · exact ⟨⟨(j,i),h⟩,(fun u h => ⟨(hu u h).2,(hu u h).1⟩),hj,hi⟩

def admissibleClasses (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n)) :
    Finset (PairClass m) := Finset.univ.filter (PairAdmissible x I S)

def maskClass (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n)) : Option (PairClass m) :=
  if 0 < I x then none else
    if h : (admissibleClasses x I S).Nonempty then some ((admissibleClasses x I S).min' h) else none

lemma maskClass_some (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n))
    (p : PairClass m) (hp : maskClass x I S=some p) : I x=0 ∧ PairAdmissible x I S p := by
  unfold maskClass at hp
  split_ifs at hp with hx he
  have hp' := Option.some.inj hp
  have hm := Finset.min'_mem (admissibleClasses x I S) he
  rw [hp'] at hm
  exact ⟨Nat.eq_zero_of_not_pos hx,(Finset.mem_filter.mp hm).2⟩

lemma maskClass_none (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n))
    (hsize : S.card < (m-(∑ u, I u)).choose 2) : maskClass x I S=none ↔ 0<I x := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨p,hp⟩ := pairAdmissible_exists x I S (Nat.eq_zero_of_not_pos hn) hsize
    have hne : (admissibleClasses x I S).Nonempty := ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
    simp only [maskClass, ite_eq_right hn, dite_eq_left hne] at he
    contradiction
  · intro hp; simp [maskClass,hp]

def classSelection (x : Point m n) (a : Option (PairClass m))
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :=
  J.filter (fun j => maskClass x j.2 j.1=a)

lemma classSelection_partition (x : Point m n)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (v : (Finset (Row m n) × (Point m n → ℕ)) → ℝ) :
    (∑ j ∈ J, v j) = ∑ a : Option (PairClass m), ∑ j ∈ classSelection x a J, v j := by
  simp only [classSelection, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp
end MinUncut.Inner
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance awayInnerDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma joint_pair_matching (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ)
    (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n)) (p : PairClass m)
    (hp : PairAdmissible x I S p) (α : Module.Dual F₂ (FaceArray A m n))
    (hmask : mask α=S) (hne : jointCoefficient f σ η x α I ≠ 0) :
    frequency α ⟨p.val.1,face x p.val.1⟩ = frequency α ⟨p.val.2,face x p.val.2⟩ ∧
    frequency α ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)=1 := by
  have hij : p.val.1 ≠ p.val.2 := ne_of_lt p.property
  refine ⟨?_,joint_local_odd f hσ η x α I hne p.val.1 (fun u hu => (hp.1 u hu).1)⟩
  apply LinearMap.ext
  intro a
  have hh := joint_cylinder_gauge f σ η x α I hne p.val.1 p.val.2 hij x a
  rw [frequency_cylinder α x p.val.1 p.val.2 hij
    (fun y hy => hp.2.1 y (by rw [← hmask]; simpa [mask] using hy))
    (fun y hy => hp.2.2 y (by rw [← hmask]; simpa [mask] using hy))] at hh
  exact (BinaryFourier.add_eq_zero_iff _ _).mp hh

def freePairRows (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m) :
    Finset (Row m n) := Finset.univ.filter (fun r =>
      (r.1=p.val.1 ∨ r.1=p.val.2) ∧ Subbox.FaceInBox H r.1 r.2)

lemma local_face_in_box (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (i : Fin m) :
    Subbox.FaceInBox H i (face x i) := fun _ => Subbox.mem_pointedSet_self _ _

lemma local_free_left (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m) :
    (⟨p.val.1,face x p.val.1⟩ : Row m n) ∈ freePairRows x H p :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl,local_face_in_box x H _⟩

lemma local_free_right (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m) :
    (⟨p.val.2,face x p.val.2⟩ : Row m n) ∈ freePairRows x H p :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr rfl,local_face_in_box x H _⟩

def retainedClass (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k)
    (a : Option (PairClass m)) (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :=
  (classSelection x a J).filter (fun j => ¬Subbox.Removed H (hermiteSupport j.2) j.1)

lemma retained_pair_admissible (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k)
    (p : PairClass m) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (j : Finset (Row m n) × (Point m n → ℕ)) (hj : j∈retainedClass x H (some p) J) :
    PairAdmissible x j.2 j.1 p := by
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  exact (maskClass_some x j.2 j.1 p hc).2

lemma retained_pair_local (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k)
    (p : PairClass m) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (j : Finset (Row m n) × (Point m n → ℕ)) (hj : j∈retainedClass x H (some p) J)
    (r : Row m n) (hr : r∈j.1) (hF : r∈freePairRows x H p) :
    r=⟨p.val.1,face x p.val.1⟩ ∨ r=⟨p.val.2,face x p.val.2⟩ := by
  have hn := (Finset.mem_filter.mp hj).2
  have hF' := (Finset.mem_filter.mp hF).2
  have hl : r.2=face x r.1 := by
    by_contra hh
    exact hn (Or.inr ⟨r,hr,hh,hF'.2⟩)
  rcases r with ⟨t,y⟩
  dsimp only at hl hF'
  subst y
  rcases hF'.1 with h | h
  · subst t; exact Or.inl rfl
  · subst t; exact Or.inr rfl

def pairSlice (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (C : FaceArray A m n) (c : Point m n → ℝ) (b : Forms A) : ℝ :=
  localSlice (retainedClass x H (some p) J) (fun B c => gradient f B σ η c x)
    (freePairRows x H p) ⟨p.val.1,face x p.val.1⟩ C c b

theorem retained_local_sum (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B C : FaceArray A m n) (hBC : ∀ t ∉ freePairRows x H p, B t=C t) (c : Point m n → ℝ) :
    selectedProject (retainedClass x H (some p) J) (fun B c => gradient f B σ η c x) B c =
      pairSlice f σ η x H p J C c (B ⟨p.val.1,face x p.val.1⟩+B ⟨p.val.2,face x p.val.2⟩) := by
  apply selectedProject_local_sum
  · intro he
    exact (ne_of_lt p.property) (congrArg Sigma.fst he)
  · exact local_free_left x H p
  · exact local_free_right x H p
  · exact retained_pair_local x H p J
  · intro j hj α hm hc
    exact (joint_pair_matching f hσ η x j.2 j.1 p
      (retained_pair_admissible x H p J j hj) α hm hc).1
  · exact hBC

theorem pairSlice_fourier (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (C : FaceArray A m n) (c : Point m n → ℝ) (b : Forms A) :
    pairSlice f σ η x H p J C c b =
      ∑ α ∈ Finset.univ.filter (fun α : Module.Dual F₂ (Forms A) => α (AffineMap.const F₂ A 1)=1),
        coefficient (pairSlice f σ η x H p J C c) α * character α b := by
  apply localSlice_fourier
  intro j hj α hm hc
  exact (joint_pair_matching f hσ η x j.2 j.1 p
    (retained_pair_admissible x H p J j hj) α hm hc).2

lemma pairSlice_background (f : FoldedProof A) (σ η : ℝ)
    (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (C D : FaceArray A m n) (hCD : ∀ t ∉ freePairRows x H p, C t=D t) :
    pairSlice f σ η x H p J C=pairSlice f σ η x H p J D := by
  have he : zeroFree (freePairRows x H p) C=zeroFree (freePairRows x H p) D := by
    funext t
    by_cases ht : t∈freePairRows x H p
    · simp [zeroFree,ht]
    · simp [zeroFree,ht,hCD t ht]
  funext c b
  unfold pairSlice localSlice
  rw [he]
end MinUncut.Inner
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] lemma H_zero (t : ℝ) : H 0 t=1 := by simp [H,he]

lemma H_mean {d : ℕ} (hd : 0<d) : (∫ t, H d t ∂γ)=0 := by
  simpa only [H_zero,mul_one,ite_eq_right (Nat.ne_zero_of_lt hd)] using H_product d 0

lemma psi_update (I : ι → ℕ) (x : ι) (C : ι → ℝ) (t : ℝ) :
    psi I (Function.update C x t) = H (I x) t * ∏ y ∈ Finset.univ.erase x, H (I y) (C y) := by
  unfold psi
  rw [← Finset.mul_prod_erase Finset.univ (fun y => H (I y) (Function.update C x t y)) (Finset.mem_univ x)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  rw [Function.update_of_ne (Finset.mem_erase.mp hy).1]

lemma memLp_psi_update (I : ι → ℕ) (x : ι) (C : ι → ℝ) :
    MemLp (fun t => psi I (Function.update C x t)) 2 γ := by
  simpa only [psi_update] using (memLp_H (I x)).mul_const (∏ y ∈ Finset.univ.erase x, H (I y) (C y))

lemma integral_psi_update (I : ι → ℕ) (x : ι) (C : ι → ℝ) (hx : 0<I x) :
    (∫ t, psi I (Function.update C x t) ∂γ)=0 := by
  simp only [psi_update,integral_mul_const,H_mean hx,zero_mul]

lemma psi_localized (I : ι → ℕ) (x : ι) (F : Finset ι)
    (hI : ∀ y ∈ F, y≠x → I y=0) (c C : ι → ℝ) (hC : ∀ y ∉ F, c y=C y) :
    psi I c=psi I (Function.update C x (c x)) := by
  apply Finset.prod_congr rfl
  intro y _
  by_cases hx : y=x
  · subst y; rw [Function.update_self]
  by_cases hF : y∈F
  · rw [hI y hF hx,H_zero,H_zero]
  · rw [Function.update_of_ne hx,hC y hF]
end MinUncut.GaussianHermite

end

end OAI
