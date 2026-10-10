import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingOrientation

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
omit [Fintype (Projectivization K (Module.Dual K V))] in
theorem popular_zero (W : State (K:=K) (V:=V))
    (hZ : (level (ranks W) 0).Nonempty) : popularDomain W 0 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hp := (mem_filter.mp hb).2
  have hempty : (level (ranks W) 0).filter (fun y => b.submodule ≤ W y) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hr : Module.finrank K (W y) = 0 := by simpa [level,ranks] using (mem_filter.mp hy).1
    have hz : W y = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hh := (mem_filter.mp hy).2
    rw [hz] at hh
    apply b.rep_nonzero
    have hm : b.rep ∈ b.submodule := by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    exact hh hm
  unfold Popular at hp
  rw [hempty, card_empty, Nat.cast_zero] at hp
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  have hn : (0:ℝ) < (level (ranks W) 0).card := by exact_mod_cast card_pos.mpr hZ
  exact (not_le_of_gt (div_pos hn (by positivity))) hp

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
theorem popular_card (W : State (K:=K) (V:=V)) (l : ℕ)
    (hZ : (level (ranks W) (l+1)).Nonempty) :
    ((popularDomain W (l+1)).card:ℝ) ≤ 32*(Nat.card K:ℝ)^(l+1) := by
  let Z := level (ranks W) (l+1)
  let B := popularDomain W (l+1)
  let q : ℝ := Nat.card K
  have hq : 0 < q := by
    change (0:ℝ) < Nat.card K
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  have hZpos : (0:ℝ) < Z.card := by exact_mod_cast card_pos.mpr hZ
  have hdouble : ∑ b ∈ B, ((Z.filter (fun y => b.submodule ≤ W y)).card:ℝ) =
      ∑ y ∈ Z, ((B.filter (fun b => b.submodule ≤ W y)).card:ℝ) := by
    simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_comm
  have hcount : (B.card:ℝ) * ((Z.card:ℝ)/(16*q)) ≤ (Z.card:ℝ)*(2*q^l) := by
    calc
      _ = ∑ _b ∈ B, ((Z.card:ℝ)/(16*q)) := by simp
      _ ≤ ∑ b ∈ B, ((Z.filter (fun y => b.submodule ≤ W y)).card:ℝ) := by
        apply sum_le_sum
        intro b hb
        exact (mem_filter.mp hb).2
      _ = ∑ y ∈ Z, ((B.filter (fun b => b.submodule ≤ W y)).card:ℝ) := hdouble
      _ ≤ ∑ _y ∈ Z, 2*q^l := by
        apply sum_le_sum
        intro y hy
        have hr : Module.finrank K (W y) = l+1 := by
          change y ∈ level (ranks W) (l+1) at hy
          exact (mem_filter.mp hy).2
        have hc := card_subspace_points_le (W y) hr
        exact (show ((B.filter (fun b => b.submodule ≤ W y)).card:ℝ) ≤
          ((univ.filter (fun b : Points (K:=K) (V:=V) => b.submodule ≤ W y)).card:ℝ) by
            exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ B))).trans hc
      _ = _ := by simp
  have hm := (mul_le_mul_of_nonneg_right hcount (show 0 ≤ 16*q by positivity))
  have he : (B.card:ℝ)*((Z.card:ℝ)/(16*q))*(16*q) = (B.card:ℝ)*Z.card := by
    field_simp
  rw [he] at hm
  change (B.card:ℝ) ≤ 32*q^(l+1)
  rw [pow_succ]
  have hh : (B.card:ℝ)*Z.card ≤ (32*(q^l*q))*Z.card := by nlinarith
  nlinarith

noncomputable def partnerDomain (W : Submodule K V) :
    Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun a => W ≤ LinearMap.ker a.rep)

omit [Fintype (Projectivization K V)] in
theorem partner_card {d r : ℕ} (hdim : Module.finrank K V = d+1)
    (W : Submodule K V) (hW : Module.finrank K W = r) (hr : r ≤ d) :
    ((partnerDomain W).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-r) := by
  have he : partnerDomain W = univ.filter (fun a => a.submodule ≤ W.dualAnnihilator) := by
    ext a
    simp only [partnerDomain, mem_filter, mem_univ, true_and,
      Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    rfl
  rw [he]
  apply card_subspace_points_le
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

noncomputable def popularJoint (W : State (K:=K) (V:=V)) (l r : ℕ) :
    Finset (Points (K:=K) (V:=V) × Projectivization K (Module.Dual K V)) :=
  (popularDomain W l).biUnion (fun b =>
    if ranks W b = r then (partnerDomain (W b)).image (Prod.mk b) else ∅)

theorem popular_joint_card {d l r : ℕ} (hdim : Module.finrank K V = d+1)
    (W : State (K:=K) (V:=V)) (hl : l ≤ r) (hr : r ≤ d)
    (hZ : (level (ranks W) l).Nonempty) :
    ((popularJoint W l r).card:ℝ) ≤ 64*(Nat.card K:ℝ)^d := by
  cases l with
  | zero => simp [popularJoint, popular_zero W hZ]
  | succ l =>
    let q : ℝ := Nat.card K
    have hq : 1 ≤ q := by
      change (1:ℝ) ≤ Nat.card K
      exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K).le
    have hc : ((popularJoint W (l+1) r).card:ℝ) ≤
        ((popularDomain W (l+1)).card:ℝ)*(2*q^(d-r)) := by
      calc
        _ ≤ ∑ b ∈ popularDomain W (l+1),
            ((if ranks W b = r then (partnerDomain (W b)).image (Prod.mk b) else ∅).card:ℝ) := by
          exact_mod_cast (card_biUnion_le (s := popularDomain W (l+1))
            (t := fun b => if ranks W b = r then (partnerDomain (W b)).image (Prod.mk b) else ∅))
        _ ≤ ∑ _b ∈ popularDomain W (l+1), 2*q^(d-r) := by
          apply sum_le_sum
          intro b hb
          split_ifs with h
          · rw [card_image_of_injective _ (by intro x y hxy; exact Prod.mk.inj hxy |>.2)]
            exact partner_card hdim (W b) h hr
          · simp; positivity
        _ = _ := by simp
    have hpop := popular_card W l hZ
    have hh := hc.trans (mul_le_mul_of_nonneg_right hpop (show 0 ≤ 2*q^(d-r) by positivity))
    have hp : q^(l+1+(d-r)) ≤ q^d := pow_le_pow_right₀ hq (by omega)
    calc
      _ ≤ (32*q^(l+1))*(2*q^(d-r)) := hh
      _ = 64*q^(l+1+(d-r)) := by rw [pow_add]; ring
      _ ≤ 64*q^d := mul_le_mul_of_nonneg_left hp (by norm_num)

end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

inductive ScanKind
  | popular | poor | expensive
  deriving DecidableEq

instance flat_ActualMarkingOrientation_1 : Fintype ScanKind := ⟨{.popular,.poor,.expensive}, by
  intro k
  cases k <;> simp⟩

def levelFromRank (W : State (K:=K) (V:=V)) (r : ℕ) : ℕ :=
  Classical.choose ((range (r+1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0,by simp⟩)

omit [FiniteDimensional K V] in
lemma chosenLevel_from_rank (W : State (K:=K) (V:=V)) (b : Points (K:=K) (V:=V)) :
    chosenLevel W b = levelFromRank W (ranks W b) := rfl

abbrev RankMask := Fin (Module.finrank K V+1) × ScanKind

abbrev ScanFlag := Module.Dual K V × Points (K:=K) (V:=V)

def flagKind (q : ℝ) (W : State (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) : ScanKind :=
  if Popular W q (chosenLevel W f.2) f.2 then .popular
  else if Poor W q (chosenLevel W f.2) f.1 then .poor else .expensive

omit [FiniteDimensional K V] in
lemma flagKind_expensive (q : ℝ) (W : State (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) :
    flagKind q W f = .expensive ↔ IsExpensive W q f := by
  unfold flagKind IsExpensive
  split_ifs <;> simp_all

def maskAt (q : ℝ) (W : State (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) :
    RankMask (K:=K) (V:=V) :=
  (⟨ranks W f.2, Nat.lt_succ_of_le (Submodule.finrank_le _)⟩, flagKind q W f)

def sentAt (q : ℝ) (W : State (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) :
    Option (ScanFlag (K:=K) (V:=V)) := if IsExpensive W q f then some f else none

def replayStep (W : State (K:=K) (V:=V)) : Option (ScanFlag (K:=K) (V:=V)) →
    State (K:=K) (V:=V)
  | none => W
  | some f => update W f.1 f.2

def markingCode (q : ℝ) : State (K:=K) (V:=V) → List (ScanFlag (K:=K) (V:=V)) →
    List (RankMask (K:=K) (V:=V) × Option (ScanFlag (K:=K) (V:=V)))
  | _, [] => []
  | W, f::fs => (maskAt q W f, sentAt q W f)::
      markingCode q (replayStep W (sentAt q W f)) fs

def replay (W : State (K:=K) (V:=V)) : List (Option (ScanFlag (K:=K) (V:=V))) →
    State (K:=K) (V:=V)
  | [] => W
  | f::fs => replay (replayStep W f) fs

lemma markingCode_length (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ScanFlag (K:=K) (V:=V))) : (markingCode q W fs).length = fs.length := by
  induction fs generalizing W with
  | nil => rfl
  | cons f fs ih => simp only [markingCode,List.length_cons,ih]

theorem replay_markingCode (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ScanFlag (K:=K) (V:=V))) :
    replay W ((markingCode q W fs).map Prod.snd) = (scan q W fs).2 := by
  induction fs generalizing W with
  | nil => rfl
  | cons f fs ih =>
    simp only [markingCode,List.map_cons,replay]
    rw [ih]
    by_cases h : IsExpensive W q f <;> simp [scan,sentAt,replayStep,h]

def decodedCheap (q : ℝ) (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) : Prop :=
  ranks W f.2 = m.1.val ∧
    match m.2 with
    | .popular => Popular W q (levelFromRank W m.1.val) f.2
    | .poor => Poor W q (levelFromRank W m.1.val) f.1
    | .expensive => False

lemma decodedCheap_maskAt (q : ℝ) (W : State (K:=K) (V:=V))
    (f : ScanFlag (K:=K) (V:=V)) (hc : ¬IsExpensive W q f) :
    decodedCheap q W (maskAt q W f) f := by
  unfold decodedCheap maskAt
  refine ⟨rfl,?_⟩
  change (match flagKind q W f with
    | .popular => Popular W q (chosenLevel W f.2) f.2
    | .poor => Poor W q (chosenLevel W f.2) f.1
    | .expensive => False)
  unfold flagKind
  split_ifs with h h'
  · exact h
  · exact h'
  · exact hc ⟨h,h'⟩

lemma mask_records_transmission (q : ℝ) (W : State (K:=K) (V:=V))
    (f : ScanFlag (K:=K) (V:=V)) :
    (sentAt q W f).isSome = true ↔ (maskAt q W f).2 = .expensive := by
  simp only [sentAt,maskAt,flagKind_expensive]
  split_ifs <;> simp_all

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma rankMask_card : Fintype.card (RankMask (K:=K) (V:=V)) =
    (Module.finrank K V+1)*3 := by
  rw [Fintype.card_prod,Fintype.card_fin]
  rfl

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

def ScanConsistent (fs : List (ScanFlag (K:=K) (V:=V))) : Prop :=
  fs.Pairwise (fun f g => f.1 g.2.rep = 0 → g.1 f.2.rep = 0)

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in

lemma update_annihilates_later (W : State (K:=K) (V:=V))
    (f g : ScanFlag (K:=K) (V:=V)) (hW : W g.2 ≤ LinearMap.ker g.1)
    (hfg : f.1 g.2.rep = 0 → g.1 f.2.rep = 0) :
    update W f.1 f.2 g.2 ≤ LinearMap.ker g.1 := by
  unfold update
  split_ifs with h
  · apply sup_le hW
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
    exact hfg h
  · exact hW

def validCode (q : ℝ) : State (K:=K) (V:=V) → List (ScanFlag (K:=K) (V:=V)) →
    List (RankMask (K:=K) (V:=V) × Option (ScanFlag (K:=K) (V:=V))) → Prop
  | _, [], [] => True
  | W, f::fs, (m,s)::cs => W f.2 ≤ LinearMap.ker f.1 ∧
      (match s with | none => decodedCheap q W m f | some g => f = g) ∧
      validCode q (replayStep W s) fs cs
  | _, _, _ => False

theorem markingCode_valid (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ScanFlag (K:=K) (V:=V))) (hcons : ScanConsistent fs)
    (hW : ∀ f ∈ fs, W f.2 ≤ LinearMap.ker f.1) :
    validCode q W fs (markingCode q W fs) := by
  induction fs generalizing W with
  | nil => trivial
  | cons f fs ih =>
    have hp := List.pairwise_cons.mp hcons
    refine ⟨hW f (by simp),?_,?_⟩
    · by_cases h : IsExpensive W q f
      · simp [sentAt,h]
      · simpa [sentAt,h] using decodedCheap_maskAt q W f h
    · apply ih _ hp.2
      intro g hg
      have hw := hW g (by simp [hg])
      by_cases h : IsExpensive W q f
      · simp only [sentAt,ite_eq_left h,replayStep]
        exact update_annihilates_later W f g hw (hp.1 g hg)
      · simpa only [sentAt,ite_eq_right h,replayStep] using hw

theorem markingCode_valid_zero (q : ℝ) (fs : List (ScanFlag (K:=K) (V:=V)))
    (hcons : ScanConsistent fs) :
    validCode q (fun _ => ⊥) fs (markingCode q (fun _ => ⊥) fs) :=
  markingCode_valid q _ fs hcons (fun _ _ => bot_le)

omit [FiniteDimensional K V] in
lemma levelFromRank_spec (W : State (K:=K) (V:=V)) (r : ℕ) :
    levelFromRank W r ≤ r ∧ ∀ j ≤ r,
      (level (ranks W) j).card ≤ (level (ranks W) (levelFromRank W r)).card := by
  have h := Classical.choose_spec ((range (r+1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0,by simp⟩)
  simpa only [levelFromRank,mem_range,Nat.lt_succ_iff] using h

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset SharpLogRamsey.Incidence
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

abbrev ProjectivePair := Points (K:=K) (V:=V) × Projectivization K (Module.Dual K V)

def incidentPairs (S : Finset (Points (K:=K) (V:=V)))
    (T : Finset (Projectivization K (Module.Dual K V))) : Finset (ProjectivePair (K:=K) (V:=V)) :=
  (S ×ˢ T).filter (fun f => Incident f.1 f.2)

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma incidentPairs_card (S : Finset (Points (K:=K) (V:=V)))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    (incidentPairs S T).card = incidenceCount S T := by
  simp only [incidentPairs,incidenceCount,card_eq_sum_ones,sum_filter,sum_product]
  rw [sum_comm]

def projectiveCheapDomain (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  if m.1.val < Module.finrank K V then
    match m.2 with
    | .popular => popularJoint W (levelFromRank W m.1.val) m.1.val
    | .poor => incidentPairs (level (ranks W) m.1.val) (poorDomain W (levelFromRank W m.1.val))
    | .expensive => ∅
  else ∅

omit [Finite K] in
lemma cheapDomain_membership (W : State (K:=K) (V:=V)) (f : ProjectivePair (K:=K) (V:=V))
    (hf : Incident f.1 f.2) (hW : W f.1 ≤ LinearMap.ker f.2.rep)
    (hc : ¬IsExpensive W (Nat.card K) (f.2.rep,f.1)) :
    f ∈ projectiveCheapDomain W (maskAt (Nat.card K) W (f.2.rep,f.1)) := by
  have hr : ranks W f.1 < Module.finrank K V := by
    have hle := Submodule.finrank_mono hW
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero f.2.rep_nonzero
    unfold ranks
    omega
  dsimp only [projectiveCheapDomain,maskAt]
  rw [ite_eq_left hr]
  unfold flagKind
  split_ifs with hp hpoor
  · apply mem_biUnion.mpr
    refine ⟨f.1,?_,?_⟩
    · simpa only [popularDomain,mem_filter,mem_univ,true_and,chosenLevel_from_rank] using hp
    · rw [ite_eq_left rfl]
      apply mem_image.mpr
      exact ⟨f.2,by simpa only [partnerDomain,mem_filter,mem_univ,true_and] using hW,rfl⟩
  · apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_,?_⟩,hf⟩
    · simp [level]
    · simpa only [poorDomain,mem_filter,mem_univ,true_and,chosenLevel_from_rank] using hpoor
  · exact False.elim (hc ⟨hp,hpoor⟩)

omit [Finite K] [FiniteDimensional K V] in
lemma popularJoint_empty_of_level_empty (W : State (K:=K) (V:=V)) (l r : ℕ)
    (he : level (ranks W) r = ∅) : popularJoint W l r = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨b,hb,hf⟩ := mem_biUnion.mp hf
  by_cases hr : ranks W b = r
  · have hm : b ∈ level (ranks W) r := by simp [level,hr]
    rw [he] at hm
    exact notMem_empty _ hm
  · simp only [ite_eq_right hr,notMem_empty] at hf

theorem projectiveCheapDomain_card {n : ℕ} (hdim : Module.finrank K V = n+3)
    (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) :
    ((projectiveCheapDomain W m).card:ℝ) ≤ 64*(Nat.card K:ℝ)^(n+2) := by
  unfold projectiveCheapDomain
  split_ifs with hr
  · have hs := levelFromRank_spec W m.1.val
    have hrd : m.1.val ≤ n+2 := by omega
    cases hk : m.2 with
    | expensive => simp
    | poor =>
      rw [incidentPairs_card]
      exact (poor_joint_domain_bound hdim W (hs.2 _ le_rfl)).trans (by
        have hq : 0 ≤ (Nat.card K:ℝ)^(n+2) := by positivity
        nlinarith)
    | popular =>
      by_cases he : level (ranks W) m.1.val = ∅
      · rw [popularJoint_empty_of_level_empty W _ _ he]
        simp
      · have hne : (level (ranks W) (levelFromRank W m.1.val)).Nonempty := by
          apply card_pos.mp
          exact (card_pos.mpr (nonempty_iff_ne_empty.mpr he)).trans_le (hs.2 _ le_rfl)
        exact popular_joint_card (by omega) W hs.1 hrd hne
  · simp

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.ProjectiveDuality
open SharpLogRamsey.Incidence
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

def mapEquiv (e : V ≃ₗ[K] W) : Projectivization K V ≃ Projectivization K W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe, e.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe, e.apply_symm_apply]

variable [FiniteDimensional K V]
def bidual : Projectivization K V ≃ Projectivization K (Module.Dual K (Module.Dual K V)) :=
  mapEquiv (Module.evalEquiv K V)

lemma incident_bidual (y : Projectivization K V) (b : Projectivization K (Module.Dual K V)) :
    Incident b (bidual y) ↔ Incident y b := by
  have he : bidual y = Projectivization.mk K ((Module.evalEquiv K V) y.rep)
      (by simpa using (Module.evalEquiv K V).injective.ne y.rep_nonzero) := by
    conv_lhs => rw [← y.mk_rep]
    rfl
  rw [Incident, he]
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K ((Module.evalEquiv K V) y.rep)
    (by simpa using (Module.evalEquiv K V).injective.ne y.rep_nonzero)
  rw [← hu]
  simp [Units.smul_def, Incident]

end
end SharpLogRamsey.ProjectiveDuality
namespace SharpLogRamsey
section Flags
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

def Incident (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) : Prop := b.rep a.rep = 0
structure Flag where
  point : Projectivization K V
  dualPoint : Projectivization K (Module.Dual K V)
  incident : Incident K V point dualPoint
variable {K V}
def Consistent {N : ℕ} (F : Fin N → Flag K V) : Prop :=
  ∀ i j, i < j → Incident K V (F i).point (F j).dualPoint →
    Incident K V (F j).point (F i).dualPoint
end Flags
end SharpLogRamsey

namespace SharpLogRamsey.Marking
open ProjectiveDuality
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def forwardScan {N : ℕ} (F : Fin N → Flag K V) :
    List (ScanFlag (K:=K) (V:=Module.Dual K V)) :=
  List.ofFn (fun i => ((bidual (F i).point).rep,(F i).dualPoint))

def backwardScan {N : ℕ} (F : Fin N → Flag K V) : List (ScanFlag (K:=K) (V:=V)) :=
  List.ofFn (fun i => ((F i.rev).dualPoint.rep,(F i.rev).point))

theorem forwardScan_consistent {N : ℕ} (F : Fin N → Flag K V) (hF : Consistent F) :
    ScanConsistent (forwardScan F) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  change Incidence.Incident (F j).dualPoint (bidual (F i).point) →
    Incidence.Incident (F i).dualPoint (bidual (F j).point)
  simp only [incident_bidual]
  exact hF i j hij

omit [FiniteDimensional K V] in
theorem backwardScan_consistent {N : ℕ} (F : Fin N → Flag K V) (hF : Consistent F) :
    ScanConsistent (backwardScan F) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact hF j.rev i.rev (Fin.rev_lt_rev.mpr hij)

theorem forward_own_incident {N : ℕ} (F : Fin N → Flag K V) (i : Fin N) :
    Incidence.Incident (F i).dualPoint (bidual (F i).point) :=
  (incident_bidual _ _).mpr (F i).incident

variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] in
theorem forwardScan_valid {N : ℕ} (F : Fin N → Flag K V) (hF : Consistent F) (q : ℝ) :
    validCode q (fun _ => ⊥) (forwardScan F)
      (markingCode q (fun _ => ⊥) (forwardScan F)) :=
  markingCode_valid_zero q _ (forwardScan_consistent F hF)

omit [Fintype (Projectivization K (Module.Dual K V))] in
theorem backwardScan_valid {N : ℕ} (F : Fin N → Flag K V) (hF : Consistent F) (q : ℝ) :
    validCode q (fun _ => ⊥) (backwardScan F)
      (markingCode q (fun _ => ⊥) (backwardScan F)) :=
  markingCode_valid_zero q _ (backwardScan_consistent F hF)

end
end SharpLogRamsey.Marking

end

end OAI
