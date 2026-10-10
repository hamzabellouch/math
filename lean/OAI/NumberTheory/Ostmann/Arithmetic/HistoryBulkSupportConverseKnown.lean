import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextBridge

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryBulkProducts HistorySignedDecode HistorySignedResidueFactorization
open Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues

theorem frequencyGiantCoprime_pair_iff_known_static
    {R : ℕ} [NeZero R] (K : ℕ) (d : List Bool → Data R) (f : List Bool → FixedFactors × FixedFactors)
    {l : ℕ} (h h' : History l) {V : ℕ → ℕ}
    (hs : StaticSkeleton V h) (hs' : StaticSkeleton V h')
    (hF : ∀s∈h.frequencies,s.natAbs∣R) (hF' : ∀s∈h'.frequencies,s.natAbs∣R)
    (hu : FrequencyUnits R h) (hu' : FrequencyUnits R h') (hle : l≤K)
    (path : List Bool) (hm : ScheduleMatches d f path h h')
    (g g' : KnownGiants R) (Xp Xm Xp' Xm' : ℤ)
    (hg : SignedGiantsMatch R l g Xp Xm) (hg' : SignedGiantsMatch R l g' Xp' Xm')
    (hi : (rebuild h Xp Xm).IntegralGuard) (hi' : (rebuild h' Xp' Xm').IntegralGuard)
    (hsame : frequencyLeaves (R^(K+2)) h=frequencyLeaves (R^(K+2)) h') :
    (FrequencyGiantCoprime (rebuild h Xp Xm) ∧ FrequencyGiantCoprime (rebuild h' Xp' Xm')) ↔
      knownPairFrequencyUnits K R d f h h' path (l,g,g') (frequencyLeaves (R^(K+2)) h) := by
  induction h generalizing path g g' Xp Xm Xp' Xm' with
  | leaf a =>
    cases h' with
    | leaf a' =>
      exact (and_congr (knownRootFrequencyUnits_iff_rebuild R (.leaf a) hF g Xp Xm hg)
        (knownRootFrequencyUnits_iff_rebuild R (.leaf a') hF' g' Xp' Xm' hg')).symm
  | @node l a p u hp hm0 left right ihl ihr =>
    cases h' with
    | node a' p' u' hp' hm' left' right' =>
      have hr := knownRootFrequencyUnits_iff_rebuild R _ hF g Xp Xm hg
      have hr' := knownRootFrequencyUnits_iff_rebuild R _ hF' g' Xp' Xm' hg'
      obtain ⟨hds,hds',hdv,hdw,hdv',hdw',hff,hff',hml,hmr⟩ := hm
      let x := BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (frequencyLeaves (R^(K+2)) left)
      let y := BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (frequencyLeaves (R^(K+2)) right)
      have hsameL : frequencyLeaves (R^(K+2)) left=frequencyLeaves (R^(K+2)) left' :=
        congrArg Prod.fst hsame
      have hsameR : frequencyLeaves (R^(K+2)) right=frequencyLeaves (R^(K+2)) right' :=
        congrArg Prod.snd hsame
      have hxy := frequencyLeaves_child_products_static hs R (K+2) hu.1
      have hxy' := frequencyLeaves_child_products_static hs' R (K+2) hu'.1
      have hx : (x:ZMod (R^(K+2)))=(bulkProduct hp:ZMod (R^(K+2))) := hxy.1
      have hy : (y:ZMod (R^(K+2)))=(bulkProduct hm0:ZMod (R^(K+2))) := hxy.2
      have hx' : (x:ZMod (R^(K+2)))=(bulkProduct hp':ZMod (R^(K+2))) := by
        simpa only [x,hsameL] using hxy'.1
      have hy' : (y:ZMod (R^(K+2)))=(bulkProduct hm':ZMod (R^(K+2))) := by
        simpa only [y,hsameR] using hxy'.2
      have hint := hi
      have hint' := hi'
      simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root] at hint hint'
      have hstep (b : Bool) := exposureStep_matches_signed_static hs.1.frequency_ne_zero hs'.1.frequency_ne_zero K R (by omega) d f path g g'
        Xp Xm Xp' Xm' hg hg' hint.2.1 hint'.2.1 hds hds' hdv hdw hdv' hdw' hff hff'
        hu.2.1 hu'.2.1 x y hx hy hx' hy' b
      let cl := exposureStep K R d f false path (l+1,g,g') (x*y) x
      let cr := exposureStep K R d f true path (l+1,g,g') (x*y) x
      have hil := ihl left' hs.2.2.1 hs'.2.2.1
        (fun s hs=>hF s (left_frequency_mem _ _ _ _ _ _ _ hs))
        (fun s hs=>hF' s (left_frequency_mem _ _ _ _ _ _ _ hs))
        hu.2.2.1 hu'.2.2.1 (by omega) (false::path) hml cl.2.1 cl.2.2 _ _ _ _
        (hstep false).2.1 (hstep false).2.2 hint.2.2.1 hint'.2.2.1 hsameL
      have hir := ihr right' hs.2.2.2 hs'.2.2.2
        (fun s hs=>hF s (right_frequency_mem _ _ _ _ _ _ _ hs))
        (fun s hs=>hF' s (right_frequency_mem _ _ _ _ _ _ _ hs))
        hu.2.2.2 hu'.2.2.2 (by omega) (true::path) hmr cr.2.1 cr.2.2 _ _ _ _
        (hstep true).2.1 (hstep true).2.2 hint.2.2.2 hint'.2.2.2 hsameR
      have hel : cl=(l,cl.2.1,cl.2.2) := Prod.ext (hstep false).1 rfl
      have her : cr=(l,cr.2.1,cr.2.2) := Prod.ext (hstep true).1 rfl
      rw [←hel] at hil
      rw [←her] at hir
      change ((RootFrequencyGiantCoprime (rebuild (.node a p u hp hm0 left right) Xp Xm) ∧ _ ∧ _) ∧
        (RootFrequencyGiantCoprime (rebuild (.node a' p' u' hp' hm' left' right') Xp' Xm') ∧ _ ∧ _)) ↔
        knownRootFrequencyUnits R (l+1) (History.node a p u hp hm0 left right).frequencies g ∧
        knownRootFrequencyUnits R (l+1) (History.node a' p' u' hp' hm' left' right').frequencies g' ∧
        knownPairFrequencyUnits K R d f left left' (false::path) cl _ ∧
        knownPairFrequencyUnits K R d f right right' (true::path) cr _
      constructor
      · rintro ⟨⟨hr0,hl0,hr1⟩,⟨hr0',hl0',hr1'⟩⟩
        exact ⟨hr.mpr hr0,hr'.mpr hr0',hil.mp ⟨hl0,hl0'⟩,hir.mp ⟨hr1,hr1'⟩⟩
      · rintro ⟨hr0,hr0',hl0,hr1⟩
        obtain ⟨hl0,hl0'⟩ := hil.mpr hl0
        obtain ⟨hr1,hr1'⟩ := hir.mpr hr1
        exact ⟨⟨hr.mp hr0,hl0,hr1⟩,⟨hr'.mp hr0',hl0',hr1'⟩⟩

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
