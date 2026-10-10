import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealization
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuards
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyNode
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyStep
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyUnits

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts HistorySupportReduction HistorySignedDecode HistorySignedNumerators
open Characters FrequencyExposure BinaryExposure

theorem rootGiantUnits_of_knownRootFrequencyUnits (R j : ℕ) {l : ℕ}
    (h : History l) (g : KnownGiants R) (Xp Xm : ℤ)
    (hg : SignedGiantsMatch R j g Xp Xm) (hd : h.root.frequency.natAbs ∣ R)
    (hk : knownRootFrequencyUnits R j h.frequencies g) :
    IsUnit (Xp : ZMod h.root.frequency.natAbs) ∧
      IsUnit (Xm : ZMod h.root.frequency.natAbs) := by
  have hh := hk h.root.frequency (HistorySupportReduction.root_frequency_mem h)
  have hd' : h.root.frequency.natAbs ∣ R^(j+2) := hd.trans (dvd_pow_self R (by omega))
  simpa only [hg.1, hg.2, ZMod.cast_intCast hd'] using hh

theorem pair_integralGuard_of_leafAdmissible_knownUnits {R : ℕ} [NeZero R]
    (K : ℕ) (d : List Bool → Data R) (f : List Bool → FixedFactors × FixedFactors)
    {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits R h) (hu' : FrequencyUnits R h')
    (hle : l≤K) (path : List Bool) (hm : ScheduleMatches d f path h h')
    (g g' : KnownGiants R) (Xp Xm Xp' Xm' : ℤ)
    (hg : SignedGiantsMatch R l g Xp Xm) (hg' : SignedGiantsMatch R l g' Xp' Xm')
    (hknown : knownPairFrequencyUnits K R d f h h' path (l,g,g')
      (frequencyLeaves (R^(K+2)) h))
    (hown : GuardedOwnDivisibility h Xp Xm) (hown' : GuardedOwnDivisibility h' Xp' Xm')
    (hsame : frequencyLeaves (R^(K+2)) h=frequencyLeaves (R^(K+2)) h')
    (had : leafAdmissible (exposureConstraint K R d f)
      (update false (exposureStep K R d f false))
      (update true (exposureStep K R d f true)) l (path,(l,g,g'))
      (frequencyLeaves (R^(K+2)) h)) :
    (rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp' Xm').IntegralGuard := by
  induction h generalizing path g g' Xp Xm Xp' Xm' with
  | leaf a => cases h'; exact ⟨trivial,trivial⟩
  | @node l a p u hp hm0 left right ihl ihr =>
    cases h' with
    | node a' p' u' hp' hm' left' right' =>
      obtain ⟨hds,hds',hdv,hdw,hdv',hdw',hff,hff',hml,hmr⟩ := hm
      let x := BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (frequencyLeaves (R^(K+2)) left)
      let y := BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ) (frequencyLeaves (R^(K+2)) right)
      have hsameL : frequencyLeaves (R^(K+2)) left=frequencyLeaves (R^(K+2)) left' :=
        congrArg Prod.fst hsame
      have hsameR : frequencyLeaves (R^(K+2)) right=frequencyLeaves (R^(K+2)) right' :=
        congrArg Prod.snd hsame
      have hxy := frequencyLeaves_child_products hs R (K+2) hu.1
      have hxy' := frequencyLeaves_child_products hs' R (K+2) hu'.1
      have hx : (x:ZMod (R^(K+2)))=(bulkProduct hp:ZMod (R^(K+2))) := hxy.1
      have hy : (y:ZMod (R^(K+2)))=(bulkProduct hm0:ZMod (R^(K+2))) := hxy.2
      have hx' : (x:ZMod (R^(K+2)))=(bulkProduct hp':ZMod (R^(K+2))) := by
        simpa only [x,hsameL] using hxy'.1
      have hy' : (y:ZMod (R^(K+2)))=(bulkProduct hm':ZMod (R^(K+2))) := by
        simpa only [y,hsameR] using hxy'.2
      change leafAdmissible _ _ _ (l+1) _
        (frequencyLeaves (R^(K+2)) left,frequencyLeaves (R^(K+2)) right) at had
      rw [Template.leafAdmissible_pair] at had
      have hc := had.1
      change exposureConstraint K R d f l (path,(l+1,g,g')) (x*y) x at hc
      dsimp only [exposureConstraint,constraint,exposureCoefficients,Template.ambientData] at hc
      rw [hdv,hdw,hdv',hdw',hff,hff'] at hc
      have hgu := rootGiantUnits_of_knownRootFrequencyUnits R (l+1)
        (.node a p u hp hm0 left right) g Xp Xm hg
        (by simpa only [History.root, hds] using (d path).divides) hknown.1
      have hgu' := rootGiantUnits_of_knownRootFrequencyUnits R (l+1)
        (.node a' p' u' hp' hm' left' right') g' Xp' Xm' hg'
        (by simpa only [History.root, hds'] using (d path).divides') hknown.2.1
      have hfreq := (signed_node_frequency_iff_of_eq hs hlarge.1 R K (l+1)
        (d path).s (d path).divides hds g Xp Xm hg hgu.1 hgu.2 x y hx.symm hy.symm).mp hc.1
      have hfreq' := (signed_node_frequency_iff_of_eq hs' hlarge'.1 R K (l+1)
        (d path).s' (d path).divides' hds' g' Xp' Xm' hg' hgu'.1 hgu'.2
        x y hx'.symm hy'.symm).mp hc.2
      have hint := node_integral_of_frequency_and_own hs hlarge.2.1 Xp Xm hfreq
        (guardedOwnDivisibility_root Xp Xm hown)
      have hint' := node_integral_of_frequency_and_own hs' hlarge'.2.1 Xp' Xm' hfreq'
        (guardedOwnDivisibility_root Xp' Xm' hown')
      have hstep (b : Bool) := exposureStep_matches_signed hs hs' K R (by omega) d f path g g'
        Xp Xm Xp' Xm' hg hg' hint.2 hint'.2
        hds hds' hdv hdw hdv' hdw' hff hff' hu.2.1 hu'.2.1 x y hx hy hx' hy' b
      have hleft : (rebuild left
          (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ left.root.frequency right.root.frequency u hp hm0) Xp).IntegralGuard ∧
          (rebuild left'
          (signedPivot ⟨a'.frequency,Xp',Xm',a'.small⟩ left'.root.frequency right'.root.frequency u' hp' hm') Xp').IntegralGuard := by
        let c := exposureStep K R d f false path (l+1,g,g') (x*y) x
        have hcl : c.1=l := (hstep false).1
        have hgl := (hstep false).2.1
        have hgl' := (hstep false).2.2
        have hadl := had.2.1
        change leafAdmissible _ _ _ l (false::path,c) _ at hadl
        have he : c=(l,c.2.1,c.2.2) := Prod.ext hcl rfl
        rw [he] at hadl
        have hkl := hknown.2.2.1
        change knownPairFrequencyUnits K R d f left left' (false::path) c
          (frequencyLeaves (R^(K+2)) left) at hkl
        rw [he] at hkl
        exact ihl left' (History.supported_left hs) (History.supported_left hs')
          hlarge.2.2.1 hlarge'.2.2.1 hu.2.2.1 hu'.2.2.1 (by omega) (false::path) hml
          c.2.1 c.2.2 _ _ _ _ hgl hgl' hkl
          (guardedOwnDivisibility_left Xp Xm hown hint.1 hint.2)
          (guardedOwnDivisibility_left Xp' Xm' hown' hint'.1 hint'.2) hsameL hadl
      have hright : (rebuild right
          (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ left.root.frequency right.root.frequency u hp hm0) Xm).IntegralGuard ∧
          (rebuild right'
          (signedPivot ⟨a'.frequency,Xp',Xm',a'.small⟩ left'.root.frequency right'.root.frequency u' hp' hm') Xm').IntegralGuard := by
        let c := exposureStep K R d f true path (l+1,g,g') (x*y) x
        have hcr : c.1=l := (hstep true).1
        have hgr := (hstep true).2.1
        have hgr' := (hstep true).2.2
        have hadr := had.2.2
        change leafAdmissible _ _ _ l (true::path,c) _ at hadr
        have he : c=(l,c.2.1,c.2.2) := Prod.ext hcr rfl
        rw [he] at hadr
        have hkr := hknown.2.2.2
        change knownPairFrequencyUnits K R d f right right' (true::path) c
          (frequencyLeaves (R^(K+2)) right) at hkr
        rw [he] at hkr
        exact ihr right' (History.supported_right hs) (History.supported_right hs')
          hlarge.2.2.2 hlarge'.2.2.2 hu.2.2.2 hu'.2.2.2 (by omega) (true::path) hmr
          c.2.1 c.2.2 _ _ _ _ hgr hgr' hkr
          (guardedOwnDivisibility_right Xp Xm hown hint.1 hint.2)
          (guardedOwnDivisibility_right Xp' Xm' hown' hint'.1 hint'.2) hsameR hadr
      simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root]
      exact ⟨⟨hint.1,hint.2,hleft.1,hright.1⟩,⟨hint'.1,hint'.2,hleft.2,hright.2⟩⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
