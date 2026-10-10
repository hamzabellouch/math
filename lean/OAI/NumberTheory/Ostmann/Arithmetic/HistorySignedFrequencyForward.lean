import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealization
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyNode
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyStep
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyUnits

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts HistorySupportReduction HistorySignedDecode
open Characters FrequencyExposure BinaryExposure

theorem signed_pair_leafAdmissible_of_integralGuard {R : ℕ} [NeZero R]
    (K : ℕ) (d : List Bool → Data R) (f : List Bool → FixedFactors × FixedFactors)
    {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits R h) (hu' : FrequencyUnits R h')
    (hle : l ≤ K) (path : List Bool) (hm : ScheduleMatches d f path h h')
    (g g' : KnownGiants R) (Xp Xm Xp' Xm' : ℤ)
    (hg : SignedGiantsMatch R l g Xp Xm) (hg' : SignedGiantsMatch R l g' Xp' Xm')
    (hgu : CurrentGiantUnits (rebuild h Xp Xm))
    (hgu' : CurrentGiantUnits (rebuild h' Xp' Xm'))
    (hi : (rebuild h Xp Xm).IntegralGuard) (hi' : (rebuild h' Xp' Xm').IntegralGuard)
    (hsame : frequencyLeaves (R^(K+2)) h = frequencyLeaves (R^(K+2)) h') :
    leafAdmissible (exposureConstraint K R d f)
      (update false (exposureStep K R d f false))
      (update true (exposureStep K R d f true)) l (path, (l, g, g'))
      (frequencyLeaves (R^(K+2)) h) := by
  induction h generalizing path g g' Xp Xm Xp' Xm' with
  | leaf a => trivial
  | @node l a p u hp hm0 left right ihl ihr =>
    cases h' with
    | node a' p' u' hp' hm' left' right' =>
      obtain ⟨hds, hds', hdv, hdw, hdv', hdw', hff, hff', hml, hmr⟩ := hm
      let x := BinaryHaar.product (G := (ZMod (R^(K+2)))ˣ) (frequencyLeaves (R^(K+2)) left)
      let y := BinaryHaar.product (G := (ZMod (R^(K+2)))ˣ) (frequencyLeaves (R^(K+2)) right)
      have hsameL : frequencyLeaves (R^(K+2)) left = frequencyLeaves (R^(K+2)) left' :=
        congrArg Prod.fst hsame
      have hsameR : frequencyLeaves (R^(K+2)) right = frequencyLeaves (R^(K+2)) right' :=
        congrArg Prod.snd hsame
      have hxy := frequencyLeaves_child_products hs R (K+2) hu.1
      have hxy' := frequencyLeaves_child_products hs' R (K+2) hu'.1
      have hx : (x : ZMod (R^(K+2))) = (bulkProduct hp : ZMod (R^(K+2))) := hxy.1
      have hy : (y : ZMod (R^(K+2))) = (bulkProduct hm0 : ZMod (R^(K+2))) := hxy.2
      have hx' : (x : ZMod (R^(K+2))) = (bulkProduct hp' : ZMod (R^(K+2))) := by
        simpa only [x, hsameL] using hxy'.1
      have hy' : (y : ZMod (R^(K+2))) = (bulkProduct hm' : ZMod (R^(K+2))) := by
        simpa only [y, hsameR] using hxy'.2
      have hint := hi
      have hint' := hi'
      simp only [rebuild, SignedHistory.IntegralGuard, rebuild_root] at hint hint'
      have hf := dvd_trans (dvd_mul_right a.frequency ((u.map SmallSlot.value).prod : ℤ)) hint.2.1
      have hf' := dvd_trans (dvd_mul_right a'.frequency ((u'.map SmallSlot.value).prod : ℤ)) hint'.2.1
      have hc := (signed_node_frequency_iff_of_eq hs hlarge.1 R K (l+1)
        (d path).s (d path).divides hds g Xp Xm hg hgu.1.1 hgu.1.2
        x y hx.symm hy.symm).mpr hf
      have hc' := (signed_node_frequency_iff_of_eq hs' hlarge'.1 R K (l+1)
        (d path).s' (d path).divides' hds' g' Xp' Xm' hg' hgu'.1.1 hgu'.1.2
        x y hx'.symm hy'.symm).mpr hf'
      have hstep (b : Bool) := exposureStep_matches_signed hs hs' K R (by omega) d f path g g'
        Xp Xm Xp' Xm' hg hg' hint.2.1 hint'.2.1
        hds hds' hdv hdw hdv' hdw' hff hff' hu.2.1 hu'.2.1 x y hx hy hx' hy' b
      change leafAdmissible _ _ _ (l+1) _
        (frequencyLeaves (R^(K+2)) left, frequencyLeaves (R^(K+2)) right)
      rw [Template.leafAdmissible_pair]
      refine ⟨?_, ?_, ?_⟩
      · change exposureConstraint K R d f l (path, (l+1, g, g')) (x*y) x
        dsimp only [exposureConstraint, constraint, exposureCoefficients, Template.ambientData]
        rw [hdv, hdw, hdv', hdw', hff, hff']
        exact ⟨hc, hc'⟩
      · let c := exposureStep K R d f false path (l+1, g, g') (x*y) x
        have hcl : c.1 = l := (hstep false).1
        have hgl := (hstep false).2.1
        have hgl' := (hstep false).2.2
        have hh := ihl left' (History.supported_left hs) (History.supported_left hs')
          hlarge.2.2.1 hlarge'.2.2.1 hu.2.2.1 hu'.2.2.1 (by omega) (false :: path) hml
          c.2.1 c.2.2 _ _ _ _ hgl hgl' hgu.2.1 hgu'.2.1 hint.2.2.1 hint'.2.2.1 hsameL
        change leafAdmissible _ _ _ l (false :: path, c) _
        have he : c = (l, c.2.1, c.2.2) := Prod.ext hcl rfl
        rw [he]
        exact hh
      · let c := exposureStep K R d f true path (l+1, g, g') (x*y) x
        have hcr : c.1 = l := (hstep true).1
        have hgr := (hstep true).2.1
        have hgr' := (hstep true).2.2
        have hh := ihr right' (History.supported_right hs) (History.supported_right hs')
          hlarge.2.2.2 hlarge'.2.2.2 hu.2.2.2 hu'.2.2.2 (by omega) (true :: path) hmr
          c.2.1 c.2.2 _ _ _ _ hgr hgr' hgu.2.2 hgu'.2.2 hint.2.2.2 hint'.2.2.2 hsameR
        change leafAdmissible _ _ _ l (true :: path, c) _
        have he : c = (l, c.2.1, c.2.2) := Prod.ext hcr rfl
        rw [he]
        exact hh

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
