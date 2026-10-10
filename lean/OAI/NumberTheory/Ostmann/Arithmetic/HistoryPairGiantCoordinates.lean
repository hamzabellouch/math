import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairActiveReindex
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinatesBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeXi

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairGiantCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryActiveCoordinates
open HistoryPairSmoothXi HistorySignedDecode HistorySymbolicEncoding
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def optionBoolEquiv : Option Unit ≃ Bool where
  toFun
    | none => false
    | some _ => true
  invFun
    | false => none
    | true => some ()
  left_inv x := by cases x with | none => rfl | some u => cases u; rfl
  right_inv b := by cases b <;> rfl

def optionEquiv (h k : History l) : Option Unit ≃ giantCoordinates h k :=
  optionBoolEquiv.trans (boolEquiv h k)

@[simp] theorem optionEquiv_none (h k : History l) :
    (optionEquiv h k none).val = leftMap h k (.inl false) := rfl

@[simp] theorem optionEquiv_some (h k : History l) :
    (optionEquiv h k (some ())).val = leftMap h k (.inl true) := rfl

@[simp] theorem giantCoordinates_card (h k : History l) : (giantCoordinates h k).card = 2 := by
  simpa only [Fintype.card_bool,Fintype.card_coe] using (Fintype.card_congr (boolEquiv h k)).symm

theorem insert_option_leftMap (h k : History l) (u : Option Unit → ℝ) :
    (fun i => HistoryActiveCoordinates.insert (giantCoordinates h k) (pairBackground h k)
      (fun q => u ((optionEquiv h k).symm q)) (leftMap h k i)) =
      realGiantSample h (fun t => if t then u (some ()) else u none) := by
  change (fun i => insertGiants h k (fun t => u (optionBoolEquiv.symm t)) (leftMap h k i)) = _
  rw [insertGiants_leftMap]
  congr 1
  funext t
  cases t <;> rfl

theorem insert_option_rightMap (h k : History l) (u : Option Unit → ℝ) :
    (fun i => HistoryActiveCoordinates.insert (giantCoordinates h k) (pairBackground h k)
      (fun q => u ((optionEquiv h k).symm q)) (rightMap h k i)) =
      realGiantSample k (fun t => if t then u (some ()) else u none) := by
  change (fun i => insertGiants h k (fun t => u (optionBoolEquiv.symm t)) (rightMap h k i)) = _
  rw [insertGiants_rightMap]
  congr 1
  funext t
  cases t <;> rfl

theorem realGiantSample_signed (h : History l) (Xp Xm : ℤ) :
    realGiantSample h (fun b => if b then (Xm:ℝ) else (Xp:ℝ)) = signedGiantSample h Xp Xm := by
  funext i
  rcases i with b | i
  · cases b <;> rfl
  · rcases i with i | i <;>
      simp only [realGiantSample,signedGiantSample,integerSample,Int.cast_natCast]

theorem insertGiants_leftMap_signed (h k : History l) (Xp Xm : ℤ) :
    (fun i => insertGiants h k (fun t => if t then (Xm:ℝ) else (Xp:ℝ)) (leftMap h k i)) =
      signedGiantSample h Xp Xm := by
  rw [insertGiants_leftMap,realGiantSample_signed]

theorem insertGiants_rightMap_signed (h k : History l) (Xp Xm : ℤ) :
    (fun i => insertGiants h k (fun t => if t then (Xm:ℝ) else (Xp:ℝ)) (rightMap h k i)) =
      signedGiantSample k Xp Xm := by
  rw [insertGiants_rightMap,realGiantSample_signed]

theorem pairedRealXi_insertGiants (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (u : Bool → ℝ) :
    pairedRealXi b s X tb td G h k hs ks (insertGiants h k u) =
      actualRealXi b s X tb td G outside h k hs ks (realGiantSample h u) (realGiantSample k u) := by
  unfold pairedRealXi
  rw [insertGiants_leftMap,insertGiants_rightMap]

theorem reindexedRealXi_bool (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (u : Bool → ℝ) :
    reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
      (boolEquiv h k) u =
      actualRealXi b s X tb td G outside h k hs ks (realGiantSample h u) (realGiantSample k u) :=
  pairedRealXi_insertGiants b s X tb td G h k hs ks u

theorem reindexedRealXi_option (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (u : Option Unit → ℝ) :
    reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
      (optionEquiv h k) u =
      actualRealXi b s X tb td G outside h k hs ks
        (realGiantSample h (fun t => if t then u (some ()) else u none))
        (realGiantSample k (fun t => if t then u (some ()) else u none)) := by
  change reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
    (boolEquiv h k) (fun t => u (optionBoolEquiv.symm t)) = _
  have hu : (fun t => u (optionBoolEquiv.symm t)) =
      (fun t => if t then u (some ()) else u none) := by
    funext t
    cases t <;> rfl
  rw [reindexedRealXi_bool,hu]

theorem reindexedRealXi_bool_signed (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (Xp Xm : ℤ) :
    reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
      (boolEquiv h k) (fun t => if t then (Xm:ℝ) else (Xp:ℝ)) =
      actualRealXi b s X tb td G outside h k hs ks
        (signedGiantSample h Xp Xm) (signedGiantSample k Xp Xm) := by
  rw [reindexedRealXi_bool,realGiantSample_signed,realGiantSample_signed]

theorem reindexedRealXi_option_signed (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (Xp Xm : ℤ) :
    reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
      (optionEquiv h k) (fun t => match t with | none => (Xp:ℝ) | some _ => (Xm:ℝ)) =
      actualRealXi b s X tb td G outside h k hs ks
        (signedGiantSample h Xp Xm) (signedGiantSample k Xp Xm) := by
  rw [reindexedRealXi_option]
  exact congrArg₂ (actualRealXi b s X tb td G outside h k hs ks)
    (realGiantSample_signed h Xp Xm) (realGiantSample_signed k Xp Xm)

end Ostmann.Arithmetic.HistoryPairGiantCoordinates

end

end OAI
