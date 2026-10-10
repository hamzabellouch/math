import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.BaseFinitePublic

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

abbrev ReversedBaseTape (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ) :=
  BaseTable UT P τ × UniversalFresh (ℙ K (Dual K V)) H q

abbrev ReversedBaseMessage (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ)
    (t : ReversedBaseTape UT P τ H q) :=
  (m : BaseMessage UT P τ) × UniversalFreshMessage (t.1 m) H q

noncomputable def reversedBaseDecoded (U : Finset (ℙ K V))
    (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ)
    (t : ReversedBaseTape UT P τ H q) (m : ReversedBaseMessage UT P τ H q t) : Finset (ℙ K V) :=
  U∩universalFreshDecoded Incident (t.1 m.1) H q t.2 m.2

noncomputable def reversedBaseEncoded (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : ReversedBaseTape UT P τ H q) : Option (ReversedBaseMessage UT P τ H q t) :=
  (baseFiniteEncoded T UT P τ t.1).bind fun m=>
    if _hv : ValidCap T UT MB (t.1 m) then
      (universalFreshEncoded Incident S U (T∩t.1 m) (t.1 m) Finset.inter_subset_right H n q MA t.2).map
        (fun f=>⟨m,f⟩)
    else none

omit [Finite K] [FiniteDimensional K V] in
lemma reversedBase_exact (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : ReversedBaseTape UT P τ H q) :
    (reversedBaseEncoded S U T UT P τ H n q MA MB t).map (reversedBaseDecoded U UT P τ H q t)=
      publicReverseResult S U T UT hT H n q MA MB ((baseFiniteEncoded T UT P τ t.1).map t.1) t.2 := by
  cases h : baseFiniteEncoded T UT P τ t.1 with
  | none => simp [reversedBaseEncoded,h,publicReverseResult]
  | some m =>
    simp only [reversedBaseEncoded,h,Option.bind_some,Option.map_some,publicReverseResult]
    split_ifs with hv
    · simp only [Option.map_map,reversedBaseDecoded,Function.comp_def]
    · rfl

omit [Finite K] [FiniteDimensional K V] in
theorem reversedBase_law (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ) :
    map (adaptiveLaw (baseTableLaw UT P τ R L₀) (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
      (fun t=>(reversedBaseEncoded S U T UT P τ H n q MA MB t).map (reversedBaseDecoded U UT P τ H q t))=
      optionCompose (baseCaptureLaw T UT P τ R L₀) (nextCapLaw S U T UT hT n q MA MB) := by
  simp only [reversedBase_exact S U T UT hT]
  rw [optionCompose_eq_second (baseCaptureLaw T UT P τ R L₀)
    (nextCapLaw S U T UT hT n q MA MB) (by rfl),←baseFinite_law T UT P τ R L₀]
  exact public_composition (baseTableLaw UT P τ R L₀) (universalFreshLaw (ℙ K (Dual K V)) H q)
    (fun t=>(baseFiniteEncoded T UT P τ t).map t)
    (publicReverseResult S U T UT hT H n q MA MB) (nextCapLaw S U T UT hT n q MA MB)
    (fun Y=>publicReverseResult_law S U T UT hT H n q MA MB Y)
end SharpRamseyFive.ScoreGeometry

end OAI
