import OAI.Analysis.KadisonKastler.FreeDiagonalLeadingSpace
import OAI.Analysis.KadisonKastler.FreeDiagonalBlockModel

namespace OAI

/-! # The complementary centered block vanishes on reduced words -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {r d : ℕ} [NeZero d] (τ : FaithfulTracialState B) (e : Fin r → Fin d → B)

local notation "J" => traceStateVector τ
local notation "π" => traceStateRepresentation τ

theorem centered_compression_word_zero
    (hp : ∀ i a, IsStarProjection (e i a)) (hs : ∀ i, ∑ a, e i a = 1)
    (hf : ScalarFreeDiagonal τ e) (i : Fin r) (a : Fin d)
    {w : List (Fin r × Fin d)} (hw : ReducedDiagonalWord w) :
    ((1 - leadingDiagonalProjection τ e i) * π (diagonalCentered e i a) *
      (1 - leadingDiagonalProjection τ e i)) (J (diagonalWord e w)) = 0 := by
  let P := leadingDiagonalProjection τ e i
  have hpword {v : List (Fin r × Fin d)} (hv : ReducedDiagonalWord ((i, a) :: v)) :
      P (J (diagonalWord e ((i, a) :: v))) = J (diagonalWord e ((i, a) :: v)) :=
    Submodule.starProjection_eq_self_iff.mpr (diagonalWord_mem_leadingDiagonalSpace τ e i a hv)
  cases w with
  | nil =>
    have hP : P (J 1) = 0 := leadingDiagonalProjection_vacuum τ e hs hf i
    have hQ := hpword (v := []) (List.IsChain.singleton (i, a))
    change (1 - P) (π (diagonalCentered e i a) ((1 - P) (J 1))) = 0
    simp only [sub_apply, one_apply_eq_self, hP, sub_zero,
      traceStateRepresentation_vector, mul_one]
    simpa using sub_eq_zero.mpr hQ.symm
  | cons b w =>
    rcases b with ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      have hP : P (J (diagonalWord e ((i, b) :: w))) = J (diagonalWord e ((i, b) :: w)) :=
        Submodule.starProjection_eq_self_iff.mpr (diagonalWord_mem_leadingDiagonalSpace τ e i b hw)
      change (1 - P) (π (diagonalCentered e i a) ((1 - P) _)) = 0
      simp only [sub_apply, one_apply_eq_self, hP, sub_self,
        map_zero]
    · have hP : P (J (diagonalWord e ((j, b) :: w))) = 0 :=
        leadingDiagonalProjection_other τ e hp hs hf hij
          (diagonalWord_mem_leadingDiagonalSpace τ e j b hw)
      have hnew : ReducedDiagonalWord ((i, a) :: (j, b) :: w) :=
        List.isChain_cons.mpr ⟨by simpa using hij, hw⟩
      have hQ := hpword hnew
      change (1 - P) (π (diagonalCentered e i a) ((1 - P) _)) = 0
      simp only [sub_apply, one_apply_eq_self, hP, sub_zero,
        traceStateRepresentation_vector]
      simpa only [diagonalWord_cons] using sub_eq_zero.mpr hQ.symm

theorem centered_compression_zero
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (hs : ∀ i, ∑ a, e i a = 1) (hf : ScalarFreeDiagonal τ e)
    (hgen : generatedDiagonal e = ⊤) (i : Fin r) (a : Fin d) :
    (1 - leadingDiagonalProjection τ e i) * π (diagonalCentered e i a) *
      (1 - leadingDiagonalProjection τ e i) = 0 := by
  let T := (1 - leadingDiagonalProjection τ e i) * π (diagonalCentered e i a) *
    (1 - leadingDiagonalProjection τ e i)
  have hsT : diagonalWordVectorSpan τ e ≤ T.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    exact centered_compression_word_zero τ e hp hs hf i a hw
  have ht := (diagonalWordVectorSpan τ e).topologicalClosure_minimal hsT T.isClosed_ker
  rw [diagonalWordVectorSpan_total τ e hp ho hgen] at ht
  apply ContinuousLinearMap.ext
  intro x
  exact ht (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ (TraceStateHilbert τ)))

/-- The faithful GNS action has the complete structural Fock model once the
finite diagonal family generates its algebra. -/
def tracialDiagonalFockModel
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (hs : ∀ i, ∑ a, e i a = 1) (hf : ScalarFreeDiagonal τ e)
    (hgen : generatedDiagonal e = ⊤) :
    FreeDiagonalModel (Fin r) (Fin d) (TraceStateHilbert τ) :=
  freeDiagonalModel_of_leadingProjections (fun i a => π (e i a))
    (fun i a => (hp i a).map π)
    (fun i a b hab => by rw [← map_mul, ho i a b hab, map_zero])
    (fun i => by rw [← map_sum, hs i, map_one])
    (leadingDiagonalProjection τ e) (leadingDiagonalProjection_isProjection τ e)
    (fun _ _ hij => leadingDiagonalProjection_mul_of_ne τ e hp hs hf hij)
    (fun i a => by
      have he : diagonalCentered (fun i a => π (e i a)) i a = π (diagonalCentered e i a) := by
        simp only [diagonalCentered, map_sub, map_smul, map_one]
      rw [he]
      exact centered_compression_zero τ e hp ho hs hf hgen i a)

end

end KadisonKastler

end OAI
