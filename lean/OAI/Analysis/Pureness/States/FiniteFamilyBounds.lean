import OAI.Analysis.Pureness.States.FiniteFamilyMetric
import OAI.Analysis.Pureness.Quasitrace.QuasitraceMatrixDiagonal

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))

lemma positiveLevel_inclusion {n m : ℕ} (h : n ≤ m) (M : Positive (FinMatrix A n)) :
    F.positiveLevel hmono m (Positive.map (matrixInclusion h) M) = F.positiveLevel hmono n M :=
  congrArg Complex.re (F.inclusion h M.1)

lemma positiveLevel_scalarMatrix (n : ℕ) (a : Positive A) :
    F.positiveLevel hmono (n+1) (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) =
      (n+1 : ℝ)*F.positiveLevel hmono 1
        (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) := by
  rw [positiveQuasitrace_scalarMatrix _ (0 : Fin (n+1)) a]
  have he : Positive.map (matrixCorner (0 : Fin (n+1))) a =
      Positive.map (matrixInclusion (show 1 ≤ n+1 from by omega))
        (Positive.map (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom a) :=
    Subtype.ext (matrixInclusion_scalar_one n a.1).symm
  rw [he,F.positiveLevel_inclusion]
  simp

lemma positiveLevel_unit (hF : F.level 1 1=1) (n : ℕ) :
    F.positiveLevel hmono n ⟨1,zero_le_one⟩ = n := by
  cases n with
  | zero =>
    have h : (1 : FinMatrix A 0) = 0 := by apply CStarMatrix.ext; intro i; exact Fin.elim0 i
    have hp : (⟨1,zero_le_one⟩ : Positive (FinMatrix A 0)) = Positive.zero := Subtype.ext h
    rw [hp,PositiveQuasitrace.map_zero,Nat.cast_zero]
  | succ n =>
    have h := F.positiveLevel_scalarMatrix hmono n ⟨1,zero_le_one⟩
    have hs (k : ℕ) : Positive.map (scalarMatrixHom (ι := Fin k)).toNonUnitalStarAlgHom
        (⟨1,zero_le_one⟩ : Positive A) = ⟨1,zero_le_one⟩ :=
      Subtype.ext (map_one (scalarMatrixHom (ι := Fin k)))
    rw [hs,hs] at h
    have h1 : F.positiveLevel hmono 1 ⟨1,zero_le_one⟩ = 1 := by
      change (F.level 1 1).re=1
      rw [hF,Complex.one_re]
    simpa only [h1,mul_one,Nat.cast_add,Nat.cast_one] using h

include hmono in
theorem unit (hF : F.level 1 1=1) (n : ℕ) : F.level n 1 = (n : ℂ) := by
  have h := (F.level n).toPositiveQuasitrace_positive (hmono n) ⟨1,zero_le_one⟩
  change ((F.positiveLevel hmono n ⟨1,zero_le_one⟩ : ℝ) : ℂ)=F.level n 1 at h
  rw [F.positiveLevel_unit hmono hF] at h
  simpa only [Complex.ofReal_natCast] using h.symm

include hmono in

theorem norm_level_le (hF : F.level 1 1=1) (n : ℕ) (x : FinMatrix A n) :
    ‖F.level n x‖ ≤ 8*(n : ℝ)*‖x‖ := by
  have h := (F.level n).norm_apply_le x
  rw [F.unit hmono hF] at h
  simpa only [Complex.norm_natCast] using h
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
