import Mathlib
import OAI.Combinatorics.ThinTrees.Signing.GramWhitening
import OAI.Combinatorics.ThinTrees.Signing.StackedSigning

namespace OAI

/-! Form signing. -/

section

namespace AlgorithmicThinTrees.FormSigning
open Matrix Finset GramWhitening StackedSigning RationalSigning
open scoped MatrixOrder
variable {a b m : ℕ}

def whiten (P : Matrix (Fin a) (Fin a) ℚ) (v : Fin m → Fin a → ℚ) :=
  fun e => (rationalFactor P)ᵀ*ᵥv e

lemma whiten_cast (P : Matrix (Fin a) (Fin a) ℚ) (v : Fin m → Fin a → ℚ) (e : Fin m) :
    realVec (whiten P v) e=((rationalFactor P).map (fun q : ℚ => (q:ℝ)))ᵀ*ᵥrealVec v e := by
  ext i
  simp only [whiten,realVec,mulVec,dotProduct,transpose_apply,map_apply,Rat.cast_sum,Rat.cast_mul]

lemma whiten_covariance (P : Matrix (Fin a) (Fin a) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) (v : Fin m → Fin a → ℚ)
    (hv : StackedSigning.gram (realVec v) univ ≤ P.map (fun q : ℚ => (q:ℝ))) :
    StackedSigning.gram (realVec (whiten P v)) univ ≤ 1 := by
  simpa only [StackedSigning.gram,whiten_cast] using
    cov_bound _ hP _ (rationalFactor_correct P hP) (realVec v) hv

lemma whiten_norm (P : Matrix (Fin a) (Fin a) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) (v : Fin m → Fin a → ℚ) (e : Fin m) :
    realVec (whiten P v) e ⬝ᵥ realVec (whiten P v) e=
      realVec v e ⬝ᵥ ((P.map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec v e) := by
  rw [whiten_cast,rectangular_norm,rationalFactor_correct P hP]

def selected (P : Matrix (Fin a) (Fin a) ℚ) (Q : Matrix (Fin b) (Fin b) ℚ)
    (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) : Finset (Fin m) :=
  StackedSigning.selected (whiten P u) (whiten Q v)

theorem simultaneous (P : Matrix (Fin a) (Fin a) ℚ) (Q : Matrix (Fin b) (Fin b) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) (hQ : (Q.map (fun q : ℚ => (q:ℝ))).PosDef)
    (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : StackedSigning.gram (realVec u) univ ≤ P.map (fun q : ℚ => (q:ℝ)))
    (hv : StackedSigning.gram (realVec v) univ ≤ Q.map (fun q : ℚ => (q:ℝ)))
    (hnorm : ∀e, realVec u e ⬝ᵥ ((P.map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec u e)+
      realVec v e ⬝ᵥ ((Q.map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec v e) ≤ δ) :
    let A := selected P Q u v
    let ε := 20*Real.sqrt (2*δ)
    (-(ε • P.map (fun q : ℚ => (q:ℝ))) ≤
        StackedSigning.gram (realVec u) A-(1/2:ℝ) • StackedSigning.gram (realVec u) univ ∧
      StackedSigning.gram (realVec u) A-(1/2:ℝ) • StackedSigning.gram (realVec u) univ ≤ ε • P.map (fun q : ℚ => (q:ℝ))) ∧
    (-(ε • Q.map (fun q : ℚ => (q:ℝ))) ≤
        StackedSigning.gram (realVec v) A-(1/2:ℝ) • StackedSigning.gram (realVec v) univ ∧
      StackedSigning.gram (realVec v) A-(1/2:ℝ) • StackedSigning.gram (realVec v) univ ≤ ε • Q.map (fun q : ℚ => (q:ℝ))) := by
  have h := StackedSigning.simultaneous (whiten P u) (whiten Q v) hδ
    (whiten_covariance P hP u hu) (whiten_covariance Q hQ v hv)
    (fun e => by simpa only [whiten_norm P hP,whiten_norm Q hQ] using hnorm e)
  constructor
  · exact transfer _ hP _ (rationalFactor_correct P hP) (realVec u) (selected P Q u v)
      (by simpa only [StackedSigning.gram,whiten_cast,selected] using h.1)
  · exact transfer _ hQ _ (rationalFactor_correct Q hQ) (realVec v) (selected P Q u v)
      (by simpa only [StackedSigning.gram,whiten_cast,selected] using h.2)

lemma gram_restrict {d : ℕ} (v : Fin m → Fin d → ℝ) (B A : Finset (Fin m))
    (h : ∀e, e ∉ B → v e=0) : StackedSigning.gram v (A∩B)=StackedSigning.gram v A := by
  unfold StackedSigning.gram
  apply sum_subset_zero_on_sdiff inter_subset_left
  · intro e he
    obtain ⟨he,he'⟩ := mem_sdiff.mp he
    have hb : e ∉ B := fun hb => he' (mem_inter.mpr ⟨he,hb⟩)
    rw [h e hb,zero_vecMulVec]
  · intros; rfl

end AlgorithmicThinTrees.FormSigning
end

end OAI
