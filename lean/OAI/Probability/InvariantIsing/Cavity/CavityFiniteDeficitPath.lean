import OAI.Probability.InvariantIsing.Cavity.CavityFiniteFieldVariance
import OAI.Probability.InvariantIsing.Fields.FieldPublishedEvaluation

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

def cavityFiniteLevel (n i : ℕ) : Fin (n + 1) :=
  ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

@[simp] lemma cavityFiniteLevel_zero (n : ℕ) : cavityFiniteLevel n 0 = 0 := by
  apply Fin.ext
  exact Nat.zero_min _

@[simp] lemma cavityFiniteLevel_last (n : ℕ) : cavityFiniteLevel n n = Fin.last n := by
  apply Fin.ext
  exact min_self _

lemma cavityFiniteLevel_castSucc {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n i = i.castSucc := by
  apply Fin.ext
  exact min_eq_left i.isLt.le

lemma cavityFiniteLevel_succ {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n (i + 1) = i.succ := by
  apply Fin.ext
  exact min_eq_left i.isLt

lemma cavityFiniteLevel_monotone (n : ℕ) : Monotone (cavityFiniteLevel n) := by
  intro i j hij
  exact min_le_min_right n hij

def cavityFiniteDeficitPath {n : ℕ} (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (i : ℕ) : ℝ := deficit p (q (cavityFiniteLevel n i))

lemma cavityFiniteDeficitPath_antitone {n : ℕ} (p : OverlapPath)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) : Antitone (cavityFiniteDeficitPath p q) :=
  (deficit_antitone_argument p).comp_monotone (hq.comp (cavityFiniteLevel_monotone n))

lemma cavityFiniteDeficitPath_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : ℕ) : 0 < cavityFiniteDeficitPath p q i :=
  finite_overlap_deficit_pos p cut hfirst hlast q hq hp htop (hq (Fin.le_last _))

lemma cavityFiniteDeficitPath_step {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    cavityFiniteDeficitPath p q i - cavityFiniteDeficitPath p q (i + 1) =
      chainExponent cut i * (q i.succ - q i.castSucc) := by
  have he := finite_overlap_deficit_increment p cut hcut hfirst hlast q hq hp i
    ⟨(hq (Fin.castSucc_lt_succ (i := i))).le, le_rfl⟩
  simp only [cavityFiniteDeficitPath, cavityFiniteLevel_castSucc, cavityFiniteLevel_succ,
    chainExponent_apply cut i.isLt]
  have hc : cut i.succ.castSucc = cut ⟨i + 1, by omega⟩ := congrArg cut (Fin.ext rfl)
  rw [hc] at he
  linarith

lemma cavityFiniteDeficitPath_step_strict {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) : cavityFiniteDeficitPath p q (i + 1) < cavityFiniteDeficitPath p q i := by
  have hc : 0 < chainExponent cut i := by
    rw [chainExponent_apply cut i.isLt, ← hfirst]
    apply hcut
    change 0 < i.val + 1
    omega
  apply sub_pos.mp
  rw [cavityFiniteDeficitPath_step p cut hcut hfirst hlast q hq hp i]
  exact mul_pos hc (sub_pos.mpr (hq (Fin.castSucc_lt_succ (i := i))))

lemma finite_chainExponent_pos {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hcut : StrictMono cut) (hfirst : cut 0 = 0) (i : ℕ) : 0 < chainExponent cut i := by
  unfold chainExponent
  rw [← hfirst]
  apply hcut
  change 0 < min (i + 1) (n + 1)
  omega

lemma field_chainExponent_pos (h : FieldStep) (i : ℕ) : 0 < chainExponent h.cut i :=
  finite_chainExponent_pos h.cut h.ordered_cut h.first i

end InvariantIsing

end

end OAI
