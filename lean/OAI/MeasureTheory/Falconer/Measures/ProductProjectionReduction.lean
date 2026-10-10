import OAI.MeasureTheory.Falconer.Geometry.CommonSmallProjections
import OAI.MeasureTheory.Falconer.Estimates.RowRegularity

namespace OAI

/-! The geometric product configuration yields a single regular parameter
set and many large subsets with small projections. This is the preparation
for the strict projection gain in Orponen--Shmerkin, Proposition A.7. -/
namespace Falconer

theorem product_projection_reduction (Y : Finset ℝ) (hY : Y.Nonempty)
    (P : ℝ → Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    {δ s KP KT n m M R : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s)
    (hKP : 0 ≤ KP) (hKT : 0 ≤ KT) (hn : 0 < n) (hm : 0 < m)
    (hM : 0 ≤ M) (hR : 0 < R) (NP : ℕ)
    (hrows : ∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
      NormalizedFiniteBallBound δ s KP (P y) ∧
      n ≤ ((P y).card : ℝ) ∧ (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y)
    (hpencils : ∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound δ s KT (T x) ∧
      m ≤ ((T x).card : ℝ) ∧ ((T x).card : ℝ) ≤ M ∧
      ∀ l ∈ T x, TubeIncident δ x l)
    (hunion : ((Y.biUnion fun y => (P y).biUnion T).card : ℝ) ≤ R*(n*m/25)) :
    let A := fun y => (P y).biUnion T
    let Krow := (4 : ℝ)^(2*s)+25*KP*KT*(M/m)*(4 : ℝ)^s
    ∃ G ⊆ Y.biUnion A, G.Nonempty ∧ (n*m/25)/2 ≤ (G.card : ℝ) ∧
      NormalizedFiniteBallBound δ (2*s) (4*R^2*Krow) G ∧
      ∃ Z ⊆ Y, Z.Nonempty ∧ (Y.card : ℝ) ≤ 4*R*(Z.card : ℝ) ∧
        ∀ y ∈ Z, (n*m/25)/4 ≤ ((G ∩ A y).card : ℝ) ∧
          (projectionCells δ y (G ∩ A y)).card ≤ 7*NP := by
  let A := fun y => (P y).biUnion T
  let Krow := (4 : ℝ)^(2*s)+25*KP*KT*(M/m)*(4 : ℝ)^s
  have hKrow : 0 ≤ Krow := by dsimp [Krow]; positivity
  have hsize (y : ℝ) (hy : y ∈ Y) : n*m/25 ≤ ((A y).card : ℝ) := by
    have hr := hrows y hy
    have hb := row_tube_union_count hδ hr.2.1 hr.2.2.2.2.2 T
      (fun x hx => (hpencils y hy x hx).1)
      (fun x hx => (hpencils y hy x hx).2.2.2.2)
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 25)).2
    calc
      n*m ≤ ((P y).card : ℝ)*m := mul_le_mul_of_nonneg_right hr.2.2.2.1 hm.le
      _ = ∑ _x ∈ P y, m := by simp
      _ ≤ ∑ x ∈ P y, ((T x).card : ℝ) :=
        Finset.sum_le_sum fun x hx => (hpencils y hy x hx).2.2.1
      _ ≤ _ := by simpa only [mul_comm] using hb
  have hregular (y : ℝ) (hy : y ∈ Y) : NormalizedFiniteBallBound δ (2*s) Krow (A y) := by
    have hr := hrows y hy
    exact row_tube_union_regular hδ hs hr.1 hKP hKT hm hM hr.2.1 hr.2.2.2.2.2 hr.2.2.1 T
      (fun x hx => (hpencils y hy x hx).1)
      (fun x hx => (hpencils y hy x hx).2.1)
      (fun x hx => ⟨(hpencils y hy x hx).2.2.1,(hpencils y hy x hx).2.2.2.1⟩)
      (fun x hx => (hpencils y hy x hx).2.2.2.2)
  have hproj (y : ℝ) (hy : y ∈ Y) : (projectionCells δ y (A y)).card ≤ 7*NP := by
    have hr := hrows y hy
    exact (projectionCells_row_count hδ hr.2.2.2.2.2 T
      (fun x hx => (hpencils y hy x hx).1)
      (fun x hx => (hpencils y hy x hx).2.2.2.2)).trans
        (Nat.mul_le_mul_left 7 hr.2.2.2.2.1)
  exact common_regular_small_projections Y hY A id hδ.le hKrow
    (by positivity : 0 < n*m/25) hR hsize hunion hregular (7*NP) hproj

end Falconer

end OAI
