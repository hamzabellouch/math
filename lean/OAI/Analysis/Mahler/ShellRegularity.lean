import OAI.Analysis.Mahler.CoordinateAnnulus

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

def coordClosedBall (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) := {x | radiusSq x ≤ R^2}

lemma continuous_radiusSq (n : ℕ) : Continuous (radiusSq (n := n)) := by
  unfold radiusSq; fun_prop

lemma isCompact_coordClosedBall (n : ℕ) (R : ℝ) : IsCompact (coordClosedBall n R) := by
  have hs : coordClosedBall n R ⊆ Icc (fun _ => -|R|) (fun _ => |R|) := by
    intro x hx
    have hi (i : Fin n) : |x i| ≤ |R| := by
      have hsum : x i ^ 2 ≤ radiusSq x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have hx' : radiusSq x ≤ R^2 := hx
      nlinarith [sq_abs (x i), sq_abs R, abs_nonneg (x i), abs_nonneg R]
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_le (continuous_radiusSq n) continuous_const) hs

lemma isCompact_closedShell (n : ℕ) (a R : ℝ) : IsCompact (closedShell n a R) := by
  apply (isCompact_coordClosedBall n R).of_isClosed_subset
  · exact (isClosed_le continuous_const (continuous_radiusSq n)).inter
      (isClosed_le (continuous_radiusSq n) continuous_const)
  · intro x hx; exact hx.2

lemma coordAnnulus_subset_shell (n : ℕ) (a R : ℝ) :
    coordAnnulus n a R ⊆ closedShell n a R := by
  intro x hx
  exact ⟨le_of_not_gt hx.2, hx.1.le⟩

lemma integrableOn_shell_annulus {n : ℕ} {a R : ℝ} {g : (Fin n → ℝ) → ℝ}
    (hg : ContinuousOn g (closedShell n a R)) : IntegrableOn g (coordAnnulus n a R) :=
  (hg.integrableOn_compact (isCompact_closedShell n a R)).mono_set (coordAnnulus_subset_shell n a R)

lemma radiusSq_boundary {n : ℕ} (i : Fin (n+1)) (R : ℝ) {y : Fin n → ℝ}
    (hy : y ∈ coordClosedBall n R) :
    radiusSq (i.insertNth (chord R y) y) = R^2 ∧
    radiusSq (i.insertNth (-chord R y) y) = R^2 := by
  have hc : (chord R y)^2 = R^2 - radiusSq y := Real.sq_sqrt (sub_nonneg.mpr hy)
  simp only [radiusSq_insertNth, neg_sq]
  constructor <;> linarith

/-- Boundary integrability follows from ordinary continuity on the sphere. -/
lemma integrable_boundary_difference {n : ℕ} (i : Fin (n+1)) (R : ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContinuousOn f {x | radiusSq x = R^2}) :
    Integrable (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) := by
  have hch : Continuous (chord (n := n) R) := by
    unfold chord; exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_radiusSq n))
  have htop : ContinuousOn (fun y : Fin n → ℝ => f (i.insertNth (chord R y) y)) (coordClosedBall n R) :=
    hf.comp (by fun_prop) (fun y hy => (radiusSq_boundary i R hy).1)
  have hbot : ContinuousOn (fun y : Fin n → ℝ => f (i.insertNth (-chord R y) y)) (coordClosedBall n R) :=
    hf.comp (by fun_prop) (fun y hy => (radiusSq_boundary i R hy).2)
  have hint : IntegrableOn (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) (coordBall n R) :=
    ((htop.sub hbot).integrableOn_compact (isCompact_coordClosedBall n R)).mono_set (fun x hy => (show radiusSq x < R^2 from hy).le)
  have he : (coordBall n R).indicator (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) =
      (fun y : Fin n → ℝ => f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) := by
    funext y
    by_cases hy : y ∈ coordBall n R
    · simp [hy]
    · simp [hy, boundary_difference_zero i R f hy]
  rw [← he]
  exact hint.integrable_indicator (measurableSet_coordBall n R)

/-- The annulus identity under local C1 assumptions only; integrability of
both volume and boundary terms is proved, not assumed. -/
theorem integral_partial_annulus_of_C1 {n : ℕ} (i : Fin (n+1)) {a R : ℝ}
    (haR : a^2 ≤ R^2) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ x ∈ closedShell (n+1) a R, DifferentiableAt ℝ f x)
    (hg : ContinuousOn (fun x => fderiv ℝ f x (Pi.single i 1)) (closedShell (n+1) a R)) :
    (∫ x in coordAnnulus (n+1) a R, fderiv ℝ f x (Pi.single i 1)) =
      (∫ y in coordBall n R, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) -
      ∫ y in coordBall n a, f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y) := by
  have hc : ContinuousOn f (closedShell (n+1) a R) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  apply integral_partial_coordAnnulus i haR f hf hg (integrableOn_shell_annulus hg)
  · apply integrable_boundary_difference
    exact hc.mono (fun x hx => ⟨hx ▸ haR, hx.le⟩)
  · apply integrable_boundary_difference
    exact hc.mono (fun x hx => ⟨hx.ge, hx ▸ haR⟩)

/-- Full divergence with the inner sphere oriented outward from its own ball.
Its flux consequently occurs with a minus sign. -/
theorem integral_divergence_annulus_of_C1 {n : ℕ} {a R : ℝ} (haR : a^2 ≤ R^2)
    (F : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hF : ∀ i x, x ∈ closedShell (n+1) a R → DifferentiableAt ℝ (F i) x)
    (hD : ∀ i, ContinuousOn (fun x => fderiv ℝ (F i) x (Pi.single i 1)) (closedShell (n+1) a R)) :
    (∫ x in coordAnnulus (n+1) a R, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) =
      (∑ i, ∫ y in coordBall n R,
        F i (i.insertNth (chord R y) y) - F i (i.insertNth (-chord R y) y)) -
      ∑ i, ∫ y in coordBall n a,
        F i (i.insertNth (chord a y) y) - F i (i.insertNth (-chord a y) y) := by
  rw [integral_finsetSum _ (fun i _ => integrableOn_shell_annulus (hD i)), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => integral_partial_annulus_of_C1 i haR (F i) (hF i) (hD i))

end MahlerStokes

end

end OAI
