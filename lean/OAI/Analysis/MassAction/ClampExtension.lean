import Mathlib

namespace OAI

universe uIota uF

noncomputable section

namespace Problem326

/-- Coordinatewise projection onto a closed finite-dimensional box. -/
def coordinateClamp {ι : Type uIota} (a b : ι → ℝ) (hab : a ≤ b)
    (x : ι → ℝ) : ι → ℝ :=
  fun i => (Set.projIcc (a i) (b i) (hab i) (x i) : ℝ)

theorem coordinateClamp_mem {ι : Type uIota} (a b : ι → ℝ) (hab : a ≤ b)
    (x : ι → ℝ) : coordinateClamp a b hab x ∈ Set.Icc a b := by
  constructor
  · intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.1
  · intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.2

theorem coordinateClamp_eq_self {ι : Type uIota} {a b x : ι → ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) : coordinateClamp a b hab x = x := by
  funext i
  simp only [coordinateClamp, Set.projIcc_of_mem (hab i) ⟨hx.1 i, hx.2 i⟩]

theorem coordinateClamp_lipschitz {ι : Type uIota} [Fintype ι]
    (a b : ι → ℝ) (hab : a ≤ b) : LipschitzWith 1 (coordinateClamp a b hab) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  have hi : LipschitzWith 1
      (fun z : ℝ => (Set.projIcc (a i) (b i) (hab i) z : ℝ)) := by
    simpa only [one_mul, Function.comp_def] using
      (LipschitzWith.subtype_val (Set.Icc (a i) (b i))).comp
        (LipschitzWith.projIcc (hab i))
  calc
    dist (coordinateClamp a b hab x i) (coordinateClamp a b hab y i) ≤ dist (x i) (y i) := by
      simpa only [coordinateClamp, NNReal.coe_one, one_mul] using hi.dist_le_mul (x i) (y i)
    _ ≤ dist x y := dist_le_pi_dist x y i

/-- A continuously differentiable field has a globally bounded, globally
 Lipschitz extension of its restriction to any nonempty closed box.
 This permits global ODE existence to be separated from first-exit trapping. -/
theorem exists_bounded_lipschitz_extension {ι : Type uIota} {F : Type uF} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (ι → ℝ) → F} (hf : ContDiff ℝ 1 f)
    (a b : ι → ℝ) (hab : a ≤ b) :
    ∃ (g : (ι → ℝ) → F) (K : NNReal) (L : ℝ), 0 < L ∧
      LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ L) ∧ Set.EqOn g f (Set.Icc a b) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc a b) isCompact_Icc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuous.continuousOn
  refine ⟨f ∘ coordinateClamp a b hab, K, max C 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo (coordinateClamp a b hab) Set.univ (Set.Icc a b) :=
      fun x _ => coordinateClamp_mem a b hab x
    simpa only [mul_one] using lipschitzOnWith_univ.mp
      (hK.comp (coordinateClamp_lipschitz a b hab).lipschitzOnWith hmaps)
  · intro x
    exact (hC _ (coordinateClamp_mem a b hab x)).trans (le_max_left _ _)
  · intro x hx
    simp only [Function.comp_apply, coordinateClamp_eq_self hab hx]

end Problem326

end

end OAI
