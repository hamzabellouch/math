import OAI.Probability.InvariantIsing.Fields.FieldTiltDerivative

namespace OAI

/-! Differentiation of the scalar tilted spin average. The potential
needs an exponential moment at the base point, rather than a global bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma parameter_exp_bound (U DU : ℝ → ℝ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hDU : ∀ s u, |DU s u| ≤ C)
    (hd : ∀ s u, HasDerivAt (fun q => U q u) (DU s u) s)
    (ζ x s u : ℝ) (hs : s ∈ Ioo (x - 1) (x + 1)) :
    Real.exp (ζ * U s u) ≤ Real.exp (|ζ| * C) * Real.exp (ζ * U x u) := by
  have hdiff : |U s u - U x u| ≤ C * |s - x| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun q (_ : q ∈ (univ : Set ℝ)) => (hd q u).hasDerivWithinAt)
        (fun q _ => by simpa only [Real.norm_eq_abs] using hDU q u)
        convex_univ (mem_univ x) (mem_univ s)
  have hdist : |s - x| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h1 := hdiff.trans (mul_le_of_le_one_right hC hdist)
  have h2 : ζ * (U s u - U x u) ≤ |ζ| * C :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg ζ))
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem hasDerivAt_tiltAverage_of_bounded_derivatives
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A DU DA : ℝ → ℝ → ℝ)
    (hU : ∀ s, Measurable (U s)) (hA : ∀ s, Measurable (A s))
    (hDU : ∀ s, Measurable (DU s)) (hDA : ∀ s, Measurable (DA s))
    {C M L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbDU : ∀ s u, |DU s u| ≤ C) (hbA : ∀ s u, |A s u| ≤ M)
    (hbDA : ∀ s u, |DA s u| ≤ L)
    (dU : ∀ s u, HasDerivAt (fun q => U q u) (DU s u) s)
    (dA : ∀ s u, HasDerivAt (fun q => A q u) (DA s u) s)
    (ζ x : ℝ) (hi : Integrable (fun u => Real.exp (ζ * U x u)) μ) :
    HasDerivAt (fun s => ∫ u, A s u ∂μ.tilted (fun u => ζ * U s u))
      ((∫ u, DA x u ∂μ.tilted (fun u => ζ * U x u)) +
        ζ * ((∫ u, A x u * DU x u ∂μ.tilted (fun u => ζ * U x u)) -
          (∫ u, A x u ∂μ.tilted (fun u => ζ * U x u)) *
            (∫ u, DU x u ∂μ.tilted (fun u => ζ * U x u)))) x := by
  have hS : Ioo (x - 1) (x + 1) ∈ 𝓝 x :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hE (s u : ℝ) (hs : s ∈ Ioo (x - 1) (x + 1)) :=
    parameter_exp_bound U DU hC hbDU dU ζ x s u hs
  have hAD (s u : ℝ) : |A s u * DU s u| ≤ M * C := by
    rw [abs_mul]
    exact mul_le_mul (hbA s u) (hbDU s u) (abs_nonneg _) hM
  have hprod {G : ℝ → ℝ} (hm : Measurable G) {K : ℝ} (hb : ∀ u, |G u| ≤ K) :
      Integrable (fun u => Real.exp (ζ * U x u) * G u) μ :=
    hi.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hb u)
  have hiA := hprod (hA x) (hbA x)
  have hiDA := hprod (hDA x) (hbDA x)
  have hiAD := hprod ((hA x).mul (hDU x)) (hAD x)
  change Integrable (fun u => Real.exp (ζ * U x u) * (A x u * DU x u)) μ at hiAD
  have hdDen (s u : ℝ) := ((dU s u).const_mul ζ).exp
  have hdNum (s u : ℝ) :
      HasDerivAt (fun q => Real.exp (ζ * U q u) * A q u)
        (Real.exp (ζ * U s u) * DA s u +
          ζ * (Real.exp (ζ * U s u) * (A s u * DU s u))) s := by
    convert (hdDen s u).mul (dA s u) using 1
    ring
  obtain ⟨_, hden⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun s => ((hU s).const_mul ζ).exp.aestronglyMeasurable) hi
    (((hU x).const_mul ζ).exp.mul ((hDU x).const_mul ζ)).aestronglyMeasurable
    (ae_of_all _ fun u s hs => by
      change |Real.exp (ζ * U s u) * (ζ * DU s u)| ≤ _
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
      calc
        _ ≤ (Real.exp (|ζ| * C) * Real.exp (ζ * U x u)) * (|ζ| * C) :=
          mul_le_mul (hE s u hs) (mul_le_mul_of_nonneg_left (hbDU s u) (abs_nonneg ζ))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
        _ = (Real.exp (|ζ| * C) * (|ζ| * C)) * Real.exp (ζ * U x u) := by ring)
    (hi.const_mul (Real.exp (|ζ| * C) * (|ζ| * C)))
    (ae_of_all _ fun u s _ => hdDen s u)
  obtain ⟨_, hnum⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun s => (((hU s).const_mul ζ).exp.mul (hA s)).aestronglyMeasurable)
    hiA ((((hU x).const_mul ζ).exp.mul (hDA x)).add
      ((((hU x).const_mul ζ).exp.mul ((hA x).mul (hDU x))).const_mul ζ)).aestronglyMeasurable
    (ae_of_all _ fun u s hs => by
      change |Real.exp (ζ * U s u) * DA s u +
        ζ * (Real.exp (ζ * U s u) * (A s u * DU s u))| ≤ _
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (Real.exp (|ζ| * C) * Real.exp (ζ * U x u)) * L +
            |ζ| * ((Real.exp (|ζ| * C) * Real.exp (ζ * U x u)) * (M * C)) :=
          add_le_add (mul_le_mul (hE s u hs) (hbDA s u) (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left
              (mul_le_mul (hE s u hs) (hAD s u) (abs_nonneg _) (by positivity)) (abs_nonneg ζ))
        _ = (Real.exp (|ζ| * C) * (L + |ζ| * (M * C))) *
            Real.exp (ζ * U x u) := by ring)
    (hi.const_mul (Real.exp (|ζ| * C) * (L + |ζ| * (M * C))))
    (ae_of_all _ fun u s _ => hdNum s u)
  have hp := IsingPerceptron.integral_exp_pos μ (U x) hi
  simp only [Pi.mul_apply] at hnum
  have hde : (∫ u, Real.exp (ζ * U x u) * (ζ * DU x u) ∂μ) =
      ζ * ∫ u, Real.exp (ζ * U x u) * DU x u ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have hne : (∫ u, Real.exp (ζ * U x u) * DA x u +
      ζ * (Real.exp (ζ * U x u) * (A x u * DU x u)) ∂μ) =
      (∫ u, Real.exp (ζ * U x u) * DA x u ∂μ) +
        ζ * ∫ u, Real.exp (ζ * U x u) * (A x u * DU x u) ∂μ := by
    rw [integral_add hiDA (hiAD.const_mul ζ), integral_const_mul]
  convert hnum.div hden hp.ne' using 1
  · funext s
    exact integral_tilted_eq_div _ _ _
  · simp only [integral_tilted_eq_div]
    rw [hde, hne]
    field_simp
    ring

end InvariantIsing

end

end OAI
