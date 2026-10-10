import OAI.Analysis.CircleDomains.Topology.OrderedCollarLift

namespace OAI

/-! Uniform control of a fixed smooth weight on the inward collar. The
smooth collar's continuous tangent gives a common variation bound before
the smoothing accuracy for the mean coordinate is chosen. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem RegularJordanInwardCollar.scalar_uniform_approach
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {O : Set ℂ} (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContinuousOn Φ O) :
    ∀ ε > 0, ∃ η > 0, η ≤ C.width ∧ ∀ ρ ∈ Icc 0 η, ∀ t : ℝ,
      |Φ (C.curve ρ t) - Φ (C.curve 0 t)| < ε := by
  obtain ⟨ζ, hζ, hζw, hinside⟩ := C.eventually_in_boundary_neighborhood hO hCO
  let K : Set (ℝ × ℝ) := Icc 0 ζ ×ˢ Icc 0 1
  have hsub : K ⊆ Icc 0 C.width ×ˢ (univ : Set ℝ) := fun p hp =>
    ⟨⟨hp.1.1, hp.1.2.trans hζw⟩, mem_univ _⟩
  have hc : ContinuousOn (fun p : ℝ × ℝ => Φ (C.curve p.1 p.2)) K :=
    hΦ.comp (C.continuous.mono hsub) (fun p hp => hinside p.1 hp.1 p.2 hp.2)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let η := min ζ (d / 2)
  have hη : 0 < η := lt_min hζ (half_pos hd)
  have hηζ : η ≤ ζ := min_le_left _ _
  refine ⟨η, hη, hηζ.trans hζw, ?_⟩
  intro ρ hρ t
  have hρζ : ρ ∈ Icc (0 : ℝ) ζ := ⟨hρ.1, hρ.2.trans hηζ⟩
  have ht : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hb := hdist (ρ, Int.fract t) ⟨hρζ, ht⟩ (0, Int.fract t) ⟨⟨le_rfl, hζ.le⟩, ht⟩
    (show dist (ρ, Int.fract t) (0, Int.fract t) < d by
      rw [Prod.dist_eq, dist_self, max_eq_left (show (0 : ℝ) ≤ dist ρ 0 from dist_nonneg),
        Real.dist_eq, sub_zero, abs_of_nonneg hρ.1]
      exact hρ.2.trans_lt ((min_le_right ζ (d / 2)).trans_lt (half_lt_self hd)))
  have heρ : C.curve ρ (Int.fract t) = C.curve ρ t := by
    simpa only [Int.fract, mul_one] using
      (C.parametrization ρ ⟨hρ.1, hρζ.2.trans hζw⟩).periodic.sub_int_mul_eq (x := t) ⌊t⌋
  have he0 : C.curve 0 (Int.fract t) = C.curve 0 t := by
    simpa only [Int.fract, mul_one] using
      (C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩).periodic.sub_int_mul_eq (x := t) ⌊t⌋
  simpa only [heρ, he0, Real.dist_eq] using hb

 theorem abs_deriv_oriented (f : ℝ → ℝ) (a : ℝ) (reverse : Bool) (t : ℝ) :
    |deriv (f ∘ orientedParameter a reverse) t| = |deriv f (orientedParameter a reverse t)| := by
  cases reverse
  · exact congrArg abs (deriv_comp_const_add f a t)
  · change |deriv (fun s => (fun x => f (a + x)) (1 - s)) t| = _
    rw [deriv_comp_const_sub (fun x => f (a + x)) 1 t, abs_neg, deriv_comp_const_add]
    rfl

 theorem real_deriv_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → ℝ => deriv g t) (funext hp)

 theorem RegularJordanInwardCollar.scalar_derivative_bound
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {O : Set ℂ} (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O) :
    ∃ (ζ B : ℝ), 0 < ζ ∧ ζ ≤ C.width ∧ 0 ≤ B ∧
      ∀ ρ ∈ Icc 0 ζ, ∀ (a : ℝ) (reverse : Bool) (t : ℝ),
        |deriv (Φ ∘ C.curve ρ ∘ orientedParameter a reverse) t| ≤ B := by
  obtain ⟨ζ, hζ, hζw, hinside⟩ := C.eventually_in_boundary_neighborhood hO hCO
  let K : Set (ℝ × ℝ) := Icc 0 ζ ×ˢ Icc 0 1
  have hsub : K ⊆ Icc 0 C.width ×ˢ (univ : Set ℝ) := fun p hp =>
    ⟨⟨hp.1.1, hp.1.2.trans hζw⟩, mem_univ _⟩
  have hf : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ Φ (C.curve p.1 p.2)) K :=
    ((hΦ.fderiv_of_isOpen (m := 0) hO (by simp)).continuousOn).comp
      (C.continuous.mono hsub) (fun p hp => hinside p.1 hp.1 p.2 hp.2)
  have hc := hf.clm_apply (C.tangent_continuous.mono hsub)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (0, 0) ⟨⟨le_rfl, hζ.le⟩, ⟨le_rfl, zero_le_one⟩⟩)
  refine ⟨ζ, B, hζ, hζw, hB0, ?_⟩
  intro ρ hρ a reverse t
  let s := orientedParameter a reverse t
  have hρw : ρ ∈ Icc (0 : ℝ) C.width := ⟨hρ.1, hρ.2.trans hζw⟩
  have hper : Function.Periodic (deriv (Φ ∘ C.curve ρ)) 1 :=
    real_deriv_periodic ((C.parametrization ρ hρw).periodic.comp Φ)
  have he : deriv (Φ ∘ C.curve ρ) (Int.fract s) = deriv (Φ ∘ C.curve ρ) s := by
    simpa only [Int.fract, mul_one] using hper.sub_int_mul_eq (x := s) ⌊s⌋
  change |deriv ((Φ ∘ C.curve ρ) ∘ orientedParameter a reverse) t| ≤ B
  rw [abs_deriv_oriented (Φ ∘ C.curve ρ) a reverse t]
  change |deriv (Φ ∘ C.curve ρ) s| ≤ B
  rw [← he]
  have hs : Int.fract s ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hd : deriv (Φ ∘ C.curve ρ) (Int.fract s) =
      (fderiv ℝ Φ (C.curve ρ (Int.fract s))) (deriv (C.curve ρ) (Int.fract s)) := by
    exact (((hΦ.contDiffAt (hO.mem_nhds (hinside ρ hρ _ hs))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt _
      (((C.parametrization ρ hρw).smooth.differentiable (by simp) _).hasDerivAt)).deriv
  rw [hd]
  simpa only [Real.norm_eq_abs] using hB (ρ, Int.fract s) ⟨hρ, hs⟩

end CircleDomainRigidity

end

end OAI
