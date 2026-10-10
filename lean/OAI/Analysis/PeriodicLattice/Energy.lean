import OAI.Analysis.PeriodicLattice.TorusIntegration

namespace OAI

/-! Energy inequalities and uniqueness of classical periodic solutions. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingEnergy {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace TorusCalculus

open scoped ContDiff Topology
open Filter Set MeasureTheory

section EnergyTime
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

theorem time_hasDerivAt {F : Field A} {t : ℝ} (ht : 0 < t) (q : Torus)
    (hd : DifferentiableWithinAt ℝ (fun s => F s q) (Ici 0) t) :
    HasDerivAt (fun s => F s q) (timeD F t q) t :=
  hd.hasDerivWithinAt.hasDerivAt (Ici_mem_nhds ht)

def energy (F : Field A) (t : ℝ) : ℝ := ∫ q, ‖F t q‖ ^ 2 ∂torusVolume

omit [InnerProductSpace ℝ A] in
theorem energy_nonneg (F : Field A) (t : ℝ) : 0 ≤ energy F t :=
  integral_nonneg (fun q => sq_nonneg ‖F t q‖)

omit [InnerProductSpace ℝ A] in
theorem energy_continuousOn {F : Field A} (hF : CylinderContinuous F)
    (T : ℝ) (hT : 0 ≤ T) : ContinuousOn (energy F) (Icc 0 T) :=
  continuousOn_integral_of_compact_support isCompact_univ
    ((hF T hT).norm.pow 2) (by simp)

theorem energy_hasDerivAt {F : Field A}
    (hF : CylinderContinuous F) (hDt : CylinderContinuous (timeD F))
    (hd : ∀ t : ℝ, 0 ≤ t → ∀ q,
      DifferentiableWithinAt ℝ (fun s => F s q) (Ici 0) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (energy F) (∫ q, 2 * inner ℝ (F t q) (timeD F t q) ∂torusVolume) t := by
  let G : ℝ → Torus → ℝ := fun s q => ‖F s q‖ ^ 2
  let G' : ℝ → Torus → ℝ := fun s q => 2 * inner ℝ (F s q) (timeD F s q)
  have hbody : ContinuousOn (Function.uncurry G') (Icc 0 (t + 1) ×ˢ univ) :=
    continuousOn_const.mul ((hF (t + 1) (by linarith)).inner (hDt (t + 1) (by linarith)))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hbody
  have hloc : Ioo 0 (t + 1) ∈ 𝓝 t := Ioo_mem_nhds ht (by linarith)
  have hi : Integrable (G t) torusVolume :=
    ((cylinder_slice_continuous hF ht.le).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := torusVolume)
    (F := G) (F' := G') (s := Ioo 0 (t + 1)) (x₀ := t) (bound := fun _ => C)
    hloc ?_ hi ?_ ?_ (integrable_const C) ?_).2
  · exact Filter.mem_of_superset hloc (fun s hs =>
      ((cylinder_slice_continuous hF hs.1.le).norm.pow 2).aestronglyMeasurable)
  · exact (continuous_const.mul ((cylinder_slice_continuous hF ht.le).inner
      (cylinder_slice_continuous hDt ht.le))).aestronglyMeasurable
  · exact Eventually.of_forall (fun q s hs => hC (s,q) ⟨⟨hs.1.le, hs.2.le⟩, mem_univ q⟩)
  · exact Eventually.of_forall (fun q s hs => (time_hasDerivAt hs.1 q (hd s hs.1.le q)).norm_sq)

end EnergyTime

theorem eq_zero_of_linear_deriv_bound {E E' : ℝ → ℝ} {T K : ℝ}
    (hE : ContinuousOn E (Icc 0 T))
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt E (E' s) s)
    (hbound : ∀ s ∈ Ioo 0 T, E' s ≤ K * E s)
    (hzero : E 0 = 0) (hpos : ∀ s ∈ Icc 0 T, 0 ≤ E s)
    {t : ℝ} (ht : t ∈ Icc 0 T) : E t = 0 := by
  let B : ℝ → ℝ := fun s => Real.exp (-K * s) * E s
  have hBd (s : ℝ) (hs : s ∈ Ioo 0 T) :
      HasDerivAt B (Real.exp (-K * s) * (E' s - K * E s)) s := by
    have hlinear : HasDerivAt (fun r : ℝ => -K * r) (-K) s := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (-K)
    exact (hlinear.exp.mul (hd s hs)).congr_deriv (by ring)
  have hBmono : AntitoneOn B (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hE)
    · intro s hs
      rw [interior_Icc] at hs
      exact (hBd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      change deriv B s ≤ 0
      rw [(hBd s hs).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hbound s hs))
  have he : B t ≤ B 0 := hBmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have hn : E t ≤ 0 := by
    have : Real.exp (-K * t) * E t ≤ 0 := by simpa [B, hzero] using he
    exact nonpos_of_mul_nonpos_right this (Real.exp_pos _)
  exact le_antisymm hn (hpos t ht)

end TorusCalculus

namespace TorusCalculus

open scoped ContDiff
open MeasureTheory

section Differences
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

omit [NormedSpace ℝ A] in
theorem cylinder_sub {F G : Field A} (hF : CylinderContinuous F) (hG : CylinderContinuous G) :
    CylinderContinuous (F - G) := fun T hT => (hF T hT).sub (hG T hT)

theorem timeD_sub {F G : Field A} {t : ℝ} {q : Torus}
    (hF : DifferentiableWithinAt ℝ (fun s => F s q) (Set.Ici 0) t)
    (hG : DifferentiableWithinAt ℝ (fun s => G s q) (Set.Ici 0) t) :
    timeD (F - G) t q = timeD F t q - timeD G t q := derivWithin_sub hF hG

theorem timeD_congr_nonneg {F G : Field A}
    (h : ∀ t : ℝ, 0 ≤ t → ∀ q, F t q = G t q) {t : ℝ} (ht : 0 ≤ t) (q : Torus) :
    timeD F t q = timeD G t q := by
  apply derivWithin_congr
  · intro s hs
    exact h s hs q
  · exact h t ht q

end Differences

theorem divergence_sub {F G : VectorField} {t : ℝ}
    (hF : Differentiable ℝ (spaceLift F t)) (hG : Differentiable ℝ (spaceLift G t)) (q : Torus) :
    divergence (F - G) t q = divergence F t q - divergence G t q := by
  simp only [divergence, spaceD_component (U := F - G) (hF.sub hG), spaceD_component hF,
    spaceD_component hG, spaceD_sub hF hG]
  simp only [PiLp.sub_apply, Finset.sum_sub_distrib]

theorem gradient_sub {p q : ScalarField} {t : ℝ}
    (hp : Differentiable ℝ (spaceLift p t)) (hq : Differentiable ℝ (spaceLift q t)) (x : Torus) :
    gradient (p - q) t x = gradient p t x - gradient q t x := by
  ext i
  exact spaceD_sub hp hq i x

theorem advection_sub {V U : VectorField} {t : ℝ}
    (hV : Differentiable ℝ (spaceLift V t)) (hU : Differentiable ℝ (spaceLift U t)) (q : Torus) :
    advection V t q - advection U t q = transport V (V - U) t q + transport (V - U) U t q := by
  simp only [advection, transport, spaceD_sub hV hU, Pi.sub_apply, PiLp.sub_apply,
    sub_smul, smul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

def gradientSize (U : VectorField) : ScalarField := fun t q => ∑ i : Fin 3, ‖spaceD i U t q‖

theorem gradientSize_nonneg (U : VectorField) (t : ℝ) (q : Torus) : 0 ≤ gradientSize U t q :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem gradientSize_cylinderContinuous {U : VectorField}
    (hU : ∀ i, CylinderContinuous (spaceD i U)) : CylinderContinuous (gradientSize U) := by
  intro T hT
  exact continuousOn_finsetSum Finset.univ (fun i _ => (hU i T hT).norm)

theorem transport_norm_le (W U : VectorField) (t : ℝ) (q : Torus) :
    ‖transport W U t q‖ ≤ ‖W t q‖ * gradientSize U t q := by
  unfold transport gradientSize
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le (W t q) i) (norm_nonneg _)

theorem inner_transport_bound (W U : VectorField) (t : ℝ) (q : Torus) :
    |inner ℝ (W t q) (transport W U t q)| ≤ gradientSize U t q * ‖W t q‖ ^ 2 := by
  calc
    _ ≤ ‖W t q‖ * ‖transport W U t q‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (W t q) (transport W U t q)
    _ ≤ ‖W t q‖ * (‖W t q‖ * gradientSize U t q) :=
      mul_le_mul_of_nonneg_left (transport_norm_le W U t q) (norm_nonneg _)
    _ = _ := by ring

theorem gradientSize_bounded {U : VectorField}
    (hU : ∀ i, CylinderContinuous (spaceD i U)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ q, gradientSize U t q ≤ K := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn
    (gradientSize_cylinderContinuous hU T hT)
  refine ⟨max C 0, le_max_right _ _, fun t ht q => ?_⟩
  exact (le_abs_self _).trans ((hC (t,q) ⟨ht, Set.mem_univ q⟩).trans (le_max_left _ _))

end TorusCalculus

namespace TorusCalculus

open scoped ContDiff
open MeasureTheory

theorem timeD_sub_cylinderContinuous {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F G : Field A} (hFc : CylinderContinuous (timeD F)) (hGc : CylinderContinuous (timeD G))
    (hF : ∀ t : ℝ, 0 ≤ t → ∀ q, DifferentiableWithinAt ℝ (fun s => F s q) (Set.Ici 0) t)
    (hG : ∀ t : ℝ, 0 ≤ t → ∀ q, DifferentiableWithinAt ℝ (fun s => G s q) (Set.Ici 0) t) :
    CylinderContinuous (timeD (F - G)) := by
  intro T hT
  apply ((hFc T hT).sub (hGc T hT)).congr
  intro tq htq
  exact timeD_sub (hF tq.1 htq.1.1 tq.2) (hG tq.1 htq.1.1 tq.2)

theorem classical_difference_equation {ν : ℝ} {F U V : VectorField} {p q : ScalarField}
    (hU : ClassicalSolution ν F U p) (hV : ClassicalSolution ν F V q)
    {t : ℝ} (ht : 0 ≤ t) (x : Torus) :
    timeD (V - U) t x = -transport V (V - U) t x - transport (V - U) U t x -
      gradient (q - p) t x + ν • laplacian (V - U) t x := by
  have hUs := hU.spaceTwiceDifferentiable t ht
  have hVs := hV.spaceTwiceDifferentiable t ht
  calc
    _ = timeD V t x - timeD U t x :=
      timeD_sub (hV.timeDifferentiable t ht x) (hU.timeDifferentiable t ht x)
    _ = (-gradient q t x + ν • laplacian V t x + F t x - advection V t x) -
        (-gradient p t x + ν • laplacian U t x + F t x - advection U t x) := by
      rw [eq_sub_of_add_eq (hV.equations.1 t ht x), eq_sub_of_add_eq (hU.equations.1 t ht x)]
    _ = -(advection V t x - advection U t x) - gradient (q - p) t x +
        ν • laplacian (V - U) t x := by
      rw [gradient_sub (hV.pressureDifferentiable t ht) (hU.pressureDifferentiable t ht),
        laplacian_sub hVs hUs, smul_sub]
      abel
    _ = _ := by
      rw [advection_sub (hVs.differentiable (by norm_num)) (hUs.differentiable (by norm_num))]
      abel

theorem classical_energy_identity {ν : ℝ} {F U V : VectorField} {p q : ScalarField}
    (hU : ClassicalSolution ν F U p) (hV : ClassicalSolution ν F V q)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, inner ℝ ((V - U) t x) (timeD (V - U) t x) ∂torusVolume) =
      -(∫ x, inner ℝ ((V - U) t x) (transport (V - U) U t x) ∂torusVolume) -
      ν * ∑ i : Fin 3, ∫ x, ‖spaceD i (V - U) t x‖ ^ 2 ∂torusVolume := by
  let W := V - U
  have hUs₂ := hU.spaceTwiceDifferentiable t ht
  have hVs₂ := hV.spaceTwiceDifferentiable t ht
  have hUs : ContDiff ℝ 1 (spaceLift U t) := hUs₂.of_le (by norm_num)
  have hVs : ContDiff ℝ 1 (spaceLift V t) := hVs₂.of_le (by norm_num)
  have hWs₂ : ContDiff ℝ 2 (spaceLift W t) := hVs₂.sub hUs₂
  have hWs : ContDiff ℝ 1 (spaceLift W t) := hVs.sub hUs
  have hWc := (slice_continuous_iff W t).mpr hWs.continuous
  have hA : Integrable (fun x => inner ℝ (W t x) (transport V W t x)) torusVolume :=
    (hWc.inner (transport_continuous hVs hWs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun x => inner ℝ (W t x) (transport W U t x)) torusVolume :=
    (hWc.inner (transport_continuous hWs hUs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hP : Continuous (gradient (q - p) t) := by
    have heq : gradient (q - p) t = gradient q t - gradient p t :=
      funext (gradient_sub (hV.pressureDifferentiable t ht) (hU.pressureDifferentiable t ht))
    rw [heq]
    exact (cylinder_slice_continuous hV.pressureGradientContinuous ht).sub
      (cylinder_slice_continuous hU.pressureGradientContinuous ht)
  have hC : Integrable (fun x => inner ℝ (W t x) (gradient (q - p) t x)) torusVolume :=
    (hWc.inner hP).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLap : Continuous (laplacian W t) := by
    apply continuous_finsetSum _ (fun i _ => ?_)
    exact (slice_continuous_iff _ t).mpr
      (slice_contDiff_spaceD (n := 0) (by
        simpa using slice_contDiff_spaceD (n := 1) (by convert hWs₂ using 1; norm_num) i) i).continuous
  have hD : Integrable (fun x => inner ℝ (W t x) (laplacian W t x)) torusVolume :=
    (hWc.inner hLap).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWdiv : ∀ x, divergence W t x = 0 := by
    intro x
    rw [divergence_sub (hVs.differentiable one_ne_zero) (hUs.differentiable one_ne_zero),
      hV.equations.2.1 t ht, hU.equations.2.1 t ht, sub_self]
  have hzeroA := integral_inner_transport_self hVs hWs (hV.equations.2.1 t ht)
  have hzeroC := integral_inner_gradient (p := q - p) hWs hWdiv
    ((cylinder_slice_continuous hV.pressureContinuous ht).sub
      (cylinder_slice_continuous hU.pressureContinuous ht))
    ((hV.pressureDifferentiable t ht).sub (hU.pressureDifferentiable t ht)) hP
  have hdiffusion := integral_inner_laplacian hWs₂
  calc
    _ = ∫ x, -inner ℝ (W t x) (transport V W t x) - inner ℝ (W t x) (transport W U t x) -
        inner ℝ (W t x) (gradient (q - p) t x) + ν * inner ℝ (W t x) (laplacian W t x) ∂torusVolume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [classical_difference_equation hU hV ht]
        simp only [inner_add_right, inner_sub_right, inner_neg_right, inner_smul_right, W])
    _ = -(∫ x, inner ℝ (W t x) (transport V W t x) ∂torusVolume) -
        (∫ x, inner ℝ (W t x) (transport W U t x) ∂torusVolume) -
        (∫ x, inner ℝ (W t x) (gradient (q - p) t x) ∂torusVolume) +
        ν * ∫ x, inner ℝ (W t x) (laplacian W t x) ∂torusVolume := by
      rw [integral_add
        (f := fun x => -inner ℝ (W t x) (transport V W t x) - inner ℝ (W t x) (transport W U t x) -
          inner ℝ (W t x) (gradient (q - p) t x))
        (g := fun x => ν * inner ℝ (W t x) (laplacian W t x))
        ((hA.neg.sub hB).sub hC) (hD.const_mul ν),
        integral_sub (f := fun x => -inner ℝ (W t x) (transport V W t x) - inner ℝ (W t x) (transport W U t x))
          (g := fun x => inner ℝ (W t x) (gradient (q - p) t x)) (hA.neg.sub hB) hC,
        integral_sub (f := fun x => -inner ℝ (W t x) (transport V W t x))
          (g := fun x => inner ℝ (W t x) (transport W U t x)) hA.neg hB, integral_neg, integral_const_mul]
    _ = _ := by rw [hzeroA, hzeroC, hdiffusion]; dsimp [W]; ring

end TorusCalculus

namespace TorusCalculus

open scoped ContDiff
open MeasureTheory

theorem classical_energy_derivative_le {ν K : ℝ} {F U V : VectorField} {p q : ScalarField}
    (hν : 0 ≤ ν) (hU : ClassicalSolution ν F U p) (hV : ClassicalSolution ν F V q)
    {t : ℝ} (ht : 0 ≤ t) (hK : ∀ x, gradientSize U t x ≤ K) :
    (∫ x, 2 * inner ℝ ((V - U) t x) (timeD (V - U) t x) ∂torusVolume) ≤
      (2 * K) * energy (V - U) t := by
  let W := V - U
  have hUs : ContDiff ℝ 1 (spaceLift U t) := (hU.spaceTwiceDifferentiable t ht).of_le (by norm_num)
  have hWs : ContDiff ℝ 1 (spaceLift W t) :=
    ((hV.spaceTwiceDifferentiable t ht).of_le (by norm_num)).sub hUs
  have hWc := (slice_continuous_iff W t).mpr hWs.continuous
  have hi : Integrable (fun x => inner ℝ (W t x) (transport W U t x)) torusVolume :=
    (hWc.inner (transport_continuous hWs hUs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsq : Integrable (fun x => ‖W t x‖ ^ 2) torusVolume :=
    (hWc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hestimate : -(∫ x, inner ℝ (W t x) (transport W U t x) ∂torusVolume) ≤ K * energy W t := by
    calc
      _ = ∫ x, -inner ℝ (W t x) (transport W U t x) ∂torusVolume := (integral_neg _).symm
      _ ≤ ∫ x, K * ‖W t x‖ ^ 2 ∂torusVolume := by
        apply integral_mono hi.neg (hsq.const_mul K)
        intro x
        exact (neg_le_abs _).trans ((inner_transport_bound W U t x).trans
          (mul_le_mul_of_nonneg_right (hK x) (sq_nonneg _)))
      _ = _ := integral_const_mul _ _
  have hdiff : 0 ≤ ν * ∑ i : Fin 3, ∫ x, ‖spaceD i W t x‖ ^ 2 ∂torusVolume :=
    mul_nonneg hν (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
  rw [integral_const_mul, classical_energy_identity hU hV ht]
  dsimp only [W] at hestimate hdiff
  nlinarith

theorem classical_velocity_unique {ν : ℝ} {F U V : VectorField} {p q : ScalarField}
    (hν : 0 ≤ ν) (hU : ClassicalSolution ν F U p) (hV : ClassicalSolution ν F V q)
    (t : ℝ) (ht : 0 ≤ t) (x : Torus) : V t x = U t x := by
  let W := V - U
  have hWc : CylinderContinuous W := cylinder_sub hV.velocityContinuous hU.velocityContinuous
  have hDtc : CylinderContinuous (timeD W) := timeD_sub_cylinderContinuous
    hV.timeContinuous hU.timeContinuous hV.timeDifferentiable hU.timeDifferentiable
  have hWd (s : ℝ) (hs : 0 ≤ s) (y : Torus) :
      DifferentiableWithinAt ℝ (fun r => W r y) (Set.Ici 0) s :=
    (hV.timeDifferentiable s hs y).sub (hU.timeDifferentiable s hs y)
  obtain ⟨K, _, hK⟩ := gradientSize_bounded hU.spaceFirstContinuous t ht
  have hEzero : energy W t = 0 := by
    apply eq_zero_of_linear_deriv_bound (E' := fun s =>
      ∫ y, 2 * inner ℝ (W s y) (timeD W s y) ∂torusVolume) (K := 2 * K)
      (energy_continuousOn hWc t ht)
    · intro s hs
      exact energy_hasDerivAt hWc hDtc hWd hs.1
    · intro s hs
      exact classical_energy_derivative_le hν hU hV hs.1.le (hK s ⟨hs.1.le, hs.2.le⟩)
    · simp only [energy, W, Pi.sub_apply, hV.equations.2.2, hU.equations.2.2, sub_self,
        norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero]
    · exact fun s _ => energy_nonneg W s
    · exact ⟨ht, le_rfl⟩
  have hzero : W t x = 0 := eq_zero_of_integral_norm_sq_eq_zero
    (cylinder_slice_continuous hWc ht) hEzero x
  exact sub_eq_zero.mp hzero

theorem classical_pressure_unique {ν : ℝ} {F U V : VectorField} {p q : ScalarField}
    (hU : ClassicalSolution ν F U p) (hV : ClassicalSolution ν F V q)
    (hvel : ∀ t : ℝ, 0 ≤ t → ∀ x, V t x = U t x)
    (t : ℝ) (ht : 0 ≤ t) (x : Torus) : q t x = p t x := by
  have hs (i : Fin 3) (y : Torus) : spaceD i V t y = spaceD i U t y :=
    spaceD_congr_slice (hvel t ht) i y
  have hss (i : Fin 3) (y : Torus) : spaceD i (spaceD i V) t y = spaceD i (spaceD i U) t y :=
    spaceD_congr_slice (hs i) i y
  have ha (y : Torus) : advection V t y = advection U t y := by
    simp only [advection, hvel t ht, hs]
  have hl (y : Torus) : laplacian V t y = laplacian U t y := by
    simp only [laplacian, hss]
  have hg (y : Torus) : gradient q t y = gradient p t y := by
    have h := hV.equations.1 t ht y
    rw [timeD_congr_nonneg hvel ht y, ha y, hl y] at h
    have he := h.symm.trans (hU.equations.1 t ht y)
    exact neg_injective (add_right_cancel (add_right_cancel he))
  have hpartial (i : Fin 3) (y : Torus) : spaceD i (q - p) t y = 0 := by
    have he := congrArg (fun v : Space => v i) (hg y)
    rw [spaceD_sub (hV.pressureDifferentiable t ht) (hU.pressureDifferentiable t ht)]
    exact sub_eq_zero.mpr he
  have hconstant (y : Torus) : (q - p) t y = (q - p) t x :=
    spatially_constant_of_partials_zero (F := q - p)
      ((hV.pressureDifferentiable t ht).sub (hU.pressureDifferentiable t ht)) hpartial y x
  have hmean : (∫ y, (q - p) t y ∂torusVolume) = 0 := by
    change (∫ y, q t y - p t y ∂torusVolume) = 0
    rw [integral_sub
      ((cylinder_slice_continuous hV.pressureContinuous ht).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((cylinder_slice_continuous hU.pressureContinuous ht).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)), hV.pressureMeanZero t ht, hU.pressureMeanZero t ht, sub_self]
  simp_rw [hconstant, integral_const] at hmean
  have hz : (q - p) t x = 0 := by simpa using hmean
  exact sub_eq_zero.mp hz

theorem classical_unique {ν : ℝ} {F U : VectorField} {p : ScalarField}
    (hν : 0 ≤ ν) (hU : ClassicalSolution ν F U p) : UniqueClassical ν F U p := by
  intro V q hV t ht
  have hv := classical_velocity_unique hν hU hV
  exact ⟨hv t ht, classical_pressure_unique hU hV hv t ht⟩

end TorusCalculus

end
end PeriodicLattice

end OAI
