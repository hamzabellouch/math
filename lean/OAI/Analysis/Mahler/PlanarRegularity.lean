import OAI.Analysis.Mahler.PlanarIntegralRegularity
import OAI.Analysis.Mahler.GlobalVerticalGeometry

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff
open MahlerConformal

lemma vertical_segment_mem_Omega_regularity {u : ℂ} (hu : u ∈ Omega) {t : ℝ}
    (ht : t ∈ uIcc 0 u.im) : (u.re : ℂ) + (t : ℂ)*I ∈ Omega := by
  have hq : u.re ∈ Ioo (-1 : ℝ) 1 := by
    rw [← image_re_F_disk]
    exact ⟨u,hu,rfl⟩
  have hv := verticalFiber_interval hq
  have hy : u.im ∈ verticalFiber u.re := by
    simpa only [verticalFiber, mem_ofPred_eq, Complex.re_add_im] using hu
  exact hv.2.1.uIcc_subset hv.2.2 hy ht

/-- The open domain used for parameter integration is exactly Omega. -/
theorem planarSegmentDomain_eq_Omega : planarSegmentDomain = Omega := by
  ext u
  constructor
  · intro hu
    have h := hu 1 (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    simpa [segmentParameterDomain,segmentPoint] using h
  · intro hu s hs
    apply vertical_segment_mem_Omega_regularity hu
    have h : s*u.im ∈ (fun x : ℝ => x*u.im) '' uIcc (0 : ℝ) 1 :=
      ⟨s,by simpa using hs,rfl⟩
    simpa only [image_mul_const_uIcc,zero_mul,one_mul] using h

/-- Full joint real C∞ regularity of P_m on
all of Omega. In particular, no exclusion of the zero or xi=0 is needed. -/
theorem contDiffOn_planarPrimitive (m : ℕ) :
    ContDiffOn ℝ ∞ (fun u : ℂ => planarPrimitive m u.re u.im) Omega := by
  rw [← planarSegmentDomain_eq_Omega]
  exact contDiffOn_planarPrimitive_segment m

theorem contDiffAt_planarPrimitive (m : ℕ) {u : ℂ} (hu : u ∈ Omega) :
    ContDiffAt ℝ ∞ (fun z : ℂ => planarPrimitive m z.re z.im) u :=
  (contDiffOn_planarPrimitive m u hu).contDiffAt (isOpen_Omega.mem_nhds hu)

theorem contDiffOn_one_planarPrimitive (m : ℕ) :
    ContDiffOn ℝ 1 (fun u : ℂ => planarPrimitive m u.re u.im) Omega :=
  (contDiffOn_planarPrimitive m).of_le (by norm_num)

theorem differentiableOn_planarPrimitive (m : ℕ) :
    DifferentiableOn ℝ (fun u : ℂ => planarPrimitive m u.re u.im) Omega :=
  (contDiffOn_one_planarPrimitive m).differentiableOn (by norm_num)

/-- Continuity of the full real Frechet derivative, for the
real Jacobian and chain rule. -/
theorem continuousOn_fderiv_planarPrimitive (m : ℕ) :
    ContinuousOn (fderiv ℝ (fun u : ℂ => planarPrimitive m u.re u.im)) Omega :=
  (contDiffOn_one_planarPrimitive m).continuousOn_fderiv_of_isOpen isOpen_Omega le_rfl

theorem hasFDerivAt_planarPrimitive (m : ℕ) {u : ℂ} (hu : u ∈ Omega) :
    HasFDerivAt (fun z : ℂ => planarPrimitive m z.re z.im)
      (fderiv ℝ (fun z : ℂ => planarPrimitive m z.re z.im) u) u :=
  ((differentiableOn_planarPrimitive m).differentiableAt (isOpen_Omega.mem_nhds hu)).hasFDerivAt

/-- The exact vertical FTC derivative on Omega, with no remaining segment premise. -/
theorem hasDerivAt_planarPrimitive_Omega (m : ℕ) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) :
    HasDerivAt (planarPrimitive m q)
      (planarDensity m ((q : ℂ)+(t : ℂ)*I)) t := by
  apply hasDerivAt_planarPrimitive
  intro s hs
  simpa using vertical_segment_mem_Omega_regularity hu (by simpa using hs)

/-- The vertical derivative formula for the planar primitive. -/
theorem hasDerivAt_planarPrimitive_source {m : ℕ} (hm : 2 ≤ m) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) :
    HasDerivAt (planarPrimitive m q)
      ((4*(m : ℝ)/Real.pi)*‖inverseF ((q : ℂ)+(t : ℂ)*I)‖^(2*(m : ℝ)-2 : ℝ)*
        ‖deriv inverseF ((q : ℂ)+(t : ℂ)*I)‖^2) t := by
  simpa only [planarDensity_eq m (by omega)] using hasDerivAt_planarPrimitive_Omega m hu

/-- Joint smoothness in the two real coordinates. -/
theorem contDiffOn_planarPrimitive_coordinates (m : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => planarPrimitive m p.1 p.2)
      {p : ℝ × ℝ | (p.1 : ℂ)+(p.2 : ℂ)*I ∈ Omega} := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)+(p.2 : ℂ)*I) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  intro p hp
  have h := (contDiffAt_planarPrimitive m hp).comp p hc.contDiffAt
  simpa [Function.comp_def] using h.contDiffWithinAt (s := {p : ℝ × ℝ | (p.1 : ℂ)+(p.2 : ℂ)*I ∈ Omega})

/-- Smoothness and the vertical derivative formula, for m >= 2. -/
theorem planar_primitive_regularity {m : ℕ} (hm : 2 ≤ m) :
    ContDiffOn ℝ ∞ (fun u : ℂ => planarPrimitive m u.re u.im) Omega ∧
    ContDiffOn ℝ 1 (fun u : ℂ => planarPrimitive m u.re u.im) Omega ∧
    (∀ q t : ℝ, (q : ℂ)+(t : ℂ)*I ∈ Omega →
      HasDerivAt (planarPrimitive m q)
        ((4*(m : ℝ)/Real.pi)*‖inverseF ((q : ℂ)+(t : ℂ)*I)‖^(2*(m : ℝ)-2 : ℝ)*
          ‖deriv inverseF ((q : ℂ)+(t : ℂ)*I)‖^2) t) :=
  ⟨contDiffOn_planarPrimitive m,contDiffOn_one_planarPrimitive m,
    fun _ _ hu => hasDerivAt_planarPrimitive_source hm hu⟩

end SymmetricMahler

end OAI
