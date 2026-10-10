import OAI.Geometry.SurfaceImmersion.Correction.LocalPeriodicCorrector
import OAI.Geometry.SurfaceImmersion.Correction.FullPeriodicCorrector

namespace OAI

/-! The complete periodic corrector with all hypotheses restricted to an open chart domain. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PeriodicCorrector
open CovarianceCorrector LocalPeriodicCalculus
open SmoothPeriodicCalculus (slowDerivative)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma directional_pairing_constraint_on {O : Set A} (hO : IsOpen O) {Y U : A → E}
    {H : A → ℝ} {p v : A} (hp : p ∈ O) {C : E} {j : ℝ}
    (hY : DifferentiableAt ℝ Y p) (hU : DifferentiableAt ℝ U p)
    (hH : DifferentiableAt ℝ H p) (he : ∀ q ∈ O, inner ℝ (Y q) (U q) = H q)
    (hC : fderiv ℝ Y p v = C)
    (hK : inner ℝ C (U p) = fderiv ℝ H p v - j) :
    inner ℝ (Y p) (fderiv ℝ U p v) = j := by
  have hd := hY.hasFDerivAt.inner ℝ hU.hasFDerivAt
  have hid : (fun q => inner ℝ (Y q) (U q)) =ᶠ[𝓝 p] H := by
    filter_upwards [hO.mem_nhds hp] with q hq
    exact he q hq
  have hv := congrArg (fun L : A →L[ℝ] ℝ => L v)
    ((hd.congr_of_eventuallyEq hid.symm).unique hH.hasFDerivAt)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply] at hv
  rw [hC] at hv
  linarith

/-- The concrete full correction uses the genuine slow derivative of the
normalized primitive in its transverse datum. -/
def fullSolutionFormula (v : A) (Y C X₀ : A → E) (V : A → C(Period, E))
    (q : A → ℝ) (h j e : A → C(Period, ℝ)) (z : A × ℝ) : E :=
  JetPolynomial.angularCorrectionFunction (Y z.1) (C z.1) (X₀ z.1) (V z.1) (q z.1)
    (fun t => h z.1 (t : Period))
    (fun t => fderiv ℝ (fun p => PeriodicPrimitive.primitive
      (fun s : ℝ => h p (s : Period)) t) z.1 v - j z.1 (t : Period))
    (fun t => e z.1 (t : Period)) z.2

/-- A mean-zero, jointly smooth solution of the complete periodic system.
The transverse equation follows from differentiating the pairing with `Y`. -/
theorem solve_full_smooth_family_on_formula (O : Set A) (hO : IsOpen O) (v : A) (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX₀ : ContDiffOn ℝ ∞ X₀ O)
    (hYC : ∀ p ∈ O, fderiv ℝ Y p v = C p)
    (hdet : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p ∈ O, ∀ t, V p t ∈ S p)
    (hV : ContDiffOn ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (q : A → ℝ) (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (h j e : A → C(Period, ℝ))
    (hhs : ContDiffOn ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hjs : ContDiffOn ℝ ∞ (fun z : A × ℝ => j z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hes : ContDiffOn ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hmh : ∀ p ∈ O, average (h p) = 0) (hmj : ∀ p ∈ O, average (j p) = 0)
    (hme : ∀ p ∈ O, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiffOn ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      (∀ p ∈ O, average (U p) = 0) ∧
      (∀ p ∈ O, ∀ (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period))
        (D p (t : Period)) t) ∧
      (∀ p ∈ O, ∀ t, inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p ∈ O, ∀ (t : ℝ), inner ℝ (Y p)
        (slowDerivative (fun z : A × ℝ => U z.1 (z.2 : Period)) v (p, t)) = j p (t : Period)) ∧
      (∀ p ∈ O, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, h p = 0) →
        (∀ p ∈ Z, j p = 0) → (∀ p ∈ Z, e p = 0) → ∀ p ∈ Z, U p = 0) ∧
      (∀ p ∈ O, ∀ t : ℝ, U p (t : Period) = fullSolutionFormula v Y C X₀ V q h j e (p, t)) := by
  let H := primitiveOn h O hO hhs hmh
  have hHs : ContDiffOn ℝ ∞ (fun z : A × ℝ => H z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    primitiveOn_smooth h O hO hhs hmh
  have hH0 : ∀ p ∈ O, average (H p) = 0 := fun p hp => primitiveOn_mean_zero h O hO hhs hmh hp
  let Hᵥ := slowOn H O hO hHs v
  have hHᵥs : ContDiffOn ℝ ∞ (fun z : A × ℝ => Hᵥ z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    slowOn_smooth H O hO hHs v
  let K : A → C(Period, ℝ) := fun p => Hᵥ p - j p
  have hKs : ContDiffOn ℝ ∞ (fun z : A × ℝ => K z.1 (z.2 : Period)) (O ×ˢ Set.univ) := hHᵥs.sub hjs
  have hK0 (p : A) (hp : p ∈ O) : average (K p) = 0 := by
    have hv0 : average (Hᵥ p) = 0 := slowOn_mean_zero H O hO hHs hH0 v hp
    change average (fun t => Hᵥ p t - j p t) = 0
    rw [average_sub (f := Hᵥ p) (g := j p) (Hᵥ p).continuous (j p).continuous,
      hv0, hmj p hp, sub_self]
  obtain ⟨U, D, hUs, hDs, hU0, hUd, hpair, hfluc, hUH, hzero, hformula⟩ :=
    solve_smooth_family_on_formula O hO S Y C X₀ hY hC hX₀ hdet hPY hPC hPX V hVmem hV
      q hq hqpos hcircle h K e hhs hKs hes hmh hK0 hme
  refine ⟨U, D, hUs, hDs, hU0, hUd, fun p hp t => (hpair p hp t).2, ?_, hfluc, ?_, ?_⟩
  · intro p hp t
    have hUt : ContDiffAt ℝ ∞ (fun q => U q (t : Period)) p :=
      (hUs.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt
    have hHt : ContDiffAt ℝ ∞ (fun q => H q (t : Period)) p :=
      (hHs.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt
    have he : ∀ q ∈ O, inner ℝ (Y q) (U q (t : Period)) = H q (t : Period) := by
      intro q hq
      exact (hUH q hq t).trans (primitiveOn_apply h O hO hhs hmh hq t).symm
    have hK : inner ℝ (C p) (U p (t : Period)) =
        fderiv ℝ (fun q => H q (t : Period)) p v - j p (t : Period) := by
      rw [LocalPeriodicCalculus.fderiv_slice hO hHs hp]
      have hk := (hpair p hp (t : Period)).1
      change inner ℝ (C p) (U p (t : Period)) = Hᵥ p (t : Period) - j p (t : Period) at hk
      rw [slowOn_apply H O hO hHs v hp] at hk
      exact hk
    have hd := directional_pairing_constraint_on hO hp
      ((hY.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))
      (hUt.differentiableAt (by simp)) (hHt.differentiableAt (by simp)) he (hYC p hp) hK
    rwa [LocalPeriodicCalculus.fderiv_slice hO hUs hp] at hd
  · intro Z hZ hZO hhZ hjZ heZ p hp
    have hHZ : ∀ q ∈ Z, H q = 0 :=
      fun q hq => primitiveOn_zero_at h O hO hhs hmh (hZO hq) (hhZ q hq)
    have hHvp : Hᵥ p = 0 := slowOn_zero_on H O hO hHs hZ hHZ v (hZO hp) hp
    have hKp : K p = 0 := by
      change Hᵥ p - j p = 0
      rw [hHvp, hjZ p hp, sub_self]
    exact hzero p (hZO hp) (hhZ p hp) hKp (heZ p hp)

  · intro p hp t
    have hK : (fun s : ℝ => K p (s : Period)) = fun s : ℝ =>
        fderiv ℝ (fun q => PeriodicPrimitive.primitive (fun u : ℝ => h q (u : Period)) s)
          p v - j p (s : Period) := by
      funext s
      change Hᵥ p (s : Period) - j p (s : Period) = _
      rw [slowOn_apply H O hO hHs v hp, ← fderiv_slice hO hHs hp]
      have heq : (fun q => H q (s : Period)) =ᶠ[𝓝 p]
          (fun q => PeriodicPrimitive.primitive (fun u : ℝ => h q (u : Period)) s) := by
        filter_upwards [hO.mem_nhds hp] with q hq
        exact primitiveOn_apply h O hO hhs hmh hq s
      rw [heq.fderiv_eq]
    rw [hformula p hp t, hK]
    rfl

theorem solve_full_smooth_family_on (O : Set A) (hO : IsOpen O) (v : A) (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX₀ : ContDiffOn ℝ ∞ X₀ O)
    (hYC : ∀ p ∈ O, fderiv ℝ Y p v = C p)
    (hdet : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p ∈ O, ∀ t, V p t ∈ S p)
    (hV : ContDiffOn ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (q : A → ℝ) (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (h j e : A → C(Period, ℝ))
    (hhs : ContDiffOn ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hjs : ContDiffOn ℝ ∞ (fun z : A × ℝ => j z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hes : ContDiffOn ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hmh : ∀ p ∈ O, average (h p) = 0) (hmj : ∀ p ∈ O, average (j p) = 0)
    (hme : ∀ p ∈ O, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiffOn ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      (∀ p ∈ O, average (U p) = 0) ∧
      (∀ p ∈ O, ∀ (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period))
        (D p (t : Period)) t) ∧
      (∀ p ∈ O, ∀ t, inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p ∈ O, ∀ (t : ℝ), inner ℝ (Y p)
        (slowDerivative (fun z : A × ℝ => U z.1 (z.2 : Period)) v (p, t)) = j p (t : Period)) ∧
      (∀ p ∈ O, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, h p = 0) →
        (∀ p ∈ Z, j p = 0) → (∀ p ∈ Z, e p = 0) → ∀ p ∈ Z, U p = 0) := by
  obtain ⟨U, D, hUs, hDs, hU0, hUd, hYd, hYs, hX, hz, _⟩ :=
    solve_full_smooth_family_on_formula O hO v S Y C X₀ hY hC hX₀ hYC hdet hPY hPC hPX V hVmem hV q hq hqpos hcircle h j e hhs hjs hes hmh hmj hme
  exact ⟨U, D, hUs, hDs, hU0, hUd, hYd, hYs, hX, hz⟩

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
