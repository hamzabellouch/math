import OAI.Geometry.Symplectic.MorseBounds.SymplecticFlow

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.GenericGeometry
open scoped Manifold ContDiff
open Filter Topology Set
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace (E) M]
  [IsManifold (SmoothModel E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma chart_inverse_derivative (p x : M)
    (hx : x ∈ (extChartAt (SmoothModel E) p).source)
    (u : TangentSpace (SmoothModel E) x) :
    mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p).symm
      ((extChartAt (SmoothModel E) p) x)
      (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p) x u) = u := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := SmoothModel E) hx
  simp only [SmoothModel, modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at h
  exact congrArg (fun L => L u) h

omit [FiniteDimensional ℝ E] in
lemma chartTwoForm_apply_derivatives (omega : SymplecticForm (E := E) (M := M))
    (p x : M) (hx : x ∈ (extChartAt (SmoothModel E) p).source)
    (u v : TangentSpace (SmoothModel E) x) :
    chartTwoForm omega.form p ((extChartAt (SmoothModel E) p) x)
      (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p) x u)
      (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p) x v) =
      omega.form x u v := by
  change omega.form ((extChartAt (SmoothModel E) p).symm ((extChartAt (SmoothModel E) p) x))
    (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p).symm
      ((extChartAt (SmoothModel E) p) x)
      (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p) x u))
    (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p).symm
      ((extChartAt (SmoothModel E) p) x)
      (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p) x v)) = _
  rw [chart_inverse_derivative p x hx u, chart_inverse_derivative p x hx v,
    (extChartAt (SmoothModel E) p).left_inv hx]

omit [FiniteDimensional ℝ E] [IsManifold (SmoothModel E) ∞ M] in
lemma coordinate_flow_smooth_at (Phi : ℝ × M → M)
    (hPhi : ContMDiff (𝓘(ℝ).prod (SmoothModel E)) (SmoothModel E) ∞ Phi)
    (t : ℝ) (x : M) :
    let c := extChartAt (SmoothModel E) x
    let d := extChartAt (SmoothModel E) (Phi (t,x))
    ContDiffAt ℝ ∞ (fun q : ℝ × E => d (Phi (q.1, c.symm q.2))) (t, c x) := by
  let c := extChartAt (SmoothModel E) x
  let d := extChartAt (SmoothModel E) (Phi (t,x))
  have hcp : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hc : ContMDiffAt (SmoothModel E) (SmoothModel E) ∞ c.symm (c x) :=
    (contMDiffWithinAt_extChartAt_symm_target_self (n := (∞ : ℕ∞ω)) x).contMDiffAt (extChartAt_target_mem_nhds x)
  have hg : ContMDiffAt (𝓘(ℝ).prod (SmoothModel E)) (𝓘(ℝ).prod (SmoothModel E)) ∞
      (fun q : ℝ × E => (q.1, c.symm q.2)) (t, c x) :=
    contMDiffAt_fst.prodMk (hc.comp (t, c x) contMDiffAt_snd)
  have hf := (hPhi.contMDiffAt (x := (t, c.symm (c x)))).comp (t, c x) hg
  have hout : ContMDiffAt (SmoothModel E) (SmoothModel E) ∞ d (Phi (t, c.symm (c x))) := by
    rw [hcp]
    exact contMDiffAt_extChartAt
  have h := hout.comp (t, c x) hf
  rw [SmoothModel, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffAt

omit [FiniteDimensional ℝ E] in
lemma coordinate_derivative_apply (g : M → M)
    (hg : ContMDiff (SmoothModel E) (SmoothModel E) ∞ g)
    (x p : M) (hp : g x ∈ (extChartAt (SmoothModel E) p).source)
    (u : TangentSpace (SmoothModel E) x) :
    fderiv ℝ ((extChartAt (SmoothModel E) p) ∘ g ∘
      (extChartAt (SmoothModel E) x).symm) ((extChartAt (SmoothModel E) x) x)
      (mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) x) x u) =
      mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p) (g x)
        (mfderiv (SmoothModel E) (SmoothModel E) g x u) := by
  let c := extChartAt (SmoothModel E) x
  let d := extChartAt (SmoothModel E) p
  have hcp : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hc : MDifferentiableAt (SmoothModel E) (SmoothModel E) c.symm (c x) :=
    ((contMDiffWithinAt_extChartAt_symm_target_self (n := (∞ : ℕ∞ω)) x).contMDiffAt
      (extChartAt_target_mem_nhds x)).mdifferentiableAt (by simp)
  have hd : MDifferentiableAt (SmoothModel E) (SmoothModel E) d (g x) :=
    mdifferentiableAt_extChartAt (extChartAt_source (SmoothModel E) p ▸ hp)
  have hgx : MDifferentiableAt (SmoothModel E) (SmoothModel E) g (c.symm (c x)) := by
    rw [hcp]; exact hg.mdifferentiable (by simp) x
  have hd' : MDifferentiableAt (SmoothModel E) (SmoothModel E) d ((g ∘ c.symm) (c x)) := by
    simpa only [Function.comp_apply, hcp] using hd
  have h := mfderiv_comp (c x) hd' (hgx.comp (c x) hc)
  rw [mfderiv_comp (c x) hgx hc] at h
  rw [mfderiv_eq_fderiv] at h
  have he := congrArg (fun L => L (mfderiv (SmoothModel E) (SmoothModel E) c x u)) h
  change fderiv ℝ (d ∘ g ∘ c.symm) (c x)
    (mfderiv (SmoothModel E) (SmoothModel E) c x u) =
      mfderiv (SmoothModel E) (SmoothModel E) d (g (c.symm (c x)))
        (mfderiv (SmoothModel E) (SmoothModel E) g (c.symm (c x))
          (mfderiv (SmoothModel E) (SmoothModel E) c.symm (c x)
            (mfderiv (SmoothModel E) (SmoothModel E) c x u))) at he
  have hci := chart_inverse_derivative x x (mem_extChartAt_source x) u
  simp only [TangentSpace] at he hci ⊢
  rw [hci, hcp] at he
  exact he

omit [FiniteDimensional ℝ E] in
lemma chart_function_smooth (F : M → ℝ)
    (hF : ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ F) (p : M) (y : E)
    (hy : y ∈ (extChartAt (SmoothModel E) p).target) :
    ContDiffAt ℝ ∞ (F ∘ (extChartAt (SmoothModel E) p).symm) y := by
  exact ((hF.contMDiffAt (x := (extChartAt (SmoothModel E) p).symm y)).comp y
    ((contMDiffOn_extChartAt_symm p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy))).contDiffAt

omit [FiniteDimensional ℝ E] in
lemma manifold_pullback_derivative_zero
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (hF : ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x)
    (Phi : ℝ × M → M)
    (hPhi : ContMDiff (𝓘(ℝ).prod (SmoothModel E)) (SmoothModel E) ∞ Phi)
    (hODE : ∀ x, IsMIntegralCurve (fun t => Phi (t,x)) V)
    (t : ℝ) (x : M) (u v : TangentSpace (SmoothModel E) x) :
    HasDerivAt (fun s => omega.form (Phi (s,x))
      (mfderiv (SmoothModel E) (SmoothModel E) (fun y => Phi (s,y)) x u)
      (mfderiv (SmoothModel E) (SmoothModel E) (fun y => Phi (s,y)) x v)) 0 t := by
  let c := extChartAt (SmoothModel E) x
  let p := Phi (t,x)
  let d := extChartAt (SmoothModel E) p
  let Psi : ℝ × E → E := fun q => d (Phi (q.1,c.symm q.2))
  let U := mfderiv (SmoothModel E) (SmoothModel E) c x u
  let W := mfderiv (SmoothModel E) (SmoothModel E) c x v
  have hcx : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hyp : Psi (t,c x) = d p := by dsimp [Psi]; rw [hcx]
  have hdp : d p ∈ d.target := mem_extChartAt_target p
  have htheta (s : ℝ) : ContMDiff (SmoothModel E) (SmoothModel E) ∞ (fun y => Phi (s,y)) :=
    hPhi.comp (contMDiff_const.prodMk contMDiff_id)
  have hc : ContMDiffAt (SmoothModel E) (SmoothModel E) ∞ c.symm (c x) :=
    ((contMDiffOn_extChartAt_symm x (c x) (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds x))
  have hyin : ∀ᶠ y in 𝓝 (c x), Phi (t,c.symm y) ∈ d.source := by
    apply ((htheta t).contMDiffAt.comp (c x) hc).continuousAt.eventually
    change d.source ∈ 𝓝 (Phi (t,c.symm (c x)))
    rw [hcx]
    exact (isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p)
  have hPsiODE : ∀ᶠ y in 𝓝 (c x), HasDerivAt (fun s => Psi (s,y))
      (MorseArnold.Dynamics.coordinateVectorField V p (Psi (t,y))) t := by
    filter_upwards [hyin] with y hy
    exact MorseArnold.Dynamics.integralCurve_coordinate_derivative V (hODE (c.symm y)) p t hy
  have hw : DifferentiableAt ℝ (chartTwoForm omega.form p) (Psi (t,c x)) := by
    rw [hyp]
    exact ((omega.smooth p (d p) hdp).contDiffAt
      (extChartAt_target_mem_nhds p)).differentiableAt (by simp)
  have hvf : DifferentiableAt ℝ (MorseArnold.Dynamics.coordinateVectorField V p) (Psi (t,c x)) := by
    rw [hyp]
    exact (MorseArnold.Dynamics.coordinateVectorField_contDiffAt V hV p).differentiableAt (by simp)
  have hf : ContDiffAt ℝ ∞ (F ∘ d.symm) (Psi (t,c x)) := by
    rw [hyp]; exact chart_function_smooth F hF p (d p) hdp
  have halt : ∀ᶠ y in 𝓝 (Psi (t,c x)), ∀ a, chartTwoForm omega.form p y a a = 0 := by
    exact Filter.Eventually.of_forall (fun y a => omega.alternating (d.symm y) _)
  have hclosed : ∀ a b z, fderiv ℝ (chartTwoForm omega.form p) (Psi (t,c x)) a b z +
      fderiv ℝ (chartTwoForm omega.form p) (Psi (t,c x)) b z a +
      fderiv ℝ (chartTwoForm omega.form p) (Psi (t,c x)) z a b = 0 := by
    rw [hyp]; exact omega.closed p (d p) hdp
  have hham : ∀ᶠ y in 𝓝 (Psi (t,c x)), ∀ a,
      chartTwoForm omega.form p y (MorseArnold.Dynamics.coordinateVectorField V p y) a =
      fderiv ℝ (F ∘ d.symm) y a := by
    rw [hyp]
    filter_upwards [extChartAt_target_mem_nhds (I := SmoothModel E) p] with y hy
    intro a
    exact congrArg (fun L => L a) (chart_hamiltonian_equation omega F hF V hHam p y hy)
  have hd := MorseArnold.SymplecticFlow.pullback_derivative_zeroAt
    (chartTwoForm omega.form p) (MorseArnold.Dynamics.coordinateVectorField V p)
    (F ∘ d.symm) Psi t (c x) U W hw hvf hf halt hclosed hham
    (coordinate_flow_smooth_at Phi hPhi t x) hPsiODE
  have hsin : ∀ᶠ s in 𝓝 t, Phi (s,x) ∈ d.source := by
    apply (hPhi.comp (contMDiff_id.prodMk contMDiff_const)).continuous.continuousAt.eventually
    exact (isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hsin] with s hs
  change omega.form (Phi (s,x)) _ _ = chartTwoForm omega.form p (Psi (s,c x))
    (fderiv ℝ (fun y => Psi (s,y)) (c x) U)
    (fderiv ℝ (fun y => Psi (s,y)) (c x) W)
  have he (a : TangentSpace (SmoothModel E) x) := coordinate_derivative_apply
    (fun y => Phi (s,y)) (htheta s) x p hs a
  change omega.form (Phi (s,x)) _ _ = chartTwoForm omega.form p (d (Phi (s,c.symm (c x))))
    (fderiv ℝ (d ∘ (fun y => Phi (s,y)) ∘ c.symm) (c x) U)
    (fderiv ℝ (d ∘ (fun y => Phi (s,y)) ∘ c.symm) (c x) W)
  rw [hcx, he u, he v]
  exact (chartTwoForm_apply_derivatives omega p (Phi (s,x)) hs _ _).symm

omit [FiniteDimensional ℝ E] in
theorem manifold_hamiltonian_flow_preserves_form
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (hF : ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x)
    (Phi : ℝ × M → M)
    (hPhi : ContMDiff (𝓘(ℝ).prod (SmoothModel E)) (SmoothModel E) ∞ Phi)
    (hzero : ∀ x, Phi (0,x) = x)
    (hODE : ∀ x, IsMIntegralCurve (fun t => Phi (t,x)) V)
    (t : ℝ) (x : M) (u v : TangentSpace (SmoothModel E) x) :
    omega.form (Phi (t,x))
      (mfderiv (SmoothModel E) (SmoothModel E) (fun y => Phi (t,y)) x u)
      (mfderiv (SmoothModel E) (SmoothModel E) (fun y => Phi (t,y)) x v) =
      omega.form x u v := by
  let f : ℝ → ℝ := fun s => omega.form (Phi (s,x))
    (mfderiv (SmoothModel E) (SmoothModel E) (fun y => Phi (s,y)) x u)
    (mfderiv (SmoothModel E) (SmoothModel E) (fun y => Phi (s,y)) x v)
  have hd (s : ℝ) : HasDerivAt f 0 s :=
    manifold_pullback_derivative_zero omega F hF V hV hHam Phi hPhi hODE s x u v
  have he : f t = f 0 := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hz : (fun y => Phi (0,y)) = id := funext hzero
  have hzD : mfderiv (SmoothModel E) (SmoothModel E) (fun y => Phi (0,y)) x =
      ContinuousLinearMap.id ℝ (TangentSpace (SmoothModel E) x) := by
    rw [hz, mfderiv_id]
  change f t = omega.form x u v
  rw [he]
  dsimp only [f]
  simp only [TangentSpace] at hzD ⊢
  rw [hzD]
  change omega.form (Phi (0,x)) u v = omega.form x u v
  exact congrArg (fun y : M => omega.form y u v) (hzero x)

end
end MorseArnold.GenericGeometry

end

end OAI
