import OAI.Geometry.SurfaceImmersion.Correction.PeriodicCorrector

namespace OAI

/-! The angular and algebraic equations in the triangular periodic solve. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector

open CovarianceCorrector PeriodicCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Solve the two angular equations and the prescribed C pairing. The slow
Y equation follows by `slow_pairing_constraint` when K=H_y-j. -/
theorem solve_system (P : Submodule ℝ E) (Y C X₀ : E)
    (hD : gramDet Y C ≠ 0)
    (hPY : ∀ w : P, inner ℝ Y (w : E) = 0)
    (hPC : ∀ w : P, inner ℝ C (w : E) = 0)
    (hPX : ∀ w : P, inner ℝ X₀ (w : E) = 0)
    {V : Period → P} (hV : Continuous V) {v : P} (hv : average V = v)
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V (t : Period)))
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q)
    {H K h k' e : Period → ℝ}
    (hH : Continuous H) (hK : Continuous K) (hh : Continuous h)
    (hk' : Continuous k') (he : Continuous e)
    (hHs : ContDiff ℝ ∞ (fun t : ℝ => H (t : Period)))
    (hKs : ContDiff ℝ ∞ (fun t : ℝ => K (t : Period)))
    (hhs : ContDiff ℝ ∞ (fun t : ℝ => h (t : Period)))
    (hk's : ContDiff ℝ ∞ (fun t : ℝ => k' (t : Period)))
    (hes : ContDiff ℝ ∞ (fun t : ℝ => e (t : Period)))
    (hmH : average H = 0) (hmK : average K = 0) (hme : average e = 0)
    (hHd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => H (s : Period)) (h (t : Period)) t)
    (hKd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => K (s : Period)) (k' (t : Period)) t) :
    ∃ U D : Period → E, Continuous U ∧ Continuous D ∧
      ContDiff ℝ ∞ (fun t : ℝ => U (t : Period)) ∧ average U = 0 ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => U (s : Period)) (D (t : Period)) t) ∧
      (∀ t, inner ℝ Y (U t) = H t ∧ inner ℝ C (U t) = K t ∧
        inner ℝ Y (D t) = h t) ∧
      fluctuation (fun t => inner ℝ (X₀ + (V t : E)) (D t)) = e := by
  let T : Period → E := fun t => spanSolve Y C (H t, K t)
  let T' : Period → E := fun t => spanSolve Y C (h t, k' t)
  let X : Period → E := fun t => X₀ + (V t : E)
  have hT : Continuous T := (spanSolve Y C).continuous.comp (hH.prodMk hK)
  have hT' : Continuous T' := (spanSolve Y C).continuous.comp (hh.prodMk hk')
  have hX : Continuous X := continuous_const.add (P.subtypeL.continuous.comp hV)
  have hTs : ContDiff ℝ ∞ (fun t : ℝ => T (t : Period)) :=
    (spanSolve Y C).contDiff.comp (hHs.prodMk hKs)
  have hT's : ContDiff ℝ ∞ (fun t : ℝ => T' (t : Period)) :=
    (spanSolve Y C).contDiff.comp (hhs.prodMk hk's)
  have hXs : ContDiff ℝ ∞ (fun t : ℝ => X (t : Period)) :=
    contDiff_const.add (P.subtypeL.contDiff.comp hVs)
  have hTd (t : ℝ) : HasDerivAt (fun s : ℝ => T (s : Period)) (T' (t : Period)) t :=
    (spanSolve Y C).hasFDerivAt.comp_hasDerivAt t ((hHd t).prodMk (hKd t))
  let a : Period → ℝ := fun t => inner ℝ (X t) (T' t)
  let r : Period → ℝ := fun t => e t - fluctuation a t
  have ha : Continuous a := hX.inner hT'
  have hr : Continuous r := he.sub (ha.sub continuous_const)
  have hrs : ContDiff ℝ ∞ (fun t : ℝ => r (t : Period)) :=
    hes.sub ((hXs.inner ℝ hT's).sub contDiff_const)
  have hr0 : average r = 0 := by
    rw [show r = fun t => e t - fluctuation a t from rfl,
      average_sub (f := e) (g := fluctuation a) he (ha.sub continuous_const), hme, average_fluctuation ha, sub_self]
  obtain ⟨Z, W, hZ, hW, hZs, hWs, hZ0, _, hZd, hsolve⟩ :=
    exists_integrated_covariance hV hv hr hr0 hVs hrs hq hcircle
  let U : Period → E := fun t => T t + (Z t : E)
  let D : Period → E := fun t => T' t + (W t : E)
  have hUc : Continuous U := hT.add (P.subtypeL.continuous.comp hZ)
  have hDc : Continuous D := hT'.add (P.subtypeL.continuous.comp hW)
  have hUs : ContDiff ℝ ∞ (fun t : ℝ => U (t : Period)) :=
    hTs.add (P.subtypeL.contDiff.comp hZs)
  have hZmean : average (fun t => (Z t : E)) = 0 := by
    have hz := P.subtypeL.integral_comp_comm (integrable_of_continuous hZ)
    change (∫ t, P.subtypeL (Z t) ∂AddCircle.haarAddCircle) = 0
    rw [hz]
    change P.subtypeL (average Z) = 0
    rw [hZ0, map_zero]
  have hU0 : average U = 0 := by
    change average (fun t => T t + (Z t : E)) = 0
    rw [average_add (f := T) (g := fun t => (Z t : E)) hT
      (P.subtypeL.continuous.comp hZ), average_spanSolve Y C hH hK hmH hmK,
      hZmean, add_zero]
  refine ⟨U, D, hUc, hDc, hUs, hU0, ?_, ?_, ?_⟩
  · intro t
    exact (hTd t).add (P.subtypeL.hasFDerivAt.comp_hasDerivAt t (hZd t))
  · intro t
    dsimp only [U, D, T, T']
    simp only [inner_add_right, hPY, hPC, add_zero]
    exact ⟨(spanSolve_pairings Y C hD _).1, (spanSolve_pairings Y C hD _).2,
      (spanSolve_pairings Y C hD _).1⟩
  · have hp : (fun t => inner ℝ (X₀ + (V t : E)) (D t)) =
        (fun t => a t + inner ℝ (V t) (W t)) := by
      funext t
      dsimp only [D, a, X]
      simp only [inner_add_right, inner_add_left, hPX, zero_add]
      rfl
    rw [hp]
    have hb : Continuous (fun t => inner ℝ (V t) (W t)) := hV.inner hW
    change (fun t => a t + inner ℝ (V t) (W t) -
      average (fun s => a s + inner ℝ (V s) (W s))) = e
    rw [average_add ha hb]
    funext t
    have hs := congrFun hsolve t
    change inner ℝ (V t) (W t) - average (fun s => inner ℝ (V s) (W s)) =
      e t - (a t - average a) at hs
    linarith

/-- The angular correction exists for arbitrary smooth mean-zero data. The
primitive and derivative data used internally are constructed on the circle. -/
theorem solve_angular_corrector (P : Submodule ℝ E) (Y C X₀ : E)
    (hdet : gramDet Y C ≠ 0)
    (hPY : ∀ w : P, inner ℝ Y (w : E) = 0)
    (hPC : ∀ w : P, inner ℝ C (w : E) = 0)
    (hPX : ∀ w : P, inner ℝ X₀ (w : E) = 0)
    {V : Period → P} (hV : Continuous V) {v : P} (hv : average V = v)
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V (t : Period)))
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q)
    {h K e : Period → ℝ} (hh : Continuous h) (hK : Continuous K)
    (he : Continuous e)
    (hhs : ContDiff ℝ ∞ (fun t : ℝ => h (t : Period)))
    (hKs : ContDiff ℝ ∞ (fun t : ℝ => K (t : Period)))
    (hes : ContDiff ℝ ∞ (fun t : ℝ => e (t : Period)))
    (hmh : average h = 0) (hmK : average K = 0) (hme : average e = 0) :
    ∃ U D : Period → E, Continuous U ∧ Continuous D ∧
      ContDiff ℝ ∞ (fun t : ℝ => U (t : Period)) ∧ average U = 0 ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => U (s : Period)) (D (t : Period)) t) ∧
      (∀ t, inner ℝ Y (D t) = h t ∧ inner ℝ C (U t) = K t) ∧
      fluctuation (fun t => inner ℝ (X₀ + (V t : E)) (D t)) = e := by
  obtain ⟨H, hH, hHs, hmH, hHd⟩ := exists_circle_primitive hhs hmh
  obtain ⟨k', hk', hk's, _, hKd⟩ := exists_circle_derivative hKs
  obtain ⟨U, D, hU, hD, hUs, hmU, hUd, hp, hf⟩ :=
    solve_system P Y C X₀ hdet hPY hPC hPX hV hv hVs hq hcircle
      hH hK hh hk' he hHs hKs hhs hk's hes hmH hmK hme hHd hKd
  exact ⟨U, D, hU, hD, hUs, hmU, hUd,
    fun t => ⟨(hp t).2.2, (hp t).2.1⟩, hf⟩

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
