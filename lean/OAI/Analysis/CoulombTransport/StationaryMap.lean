import OAI.Analysis.CoulombTransport.CoulombCalculus

namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.StationaryMap

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The state potential with the explicit common central quadratic, K = 20. -/
def statePotential (a y : E) (s : E × E) : ℝ :=
  pairCost (s.1 - y) + pairCost (s.1 - s.2) + pairCost (s.2 - y) -
    ((5 : ℝ) / 2 - 10 * ‖s.1‖ ^ 2) -
    ((5 : ℝ) / 4 * ⟪a, s.2 + a⟫ - 10 * ‖s.2 + a‖ ^ 2)

/-- The concrete stationary equation, with parameter first and state second. -/
def stationary (a : E) (p : E × (E × E)) : E × E :=
  (pairGradient (p.2.1 - p.1) + pairGradient (p.2.1 - p.2.2) + (20 : ℝ) • p.2.1,
   pairGradient (p.2.2 - p.2.1) + pairGradient (p.2.2 - p.1) -
     (5 / 4 : ℝ) • a + (20 : ℝ) • (p.2.2 + a))

/-- Analyticity of the actual stationary equation on pairwise-distinct triples. -/
theorem contDiffAt_stationary (a : E) {p : E × (E × E)}
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hzy : p.2.2 ≠ p.1)
    {n : WithTop ENat} : ContDiffAt ℝ n (stationary a) p := by
  have hY : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hX : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p :=
    contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p :=
    contDiffAt_snd.snd
  have hXY := (contDiffAt_pairGradient (sub_ne_zero.mpr hxy)).comp p (hX.sub hY)
  have hXZ := (contDiffAt_pairGradient (sub_ne_zero.mpr hxz)).comp p (hX.sub hZ)
  have hZX := (contDiffAt_pairGradient (sub_ne_zero.mpr hxz.symm)).comp p (hZ.sub hX)
  have hZY := (contDiffAt_pairGradient (sub_ne_zero.mpr hzy)).comp p (hZ.sub hY)
  exact ((hXY.add hXZ).add (hX.const_smul (20 : ℝ))).prodMk
    (((hZX.add hZY).sub contDiffAt_const).add ((hZ.add contDiffAt_const).const_smul (20 : ℝ)))

/-- Analyticity of the state potential away from all collisions. -/
theorem contDiffAt_statePotential (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y)
    {n : WithTop ENat} : ContDiffAt ℝ n (statePotential a y) s := by
  have hX : ContDiffAt ℝ n (fun q : E × E => q.1) s := contDiffAt_fst
  have hZ : ContDiffAt ℝ n (fun q : E × E => q.2) s := contDiffAt_snd
  have hXY := (contDiffAt_pairCost (sub_ne_zero.mpr hxy)).comp s
    (hX.sub contDiffAt_const)
  have hXZ := (contDiffAt_pairCost (sub_ne_zero.mpr hxz)).comp s (hX.sub hZ)
  have hZY := (contDiffAt_pairCost (sub_ne_zero.mpr hzy)).comp s
    (hZ.sub contDiffAt_const)
  exact (((hXY.add hXZ).add hZY).sub
    (contDiffAt_const.sub (contDiffAt_const.mul (hX.norm_sq ℝ)))).sub
    ((contDiffAt_const.mul (contDiffAt_const.inner ℝ (hZ.add contDiffAt_const))).sub
      (contDiffAt_const.mul ((hZ.add contDiffAt_const).norm_sq ℝ)))

/-- The scalar potential with parameter and state bundled together. -/
def jointPotential (a : E) (p : E × (E × E)) : ℝ := statePotential a p.1 p.2

/-- Joint parameter/state analyticity on pairwise-distinct triples. -/
theorem contDiffAt_jointPotential (a : E) {p : E × (E × E)}
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hzy : p.2.2 ≠ p.1)
    {n : WithTop ENat} : ContDiffAt ℝ n (jointPotential a) p := by
  have hY : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hX : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p := contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p := contDiffAt_snd.snd
  have hXY := (contDiffAt_pairCost (sub_ne_zero.mpr hxy)).comp p (hX.sub hY)
  have hXZ := (contDiffAt_pairCost (sub_ne_zero.mpr hxz)).comp p (hX.sub hZ)
  have hZY := (contDiffAt_pairCost (sub_ne_zero.mpr hzy)).comp p (hZ.sub hY)
  exact (((hXY.add hXZ).add hZY).sub
    (contDiffAt_const.sub (contDiffAt_const.mul (hX.norm_sq ℝ)))).sub
    ((contDiffAt_const.mul (contDiffAt_const.inner ℝ (hZ.add contDiffAt_const))).sub
      (contDiffAt_const.mul ((hZ.add contDiffAt_const).norm_sq ℝ)))

/-- The linear form represented by the two components of the stationary map. -/
def stateDifferential (a y : E) (s : E × E) : E × E →L[ℝ] ℝ :=
  (innerSL ℝ (stationary a (y, s)).1).comp (ContinuousLinearMap.fst ℝ E E) +
    (innerSL ℝ (stationary a (y, s)).2).comp (ContinuousLinearMap.snd ℝ E E)

/-- The displayed stationary equation really is the state derivative of the supporting potential. -/
theorem hasFDerivAt_statePotential (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y) :
    HasFDerivAt (statePotential a y) (stateDifferential a y s) s := by
  have hX : HasFDerivAt (fun q : E × E => q.1)
      (ContinuousLinearMap.fst ℝ E E) s := hasFDerivAt_fst
  have hZ : HasFDerivAt (fun q : E × E => q.2)
      (ContinuousLinearMap.snd ℝ E E) s := hasFDerivAt_snd
  have hXY := (hasFDerivAt_pairCost (sub_ne_zero.mpr hxy)).comp s (hX.sub_const y)
  have hXZ := (hasFDerivAt_pairCost (sub_ne_zero.mpr hxz)).comp s (hX.sub hZ)
  have hZY := (hasFDerivAt_pairCost (sub_ne_zero.mpr hzy)).comp s (hZ.sub_const y)
  have h := (((hXY.add hXZ).add hZY).sub
    ((hasFDerivAt_const ((5 : ℝ) / 2) s).sub (hX.norm_sq.const_mul 10))).sub
    ((((hasFDerivAt_const a s).inner ℝ (hZ.add_const a)).const_mul ((5 : ℝ) / 4)).sub
      ((hZ.add_const a).norm_sq.const_mul 10))
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [stateDifferential, stationary, pairGradient, mul_sub, norm_sub_rev s.2 s.1]
  ring

/-- The full parameter/state derivative of the concrete stationary equation. -/
def stationaryDifferential (p : E × (E × E)) :
    E × (E × E) →L[ℝ] E × E :=
  let Y := ContinuousLinearMap.fst ℝ E (E × E)
  let X := (ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))
  let Z := (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))
  ((pairHessian (p.2.1 - p.1)).comp (X - Y) +
      (pairHessian (p.2.1 - p.2.2)).comp (X - Z) + (20 : ℝ) • X).prod
    ((pairHessian (p.2.2 - p.2.1)).comp (Z - X) +
      (pairHessian (p.2.2 - p.1)).comp (Z - Y) + (20 : ℝ) • Z)

theorem hasFDerivAt_stationary (a : E) {p : E × (E × E)}
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hzy : p.2.2 ≠ p.1) :
    HasFDerivAt (stationary a) (stationaryDifferential p) p := by
  have hY : HasFDerivAt (fun q : E × (E × E) => q.1)
      (ContinuousLinearMap.fst ℝ E (E × E)) p := hasFDerivAt_fst
  have hX : HasFDerivAt (fun q : E × (E × E) => q.2.1)
      ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))) p :=
    (hasFDerivAt_fst (𝕜 := ℝ)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hZ : HasFDerivAt (fun q : E × (E × E) => q.2.2)
      ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))) p :=
    (hasFDerivAt_snd (𝕜 := ℝ)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hXY := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hxy)).comp p (hX.sub hY)
  have hXZ := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hxz)).comp p (hX.sub hZ)
  have hZX := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hxz.symm)).comp p (hZ.sub hX)
  have hZY := (hasFDerivAt_pairGradient (sub_ne_zero.mpr hzy)).comp p (hZ.sub hY)
  exact ((hXY.add hXZ).add (hX.const_smul (20 : ℝ))).prodMk
    (((hZX.add hZY).sub_const ((5 / 4 : ℝ) • a)).add ((hZ.add_const a).const_smul (20 : ℝ)))

/-- A zero of the explicit stationary map is a stationary point of the scalar potential. -/
theorem hasFDerivAt_statePotential_zero (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y)
    (hzero : stationary a (y, s) = 0) :
    HasFDerivAt (statePotential a y) (0 : E × E →L[ℝ] ℝ) s := by
  have h := hasFDerivAt_statePotential a y hxy hxz hzy
  simpa [stateDifferential, hzero] using h

end Problem356.StationaryMap

end

end OAI
