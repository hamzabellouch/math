import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedComplement
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalH1

namespace OAI

/-! The corrected orbital span lies in the actual one-electron weak-H1
domain, with arbitrary complex coefficients in each spin component. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedOneElectronValue (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (c : SpinConfiguration 1 → Fin m → ℂ) (s : SpinConfiguration 1) (x : Configuration 1) : ℂ :=
  ∑ i, c s i*(correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ)

private theorem lifted_corrected_mode_C1 (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) :
    ContDiff ℝ 1 (fun x : Configuration 1 =>
      (correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((correctedLocalizedMode_C1 freq u i).comp
    oneElectronCoordinates.contDiff)

private theorem lifted_corrected_mode_partial (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Configuration 1) (b : Fin 3) :
    fderiv ℝ (fun y : Configuration 1 =>
      (correctedLocalizedMode freq u i (oneElectronCoordinates y) : ℂ)) x
        (EuclideanSpace.single (0,b) 1) =
      (fderiv ℝ (correctedLocalizedMode freq u i) (oneElectronCoordinates x)
        (EuclideanSpace.single b 1) : ℂ) := by
  have hr := ((correctedLocalizedMode_C1 freq u i).differentiable (by norm_num)
    (oneElectronCoordinates x)).hasFDerivAt.comp x
      oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt
  have h := congrArg (fun L : Configuration 1 →L[ℝ] ℂ =>
    L (EuclideanSpace.single (0,b) 1)) (Complex.ofRealCLM.hasFDerivAt.comp x hr).fderiv
  simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    oneElectronCoordinates_single, Function.comp_def] using h

theorem correctedOneElectronValue_C1 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (c : SpinConfiguration 1 → Fin m → ℂ) (s : SpinConfiguration 1) :
    ContDiff ℝ 1 (correctedOneElectronValue freq u c s) :=
  ContDiff.sum (fun i _ => contDiff_const.mul (lifted_corrected_mode_C1 freq u i))

theorem correctedOneElectronValue_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) : MemLp (correctedOneElectronValue freq u c s) 2 :=
  memLp_finsetSum Finset.univ (fun i _ =>
    ((correctedLocalizedMode_memLp hfreq u i).ofReal.comp_measurePreserving
      oneElectronCoordinates.measurePreserving).const_mul (c s i))

theorem correctedOneElectronValue_partial (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) (x : Configuration 1) (b : Fin 3) :
    fderiv ℝ (correctedOneElectronValue freq u c s) x (EuclideanSpace.single (0,b) 1) =
      ∑ i, c s i*(fderiv ℝ (correctedLocalizedMode freq u i) (oneElectronCoordinates x)
        (EuclideanSpace.single b 1) : ℂ) := by
  have hd (i : Fin m) := (lifted_corrected_mode_C1 freq u i).differentiable (by norm_num) x
  unfold correctedOneElectronValue
  rw [fderiv_fun_sum (fun i _ => (hd i).const_mul (c s i))]
  simp only [sum_apply, fderiv_const_mul (hd _),
    smul_apply, smul_eq_mul, lifted_corrected_mode_partial]

theorem correctedOneElectronValue_partial_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) (a : Fin 1 × Fin 3) :
    MemLp (fun x => fderiv ℝ (correctedOneElectronValue freq u c s) x
      (EuclideanSpace.single a 1)) 2 := by
  obtain ⟨a,b⟩ := a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  simp_rw [correctedOneElectronValue_partial]
  exact memLp_finsetSum Finset.univ (fun i _ =>
    ((correctedLocalizedMode_partial_memLp hfreq u i b).ofReal.comp_measurePreserving
      oneElectronCoordinates.measurePreserving).const_mul (c s i))

def correctedOneElectronState {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ) : Coulomb.H1Vector 1 :=
  classicalH1State (correctedOneElectronValue freq u c) (correctedOneElectronValue_C1 freq u c)
    (correctedOneElectronValue_memLp hfreq u c) (correctedOneElectronValue_partial_memLp hfreq u c)

theorem correctedOneElectronOrbital_orthonormal {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) :
    Orthonormal ℂ (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
      (correctedLocalizedMode_memLp hfreq u i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [L2.inner_def]
  have hL2 (k : Fin m) : MemLp (fun x : Configuration 1 =>
      (correctedLocalizedMode freq u k (oneElectronCoordinates x) : ℂ)) 2 :=
    (correctedLocalizedMode_memLp hfreq u k).ofReal.comp_measurePreserving
      oneElectronCoordinates.measurePreserving
  have he : (∫ x : Configuration 1, inner ℂ
      (oneElectronOrbitalLp (correctedLocalizedMode freq u i) (correctedLocalizedMode_memLp hfreq u i) x)
      (oneElectronOrbitalLp (correctedLocalizedMode freq u j) (correctedLocalizedMode_memLp hfreq u j) x)) =
      (∫ x : Configuration 1, ((correctedLocalizedMode freq u i (oneElectronCoordinates x)*
        correctedLocalizedMode freq u j (oneElectronCoordinates x) : ℝ) : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [(hL2 i).coeFn_toLp, (hL2 j).coeFn_toLp] with x hi hj
    change inner ℂ ((hL2 i).toLp _ x) ((hL2 j).toLp _ x) = _
    rw [hi,hj,RCLike.inner_apply]
    simp only [Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [he, integral_complex_ofReal]
  rw [oneElectronCoordinates_integral (fun x =>
    correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x),
    correctedLocalizedMode_inner hfreq u hsep hs]
  split_ifs <;> simp

theorem correctedOneElectronState_coordinate {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) :
    h1Coordinates (correctedOneElectronState hfreq u c) (Sum.inl s) =
      ∑ i, c s i • oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i) := by
  let w (i : Fin m) := oneElectronOrbitalLp (correctedLocalizedMode freq u i)
    (correctedLocalizedMode_memLp hfreq u i)
  have hw (i : Fin m) : (c s i • w i : Lp ℂ 2 (volume : Measure (Configuration 1))) =ᵐ[volume]
      fun x => c s i*(correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ) := by
    have hmem : MemLp (fun x : Configuration 1 =>
        (correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ)) 2 :=
      (correctedLocalizedMode_memLp hfreq u i).ofReal.comp_measurePreserving
        oneElectronCoordinates.measurePreserving
    have hi := hmem.coeFn_toLp
    filter_upwards [Lp.coeFn_smul (c s i) (w i), hi] with x hsm hi
    rw [hsm]
    change c s i*(w i x) = _
    rw [show w i x = (correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ) from hi]
  have hwall := Filter.eventually_all.2 hw
  apply Lp.ext
  filter_upwards [(h1Coordinate_memLp (correctedOneElectronState hfreq u c) (Sum.inl s)).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => c s i • w i), hwall] with x hx hy hz
  change h1Coordinates (correctedOneElectronState hfreq u c) (Sum.inl s) x = _ at hx
  rw [hy, hx]
  change (∑ i, c s i*(correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact (hz i).symm

def correctedOneElectronCoefficients {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1)
    (s : SpinConfiguration 1) (i : Fin m) : ℂ :=
  inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
    (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s))

def correctedOneElectronProjection {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1) : Coulomb.H1Vector 1 :=
  correctedOneElectronState hfreq u (correctedOneElectronCoefficients hfreq u v)

def correctedOneElectronRemainder {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1) : Coulomb.H1Vector 1 :=
  v.add ((correctedOneElectronProjection hfreq u v).rsmul (-1))

theorem correctedOneElectronRemainder_coordinate {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) :
    h1Coordinates (correctedOneElectronRemainder hfreq u v) (Sum.inl s) =
      h1Coordinates v (Sum.inl s)-
        ∑ i, correctedOneElectronCoefficients hfreq u v s i •
          oneElectronOrbitalLp (correctedLocalizedMode freq u i) (correctedLocalizedMode_memLp hfreq u i) := by
  rw [← correctedOneElectronState_coordinate hfreq u (correctedOneElectronCoefficients hfreq u v) s]
  apply Lp.ext
  filter_upwards [(h1Coordinate_memLp (correctedOneElectronRemainder hfreq u v) (Sum.inl s)).coeFn_toLp,
    (h1Coordinate_memLp v (Sum.inl s)).coeFn_toLp,
    (h1Coordinate_memLp (correctedOneElectronProjection hfreq u v) (Sum.inl s)).coeFn_toLp,
    Lp.coeFn_sub (h1Coordinates v (Sum.inl s))
      (h1Coordinates (correctedOneElectronProjection hfreq u v) (Sum.inl s))] with x hr hv hp hs
  change h1Coordinates (correctedOneElectronRemainder hfreq u v) (Sum.inl s) x =
    (h1Coordinates v (Sum.inl s)-h1Coordinates (correctedOneElectronProjection hfreq u v) (Sum.inl s)) x
  rw [hs]
  simp only [Pi.sub_apply]
  change h1Coordinates v (Sum.inl s) x = v.value s x at hv
  change h1Coordinates (correctedOneElectronProjection hfreq u v) (Sum.inl s) x =
    (correctedOneElectronProjection hfreq u v).value s x at hp
  change h1Coordinates (correctedOneElectronRemainder hfreq u v) (Sum.inl s) x =
    (correctedOneElectronRemainder hfreq u v).value s x at hr
  rw [hv,hp,hr]
  change v.value s x+((-1:ℝ):ℂ)*(correctedOneElectronProjection hfreq u v).value s x = _
  push_cast
  ring

theorem correctedOneElectronRemainder_orthogonal {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (v : Coulomb.H1Vector 1)
    (s : SpinConfiguration 1) (i : Fin m) :
    inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
      (correctedLocalizedMode_memLp hfreq u i))
      (h1Coordinates (correctedOneElectronRemainder hfreq u v) (Sum.inl s)) = 0 := by
  rw [correctedOneElectronRemainder_coordinate, inner_sub_right]
  have ho := correctedOneElectronOrbital_orthonormal hfreq u hsep hs
  rw [ho.inner_right_sum (correctedOneElectronCoefficients hfreq u v s) (Finset.mem_univ i)]
  exact sub_self _

private theorem orthonormal_combination_norm {m : ℕ}
    (w : Fin m → Lp ℂ 2 (volume : Measure (Configuration 1)))
    (hw : Orthonormal ℂ w) (c : Fin m → ℂ) :
    ‖∑ i, c i • w i‖^2 = ∑ i, ‖c i‖^2 := by
  have hz (z : ℂ) : (starRingEnd ℂ) z*z = (‖z‖^2 : ℝ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.sq_norm, Complex.normSq_apply]
      ring
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
      ring
  have h := congrArg Complex.re (hw.inner_sum c c Finset.univ)
  simp only [inner_self_eq_norm_sq_to_K, hz] at h
  norm_cast at h

theorem correctedOneElectronState_mass {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (c : SpinConfiguration 1 → Fin m → ℂ) :
    Coulomb.mass (correctedOneElectronState hfreq u c) = ∑ s, ∑ i, ‖c s i‖^2 := by
  rw [mass_eq_graphMass]
  unfold graphMass
  apply Finset.sum_congr rfl
  intro s _
  rw [correctedOneElectronState_coordinate]
  exact orthonormal_combination_norm _ (correctedOneElectronOrbital_orthonormal hfreq u hsep hs) _

theorem correctedOneElectronProjection_mass {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (v : Coulomb.H1Vector 1) :
    Coulomb.mass (correctedOneElectronProjection hfreq u v) =
      graphOrbitalMass (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v) :=
  correctedOneElectronState_mass hfreq u hsep hs _

theorem correctedOneElectron_mass_decomposition {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (v : Coulomb.H1Vector 1) :
    Coulomb.mass v = Coulomb.mass (correctedOneElectronProjection hfreq u v)+
      Coulomb.mass (correctedOneElectronRemainder hfreq u v) := by
  simp only [mass_eq_graphMass, graphMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hp := correctedOneElectronState_coordinate hfreq u (correctedOneElectronCoefficients hfreq u v) s
  change h1Coordinates (correctedOneElectronProjection hfreq u v) (Sum.inl s) = _ at hp
  have horth : inner ℂ (h1Coordinates (correctedOneElectronProjection hfreq u v) (Sum.inl s))
      (h1Coordinates (correctedOneElectronRemainder hfreq u v) (Sum.inl s)) = 0 := by
    rw [hp, sum_inner]
    simp only [inner_smul_left, correctedOneElectronRemainder_orthogonal hfreq u hsep hs,
      mul_zero, Finset.sum_const_zero]
  have he : h1Coordinates v (Sum.inl s) =
      h1Coordinates (correctedOneElectronProjection hfreq u v) (Sum.inl s)+
      h1Coordinates (correctedOneElectronRemainder hfreq u v) (Sum.inl s) := by
    rw [correctedOneElectronRemainder_coordinate, hp]
    abel
  rw [he]
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth

end ContinuumCoulomb

end

end OAI
