import OAI.Analysis.Brenier.CellEnergy
import OAI.Analysis.Brenier.FixedMass
import OAI.Analysis.Brenier.MassDerivative
import OAI.Analysis.Brenier.StationaryMoment

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358.CellGeometry

/-- The stationary moment estimate in the face-coordinate form required by the
mass-Jacobian argument. The two derivative hypotheses are ordinary derivatives
of the actual closed-cell integrals, not quantitative inequalities. -/
theorem stationary_face_moment_estimate
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c q : ι → ℝ)
    (hy : Function.Injective y) (R : ℝ) (hR : 0 ≤ R)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i)
    (hmass : ∀ i, (uniformMeasure K).real (closedCell K y c i) = m i)
    (g : ι → ι → ℝ) (b : ι → ι → E d)
    (hB : ∀ i, HasDerivAt
      (fun s : ℝ => ∫ x in closedCell K y (fun j => c j + s * q j) i,
        x ∂uniformMeasure K) (∑ j, (q i - q j) • b i j) 0)
    (hM : ∀ i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real
        (closedCell K y (fun j => c j + s * q j) i))
      (CellLaplacian.apply g q i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
      162 * R ^ 2 * ∑ i, (CellLaplacian.apply g q i) ^ 2 / m i := by
  have hpos : ∀ i, 0 < (uniformMeasure K).real (closedCell K y c i) := by
    intro i
    rw [hmass i]
    exact hm i
  simpa only [hmass] using stationary_moment_derivative_of_convex_midpoint
    hK hconv hKi y c q hy R hR hbounded
    (fun i => ∑ j, (q i - q j) • b i j) (CellLaplacian.apply g q) hpos hB hM hmid

/-- Actual cell derivatives and convex-body midpoint couplings supply the full
weighted intercept-energy estimate. No moment inequality or inverse-Jacobian
estimate is assumed: the stationary estimate and connected range argument are
both invoked internally. -/
theorem fixed_mass_intercept_energy_of_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (R : ℝ) (hR : 0 ≤ R)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (m r : ι → ℝ) (v : ι → E d) {w : ℝ}
    (hm : ∀ i, 0 < m i)
    (hmass : ∀ i, (uniformMeasure K).real (closedCell K y c i) = m i)
    (g : ι → ι → ℝ) (b : ι → ι → E d)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (hmean : ∑ i, m i * r i = 0)
    (hfixed : ∀ i, CellLaplacian.apply g r i +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hB : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => ∫ x in closedCell K y (fun j => c j + s * q j) i,
        x ∂uniformMeasure K) (∑ j, (q i - q j) • b i j) 0)
    (hM : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real
        (closedCell K y (fun j => c j + s * q j) i))
      (CellLaplacian.apply g q i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    (∑ i, m i * r i ^ 2) ≤ 162 * R ^ 2 * w ^ 2 := by
  apply Problem358.fixed_mass_intercept_energy_le_162 g b hg hb hg0 G hG hpos
    m r v hm hmean hfixed hspeed
  intro q
  exact stationary_face_moment_estimate hK hconv hKi y c q hy R hR hbounded
    m hm hmass g b (hB q) (hM q) hmid

end Problem358.CellGeometry

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal ContDiff

namespace Problem358.FixedMassIntercepts

/-- The canonical prescribed-mass intercept path has the required uniform
weighted derivative energy. All branch existence, uniqueness, differentiability,
normalization and fixed-mass differentiation are supplied internally. The
remaining inputs are the actual geometric mass/moment differentials and the
convex-body midpoint coupling. -/
theorem intercepts_comp_deriv_energy_le_of_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (Y : ℝ → (ι → E d)) (v : ι → E d) (t : ℝ)
    (hY : HasDerivAt Y v t) (hy : Function.Injective (Y t))
    (R : ℝ) (hR : 0 ≤ R) {w : ℝ}
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (g : ι → ι → ℝ) (b : ι → ι → E d)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hC1 : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (Y t, intercepts hK hconv hKi m hm hsum (Y t)))
    (hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A
      (Y t, intercepts hK hconv hKi m hm hsum (Y t)))
    (hA : ∀ q : CellLaplacian.normalizedSpace m, A (0, q) = CellLaplacian.apply g q)
    (hsite : A (v, 0) = CellLaplacian.siteFlux b v)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hB : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => ∫ x in CellGeometry.closedCell K (Y t)
        (fun j => (intercepts hK hconv hKi m hm hsum (Y t) : ι → ℝ) j + s * q j) i,
        x ∂uniformMeasure K) (∑ j, (q i - q j) • b i j) 0)
    (hM : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real (CellGeometry.closedCell K (Y t)
        (fun j => (intercepts hK hconv hKi m hm hsum (Y t) : ι → ℝ) j + s * q j) i))
      (CellLaplacian.apply g q i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    let C := fun q => intercepts hK hconv hKi m hm hsum (Y q)
    HasDerivAt C (deriv C t) t ∧
      (∑ i, m i * ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i ^ 2) ≤
        162 * R ^ 2 * w ^ 2 := by
  let C := fun q => intercepts hK hconv hKi m hm hsum (Y q)
  have hregular := contDiffAt_intercepts_of_massDifferential hK hconv hKi m hm hsum
    (Y t) hy g hg hg0 G hG hpos A hC1 hD hA
  have hs := hregular.differentiableAt (by norm_num)
  obtain ⟨hdC, hfixed, hmean⟩ := hasDerivAt_intercepts_comp_and_mass_constraint
    hK hconv hKi m hm hsum Y v t hY hy hs A hD
  refine ⟨hdC, ?_⟩
  apply CellGeometry.fixed_mass_intercept_energy_of_convex_midpoint
    hK hconv hKi (Y t) (C t) hy R hR hbounded m
    ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) v hm
    (fun i => congrFun (intercepts_spec hK hconv hKi m hm hsum (Y t) hy) i)
    g b hg hb hg0 G hG hpos hmean _ hspeed hB hM hmid
  have hsplit : A (v, deriv C t) = A (v, 0) + A (0, deriv C t) := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [hsplit, hA, hsite] at hfixed
  intro i
  have hi := congrFun hfixed i
  change CellLaplacian.siteFlux b v i + CellLaplacian.apply g
    ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i = 0 at hi
  simpa only [CellLaplacian.siteFlux, add_comm] using hi

end Problem358.FixedMassIntercepts

namespace Problem358.CellGeometry

/-- Any Fréchet derivative of the actual normalized mass map has the canonical
geometric formula. This follows by uniqueness from the proved line derivative;
it is independent of how the bounded linear operator was constructed. -/
theorem normalizedMassMap_derivative_apply
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (m : ι → ℝ) (y : ι → E d) (c : CellLaplacian.normalizedSpace m)
    (hy : Function.Injective y) (hpos : ∀ i, ρ (closedCell K y c i) ≠ 0)
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hD : HasFDerivAt (normalizedMassMap K m) A (y, c))
    (v : ι → E d) (q : CellLaplacian.normalizedSpace m) :
    A (v, q) = CellLaplacian.apply (PositiveFacet.canonicalFaceWeight K y c) q +
      CellLaplacian.siteFlux (faceMoment K y c) v := by
  classical
  have hd := hD.hasLineDerivAt (v, q)
  change HasDerivAt (fun s : ℝ => normalizedMassMap K m ((y, c) + s • (v, q)))
    (A (v, q)) 0 at hd
  funext i
  apply (hasDerivAt_pi.mp hd i).unique
  simpa [normalizedMassMap, CellLaplacian.apply, CellLaplacian.siteFlux,
    PositiveFacet.canonicalFaceWeight, Finset.sum_add_distrib,
    Pi.add_def, Pi.smul_def, smul_eq_mul] using
    hasDerivAt_uniformMass_line hρ hK hconv y v c q hy hpos i

end Problem358.CellGeometry

namespace Problem358.FixedMassIntercepts

/-- Genuine C¹ regularity of the normalized mass map implies C¹ regularity of
the canonical prescribed-mass choice. The geometric derivative and connected
Laplacian are identified internally, independently of any operator API. -/
theorem contDiffAt_intercepts_of_normalizedMassC1
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y)
    (hC1 : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (y, intercepts hK hconv hKi m hm hsum y)) :
    ContDiffAt ℝ 1 (intercepts hK hconv hKi m hm hsum) y := by
  classical
  let c := intercepts hK hconv hKi m hm hsum y
  let g := PositiveFacet.canonicalFaceWeight K y c
  have hρ : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hpos : ∀ i, uniformMeasure K (CellGeometry.closedCell K y c i) ≠ 0 := by
    intro i hz
    have hi := congrFun (intercepts_spec hK hconv hKi m hm hsum y hy) i
    change (uniformMeasure K).real (CellGeometry.closedCell K y c i) = m i at hi
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hi
    exact (hm i).ne' hi.symm
  obtain ⟨G, hG, hGp⟩ := PositiveFacet.canonicalFaceWeight_connected
    (uniformMeasure K) hρ K hK hconv y c hy hpos
  let A := fderiv ℝ (CellGeometry.normalizedMassMap K m) (y, c)
  have hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A (y, c) :=
    (hC1.differentiableAt (by norm_num)).hasFDerivAt
  apply contDiffAt_intercepts_of_massDifferential hK hconv hKi m hm hsum y hy g
    (PositiveFacet.canonicalFaceWeight_symm K y c)
    (PositiveFacet.canonicalFaceWeight_nonneg K y c) G hG hGp A hC1 hD
  intro q
  funext i
  simpa [CellLaplacian.siteFlux, g] using congrFun
    (CellGeometry.normalizedMassMap_derivative_apply hρ hK hconv m y c hy hpos A hD 0 q) i

/-- Pointwise derivative energy for the actual canonical intercepts, with every
face, graph, mass and moment differential supplied by the geometry. Only C¹
regularity of the actual normalized mass map and the convex midpoint coupling
remain as analytic inputs. No operator formula or chosen-branch hypothesis is
assumed. -/
theorem intercepts_comp_deriv_energy_le_of_massC1_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (Y : ℝ → (ι → E d)) (v : ι → E d) (t : ℝ)
    (hY : HasDerivAt Y v t) (hy : Function.Injective (Y t))
    (R : ℝ) (hR : 0 ≤ R) {w : ℝ}
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hC1 : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (Y t, intercepts hK hconv hKi m hm hsum (Y t)))
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    let C := fun q => intercepts hK hconv hKi m hm hsum (Y q)
    HasDerivAt C (deriv C t) t ∧
      (∑ i, m i * ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i ^ 2) ≤
        162 * R ^ 2 * w ^ 2 := by
  classical
  let c := intercepts hK hconv hKi m hm hsum (Y t)
  let g := PositiveFacet.canonicalFaceWeight K (Y t) c
  let b := CellGeometry.faceMoment K (Y t) c
  have hρ : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hpos : ∀ i, uniformMeasure K (CellGeometry.closedCell K (Y t) c i) ≠ 0 := by
    intro i hz
    have hi := congrFun (intercepts_spec hK hconv hKi m hm hsum (Y t) hy) i
    change (uniformMeasure K).real (CellGeometry.closedCell K (Y t) c i) = m i at hi
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hi
    exact (hm i).ne' hi.symm
  obtain ⟨G, hG, hGp⟩ := PositiveFacet.canonicalFaceWeight_connected
    (uniformMeasure K) hρ K hK hconv (Y t) c hy hpos
  let A := fderiv ℝ (CellGeometry.normalizedMassMap K m) (Y t, c)
  have hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A (Y t, c) :=
    (hC1.differentiableAt (by norm_num)).hasFDerivAt
  have hformula := CellGeometry.normalizedMassMap_derivative_apply
    hρ hK hconv m (Y t) c hy hpos A hD
  apply intercepts_comp_deriv_energy_le_of_convex_midpoint hK hconv hKi m hm hsum
    Y v t hY hy R hR hbounded g b
    (PositiveFacet.canonicalFaceWeight_symm K (Y t) c)
    (CellGeometry.faceMoment_symm K (Y t) c)
    (PositiveFacet.canonicalFaceWeight_nonneg K (Y t) c) G hG hGp A hC1 hD
  · intro q
    funext i
    simpa [CellLaplacian.siteFlux, b, g] using congrFun (hformula 0 q) i
  · funext i
    simpa [CellLaplacian.apply, b, g] using congrFun (hformula v 0) i
  · exact hspeed
  · intro q i
    exact PositiveCellFullDerivative.hasDerivAt_uniform_closedCell_moment_stationary
      hρ hK hconv (Y t) c q hy hpos i
  · intro q i
    simpa [CellLaplacian.apply, g, PositiveFacet.canonicalFaceWeight] using
      CellGeometry.hasDerivAt_uniformMass_line hρ hK hconv (Y t) (fun _ => 0) c q hy hpos i
  · exact hmid

end Problem358.FixedMassIntercepts

end

end OAI
