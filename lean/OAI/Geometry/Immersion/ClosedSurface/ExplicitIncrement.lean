import OAI.Geometry.Immersion.ClosedSurface.FiniteIncrement

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open Set
open ClosedSurfaceR4.QuadraticMean (sumDisplacement displacement)

theorem constructed_quadratic_correction_explicit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {φ ψ u : ι → Base → ℝ} {S : ι → Set Base}
    (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    (d : ∀ l : QuadraticLabel ι, SupportedSolveChart F (quadraticPhase φ l) (quadraticSupport S l))
    {τ s P : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hP : 0 ≤ P) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q r m : ℕ)
    (b : ∀ i, FreeBudget (c i) (u i) τ s q (m + r + 1 + 1))
    (g : ∀ l, ForcedGeometryBudget (d l) τ s r m)
    (hpφ : ∀ i v, ‖v‖ ≤ 1 → WeightedBound univ s (m + r + 1) P (coordDeriv v (φ i))) :
    let Q : ℝ := 4 * 2 ^ (m + r + 1) * ((1 + 2 ^ (m + r + 1) * P) * ∑ i, (b i).slowSize) ^ 2
    let B := (∑ l, (g l).sizeFactor) * Q
    let R := (∑ l, (g l).errorFactor) * Q
    0 ≤ B ∧ 0 ≤ R ∧ ∀ δ : ℝ, 0 ≤ δ →
      let Z := fun i => (c i).amplitude (u i) δ τ q
      let V := fun p => ∑ l, (d l).solve τ (quadraticAmplitude τ φ Z l) r p
      ContDiff ℝ ∞ V ∧ tsupport V ⊆ ⋃ i, S i ∧
      WeightedBound univ τ m (B * δ ^ 2) V ∧
      WeightedBound univ τ m (R * (τ / s) ^ (r + 1) * δ ^ 2)
        (fun p => realLinearizedTensor F V p + nonzeroPhaseSum τ φ Z p) := by
  classical
  let Q : ℝ := 4 * 2 ^ (m + r + 1) * ((1 + 2 ^ (m + r + 1) * P) * ∑ i, (b i).slowSize) ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨mul_nonneg (Finset.sum_nonneg fun l _ => (g l).sizeFactor_nonneg) hQ,
    mul_nonneg (Finset.sum_nonneg fun l _ => (g l).errorFactor_nonneg) hQ, ?_⟩
  intro δ hδ
  dsimp only
  let Z := fun i => (c i).amplitude (u i) δ τ q
  have hZ (i) := (c i).amplitude_smooth (b i).smoothAmplitude δ τ q
  have hbA := weighted_free_quadraticAmplitude c hδ hτ hs hτs hs1 hP hφ b hpφ
  have hA := quadraticAmplitude_smooth hφ (fun i => (hZ i).1) τ
  let budget := fun l => (g l).toSolveBudget hs hs1 (mul_nonneg hQ (sq_nonneg δ)) (hA l) (hbA l)
  obtain ⟨hsm, hsp, hsize, hres⟩ := finite_quadratic_cancellation hF hφ
    (fun i => (hZ i).1) (fun i => (hZ i).2) d hτ hs hτs hs1 r m budget
  refine ⟨hsm, hsp, ?_, ?_⟩
  · have he : (∑ l, (budget l).size) = ((∑ l, (g l).sizeFactor) * Q) * δ ^ 2 := by
      simp only [budget, ForcedGeometryBudget.toSolveBudget_size, ← Finset.sum_mul]
      ring
    rwa [he] at hsize
  · have he : (∑ l, (budget l).residual) =
        ((∑ l, (g l).errorFactor) * Q) * (τ / s) ^ (r + 1) * δ ^ 2 := by
      simp only [budget, ForcedGeometryBudget.toSolveBudget_residual, ← Finset.sum_mul]
      ring
    rwa [he] at hres


theorem constructed_finite_increment_explicit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {φ ψ u : ι → Base → ℝ} {S : ι → Set Base}
    (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    (d : ∀ l : QuadraticLabel ι, SupportedSolveChart F (quadraticPhase φ l) (quadraticSupport S l))
    {τ s P : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hP : 0 ≤ P) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q m : ℕ)
    (b : ∀ i, FreeBudget (c i) (u i) τ s q (m + 1 + q + 1 + 1))
    (g : ∀ l, ForcedGeometryBudget (d l) τ s q (m + 1))
    (hpφ : ∀ i v, ‖v‖ ≤ 1 → WeightedBound univ s (m + 1 + q + 1) P (coordDeriv v (φ i))) :
    let low := fun i => (b i).mono_order (r := m + 1) (by omega)
    let A : ℝ := ∑ i, (low i).size
    let L : ℝ := ∑ i, (low i).errorFactor
    let Q : ℝ := 4 * 2 ^ (m + 1 + q + 1) * ((1 + 2 ^ (m + 1 + q + 1) * P) * ∑ i, (b i).slowSize) ^ 2
    let B := (∑ l, (g l).sizeFactor) * Q
    let R := (∑ l, (g l).errorFactor) * Q
    let C := A + B
    let E := L + R
    let T := 4 * 2 ^ m * (2 * A * B + B ^ 2)
    0 ≤ C ∧ 0 ≤ E ∧ 0 ≤ T ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ τ →
      let Z := fun i => (c i).amplitude (u i) δ τ q
      let X := sumDisplacement τ φ Z
      let V := fun p => ∑ l, (d l).solve τ (quadraticAmplitude τ φ Z l) q p
      let U := fun p => X p + V p
      ContDiff ℝ ∞ U ∧ tsupport U ⊆ ⋃ i, S i ∧
      WeightedBound univ τ m (C * (δ * τ)) U ∧
      WeightedBound univ τ m (E * δ * (τ / s) ^ (q + 1) + T * (δ ^ 3 / τ))
        (fun p => realMetricTensor (fun x => F x + U x) p - realMetricTensor F p - zeroPhaseSum τ φ Z p) := by
  classical
  let low := fun i => (b i).mono_order (r := m + 1) (by omega)
  let A : ℝ := ∑ i, (low i).size
  let L : ℝ := ∑ i, (low i).errorFactor
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => (low i).size_nonneg
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => (low i).errorFactor_nonneg
  let Q : ℝ := 4 * 2 ^ (m + 1 + q + 1) * ((1 + 2 ^ (m + 1 + q + 1) * P) * ∑ i, (b i).slowSize) ^ 2
  let B := (∑ l, (g l).sizeFactor) * Q
  let R := (∑ l, (g l).errorFactor) * Q
  have hh := constructed_quadratic_correction_explicit hF c d hτ hs hτs hs1
    hP hφ q q (m + 1) b g hpφ
  obtain ⟨hB, hR, hv⟩ := hh
  refine ⟨add_nonneg hA hB,
    add_nonneg hL hR, by positivity, ?_⟩
  intro δ hδ hδτ
  dsimp only
  let Z := fun i => (c i).amplitude (u i) δ τ q
  let X := sumDisplacement τ φ Z
  let V := fun p => ∑ l, (d l).solve τ (quadraticAmplitude τ φ Z l) q p
  obtain ⟨hZ, hX, hXsp, hXb, hXr⟩ := finite_free_displacement hF c hδ hτ hs hτs hs1 q (m + 1) low
  obtain ⟨hV, hVsp, hVb, hVr⟩ := hv δ hδ
  have hXS : ContDiffOn ℝ ∞ X univ := hX.contDiffOn
  have hVS : ContDiffOn ℝ ∞ V univ := hV.contDiffOn
  have hXb' : WeightedBound univ τ (m + 1) (A * δ * τ) X := by
    convert hXb using 1
    first | rfl | ring
  have hc := weighted_cubic_remainder isOpen_univ hτ hδ hδτ hA hB hXS hVS hXb' hVb
  have hXS0 := contDiffOn_realLinearizedTensor isOpen_univ hF.contDiffOn hXS
  have hVS0 := (contDiffOn_realLinearizedTensor isOpen_univ hF.contDiffOn hVS).add
    (contDiff_nonzeroPhaseSum hφ (fun i => (hZ i).1) τ).contDiffOn
  have hCS0 := (contDiffOn_realLinearizedTensor isOpen_univ hXS hVS).add
    (contDiffOn_realMetricTensor isOpen_univ hVS)
  have hη : 0 ≤ (τ / s) ^ (q + 1) := by positivity
  have hτ1 := hτs.trans hs1
  have hδ1 := hδτ.trans hτ1
  have hXR : WeightedBound univ τ m (L * δ * (τ / s) ^ (q + 1)) (realLinearizedTensor F X) := by
    apply (hXr.mono_order (Nat.le_succ m)).mono_const
    have he : (∑ i, (low i).residual) * (δ * τ) = L * δ * (τ / s) ^ (q + 1) * τ := by
      simp only [FreeBudget.residual_eq, ← Finset.sum_mul, L]
      ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hτ1
  have hVR : WeightedBound univ τ m (R * δ * (τ / s) ^ (q + 1))
      (fun p => realLinearizedTensor F V p + nonzeroPhaseSum τ φ Z p) := by
    apply (hVr.mono_order (Nat.le_succ m)).mono_const
    have hd2 : δ ^ 2 ≤ δ := by nlinarith
    calc
      R * (τ / s) ^ (q + 1) * δ ^ 2 ≤ R * (τ / s) ^ (q + 1) * δ :=
        mul_le_mul_of_nonneg_left hd2 (mul_nonneg hR hη)
      _ = _ := by ring
  refine ⟨hX.add hV, ?_, ?_, ?_⟩
  · intro p hp
    by_contra hn
    have hx : p ∉ tsupport X := fun hh => hn (hXsp hh)
    have hy : p ∉ tsupport V := fun hh => hn (hVsp hh)
    have he : (fun p => X p + V p) =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx,
        notMem_tsupport_iff_eventuallyEq.mp hy] with x hx hy
      simp [hx, hy]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hp
  · have hb := (hXb.mono_order (Nat.le_succ m)).add isOpen_univ.uniqueDiffOn hτ.le hXS hVS
      (hVb.mono_order (Nat.le_succ m))
    apply hb.mono_const
    change A * (δ * τ) + B * δ ^ 2 ≤ (A + B) * (δ * τ)
    nlinarith [mul_le_mul_of_nonneg_left hδτ (mul_nonneg hB hδ)]
  · have hb := ((hXR.add isOpen_univ.uniqueDiffOn hτ.le hXS0 hVS0 hVR).add
      isOpen_univ.uniqueDiffOn hτ.le (hXS0.add hVS0) hCS0 hc)
    have he : L * δ * (τ / s) ^ (q + 1) + R * δ * (τ / s) ^ (q + 1) +
        (4 : ℝ) * 2 ^ m * (2 * A * B + B ^ 2) * (δ ^ 3 / τ) =
        (L + R) * δ * (τ / s) ^ (q + 1) +
        4 * 2 ^ m * (2 * A * B + B ^ 2) * (δ ^ 3 / τ) := by ring
    norm_num only [Nat.cast_ofNat] at hb
    rw [he] at hb
    apply hb.congr
    intro p hp
    have hh := finite_phase_metric_identity (hF.differentiable (by simp) p)
      (hV.differentiable (by simp) p) (fun i => (hφ i).differentiable (by simp) p)
      (fun i => (hZ i).1.differentiable (by simp) p) τ (zeroPhaseSum τ φ Z)
    simpa only [Z, X, V, sub_self, add_zero] using hh


end ClosedSurfaceR4.RealModes

end

end OAI
