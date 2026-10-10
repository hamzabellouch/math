import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.InducedSphereAlgebra

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 3) ℝ

def radiusSq : Poly := ∑ i : Fin 3, X i ^ 2

def laplacian : Poly →ₗ[ℝ] Poly :=
  ∑ i : Fin 3, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

def radialHarmonicSpan (n : ℕ) : Submodule ℝ Poly :=
  Submodule.span ℝ {p | ∃ j l : ℕ, ∃ h : Poly,
    h.IsHomogeneous l ∧ laplacian h = 0 ∧ 2 * j + l = n ∧
      p = radiusSq ^ j * h}

lemma laplacian_apply (p : Poly) :
    laplacian p = ∑ i : Fin 3, pderiv i (pderiv i p) := by
  simp [laplacian]

lemma radiusSq_homogeneous : radiusSq.IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i hi
  exact isHomogeneous_X_pow i 2

lemma pderiv_radiusSq (i : Fin 3) : pderiv i radiusSq = 2 * X i := by
  fin_cases i <;> simp [radiusSq, Fin.sum_univ_three]

lemma laplacian_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (laplacian p).IsHomogeneous (n - 2) := by
  rw [laplacian_apply]
  apply IsHomogeneous.sum
  intro i hi
  simpa [Nat.sub_sub] using (hp.pderiv (i := i)).pderiv (i := i)

lemma laplacian_radiusSq_mul (p : Poly) :
    laplacian (radiusSq * p) = radiusSq * laplacian p +
      4 * (∑ i : Fin 3, X i * pderiv i p) + 6 * p := by
  simp only [laplacian_apply, pderiv_mul, pderiv_radiusSq, map_add,
    pderiv_X_self, Derivation.map_natCast, show (2 : Poly) = (2 : ℕ) by rfl]
  simp only [Fin.sum_univ_three]
  ring

lemma laplacian_radiusSq_mul_homogeneous {p : Poly} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    laplacian (radiusSq * p) = radiusSq * laplacian p + (4 * (n : ℝ) + 6) • p := by
  rw [laplacian_radiusSq_mul, hp.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul, smul_eq_C_mul, map_add, map_mul, map_natCast, map_ofNat]
  ring

lemma laplacian_radial_power {h : Poly} {l : ℕ}
    (hh : h.IsHomogeneous l) (hΔ : laplacian h = 0) (j : ℕ) :
    laplacian (radiusSq ^ (j + 1) * h) =
      ((2 * (j : ℝ) + 2) * (2 * (l : ℝ) + 2 * (j : ℝ) + 3)) •
        (radiusSq ^ j * h) := by
  induction j with
  | zero =>
    rw [pow_one, laplacian_radiusSq_mul_homogeneous hh, hΔ]
    simp only [mul_zero, zero_add, pow_zero, one_mul, Nat.cast_zero, add_zero]
    congr 1
    ring
  | succ j ih =>
    have hg := (radiusSq_homogeneous.pow (j + 1)).mul hh
    have hmul : radiusSq * (radiusSq ^ j * h) = radiusSq ^ (j + 1) * h := by ring
    calc
      laplacian (radiusSq ^ (j + 1 + 1) * h) =
          laplacian (radiusSq * (radiusSq ^ (j + 1) * h)) := by congr 1; ring
      _ = radiusSq * laplacian (radiusSq ^ (j + 1) * h) +
          (4 * ((2 * (j + 1) + l : ℕ) : ℝ) + 6) • (radiusSq ^ (j + 1) * h) :=
        laplacian_radiusSq_mul_homogeneous hg
      _ = (((2 * (j : ℝ) + 2) * (2 * (l : ℝ) + 2 * (j : ℝ) + 3)) +
          (4 * ((2 * (j + 1) + l : ℕ) : ℝ) + 6)) •
            (radiusSq ^ (j + 1) * h) := by
        rw [ih, mul_smul_comm, hmul, ← add_smul]
      _ = _ := by congr 1; push_cast; ring

lemma radialHarmonicSpan_le_homogeneous (n : ℕ) :
    radialHarmonicSpan n ≤ homogeneousSubmodule (Fin 3) ℝ n := by
  apply Submodule.span_le.mpr
  rintro p ⟨j, l, h, hh, hΔ, hn, rfl⟩
  change (radiusSq ^ j * h).IsHomogeneous n
  rw [← hn]
  exact (radiusSq_homogeneous.pow j).mul hh

lemma harmonic_mem_radialHarmonicSpan {h : Poly} {n : ℕ}
    (hh : h.IsHomogeneous n) (hΔ : laplacian h = 0) :
    h ∈ radialHarmonicSpan n := by
  apply Submodule.subset_span
  refine ⟨0, n, h, hh, hΔ, by omega, ?_⟩
  simp

lemma radialHarmonicSpan_le_map_laplacian (n : ℕ) :
    radialHarmonicSpan n ≤ (radialHarmonicSpan (n + 2)).map laplacian := by
  apply Submodule.span_le.mpr
  rintro p ⟨j, l, h, hh, hΔ, hn, rfl⟩
  let a : ℝ := (2 * (j : ℝ) + 2) * (2 * (l : ℝ) + 2 * (j : ℝ) + 3)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  refine ⟨a⁻¹ • (radiusSq ^ (j + 1) * h), ?_, ?_⟩
  · apply (radialHarmonicSpan (n + 2)).smul_mem
    apply Submodule.subset_span
    exact ⟨j + 1, l, h, hh, hΔ, by omega, rfl⟩
  · rw [map_smul, laplacian_radial_power hh hΔ, smul_smul]
    change (a⁻¹ * a) • _ = _
    simp [ha]

lemma laplacian_homogeneous_low {p : Poly} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n < 2) : laplacian p = 0 := by
  rw [laplacian_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hd := hp.pderiv (i := i)
  have hdeg : n - 1 = 0 := by omega
  rw [hdeg] at hd
  have hC : pderiv i p = C ((pderiv i p).coeff 0) := by
    apply totalDegree_eq_zero_iff_eq_C.mp
    exact (totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hd
  rw [hC, pderiv_C]

theorem harmonic_radial_decomposition (n : ℕ) :
    homogeneousSubmodule (Fin 3) ℝ n ≤ radialHarmonicSpan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hp
    change p.IsHomogeneous n at hp
    by_cases hn : n < 2
    · exact harmonic_mem_radialHarmonicSpan hp (laplacian_homogeneous_low hp hn)
    · have hlt : n - 2 < n := by omega
      have hpΔ : laplacian p ∈ radialHarmonicSpan (n - 2) :=
        ih (n - 2) hlt (laplacian_homogeneous hp)
      have hpre := radialHarmonicSpan_le_map_laplacian (n - 2) hpΔ
      obtain ⟨q, hq, hqΔ⟩ := hpre
      have hn' : n - 2 + 2 = n := by omega
      rw [hn'] at hq
      have hqhom : q.IsHomogeneous n := radialHarmonicSpan_le_homogeneous n hq
      have hhΔ : laplacian (p - q) = 0 := by rw [map_sub, hqΔ, sub_self]
      have hh := harmonic_mem_radialHarmonicSpan (hp.sub hqhom) hhΔ
      simpa using (radialHarmonicSpan n).add_mem hh hq

def rotation (i j : Fin 3) : Derivation ℝ Poly Poly :=
  (X i : Poly) • pderiv j - (X j : Poly) • pderiv i

def euler : Derivation ℝ Poly Poly := ∑ i : Fin 3, (X i : Poly) • pderiv i

lemma rotation_apply (i j : Fin 3) (p : Poly) :
    rotation i j p = X i * pderiv j p - X j * pderiv i p := by
  simp [rotation, smul_eq_mul]

lemma euler_apply (p : Poly) : euler p = ∑ i : Fin 3, X i * pderiv i p := by
  simp [euler, Fin.sum_univ_three, Derivation.smul_apply, smul_eq_mul]

lemma euler_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    euler p = (n : ℝ) • p := by
  rw [euler_apply, hp.sum_X_mul_pderiv, Nat.cast_smul_eq_nsmul ℝ]

lemma pderiv_commute (i j : Fin 3) (p : Poly) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp_all [map_add, pderiv_X] <;> ring

lemma laplacian_X_mul (i : Fin 3) (p : Poly) :
    laplacian (X i * p) = X i * laplacian p + 2 * pderiv i p := by
  fin_cases i <;>
    simp [laplacian_apply, Fin.sum_univ_three, map_add, pderiv_X] <;> ring

lemma laplacian_pderiv (i : Fin 3) (p : Poly) :
    laplacian (pderiv i p) = pderiv i (laplacian p) := by
  simp only [laplacian_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pderiv_commute j i p, pderiv_commute j i (pderiv j p)]

lemma laplacian_rotation (i j : Fin 3) (p : Poly) :
    laplacian (rotation i j p) = rotation i j (laplacian p) := by
  rw [rotation_apply, map_sub, laplacian_X_mul, laplacian_X_mul,
    laplacian_pderiv, laplacian_pderiv, rotation_apply, pderiv_commute i j p]
  ring

lemma rotation_homogeneous (i j : Fin 3) {p : Poly} {n : ℕ}
    (hp : p.IsHomogeneous n) : (rotation i j p).IsHomogeneous n := by
  cases n with
  | zero =>
    have hC := totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
    rw [hC, rotation_apply]
    simpa using (isHomogeneous_zero (σ := Fin 3) (R := ℝ) 0)
  | succ n =>
    rw [rotation_apply]
    have hi := (isHomogeneous_X (R := ℝ) i).mul (hp.pderiv (i := j))
    have hj := (isHomogeneous_X (R := ℝ) j).mul (hp.pderiv (i := i))
    simpa [Nat.add_comm] using hi.sub hj

lemma rotation_casimir (p : Poly) :
    rotation 0 1 (rotation 0 1 p) + rotation 0 2 (rotation 0 2 p) +
      rotation 1 2 (rotation 1 2 p) =
      radiusSq * laplacian p - euler (euler p) - euler p := by
  simp [rotation_apply, euler_apply, laplacian_apply, radiusSq,
    Fin.sum_univ_three, map_add, map_sub, pderiv_X]
  ring

theorem harmonic_rotation_eigenvalue {h : Poly} {l : ℕ}
    (hh : h.IsHomogeneous l) (hΔ : laplacian h = 0) :
    rotation 0 1 (rotation 0 1 h) + rotation 0 2 (rotation 0 2 h) +
      rotation 1 2 (rotation 1 2 h) = -((l : ℝ) * ((l : ℝ) + 1)) • h := by
  rw [rotation_casimir, hΔ, euler_homogeneous hh, Derivation.map_smul, euler_homogeneous hh]
  simp only [mul_zero, zero_sub, smul_smul, ← neg_smul, ← sub_smul]
  congr 1
  ring

def sphereCoordinate (i : Fin 3) : C(Sphere, ℝ) :=
  ⟨fun x => x.1 i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩

def sphereEval : Poly →ₐ[ℝ] C(Sphere, ℝ) := aeval sphereCoordinate

def harmonicPolynomials (l : ℕ) : Submodule ℝ Poly :=
  homogeneousSubmodule (Fin 3) ℝ l ⊓ LinearMap.ker laplacian

def harmonicSpace (l : ℕ) : Submodule ℝ C(Sphere, ℝ) :=
  (harmonicPolynomials l).map sphereEval.toLinearMap

lemma sphereEval_X (i : Fin 3) : sphereEval (X i) = sphereCoordinate i :=
  aeval_X _ _

lemma sphereEval_radiusSq : sphereEval radiusSq = 1 := by
  ext x
  simp only [radiusSq, map_sum, map_pow, sphereEval_X, ContinuousMap.sum_apply,
    ContinuousMap.pow_apply, ContinuousMap.one_apply, sphereCoordinate]
  have hx : ‖x.1‖ = 1 := by simp
  change (∑ i : Fin 3, x.1 i ^ 2) = 1
  simpa [hx] using (EuclideanSpace.real_norm_sq_eq x.1).symm

lemma polynomialRestrictions_separate : sphereEval.range.SeparatesPoints := by
  intro x y hxy
  have hcoord : ∃ i : Fin 3, x.1 i ≠ y.1 i := by
    by_contra! h
    apply hxy
    apply Subtype.ext
    exact PiLp.ext h
  obtain ⟨i, hi⟩ := hcoord
  exact ⟨sphereCoordinate i, ⟨sphereCoordinate i, ⟨X i, sphereEval_X i⟩, rfl⟩, hi⟩

lemma radialRestriction_mem_harmonicSpan (n : ℕ) :
    radialHarmonicSpan n ≤
      (⨆ l : ℕ, harmonicSpace l).comap sphereEval.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro p ⟨j, l, h, hh, hΔ, hn, rfl⟩
  change sphereEval (radiusSq ^ j * h) ∈ ⨆ l : ℕ, harmonicSpace l
  rw [map_mul, map_pow, sphereEval_radiusSq, one_pow, one_mul]
  exact (le_iSup (fun l => harmonicSpace l) l) ⟨h, ⟨hh, hΔ⟩, rfl⟩

lemma polynomialRestriction_mem_harmonicSpan (p : Poly) :
    sphereEval p ∈ ⨆ l : ℕ, harmonicSpace l := by
  rw [← sum_homogeneousComponent p, map_sum]
  apply Submodule.sum_mem
  intro n hn
  exact radialRestriction_mem_harmonicSpan n
    (harmonic_radial_decomposition n (homogeneousComponent_mem n p))

theorem spherical_harmonics_dense :
    (⨆ l : ℕ, harmonicSpace l).topologicalClosure = ⊤ := by
  apply top_unique
  intro f hf
  have h := ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints
    sphereEval.range polynomialRestrictions_separate f
  exact (closure_mono (show (sphereEval.range : Set C(Sphere, ℝ)) ⊆
      ((⨆ l : ℕ, harmonicSpace l : Submodule ℝ C(Sphere, ℝ)) : Set C(Sphere, ℝ)) from by
    rintro g ⟨p, rfl⟩
    exact polynomialRestriction_mem_harmonicSpan p)) h

instance harmonicPolynomials_finite (l : ℕ) :
    Module.Finite ℝ (harmonicPolynomials l) :=
  Module.Finite.iff_fg.mpr
    ((homogeneousSubmodule_fg (Fin 3) ℝ l).of_le inf_le_left)

instance harmonicSpace_finite (l : ℕ) : Module.Finite ℝ (harmonicSpace l) :=
  Module.Finite.iff_fg.mpr
    ((Module.Finite.iff_fg.mp (harmonicPolynomials_finite l)).map sphereEval.toLinearMap)

open MeasureTheory

abbrev SphereL2 := Lp ℝ 2 surfaceMeasure

def toL2 : C(Sphere, ℝ) →L[ℝ] SphereL2 := ContinuousMap.toLp 2 surfaceMeasure ℝ

def harmonicL2 (l : ℕ) : Submodule ℝ SphereL2 :=
  (harmonicSpace l).map toL2.toLinearMap

instance harmonicL2_finite (l : ℕ) : Module.Finite ℝ (harmonicL2 l) :=
  Module.Finite.iff_fg.mpr
    ((Module.Finite.iff_fg.mp (harmonicSpace_finite l)).map toL2.toLinearMap)

def harmonicProjection (l : ℕ) : SphereL2 →L[ℝ] harmonicL2 l :=
  (harmonicL2 l).orthogonalProjectionOnto

lemma harmonicProjection_norm_le (l : ℕ) (f : SphereL2) :
    ‖harmonicProjection l f‖ ≤ ‖f‖ :=
  (harmonicL2 l).norm_orthogonalProjectionOnto_apply_le f

theorem spherical_harmonics_L2_dense :
    (⨆ l : ℕ, harmonicL2 l).topologicalClosure = ⊤ := by
  have hmap := Submodule.topologicalClosure_map toL2 (⨆ l : ℕ, harmonicSpace l)
  rw [spherical_harmonics_dense, Submodule.map_top, Submodule.map_iSup] at hmap
  have hclosed := (⨆ l : ℕ, harmonicL2 l).isClosed_topologicalClosure
  have hd : DenseRange toL2 := ContinuousMap.toLp_denseRange ℝ surfaceMeasure ℝ (by norm_num)
  apply top_unique
  intro f hf
  apply closure_minimal (t := ((⨆ l : ℕ, harmonicL2 l).topologicalClosure : Set SphereL2))
    (s := Set.range toL2) ?_ hclosed (hd f)
  rintro g ⟨c, rfl⟩
  exact hmap ⟨c, rfl⟩

lemma toL2_injective : Function.Injective toL2 :=
  ContinuousMap.toLp_injective surfaceMeasure

def harmonicContinuousEquiv (l : ℕ) : harmonicSpace l ≃ₗ[ℝ] harmonicL2 l :=
  Submodule.equivMapOfInjective toL2.toLinearMap toL2_injective (harmonicSpace l)

def harmonicCoefficient (l : ℕ) : SphereL2 →L[ℝ] C(Sphere, ℝ) :=
  (harmonicSpace l).subtypeL.comp
    ((harmonicContinuousEquiv l).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (harmonicProjection l))

lemma harmonicCoefficient_mem (l : ℕ) (f : SphereL2) :
    harmonicCoefficient l f ∈ harmonicSpace l :=
  ((harmonicContinuousEquiv l).symm (harmonicProjection l f)).property

lemma toL2_harmonicCoefficient (l : ℕ) (f : SphereL2) :
    toL2 (harmonicCoefficient l f) = (harmonicProjection l f : SphereL2) := by
  exact congrArg Subtype.val
    ((harmonicContinuousEquiv l).apply_symm_apply (harmonicProjection l f))

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

lemma sphereHome_val (u : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) :
    (sphereHome u x).1 = u x.1 := rfl

lemma volume_preimage_isometry (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Ambient) :
    (volume : Measure Ambient) (u ⁻¹' s) = volume s := by
  have hm := u.toHomeomorph.toMeasurableEquiv.map_apply (μ := volume) s
  change (Measure.map u volume) s = volume (u ⁻¹' s) at hm
  rw [u.measurePreserving.map_eq] at hm
  exact hm.symm

lemma sphereCone_preimage (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Sphere) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereHome u ⁻¹' s)) =
      u ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨r, hr, u v.1, ⟨sphereHome u v, hv, rfl⟩, (u.map_smul r v.1).symm⟩
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, hx⟩
    refine ⟨r, hr, u.symm v.1, ⟨sphereHome u.symm v, ?_, rfl⟩, ?_⟩
    · change sphereHome u (sphereHome u.symm v) ∈ s
      have h : sphereHome u (sphereHome u.symm v) = v := by
        apply Subtype.ext
        exact u.apply_symm_apply v.1
      simpa [h] using hv
    · apply u.injective
      simpa using hx

theorem sphereHome_measurePreserving (u : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereHome u) surfaceMeasure surfaceMeasure := by
  refine ⟨(sphereHome u).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereHome u).continuous.measurable hs,
    Measure.toSphere_apply' _ (hs.preimage (sphereHome u).continuous.measurable),
    Measure.toSphere_apply' _ hs, sphereCone_preimage, volume_preimage_isometry]

def planeRotationMap (i j : Fin 3) (t : ℝ) : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun k =>
    if k = i then Real.cos t * x i - Real.sin t * x j
    else if k = j then Real.sin t * x i + Real.cos t * x j else x k)
  map_add' x y := by
    apply PiLp.ext
    intro k
    dsimp
    split_ifs <;> ring
  map_smul' a x := by
    apply PiLp.ext
    intro k
    dsimp
    split_ifs <;> ring

lemma planeRotationMap_apply (i j k : Fin 3) (t : ℝ) (x : Ambient) :
    planeRotationMap i j t x k =
      if k = i then Real.cos t * x i - Real.sin t * x j
      else if k = j then Real.sin t * x i + Real.cos t * x j else x k := rfl

lemma planeRotationMap_norm (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (x : Ambient) :
    ‖planeRotationMap i j t x‖ = ‖x‖ := by
  have hs : ‖planeRotationMap i j t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have h := congrArg (fun z : ℝ => z * (x i ^ 2 + x j ^ 2))
      (Real.cos_sq_add_sin_sq t)
    ring_nf at h
    fin_cases i <;> fin_cases j <;>
      simp_all [Fin.sum_univ_three, planeRotationMap_apply] <;> nlinarith
  nlinarith only [hs, norm_nonneg (planeRotationMap i j t x), norm_nonneg x]

lemma planeRotationMap_neg (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (x : Ambient) :
    planeRotationMap i j (-t) (planeRotationMap i j t x) = x := by
  apply PiLp.ext
  intro k
  by_cases hi : k = i
  · subst k
    simp [planeRotationMap_apply, hij.symm]
    linear_combination (x i) * (Real.cos_sq_add_sin_sq t)
  · by_cases hj : k = j
    · subst k
      simp [planeRotationMap_apply, hij.symm]
      linear_combination (x j) * (Real.cos_sq_add_sin_sq t)
    · simp [planeRotationMap_apply, hi, hj]

def planeRotation (i j : Fin 3) (hij : i ≠ j) (t : ℝ) :
    Ambient ≃ₗᵢ[ℝ] Ambient where
  toLinearEquiv :=
    { planeRotationMap i j t with
      invFun := planeRotationMap i j (-t)
      left_inv := planeRotationMap_neg i j hij t
      right_inv := by intro x; simpa using planeRotationMap_neg i j hij (-t) x }
  norm_map' := planeRotationMap_norm i j hij t

lemma planeRotation_apply (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (x : Ambient) :
    planeRotation i j hij t x = planeRotationMap i j t x := rfl


def rotatedCoordinate (i j : Fin 3) (t : ℝ) (k : Fin 3) : C(Sphere, ℝ) :=
  if k = i then Real.cos t • sphereCoordinate i - Real.sin t • sphereCoordinate j
  else if k = j then Real.sin t • sphereCoordinate i + Real.cos t • sphereCoordinate j
  else sphereCoordinate k

def rotationAction (i j : Fin 3) (t : ℝ) : Poly →ₐ[ℝ] C(Sphere, ℝ) :=
  aeval (rotatedCoordinate i j t)

lemma rotationAction_zero (i j : Fin 3) : rotationAction i j 0 = sphereEval := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [rotationAction, sphereEval, aeval_X, rotatedCoordinate, Real.cos_zero,
    Real.sin_zero, one_smul, zero_smul, sub_zero, zero_add]
  split_ifs with hi hj
  · subst k; rfl
  · subst k; rfl
  · rfl

lemma rotationAction_apply (i j : Fin 3) (hij : i ≠ j) (t : ℝ)
    (p : Poly) (x : Sphere) :
    rotationAction i j t p x = sphereEval p (sphereHome (planeRotation i j hij t) x) := by
  have h : (ContinuousMap.evalAlgHom ℝ ℝ x).comp (rotationAction i j t) =
      (ContinuousMap.evalAlgHom ℝ ℝ (sphereHome (planeRotation i j hij t) x)).comp
        sphereEval := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply, rotationAction,
      aeval_X, sphereEval]
    change rotatedCoordinate i j t k x = (planeRotationMap i j t x.1) k
    rw [planeRotationMap_apply]
    simp only [rotatedCoordinate]
    split_ifs <;> rfl
  exact congrArg (fun f : Poly →ₐ[ℝ] ℝ => f p) h

lemma rotatedCoordinate_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (k : Fin 3) :
    HasDerivAt (fun t => rotatedCoordinate i j t k)
      (sphereEval (rotation i j (X k))) 0 := by
  have hs := (Real.hasDerivAt_sin (0 : ℝ))
  have hc := (Real.hasDerivAt_cos (0 : ℝ))
  by_cases hi : k = i
  · subst k
    convert! (hc.smul_const (sphereCoordinate i)).sub
        (hs.smul_const (sphereCoordinate j)) using 1 <;>
      simp [rotatedCoordinate, rotation_apply, hij, pderiv_X, sphereEval_X]
    rfl
  · by_cases hj : k = j
    · subst k
      convert! (hs.smul_const (sphereCoordinate i)).add
          (hc.smul_const (sphereCoordinate j)) using 1 <;>
        simp [rotatedCoordinate, rotation_apply, hij.symm, pderiv_X, sphereEval_X]
      rfl
    · simpa [rotatedCoordinate, rotation_apply, hi, hj, Ne.symm hi, Ne.symm hj,
        pderiv_X] using hasDerivAt_const (0 : ℝ) (sphereCoordinate k)

lemma rotationAction_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (p : Poly) :
    HasDerivAt (fun t => rotationAction i j t p) (sphereEval (rotation i j p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [rotationAction, rotation_apply] using
      hasDerivAt_const (0 : ℝ) (algebraMap ℝ C(Sphere, ℝ) a)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> simp only [map_add]
    rfl
  | mul_X p k hp =>
    have hk : HasDerivAt (fun t => rotationAction i j t (X k))
        (sphereEval (rotation i j (X k))) 0 :=
      by simpa only [rotationAction, aeval_X] using
        rotatedCoordinate_hasDerivAt_zero i j hij k
    convert! hp.mul hk using 1
    · funext t; exact map_mul (rotationAction i j t) p (X k)
    · rw [Derivation.leibniz, map_add]
      simp only [smul_eq_mul, map_mul, rotationAction_zero]
      ring

def sphereIntegral : C(Sphere, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (toL2 1)).comp toL2

lemma sphereIntegral_apply (f : C(Sphere, ℝ)) :
    sphereIntegral f = ∫ x, f x ∂surfaceMeasure := by
  change inner ℝ (toL2 1) (toL2 f) = _
  rw [toL2, MeasureTheory.ContinuousMap.inner_toLp]
  simp

lemma sphereIntegral_rotationAction (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (p : Poly) :
    sphereIntegral (rotationAction i j t p) = sphereIntegral (sphereEval p) := by
  rw [sphereIntegral_apply, sphereIntegral_apply]
  simp only [rotationAction_apply i j hij]
  exact (sphereHome_measurePreserving (planeRotation i j hij t)).integral_comp
    (sphereHome (planeRotation i j hij t)).measurableEmbedding (sphereEval p)

theorem sphereIntegral_rotation (i j : Fin 3) (hij : i ≠ j) (p : Poly) :
    sphereIntegral (sphereEval (rotation i j p)) = 0 := by
  have hd := sphereIntegral.hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he : (fun t => sphereIntegral (rotationAction i j t p)) =
      fun _ => sphereIntegral (sphereEval p) := by
    funext t
    exact sphereIntegral_rotationAction i j hij t p
  change HasDerivAt (fun t => sphereIntegral (rotationAction i j t p)) _ 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 _)

lemma inner_sphereEval (p q : Poly) :
    inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval q)) =
      sphereIntegral (sphereEval (p * q)) := by
  rw [sphereIntegral_apply]
  change inner ℝ (ContinuousMap.toLp 2 surfaceMeasure ℝ (sphereEval p))
    (ContinuousMap.toLp 2 surfaceMeasure ℝ (sphereEval q)) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp [map_mul, mul_comm]

theorem rotation_skew_adjoint (i j : Fin 3) (hij : i ≠ j) (p q : Poly) :
    inner ℝ (toL2 (sphereEval (rotation i j p))) (toL2 (sphereEval q)) =
      -inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval (rotation i j q))) := by
  have h := sphereIntegral_rotation i j hij (p * q)
  rw [Derivation.leibniz] at h
  simp only [smul_eq_mul, map_add] at h
  rw [inner_sphereEval, inner_sphereEval]
  rw [mul_comm q] at h
  linarith

def angularLaplacian : Poly →ₗ[ℝ] Poly :=
  ((rotation 0 1).toLinearMap.comp (rotation 0 1).toLinearMap) +
  ((rotation 0 2).toLinearMap.comp (rotation 0 2).toLinearMap) +
  ((rotation 1 2).toLinearMap.comp (rotation 1 2).toLinearMap)

lemma angularLaplacian_apply (p : Poly) :
    angularLaplacian p = rotation 0 1 (rotation 0 1 p) +
      rotation 0 2 (rotation 0 2 p) + rotation 1 2 (rotation 1 2 p) := rfl

lemma rotation_square_symmetric (i j : Fin 3) (hij : i ≠ j) (p q : Poly) :
    inner ℝ (toL2 (sphereEval (rotation i j (rotation i j p)))) (toL2 (sphereEval q)) =
      inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval (rotation i j (rotation i j q)))) := by
  rw [rotation_skew_adjoint i j hij, rotation_skew_adjoint i j hij, neg_neg]

lemma angularLaplacian_symmetric (p q : Poly) :
    inner ℝ (toL2 (sphereEval (angularLaplacian p))) (toL2 (sphereEval q)) =
      inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval (angularLaplacian q))) := by
  simp only [angularLaplacian_apply, map_add, inner_add_left, inner_add_right]
  rw [rotation_square_symmetric 0 1 (by decide),
    rotation_square_symmetric 0 2 (by decide), rotation_square_symmetric 1 2 (by decide)]

def eigenvalue (l : ℕ) : ℝ := (l : ℝ) * ((l : ℝ) + 1)

lemma eigenvalue_injective : Function.Injective eigenvalue := by
  intro l m h
  apply Nat.cast_injective (R := ℝ)
  have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  change (l : ℝ) * ((l : ℝ) + 1) = (m : ℝ) * ((m : ℝ) + 1) at h
  rcases lt_trichotomy (l : ℝ) (m : ℝ) with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

lemma different_harmonics_inner_zero {l m : ℕ} (hlm : l ≠ m) {p q : Poly}
    (hp : p.IsHomogeneous l) (hΔp : laplacian p = 0)
    (hq : q.IsHomogeneous m) (hΔq : laplacian q = 0) :
    inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval q)) = 0 := by
  have h := angularLaplacian_symmetric p q
  rw [angularLaplacian_apply, harmonic_rotation_eigenvalue hp hΔp,
    angularLaplacian_apply, harmonic_rotation_eigenvalue hq hΔq] at h
  simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial] at h
  have he : eigenvalue l ≠ eigenvalue m := fun e => hlm (eigenvalue_injective e)
  have hz : (eigenvalue l - eigenvalue m) *
      inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval q)) = 0 := by
    dsimp [eigenvalue]
    linarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)

theorem harmonicL2_orthogonal {l m : ℕ} (hlm : l ≠ m) :
    (harmonicL2 l).IsOrtho (harmonicL2 m) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro f ⟨cf, ⟨p, ⟨hp, hΔp⟩, rfl⟩, rfl⟩
    g ⟨cg, ⟨q, ⟨hq, hΔq⟩, rfl⟩, rfl⟩
  exact different_harmonics_inner_zero hlm hp hΔp hq hΔq

lemma harmonicL2_orthogonalFamily :
    OrthogonalFamily ℝ (fun l => harmonicL2 l) (fun l => (harmonicL2 l).subtypeₗᵢ) := by
  intro l m hlm f g
  exact (harmonicL2_orthogonal hlm).inner_eq f.property g.property

theorem harmonicHilbertSum :
    IsHilbertSum ℝ (fun l => harmonicL2 l) (fun l => (harmonicL2 l).subtypeₗᵢ) :=
  IsHilbertSum.mkInternal harmonicL2 harmonicL2_orthogonalFamily
    (by rw [spherical_harmonics_L2_dense])

lemma harmonicProjection_other {l m : ℕ} (hlm : l ≠ m) (f : harmonicL2 m) :
    harmonicProjection l (f : SphereL2) = 0 := by
  apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
  exact (harmonicL2_orthogonal hlm).symm f.property

lemma harmonicHilbertSum_coefficient (f : SphereL2) (l : ℕ) :
    harmonicHilbertSum.linearIsometryEquiv f l = harmonicProjection l f := by
  let w := harmonicHilbertSum.linearIsometryEquiv f
  have hs : HasSum (fun m => ((w m : harmonicL2 m) : SphereL2)) f := by
    simpa [w] using harmonicHilbertSum.hasSum_linearIsometryEquiv_symm w
  have hsp := (harmonicProjection l).hasSum hs
  have hr : (fun m => harmonicProjection l (w m : SphereL2)) =
      fun m => if m = l then w l else 0 := by
    funext m
    split_ifs with hml
    · subst m
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    · exact harmonicProjection_other (Ne.symm hml) (w m)
  rw [hr] at hsp
  exact (hasSum_ite_eq l (w l)).unique hsp

theorem harmonicProjections_hasSum (f : SphereL2) :
    HasSum (fun l => (harmonicProjection l f : SphereL2)) f := by
  have hs := harmonicHilbertSum.hasSum_linearIsometryEquiv_symm
    (harmonicHilbertSum.linearIsometryEquiv f)
  convert! hs using 1
  · funext l
    simp only [harmonicHilbertSum_coefficient]
    rfl
  · exact (harmonicHilbertSum.linearIsometryEquiv.symm_apply_apply f).symm

lemma rotation_harmonic {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (i j : Fin 3) :
    (rotation i j p).IsHomogeneous l ∧ laplacian (rotation i j p) = 0 := by
  exact ⟨rotation_homogeneous i j hp, by rw [laplacian_rotation, hΔ, map_zero]⟩

lemma rotational_energy {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) :
    ‖toL2 (sphereEval (rotation 0 1 p))‖ ^ 2 +
      ‖toL2 (sphereEval (rotation 0 2 p))‖ ^ 2 +
      ‖toL2 (sphereEval (rotation 1 2 p))‖ ^ 2 =
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
  have h := congrArg (fun q : Poly => inner ℝ (toL2 (sphereEval q)) (toL2 (sphereEval p)))
    (harmonic_rotation_eigenvalue hp hΔ)
  simp only [map_add, map_smul, inner_add_left, inner_smul_left, conj_trivial] at h
  rw [rotation_skew_adjoint 0 1 (by decide), rotation_skew_adjoint 0 2 (by decide),
    rotation_skew_adjoint 1 2 (by decide)] at h
  simp only [real_inner_self_eq_norm_sq] at h
  unfold eigenvalue
  linarith

lemma eigenvalue_nonneg (l : ℕ) : 0 ≤ eigenvalue l := by unfold eigenvalue; positivity
lemma eigenvalue_pos {l : ℕ} (hl : l ≠ 0) : 0 < eigenvalue l := by
  have : 0 < (l : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)
  unfold eigenvalue
  positivity

lemma rotation_norm_le {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (i j : Fin 3) :
    ‖toL2 (sphereEval (rotation i j p))‖ ≤
      Real.sqrt (eigenvalue l) * ‖toL2 (sphereEval p)‖ := by
  have he := rotational_energy hp hΔ
  have hs := Real.sq_sqrt (eigenvalue_nonneg l)
  have hsq : ‖toL2 (sphereEval (rotation i j p))‖ ^ 2 ≤
      eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
    have hn01 := sq_nonneg ‖toL2 (sphereEval (rotation 0 1 p))‖
    have hn02 := sq_nonneg ‖toL2 (sphereEval (rotation 0 2 p))‖
    have hn12 := sq_nonneg ‖toL2 (sphereEval (rotation 1 2 p))‖
    have hrev : ∀ a b : Fin 3, rotation a b p = -rotation b a p := by
      intro a b; simp only [rotation_apply]; ring
    have hdiag : ∀ a : Fin 3, rotation a a p = 0 := by
      intro a; simp [rotation_apply]
    have h01 : ‖toL2 (sphereEval (rotation 0 1 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by linarith
    have h02 : ‖toL2 (sphereEval (rotation 0 2 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by linarith
    have h12 : ‖toL2 (sphereEval (rotation 1 2 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by linarith
    have h10 : ‖toL2 (sphereEval (rotation 1 0 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      rw [hrev 1 0, map_neg, map_neg, norm_neg]; exact h01
    have h20 : ‖toL2 (sphereEval (rotation 2 0 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      rw [hrev 2 0, map_neg, map_neg, norm_neg]; exact h02
    have h21 : ‖toL2 (sphereEval (rotation 2 1 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      rw [hrev 2 1, map_neg, map_neg, norm_neg]; exact h12
    have hdd (a : Fin 3) : ‖toL2 (sphereEval (rotation a a p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      simp only [hdiag, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (eigenvalue_nonneg l) (sq_nonneg _)
    fin_cases i <;> fin_cases j
    · exact hdd _
    · convert! h01 using 1
    · convert! h02 using 1
    · convert! h10 using 1
    · exact hdd _
    · convert! h12 using 1
    · convert! h20 using 1
    · convert! h21 using 1
    · exact hdd _
  have hn : 0 ≤ Real.sqrt (eigenvalue l) * ‖toL2 (sphereEval p)‖ := by positivity
  nlinarith only [hsq, hs, hn, norm_nonneg (toL2 (sphereEval (rotation i j p)))]

lemma sphereEval_rotation_of_zero {p : Poly} (hp : sphereEval p = 0)
    (i j : Fin 3) (hij : i ≠ j) : sphereEval (rotation i j p) = 0 := by
  have hd := rotationAction_hasDerivAt_zero i j hij p
  have he : (fun t => rotationAction i j t p) = fun _ => 0 := by
    funext t
    ext x
    rw [rotationAction_apply i j hij, hp]
    rfl
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 0)

lemma harmonicSpace_zero_constant (f : C(Sphere, ℝ)) (hf : f ∈ harmonicSpace 0) :
    ∃ c : ℝ, f = c • (1 : C(Sphere, ℝ)) := by
  obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hf
  have hC := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
  refine ⟨constantCoeff p, ?_⟩
  rw [hC]
  ext x
  simp [sphereEval]

lemma angular_kernel_constant {p : Poly} (hp : sphereEval (angularLaplacian p) = 0) :
    ∃ c : ℝ, sphereEval p = c • (1 : C(Sphere, ℝ)) := by
  have hproj : ∀ l : ℕ, l ≠ 0 → harmonicProjection l (toL2 (sphereEval p)) = 0 := by
    intro l hl
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    rw [Submodule.mem_orthogonal]
    rintro f ⟨cf, ⟨q, ⟨hq, hΔq⟩, rfl⟩, rfl⟩
    have h := angularLaplacian_symmetric q p
    rw [angularLaplacian_apply, harmonic_rotation_eigenvalue hq hΔq, hp] at h
    simp only [map_smul, map_zero, inner_zero_right, inner_smul_left, conj_trivial] at h
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (eigenvalue_pos hl).ne')
  have hs := harmonicProjections_hasSum (toL2 (sphereEval p))
  have he : (fun l => (harmonicProjection l (toL2 (sphereEval p)) : SphereL2)) =
      fun l => if l = 0 then (harmonicProjection 0 (toL2 (sphereEval p)) : SphereL2) else 0 := by
    funext l
    split_ifs with hl
    · subst l; rfl
    · rw [hproj l hl]; rfl
  rw [he] at hs
  have hh := hs.unique (hasSum_ite_eq 0 _)
  obtain ⟨c, hc⟩ := harmonicSpace_zero_constant
    (harmonicCoefficient 0 (toL2 (sphereEval p))) (harmonicCoefficient_mem _ _)
  refine ⟨c, toL2_injective ?_⟩
  rw [hh, ← toL2_harmonicCoefficient, hc]

abbrev HarmonicBasisIndex (l : ℕ) := Fin (Module.finrank ℝ (harmonicL2 l))
def harmonicBasis (l : ℕ) := stdOrthonormalBasis ℝ (harmonicL2 l)

lemma harmonicL2_exists_polynomial {l : ℕ} (v : harmonicL2 l) :
    ∃ p : Poly, p.IsHomogeneous l ∧ laplacian p = 0 ∧ toL2 (sphereEval p) = v := by
  obtain ⟨f, ⟨p, ⟨hp, hΔ⟩, rfl⟩, hf⟩ := v.property
  exact ⟨p, hp, hΔ, hf⟩

def harmonicBasisPolynomial (l : ℕ) (a : HarmonicBasisIndex l) : Poly :=
  Classical.choose (harmonicL2_exists_polynomial (harmonicBasis l a))

lemma harmonicBasisPolynomial_spec (l : ℕ) (a : HarmonicBasisIndex l) :
    (harmonicBasisPolynomial l a).IsHomogeneous l ∧
      laplacian (harmonicBasisPolynomial l a) = 0 ∧
      toL2 (sphereEval (harmonicBasisPolynomial l a)) = harmonicBasis l a :=
  Classical.choose_spec (harmonicL2_exists_polynomial (harmonicBasis l a))

lemma harmonic_polynomial_basis_expansion {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    sphereEval p = ∑ a : HarmonicBasisIndex l,
      inner ℝ (harmonicBasis l a : SphereL2) (toL2 (sphereEval p)) •
        sphereEval (harmonicBasisPolynomial l a) := by
  apply toL2_injective
  simp only [map_sum, map_smul, (harmonicBasisPolynomial_spec _ _).2.2]
  let v : harmonicL2 l := ⟨toL2 (sphereEval p), ⟨sphereEval p, ⟨p, ⟨hp, hΔ⟩, rfl⟩, rfl⟩⟩
  have ht := (congrArg (fun w : harmonicL2 l => (w : SphereL2))
      ((harmonicBasis l).sum_repr' v)).symm
  simp only [Submodule.coe_sum, Submodule.coe_smul] at ht
  convert! ht using 1

def harmonicKernelPolynomial (l : ℕ) : Poly :=
  ∑ a : HarmonicBasisIndex l, harmonicBasisPolynomial l a * harmonicBasisPolynomial l a

lemma harmonicKernel_rotation (l : ℕ) (i j : Fin 3) (hij : i ≠ j) :
    sphereEval (rotation i j (harmonicKernelPolynomial l)) = 0 := by
  ext x
  let p := harmonicBasisPolynomial l
  let z : HarmonicBasisIndex l → ℝ := fun a => sphereEval (p a) x
  let c : HarmonicBasisIndex l → HarmonicBasisIndex l → ℝ := fun a b =>
    inner ℝ (toL2 (sphereEval (p b))) (toL2 (sphereEval (rotation i j (p a))))
  have hskew (a b) : c a b = -c b a := by
    dsimp only [c]
    rw [real_inner_comm, rotation_skew_adjoint i j hij]
  have he (a) : sphereEval (rotation i j (p a)) x = ∑ b, c a b * z b := by
    have hp := harmonicBasisPolynomial_spec l a
    have hr := rotation_harmonic hp.1 hp.2.1 i j
    have hh := congrArg (fun f : C(Sphere, ℝ) => f x)
      (harmonic_polynomial_basis_expansion hr.1 hr.2)
    simpa only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      c, z, p, (harmonicBasisPolynomial_spec _ _).2.2] using hh
  have hs : (∑ a, ∑ b, c a b * z a * z b) = 0 := by
    have hh : (∑ a, ∑ b, c a b * z a * z b) = -(∑ a, ∑ b, c a b * z a * z b) := by
      calc
        (∑ a, ∑ b, c a b * z a * z b) = ∑ a, ∑ b, c b a * z b * z a :=
          Finset.sum_comm
        _ = -(∑ a, ∑ b, c a b * z a * z b) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          rw [hskew b a]
          ring
    linarith
  calc
    sphereEval (rotation i j (harmonicKernelPolynomial l)) x =
        ∑ a, 2 * ((∑ b, c a b * z b) * z a) := by
      simp only [harmonicKernelPolynomial, map_sum, Derivation.leibniz, smul_eq_mul,
        map_add, map_mul, ContinuousMap.sum_apply, ContinuousMap.add_apply,
        ContinuousMap.mul_apply]
      apply Finset.sum_congr rfl
      intro a ha
      change z a * sphereEval (rotation i j (p a)) x +
        z a * sphereEval (rotation i j (p a)) x = _
      rw [he]
      ring
    _ = 2 * ∑ a, ∑ b, c a b * z a * z b := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = 0 := by rw [hs]; ring

def sphereArea : ℝ := sphereIntegral 1

lemma sphereArea_pos : 0 < sphereArea := by
  have hn : toL2 1 ≠ 0 := by
    intro h
    have h' : (1 : C(Sphere, ℝ)) = 0 := toL2_injective (h.trans (map_zero toL2).symm)
    have hx : (Metric.sphere (0 : Ambient) 1).Nonempty :=
      (NormedSpace.sphere_nonempty.mpr (by norm_num))
    obtain ⟨x, hx⟩ := hx
    exact one_ne_zero (congrArg (fun f : C(Sphere, ℝ) => f ⟨x, hx⟩) h')
  have hh : sphereArea = ‖toL2 1‖ ^ 2 := by
    have h := inner_sphereEval 1 1
    simpa only [map_one, one_mul, real_inner_self_eq_norm_sq, sphereArea] using h.symm
  rw [hh]
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

lemma harmonicKernel_integral (l : ℕ) :
    sphereIntegral (sphereEval (harmonicKernelPolynomial l)) =
      (Module.finrank ℝ (harmonicL2 l) : ℝ) := by
  simp only [harmonicKernelPolynomial, map_sum, ← inner_sphereEval,
    (harmonicBasisPolynomial_spec _ _).2.2]
  have he (a : HarmonicBasisIndex l) : ‖(harmonicBasis l a : SphereL2)‖ = 1 := by
    change ‖harmonicBasis l a‖ = 1
    exact (harmonicBasis l).norm_eq_one a
  simp only [real_inner_self_eq_norm_sq, he, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma harmonicKernel_constant (l : ℕ) :
    sphereEval (harmonicKernelPolynomial l) =
      ((Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea) • (1 : C(Sphere, ℝ)) := by
  have hz : sphereEval (angularLaplacian (harmonicKernelPolynomial l)) = 0 := by
    simp only [angularLaplacian_apply, map_add,
      sphereEval_rotation_of_zero (harmonicKernel_rotation l 0 1 (by decide)) 0 1 (by decide),
      sphereEval_rotation_of_zero (harmonicKernel_rotation l 0 2 (by decide)) 0 2 (by decide),
      sphereEval_rotation_of_zero (harmonicKernel_rotation l 1 2 (by decide)) 1 2 (by decide),
      add_zero]
  obtain ⟨c, hc⟩ := angular_kernel_constant hz
  have hi := harmonicKernel_integral l
  rw [hc, map_smul] at hi
  change c * sphereArea = _ at hi
  rw [hc, ← hi, mul_div_cancel_right₀ _ sphereArea_pos.ne']

lemma harmonic_coefficients_sq_sum {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    (∑ a : HarmonicBasisIndex l,
      (inner ℝ (harmonicBasis l a : SphereL2) (toL2 (sphereEval p))) ^ 2) =
      ‖toL2 (sphereEval p)‖ ^ 2 := by
  let v : harmonicL2 l := ⟨toL2 (sphereEval p), ⟨sphereEval p, ⟨p, ⟨hp, hΔ⟩, rfl⟩, rfl⟩⟩
  convert! (harmonicBasis l).sum_sq_inner_right v using 1

lemma harmonic_sup_norm_le {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    ‖sphereEval p‖ ≤ Real.sqrt ((Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea) *
      ‖toL2 (sphereEval p)‖ := by
  have hpos : 0 ≤ (Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea :=
    div_nonneg (Nat.cast_nonneg _) sphereArea_pos.le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  have hf := congrArg (fun f : C(Sphere, ℝ) => f x)
    (harmonic_polynomial_basis_expansion hp hΔ)
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] at hf
  have hk := congrArg (fun f : C(Sphere, ℝ) => f x) (harmonicKernel_constant l)
  simp only [harmonicKernelPolynomial, map_sum, map_mul, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one] at hk
  simp only [← pow_two] at hk
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (HarmonicBasisIndex l))
    (fun a => inner ℝ (harmonicBasis l a : SphereL2) (toL2 (sphereEval p)))
    (fun a => sphereEval (harmonicBasisPolynomial l a) x)
  rw [← hf, harmonic_coefficients_sq_sum hp hΔ, hk] at hc
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hpos, Real.norm_eq_abs, sq_abs]
  nlinarith only [hc]

def boundedExponentEquiv (l : ℕ) :
    {d : Fin 3 →₀ ℕ // ∀ i, d i ≤ l} ≃ (Fin 3 → Fin (l+1)) where
  toFun d i := ⟨d.1 i, Nat.lt_succ_of_le (d.2 i)⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val),
    fun i => Nat.le_of_lt_succ (a i).isLt⟩
  left_inv d := by ext i; rfl
  right_inv a := by funext i; rfl

lemma restrictDegree_finrank (l : ℕ) :
    Module.finrank ℝ (restrictDegree (Fin 3) ℝ l) = (l+1)^3 := by
  let b := (basisRestrictSupport ℝ {d : Fin 3 →₀ ℕ | ∀ i, d i ≤ l}).reindex
    (boundedExponentEquiv l)
  have h := Module.finrank_eq_card_basis b
  simp only [Fintype.card_fun, Fintype.card_fin] at h
  convert! h using 1

lemma harmonic_dimension_le (l : ℕ) :
    Module.finrank ℝ (harmonicL2 l) ≤ (l+1)^3 := by
  calc
    Module.finrank ℝ (harmonicL2 l) ≤ Module.finrank ℝ (harmonicSpace l) :=
      Submodule.finrank_map_le _ _
    _ ≤ Module.finrank ℝ (harmonicPolynomials l) := Submodule.finrank_map_le _ _
    _ ≤ Module.finrank ℝ (restrictDegree (Fin 3) ℝ l) := by
      apply Submodule.finrank_mono
      intro p hp
      apply restrictTotalDegree_le_restrictDegree (Fin 3) ℝ l
      exact (mem_restrictTotalDegree _ _ _).mpr hp.1.totalDegree_le
    _ = (l+1)^3 := restrictDegree_finrank l

lemma harmonic_sup_norm_polynomial {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    ‖sphereEval p‖ ≤ (sphereArea⁻¹ + 1) * ((l : ℝ) + 1)^2 * ‖toL2 (sphereEval p)‖ := by
  apply (harmonic_sup_norm_le hp hΔ).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have ha : 0 ≤ sphereArea⁻¹ := inv_nonneg.mpr sphereArea_pos.le
  have hl : 1 ≤ (l : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) l; linarith
  have hd : (Module.finrank ℝ (harmonicL2 l) : ℝ) ≤ ((l : ℝ)+1)^3 := by
    exact_mod_cast harmonic_dimension_le l
  have hm : (Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea ≤
      ((sphereArea⁻¹+1) * ((l : ℝ)+1)^2)^2 := by
    have h1 : ((l : ℝ)+1)^3 ≤ (((l : ℝ)+1)^2)^2 := by nlinarith
    have h2 : sphereArea⁻¹ ≤ (sphereArea⁻¹+1)^2 := by nlinarith
    calc
      _ = (Module.finrank ℝ (harmonicL2 l) : ℝ) * sphereArea⁻¹ := div_eq_mul_inv _ _
      _ ≤ ((l : ℝ)+1)^3 * sphereArea⁻¹ := mul_le_mul_of_nonneg_right hd ha
      _ ≤ (((l : ℝ)+1)^2)^2 * (sphereArea⁻¹+1)^2 :=
        mul_le_mul h1 h2 ha (by positivity)
      _ = _ := by ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hm⟩

def rotationWord : List (Fin 3 × Fin 3) → Poly → Poly
  | [], p => p
  | ij :: w, p => rotation ij.1 ij.2 (rotationWord w p)

lemma rotationWord_harmonic {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    (rotationWord w p).IsHomogeneous l ∧ laplacian (rotationWord w p) = 0 := by
  induction w with
  | nil => exact ⟨hp, hΔ⟩
  | cons ij w ih => exact rotation_harmonic ih.1 ih.2 ij.1 ij.2

lemma rotationWord_L2_norm_le {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    ‖toL2 (sphereEval (rotationWord w p))‖ ≤
      Real.sqrt (eigenvalue l) ^ w.length * ‖toL2 (sphereEval p)‖ := by
  induction w with
  | nil => simp [rotationWord]
  | cons ij w ih =>
    have hh := rotationWord_harmonic hp hΔ w
    calc
      _ ≤ Real.sqrt (eigenvalue l) * ‖toL2 (sphereEval (rotationWord w p))‖ :=
        rotation_norm_le hh.1 hh.2 ij.1 ij.2
      _ ≤ Real.sqrt (eigenvalue l) *
          (Real.sqrt (eigenvalue l) ^ w.length * ‖toL2 (sphereEval p)‖) :=
        mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _)
      _ = _ := by simp [List.length_cons, pow_succ]; ring

lemma rotationWord_sup_norm_le {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    ‖sphereEval (rotationWord w p)‖ ≤
      (sphereArea⁻¹+1) * ((l : ℝ)+1)^(w.length+2) * ‖toL2 (sphereEval p)‖ := by
  have hh := rotationWord_harmonic hp hΔ w
  have hr : Real.sqrt (eigenvalue l) ≤ (l : ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    unfold eigenvalue
    have := Nat.cast_nonneg (α := ℝ) l
    nlinarith
  calc
    _ ≤ (sphereArea⁻¹+1) * ((l : ℝ)+1)^2 *
        ‖toL2 (sphereEval (rotationWord w p))‖ := harmonic_sup_norm_polynomial hh.1 hh.2
    _ ≤ (sphereArea⁻¹+1) * ((l : ℝ)+1)^2 *
        (Real.sqrt (eigenvalue l)^w.length * ‖toL2 (sphereEval p)‖) :=
      mul_le_mul_of_nonneg_left (rotationWord_L2_norm_le hp hΔ w) (by
        have := sphereArea_pos; positivity)
    _ ≤ (sphereArea⁻¹+1) * ((l : ℝ)+1)^2 *
        (((l : ℝ)+1)^w.length * ‖toL2 (sphereEval p)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by have := sphereArea_pos; positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hr _) (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring

open scoped Manifold ContDiff Topology
open Set
instance ambient_finrank : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def puncturedSpace : TopologicalSpace.Opens Ambient :=
  ⟨{x | x ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩

lemma sphere_ne_zero (x : Sphere) : (x : Ambient) ≠ 0 :=
  ne_zero_of_mem_unit_sphere x

lemma normalize_mem_sphere (x : Ambient) (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Ambient) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

def normalizeSphere (x : puncturedSpace) : Sphere :=
  ⟨‖(x : Ambient)‖⁻¹ • (x : Ambient), normalize_mem_sphere x x.2⟩

lemma normalizeSphere_smooth : ContMDiff 𝓘(ℝ, Ambient) (𝓡 2) ∞ normalizeSphere := by
  have hcoe : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) ∞
      (fun x : puncturedSpace => (x : Ambient)) := contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞
      (fun x : puncturedSpace => ‖(x : Ambient)‖) := by
    intro x
    exact (contDiffAt_norm ℝ (show (x : Ambient) ≠ 0 from x.2)).comp_contMDiffAt hcoe.contMDiffAt
  have h := (hn.inv₀ (fun x => norm_ne_zero_iff.mpr (show (x : Ambient) ≠ 0 from x.2))).smul hcoe
  exact h.codRestrict_sphere (fun x => normalize_mem_sphere x x.2)

def radialExtension (f : Sphere → ℝ) (x : Ambient) : ℝ :=
  if hx : x ≠ 0 then f (normalizeSphere ⟨x, hx⟩) else 0

lemma radialExtension_on_sphere (f : Sphere → ℝ) (x : Sphere) :
    radialExtension f x = f x := by
  rw [radialExtension, dite_eq_left (sphere_ne_zero x)]
  congr 1
  apply Subtype.ext
  have hx : ‖(x : Ambient)‖ = 1 := by simp
  simp [normalizeSphere, hx]

theorem radialExtension_smooth {f : Sphere → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (radialExtension f) puncturedSpace := by
  have h : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞
      (fun x : puncturedSpace => radialExtension f x) := by
    have he : (fun x : puncturedSpace => radialExtension f x) = f ∘ normalizeSphere := by
      funext x
      exact dite_eq_left (show (x : Ambient) ≠ 0 from x.2)
    rw [he]
    exact hf.comp normalizeSphere_smooth
  intro x hx
  have hx' := (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : puncturedSpace))).mp
    (h.contMDiffAt (x := ⟨x, hx⟩))
  exact hx'.contDiffAt.contDiffWithinAt

def rotationGenerator (i j : Fin 3) : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun k => (if k = j then x i else 0) - (if k = i then x j else 0))
  map_add' x y := by ext k; dsimp; split_ifs <;> ring
  map_smul' a x := by ext k; dsimp; split_ifs <;> ring

lemma rotationGenerator_apply (i j k : Fin 3) (x : Ambient) :
    rotationGenerator i j x k = (if k = j then x i else 0) - (if k = i then x j else 0) := rfl

local instance : ContinuousSMul ℝ Ambient := IsBoundedSMul.continuousSMul

lemma rotationGenerator_smooth (i j : Fin 3) : ContDiff ℝ ∞ (rotationGenerator i j) :=
  (rotationGenerator i j).toContinuousLinearMap.contDiff

def smoothRotation (i j : Fin 3) (F : Ambient → ℝ) (x : Ambient) : ℝ :=
  fderiv ℝ F x (rotationGenerator i j x)

lemma smoothRotation_smooth {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (i j : Fin 3) : ContDiffOn ℝ ∞ (smoothRotation i j F) puncturedSpace := by
  exact (hF.fderiv_of_isOpen puncturedSpace.isOpen (by simp)).clm_apply
    (rotationGenerator_smooth i j).contDiffOn

def smoothRestriction (F : Ambient → ℝ) (hF : ContDiffOn ℝ ∞ F puncturedSpace) : C(Sphere, ℝ) :=
  ⟨fun x => F x, hF.continuousOn.comp_continuous continuous_subtype_val sphere_ne_zero⟩

lemma planeRotation_hasDerivAt (i j : Fin 3) (hij : i ≠ j) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j hij s x)
      (rotationGenerator i j (planeRotation i j hij t x)) t := by
  have h : HasDerivAt (fun s => fun k : Fin 3 =>
      if k = i then Real.cos s * x i - Real.sin s * x j
      else if k = j then Real.sin s * x i + Real.cos s * x j else x k)
      (fun k => (rotationGenerator i j (planeRotation i j hij t x)) k) t := by
    apply hasDerivAt_pi.mpr
    intro k
    by_cases hi : k = i
    · subst k
      convert! ((Real.hasDerivAt_cos t).mul_const (x i)).sub
        ((Real.hasDerivAt_sin t).mul_const (x j)) using 1
      · funext s; simp
      · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij, hij.symm]
        ring
    · by_cases hj : k = j
      · subst k
        convert! ((Real.hasDerivAt_sin t).mul_const (x i)).add
          ((Real.hasDerivAt_cos t).mul_const (x j)) using 1
        · funext s; simp [hij.symm]
        · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij.symm]
          ring
      · simpa [rotationGenerator_apply, hi, hj] using hasDerivAt_const t (x k)
  convert! (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t h using 1

lemma smoothRotation_orbit_derivative {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun s => F (planeRotation i j hij s (x : Ambient)))
      (smoothRotation i j F (planeRotation i j hij t (x : Ambient))) t := by
  have hn : (planeRotation i j hij t (x : Ambient)) ≠ 0 := by
    simpa using (planeRotation i j hij t).injective.ne (sphere_ne_zero x)
  have hd := (hF.contDiffAt (puncturedSpace.isOpen.mem_nhds hn)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt t (planeRotation_hasDerivAt i j hij x t)

@[simp] lemma planeRotation_zero (i j : Fin 3) (hij : i ≠ j) (x : Ambient) :
    planeRotation i j hij 0 x = x := by
  apply PiLp.ext
  intro k
  simp only [planeRotation_apply, planeRotationMap_apply, Real.cos_zero, Real.sin_zero,
    one_mul, zero_mul, sub_zero, zero_add]
  split_ifs <;> simp_all

theorem sphereIntegral_smoothRotation {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (i j : Fin 3) (hij : i ≠ j) :
    sphereIntegral (smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)) = 0 := by
  let f := smoothRestriction F hF
  let g := smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)
  let orb (t : ℝ) (x : Sphere) := sphereHome (planeRotation i j hij t) x
  have hcF (t : ℝ) : Continuous (fun x : Sphere => f (orb t x)) :=
    f.continuous.comp (sphereHome (planeRotation i j hij t)).continuous
  have hcG (t : ℝ) : Continuous (fun x : Sphere => g (orb t x)) :=
    g.continuous.comp (sphereHome (planeRotation i j hij t)).continuous
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceMeasure) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t x => f (orb t x)) (F' := fun t x => g (orb t x))
    (bound := fun _ => ‖g‖)
    (by simp) (Filter.Eventually.of_forall (fun t => (hcF t).aestronglyMeasurable))
    ((hcF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hcG 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x t _ => g.norm_coe_le_norm (orb t x)))
    (integrable_const ‖g‖)
    (Filter.Eventually.of_forall (fun x t _ => smoothRotation_orbit_derivative hF i j hij x t))
  have he : (fun t : ℝ => ∫ x, f (orb t x) ∂surfaceMeasure) =
      fun _ => sphereIntegral f := by
    funext t
    rw [sphereIntegral_apply]
    exact (sphereHome_measurePreserving (planeRotation i j hij t)).integral_comp
      (sphereHome (planeRotation i j hij t)).measurableEmbedding f
  have hz := hd.2
  rw [he] at hz
  have he' := hz.unique (hasDerivAt_const 0 (sphereIntegral f))
  simpa [sphereIntegral_apply, orb, sphereHome_val, g, smoothRestriction] using he'

lemma smoothRestriction_add {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace) :
    smoothRestriction (F + G) (hF.add hG) = smoothRestriction F hF + smoothRestriction G hG := rfl

lemma smoothRestriction_mul {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace) :
    smoothRestriction (F * G) (hF.mul hG) = smoothRestriction F hF * smoothRestriction G hG := rfl

lemma smoothRotation_mul {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (F * G) x = F x * smoothRotation i j G x + G x * smoothRotation i j F x := by
  have hf := (hF.contDiffAt (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hg := (hG.contDiffAt (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  simp [smoothRotation, fderiv_mul hf hg]

lemma inner_toL2 (f g : C(Sphere, ℝ)) :
    inner ℝ (toL2 f) (toL2 g) = sphereIntegral (f * g) := by
  rw [sphereIntegral_apply]
  change inner ℝ (ContinuousMap.toLp 2 surfaceMeasure ℝ f)
    (ContinuousMap.toLp 2 surfaceMeasure ℝ g) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp [mul_comm]

theorem smoothRotation_skew_adjoint {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (toL2 (smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)))
      (toL2 (smoothRestriction G hG)) =
    -inner ℝ (toL2 (smoothRestriction F hF))
      (toL2 (smoothRestriction (smoothRotation i j G) (smoothRotation_smooth hG i j))) := by
  have he : smoothRestriction (smoothRotation i j (F * G)) (smoothRotation_smooth (hF.mul hG) i j) =
      smoothRestriction F hF * smoothRestriction (smoothRotation i j G) (smoothRotation_smooth hG i j) +
      smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j) * smoothRestriction G hG := by
    ext x
    change smoothRotation i j (F * G) x = _
    rw [smoothRotation_mul hF hG i j (sphere_ne_zero x)]
    change _ = F x * smoothRotation i j G x + smoothRotation i j F x * G x
    ring
  have h := sphereIntegral_smoothRotation (F := F * G) (hF.mul hG) i j hij
  rw [he, map_add] at h
  rw [inner_toL2, inner_toL2]
  linarith

def polynomialExtension (p : Poly) (x : Ambient) : ℝ := aeval (fun i => x i) p

lemma polynomialExtension_smooth (p : Poly) : ContDiff ℝ ∞ (polynomialExtension p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    convert! (contDiff_const : ContDiff ℝ ∞ (fun _ : Ambient => a)) using 1
    funext x; simp [polynomialExtension]
  | add p q hp hq =>
    convert! hp.add hq using 1
    funext x; exact map_add (aeval (fun i => x i)) p q
  | mul_X p k hp =>
    convert! hp.mul (EuclideanSpace.proj k).contDiff using 1
    funext x; simp [polynomialExtension]

lemma polynomialExtension_on_sphere (p : Poly) (x : Sphere) :
    polynomialExtension p x = sphereEval p x := by
  have h : aeval (fun i => (x : Ambient) i) =
      (ContinuousMap.evalAlgHom ℝ ℝ x).comp sphereEval := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [sphereEval, sphereCoordinate]
    rfl
  exact congrArg (fun h : Poly →ₐ[ℝ] ℝ => h p) h

lemma polynomialExtension_restriction (p : Poly) :
    smoothRestriction (polynomialExtension p) (polynomialExtension_smooth p).contDiffOn = sphereEval p := by
  ext x
  exact polynomialExtension_on_sphere p x

lemma smoothRotation_restriction_eq {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {p : Poly} (he : smoothRestriction F hF = sphereEval p)
    (i j : Fin 3) (hij : i ≠ j) :
    smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j) = sphereEval (rotation i j p) := by
  ext x
  have h1 := smoothRotation_orbit_derivative hF i j hij x 0
  have h2 := (ContinuousMap.evalCLM (R := ℝ) x).hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he' : (fun t => F (planeRotation i j hij t (x : Ambient))) =
      fun t => rotationAction i j t p x := by
    funext t
    rw [rotationAction_apply i j hij]
    exact congrArg (fun f : C(Sphere, ℝ) => f (sphereHome (planeRotation i j hij t) x)) he
  rw [he'] at h1
  have h := h1.unique h2
  simpa [smoothRestriction] using h

def smoothCasimir (F : Ambient → ℝ) : Ambient → ℝ :=
  smoothRotation 0 1 (smoothRotation 0 1 F) +
    smoothRotation 0 2 (smoothRotation 0 2 F) +
    smoothRotation 1 2 (smoothRotation 1 2 F)

lemma smoothCasimir_smooth {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ContDiffOn ℝ ∞ (smoothCasimir F) puncturedSpace :=
  ((smoothRotation_smooth (smoothRotation_smooth hF 0 1) 0 1).add
    (smoothRotation_smooth (smoothRotation_smooth hF 0 2) 0 2)).add
    (smoothRotation_smooth (smoothRotation_smooth hF 1 2) 1 2)

lemma smoothRestriction_casimir {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF) =
      smoothRestriction (smoothRotation 0 1 (smoothRotation 0 1 F)) (smoothRotation_smooth (smoothRotation_smooth hF 0 1) 0 1) +
      smoothRestriction (smoothRotation 0 2 (smoothRotation 0 2 F)) (smoothRotation_smooth (smoothRotation_smooth hF 0 2) 0 2) +
      smoothRestriction (smoothRotation 1 2 (smoothRotation 1 2 F)) (smoothRotation_smooth (smoothRotation_smooth hF 1 2) 1 2) := rfl

lemma smoothCasimir_restriction_eq {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {p : Poly} (he : smoothRestriction F hF = sphereEval p) :
    smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF) = sphereEval (angularLaplacian p) := by
  rw [smoothRestriction_casimir hF]
  rw [smoothRotation_restriction_eq _ (smoothRotation_restriction_eq hF he 0 1 (by decide)) 0 1 (by decide),
      smoothRotation_restriction_eq _ (smoothRotation_restriction_eq hF he 0 2 (by decide)) 0 2 (by decide),
      smoothRotation_restriction_eq _ (smoothRotation_restriction_eq hF he 1 2 (by decide)) 1 2 (by decide)]
  simp [angularLaplacian_apply]

lemma smoothRotation_square_symmetric {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (toL2 (smoothRestriction (smoothRotation i j (smoothRotation i j F))
      (smoothRotation_smooth (smoothRotation_smooth hF i j) i j))) (toL2 (smoothRestriction G hG)) =
    inner ℝ (toL2 (smoothRestriction F hF))
      (toL2 (smoothRestriction (smoothRotation i j (smoothRotation i j G))
        (smoothRotation_smooth (smoothRotation_smooth hG i j) i j))) := by
  rw [smoothRotation_skew_adjoint (smoothRotation_smooth hF i j) hG i j hij,
    smoothRotation_skew_adjoint hF (smoothRotation_smooth hG i j) i j hij, neg_neg]

lemma smoothCasimir_symmetric {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace) :
    inner ℝ (toL2 (smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF))) (toL2 (smoothRestriction G hG)) =
    inner ℝ (toL2 (smoothRestriction F hF)) (toL2 (smoothRestriction (smoothCasimir G) (smoothCasimir_smooth hG))) := by
  rw [smoothRestriction_casimir hF, smoothRestriction_casimir hG]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [smoothRotation_square_symmetric hF hG 0 1 (by decide),
    smoothRotation_square_symmetric hF hG 0 2 (by decide),
    smoothRotation_square_symmetric hF hG 1 2 (by decide)]

lemma smooth_harmonic_pairing {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    inner ℝ (toL2 (smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF))) (toL2 (sphereEval p)) =
      -(eigenvalue l) * inner ℝ (toL2 (smoothRestriction F hF)) (toL2 (sphereEval p)) := by
  have he := smoothCasimir_symmetric hF (polynomialExtension_smooth p).contDiffOn
  rw [polynomialExtension_restriction,
    smoothCasimir_restriction_eq _ (polynomialExtension_restriction p),
    angularLaplacian_apply, harmonic_rotation_eigenvalue hp hΔ] at he
  simpa only [map_smul, inner_smul_right, eigenvalue] using he

lemma harmonicProjection_smoothCasimir {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (l : ℕ) :
    harmonicProjection l (toL2 (smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF))) =
      -(eigenvalue l) • harmonicProjection l (toL2 (smoothRestriction F hF)) := by
  apply ext_inner_right ℝ
  intro v
  have hv := harmonicL2_exists_polynomial v
  obtain ⟨p, hp, hΔ, he⟩ := hv
  have h := smooth_harmonic_pairing hF hp hΔ
  have hproj (f : SphereL2) :
      inner ℝ (harmonicProjection l f : SphereL2) (v : SphereL2) =
        inner ℝ f (v : SphereL2) :=
    (harmonicL2 l).inner_orthogonalProjectionOnto_eq_of_mem_right v f
  simp only [Submodule.coe_inner, Submodule.coe_smul]
  rw [real_inner_smul_left, hproj, hproj]
  simpa only [he] using h

def smoothCasimirIterate : ℕ → (Ambient → ℝ) → (Ambient → ℝ)
  | 0, F => F
  | N + 1, F => smoothCasimir (smoothCasimirIterate N F)

lemma smoothCasimirIterate_smooth {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (N : ℕ) : ContDiffOn ℝ ∞ (smoothCasimirIterate N F) puncturedSpace := by
  induction N with
  | zero => exact hF
  | succ N ih => exact smoothCasimir_smooth ih

lemma harmonicProjection_smoothCasimirIterate {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (l N : ℕ) :
    harmonicProjection l (toL2 (smoothRestriction (smoothCasimirIterate N F)
      (smoothCasimirIterate_smooth hF N))) =
      (-(eigenvalue l)) ^ N • harmonicProjection l (toL2 (smoothRestriction F hF)) := by
  induction N with
  | zero => simp [smoothCasimirIterate]
  | succ N ih =>
    change harmonicProjection l (toL2 (smoothRestriction (smoothCasimir (smoothCasimirIterate N F))
      (smoothCasimir_smooth (smoothCasimirIterate_smooth hF N)))) = _
    rw [harmonicProjection_smoothCasimir (smoothCasimirIterate_smooth hF N), ih, smul_smul, pow_succ']

theorem harmonicProjection_rapid_L2 {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (l N : ℕ) :
    eigenvalue l ^ N * ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖ ≤
      ‖toL2 (smoothRestriction (smoothCasimirIterate N F) (smoothCasimirIterate_smooth hF N))‖ := by
  have h := harmonicProjection_norm_le l
    (toL2 (smoothRestriction (smoothCasimirIterate N F) (smoothCasimirIterate_smooth hF N)))
  rw [harmonicProjection_smoothCasimirIterate hF, norm_smul, norm_pow,
    norm_neg, Real.norm_eq_abs, abs_of_nonneg (eigenvalue_nonneg l)] at h
  exact h

def harmonicCoefficientPolynomial (l : ℕ) (f : SphereL2) : Poly :=
  Classical.choose (harmonicL2_exists_polynomial (harmonicProjection l f))

lemma harmonicCoefficientPolynomial_spec (l : ℕ) (f : SphereL2) :
    (harmonicCoefficientPolynomial l f).IsHomogeneous l ∧
    laplacian (harmonicCoefficientPolynomial l f) = 0 ∧
    toL2 (sphereEval (harmonicCoefficientPolynomial l f)) = (harmonicProjection l f : SphereL2) :=
  Classical.choose_spec (harmonicL2_exists_polynomial (harmonicProjection l f))

lemma harmonicCoefficientPolynomial_restriction (l : ℕ) (f : SphereL2) :
    sphereEval (harmonicCoefficientPolynomial l f) = harmonicCoefficient l f := by
  apply toL2_injective
  rw [(harmonicCoefficientPolynomial_spec l f).2.2, toL2_harmonicCoefficient]

def rotatedHarmonicCoefficient (w : List (Fin 3 × Fin 3)) (l : ℕ) (f : SphereL2) : C(Sphere, ℝ) :=
  sphereEval (rotationWord w (harmonicCoefficientPolynomial l f))

lemma rotatedHarmonicCoefficient_nil (l : ℕ) (f : SphereL2) :
    rotatedHarmonicCoefficient [] l f = harmonicCoefficient l f :=
  harmonicCoefficientPolynomial_restriction l f

lemma rotatedHarmonicCoefficient_bound (w : List (Fin 3 × Fin 3)) (l : ℕ) (f : SphereL2) :
    ‖rotatedHarmonicCoefficient w l f‖ ≤
      (sphereArea⁻¹ + 1) * ((l : ℝ) + 1) ^ (w.length + 2) * ‖harmonicProjection l f‖ := by
  obtain ⟨hp, hΔ, he⟩ := harmonicCoefficientPolynomial_spec l f
  have h := rotationWord_sup_norm_le hp hΔ w
  rw [he] at h
  exact h

lemma eigenvalue_ge_degree {l : ℕ} (hl : 1 ≤ l) : (l : ℝ) + 1 ≤ eigenvalue l := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold eigenvalue
  nlinarith

lemma rotatedHarmonicCoefficient_pseries_bound {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (w : List (Fin 3 × Fin 3)) (b : ℕ)
    {l : ℕ} (hl : 2 ≤ l) :
    eigenvalue l ^ b * ‖rotatedHarmonicCoefficient w l (toL2 (smoothRestriction F hF))‖ ≤
      ((sphereArea⁻¹ + 1) * ‖toL2 (smoothRestriction (smoothCasimirIterate (b + w.length + 4) F)
        (smoothCasimirIterate_smooth hF _))‖) / ((l : ℝ) + 1) ^ 2 := by
  have hx : 0 < (l : ℝ) + 1 := by positivity
  have hC : 0 ≤ sphereArea⁻¹ + 1 := by
    have := sphereArea_pos
    positivity
  have he : eigenvalue l ^ b * ((l : ℝ) + 1) ^ (w.length + 4) ≤
      eigenvalue l ^ (b + w.length + 4) := by
    rw [show b + w.length + 4 = b + (w.length + 4) by omega,
      pow_add (eigenvalue l) b (w.length + 4)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx.le (eigenvalue_ge_degree (by omega)) _) (pow_nonneg (eigenvalue_nonneg l) b)
  apply (le_div_iff₀ (pow_pos hx 2)).mpr
  calc
    (eigenvalue l ^ b * ‖rotatedHarmonicCoefficient w l (toL2 (smoothRestriction F hF))‖) *
        ((l : ℝ) + 1) ^ 2 ≤
      (eigenvalue l ^ b * ((sphereArea⁻¹ + 1) * ((l : ℝ) + 1) ^ (w.length + 2) *
        ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖)) * ((l : ℝ) + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rotatedHarmonicCoefficient_bound w l _)
          (pow_nonneg (eigenvalue_nonneg l) b)) (sq_nonneg _)
    _ = (sphereArea⁻¹ + 1) * ((eigenvalue l ^ b * ((l : ℝ) + 1) ^ (w.length + 4)) *
        ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖) := by
      simp only [pow_add]
      ring
    _ ≤ (sphereArea⁻¹ + 1) * (eigenvalue l ^ (b + w.length + 4) *
        ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (norm_nonneg _)) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonicProjection_rapid_L2 hF l _) hC

theorem rotatedHarmonicCoefficient_rapid {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (w : List (Fin 3 × Fin 3)) (b : ℕ) :
    Summable (fun n : ℕ => eigenvalue (n + 2) ^ b *
      ‖rotatedHarmonicCoefficient w (n + 2) (toL2 (smoothRestriction F hF))‖) := by
  let C := (sphereArea⁻¹ + 1) * ‖toL2 (smoothRestriction (smoothCasimirIterate (b + w.length + 4) F)
    (smoothCasimirIterate_smooth hF _))‖
  have hp : Summable (fun n : ℕ => C / ((n : ℝ) + 3) ^ 2) := by
    have h := (summable_nat_add_iff 3).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    convert! h.mul_left C using 1
    funext n
    simp [Nat.cast_add, div_eq_mul_inv]
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (eigenvalue_nonneg _) _) (norm_nonneg _)) _ hp
  intro n
  convert! rotatedHarmonicCoefficient_pseries_bound hF w b (l := n + 2) (by omega) using 1
  norm_num [C, Nat.cast_add, add_assoc]

theorem smoothSphere_actual_projections_rapid (f : Sphere → ℝ) (hf : SmoothSphere f)
    (w : List (Fin 3 × Fin 3)) (b : ℕ) :
    Summable (fun n : ℕ => eigenvalue (n + 2) ^ b *
      ‖rotatedHarmonicCoefficient w (n + 2)
        (toL2 (smoothRestriction (radialExtension f) (radialExtension_smooth hf)))‖) :=
  rotatedHarmonicCoefficient_rapid (radialExtension_smooth hf) w b

lemma radialExtension_pos_smul (f : Sphere → ℝ) (x : Ambient) {a : ℝ} (ha : 0 < a) :
    radialExtension f (a • x) = radialExtension f x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  rw [radialExtension, dite_eq_left (smul_ne_zero ha.ne' hx), radialExtension, dite_eq_left hx]
  congr 1
  apply Subtype.ext
  simp only [normalizeSphere, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_inv_rev,
    smul_smul]
  congr 1
  field_simp

lemma radialExtension_isometry (f : Sphere → ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (x : Ambient) (hx : x ≠ 0) :
    radialExtension f (e x) = f (sphereHome e (normalizeSphere ⟨x, hx⟩)) := by
  rw [radialExtension, dite_eq_left (by simpa using e.injective.ne hx)]
  congr 1
  apply Subtype.ext
  simp [normalizeSphere, sphereHome]

lemma polynomial_sphere_smooth (p : Poly) : SmoothSphere (sphereEval p) := by
  have h := (polynomialExtension_smooth p).contMDiff.comp (contMDiff_coe_sphere (n := 2))
  convert! h using 1
  funext x
  exact (polynomialExtension_on_sphere p x).symm

lemma radialExtension_fderiv_self {f : Sphere → ℝ} (hf : SmoothSphere f)
    {x : Ambient} (hx : x ≠ 0) : fderiv ℝ (radialExtension f) x x = 0 := by
  have hd := ((radialExtension_smooth hf).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension f) (fderiv ℝ (radialExtension f) x) ((1 : ℝ) • x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have he : (fun s : ℝ => radialExtension f (s • x)) =ᶠ[nhds 1]
      (fun _ => radialExtension f x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact radialExtension_pos_smul f x hs
  have h2 := (hasDerivAt_const (1 : ℝ) (radialExtension f x)).congr_of_eventuallyEq he
  simpa using h1.unique h2

lemma smoothRotation_radial_polynomial (p : Poly) (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (radialExtension (sphereEval p)) x =
      radialExtension (sphereEval (rotation i j p)) x := by
  by_cases hij : i = j
  · subst j
    have hg : rotationGenerator i i x = 0 := by ext k; simp [rotationGenerator_apply]
    simp [smoothRotation, hg, rotation_apply, radialExtension]
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension (sphereEval p))
      (fderiv ℝ (radialExtension (sphereEval p)) x) (planeRotation i j hij 0 x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) (planeRotation_hasDerivAt i j hij x 0)
  let y : Sphere := normalizeSphere ⟨x, hx⟩
  have h2 := (ContinuousMap.evalCLM (R := ℝ) y).hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he : (fun t => radialExtension (sphereEval p) (planeRotation i j hij t x)) =
      fun t => rotationAction i j t p y := by
    funext t
    rw [rotationAction_apply i j hij]
    exact radialExtension_isometry _ _ _ hx
  change HasDerivAt (fun s => radialExtension (sphereEval p) (planeRotation i j hij s x)) _ 0 at h1
  rw [he] at h1
  have h := h1.unique h2
  simpa [smoothRotation, radialExtension, hx, y] using h

lemma rotationGenerator_decomposition (x v : Ambient) :
    ‖x‖ ^ 2 • v = (∑ i : Fin 3, ∑ j : Fin 3, (x i * v j) • rotationGenerator i j x) +
      (∑ i : Fin 3, x i * v i) • x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Fin.sum_univ_three, rotationGenerator_apply] <;> ring

lemma radial_polynomial_fderiv (p : Poly) {x : Ambient} (hx : x ≠ 0) (v : Ambient) :
    fderiv ℝ (radialExtension (sphereEval p)) x v =
      ∑ i : Fin 3, ∑ j : Fin 3, (x i * v j / ‖x‖ ^ 2) *
        radialExtension (sphereEval (rotation i j p)) x := by
  have h := congrArg (fderiv ℝ (radialExtension (sphereEval p)) x)
    (rotationGenerator_decomposition x v)
  simp only [map_add, map_sum, map_smul, radialExtension_fderiv_self (polynomial_sphere_smooth p) hx,
    smul_eq_mul] at h
  have hrot (i j : Fin 3) : fderiv ℝ (radialExtension (sphereEval p)) x (rotationGenerator i j x) =
      radialExtension (sphereEval (rotation i j p)) x := smoothRotation_radial_polynomial p i j hx
  simp only [hrot] at h
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).mpr
  simpa [mul_comm, mul_zero] using h

end
end CKSSphericalHarmonics

end

noncomputable section
namespace CKSSpectralHeat
noncomputable section
open Set Filter Real
open scoped Topology ContDiff

def eigenvalue (n : ℕ) : ℝ := (n + 2) * (n + 3)

lemma eigenvalue_ge_six (n : ℕ) : 6 ≤ eigenvalue n := by
  unfold eigenvalue
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith
lemma eigenvalue_pos (n : ℕ) : 0 < eigenvalue n := by linarith [eigenvalue_ge_six n]

def kernel (t : ℝ) : ℝ := smoothTransition (t + 1) * exp (-t)

lemma kernel_smooth : ContDiff ℝ ∞ kernel := by unfold kernel; fun_prop

lemma kernel_nonneg_time {t : ℝ} (ht : 0 ≤ t) : kernel t = exp (-t) := by
  simp [kernel, smoothTransition.one_of_one_le (show 1 ≤ t + 1 by linarith)]

lemma kernel_zero {t : ℝ} (ht : t ≤ -1) : kernel t = 0 := by
  simp [kernel, smoothTransition.zero_of_nonpos (show t + 1 ≤ 0 by linarith)]

lemma kernel_derivative_bounded (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, ‖iteratedDeriv b kernel t‖ ≤ C := by
  have hc : Continuous (iteratedDeriv b kernel) :=
    kernel_smooth.continuous_iteratedDeriv b (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro t
  by_cases htlo : t < -2
  · have heq : kernel =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds (show t < -1 by linarith)] with x hx
      exact kernel_zero hx.le
    rw [heq.iteratedDeriv_eq b]
    simp [le_trans zero_le_one (le_max_right C 1)]
  by_cases hthi : 1 < t
  · have heq : kernel =ᶠ[𝓝 t] (fun x => exp (-1 * x)) := by
      filter_upwards [Ioi_mem_nhds (show 0 < t by linarith)] with x hx
      simpa using kernel_nonneg_time hx.le
    rw [heq.iteratedDeriv_eq b, iteratedDeriv_exp_const_mul]
    have he : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith)
    calc
      ‖(-1 : ℝ) ^ b * exp (-1 * t)‖ = exp (-t) := by
        rw [norm_mul, norm_pow]
        simp [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      _ ≤ 1 := he
      _ ≤ max C 1 := le_max_right _ _
  · exact (hC t ⟨not_lt.mp htlo, not_lt.mp hthi⟩).trans (le_max_left _ _)

lemma kernel_deriv_nonneg_time (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv b kernel t = (-1 : ℝ) ^ b * exp (-t) := by
  have heq : Set.EqOn kernel (fun x : ℝ => exp (-1 * x)) (Ici 0) := by
    intro x hx
    simpa using kernel_nonneg_time hx
  have hk : ContDiffAt ℝ b kernel t := kernel_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  have he : ContDiffAt ℝ b (fun x : ℝ => exp (-1 * x)) t := by fun_prop
  have hid := iteratedDerivWithin_congr (n := b) heq ht
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hk ht,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) he ht] at hid
  rw [iteratedDeriv_exp_const_mul] at hid
  simpa only [neg_one_mul] using hid

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def Rapid (coeff : ℕ → B) : Prop :=
  ∀ b : ℕ, Summable (fun n => eigenvalue n ^ b * ‖coeff n‖)

def term (coeff : ℕ → B) (n : ℕ) (t : ℝ) : B :=
  kernel (eigenvalue n * t) • coeff n

def heat (coeff : ℕ → B) (t : ℝ) : B := ∑' n, term coeff n t

omit [CompleteSpace B] in
lemma term_smooth [CompleteSpace B] (coeff : ℕ → B) (n : ℕ) : ContDiff ℝ ∞ (term coeff n) := by
  unfold term
  exact (kernel_smooth.comp (contDiff_const.mul contDiff_id)).smul contDiff_const

omit [CompleteSpace B] in
lemma term_deriv [CompleteSpace B] (coeff : ℕ → B) (b n : ℕ) (t : ℝ) :
    iteratedDeriv b (term coeff n) t =
      (eigenvalue n ^ b * iteratedDeriv b kernel (eigenvalue n * t)) • coeff n := by
  have hf : ContDiff ℝ b (fun t : ℝ => kernel (eigenvalue n * t)) :=
    (kernel_smooth.comp (contDiff_const.mul contDiff_id)).of_le
      (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  unfold term
  rw [iteratedDeriv_smul_const hf.contDiffAt (coeff n)]
  rw [iteratedDeriv_comp_const_mul (kernel_smooth.of_le
    (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))) (eigenvalue n)]

lemma heat_majorant (coeff : ℕ → B) (h : Rapid coeff) :
    ∃ v : ℕ → ℕ → ℝ, (∀ b, Summable (v b)) ∧
      ∀ b n t, ‖iteratedFDeriv ℝ b (term coeff n) t‖ ≤ v b n := by
  choose C hC hbound using kernel_derivative_bounded
  refine ⟨fun b n => C b * (eigenvalue n ^ b * ‖coeff n‖),
    fun b => (h b).mul_left (C b), ?_⟩
  intro b n t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, term_deriv,
    norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (eigenvalue_pos n)]
  calc
    eigenvalue n ^ b * |iteratedDeriv b kernel (eigenvalue n * t)| * ‖coeff n‖ ≤
        eigenvalue n ^ b * C b * ‖coeff n‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (hbound b _) (pow_nonneg (eigenvalue_pos n).le _)
    _ = C b * (eigenvalue n ^ b * ‖coeff n‖) := by ring

theorem heat_smooth (coeff : ℕ → B) (h : Rapid coeff) : ContDiff ℝ ∞ (heat coeff) := by
  obtain ⟨v, hv, hb⟩ := heat_majorant coeff h
  exact contDiff_tsum (term_smooth coeff) (fun b _ => hv b) (fun b n t _ => hb b n t)

lemma term_deriv_nonneg_time (coeff : ℕ → B) (b n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv b (term coeff n) t =
      ((-eigenvalue n) ^ b * exp (-eigenvalue n * t)) • coeff n := by
  rw [term_deriv, kernel_deriv_nonneg_time b (mul_nonneg (eigenvalue_pos n).le ht)]
  congr 1
  rw [neg_mul]
  ring

omit [CompleteSpace B] in
lemma heat_eq_series [CompleteSpace B] (coeff : ℕ → B) {t : ℝ} (ht : 0 ≤ t) :
    heat coeff t = ∑' n, exp (-eigenvalue n * t) • coeff n := by
  unfold heat term
  congr 1
  funext n
  rw [kernel_nonneg_time (mul_nonneg (eigenvalue_pos n).le ht)]
  simp

lemma heat_initial (coeff : ℕ → B) : heat coeff 0 = ∑' n, coeff n := by
  rw [heat_eq_series coeff le_rfl]
  simp

lemma heat_deriv (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) (t : ℝ) :
    iteratedDeriv b (heat coeff) t = ∑' n, iteratedDeriv b (term coeff n) t := by
  obtain ⟨v, hv, hb⟩ := heat_majorant coeff h
  simp_rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
  unfold heat
  rw [iteratedFDeriv_tsum_apply (term_smooth coeff) (fun k _ => hv k)
    (fun k n t _ => hb k n t) (by simp)]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin b) B).symm.toContinuousLinearEquiv.map_tsum

lemma heat_deriv_nonneg_time (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv b (heat coeff) t =
      ∑' n, ((-eigenvalue n) ^ b * exp (-eigenvalue n * t)) • coeff n := by
  rw [heat_deriv coeff h]
  congr 1
  funext n
  exact term_deriv_nonneg_time coeff b n ht

lemma term_decay (coeff : ℕ → B) (b n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖iteratedDeriv b (term coeff n) t‖ ≤
      exp (-6 * t) * (eigenvalue n ^ b * ‖coeff n‖) := by
  rw [term_deriv_nonneg_time coeff b n ht, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_pow, abs_neg, abs_of_pos (eigenvalue_pos n), abs_of_pos (exp_pos _)]
  have he : exp (-eigenvalue n * t) ≤ exp (-6 * t) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr (eigenvalue_ge_six n)) ht]
  calc
    eigenvalue n ^ b * exp (-eigenvalue n * t) * ‖coeff n‖ ≤
      eigenvalue n ^ b * exp (-6 * t) * ‖coeff n‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he
          (pow_nonneg (eigenvalue_pos n).le b)) (norm_nonneg _)
    _ = exp (-6 * t) * (eigenvalue n ^ b * ‖coeff n‖) := by ring

theorem heat_decay (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖iteratedDeriv b (heat coeff) t‖ ≤
      exp (-6 * t) * ∑' n, eigenvalue n ^ b * ‖coeff n‖ := by
  have hm := (h b).mul_left (exp (-6 * t))
  have hn : Summable (fun n => ‖iteratedDeriv b (term coeff n) t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_decay coeff b n ht) hm
  rw [heat_deriv coeff h]
  calc
    ‖∑' n, iteratedDeriv b (term coeff n) t‖ ≤ ∑' n, ‖iteratedDeriv b (term coeff n) t‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, exp (-6 * t) * (eigenvalue n ^ b * ‖coeff n‖) :=
      hn.tsum_le_tsum (fun n => term_decay coeff b n ht) hm
    _ = exp (-6 * t) * ∑' n, eigenvalue n ^ b * ‖coeff n‖ := tsum_mul_left

lemma term_deriv_summable (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) (t : ℝ) :
    Summable (fun n => iteratedDeriv b (term coeff n) t) := by
  obtain ⟨v, hv, hb⟩ := heat_majorant coeff h
  apply Summable.of_norm_bounded (hv b)
  intro n
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb b n t

lemma term_summable (coeff : ℕ → B) (h : Rapid coeff) (t : ℝ) :
    Summable (fun n => term coeff n t) := by
  simpa using term_deriv_summable coeff h 0 t

def generator (coeff : ℕ → B) (n : ℕ) : B := (-eigenvalue n) • coeff n

omit [CompleteSpace B] in
lemma generator_rapid [CompleteSpace B] (coeff : ℕ → B) (h : Rapid coeff) : Rapid (generator coeff) := by
  intro b
  simpa [generator, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (eigenvalue_pos _), pow_succ, mul_assoc] using h (b + 1)

theorem spectral_heat_equation (coeff : ℕ → B) (h : Rapid coeff) {t : ℝ} (ht : 0 ≤ t) :
    deriv (heat coeff) t = heat (generator coeff) t := by
  rw [← iteratedDeriv_one, heat_deriv_nonneg_time coeff h 1 ht,
    heat_eq_series (generator coeff) ht]
  congr 1
  funext n
  simp only [pow_one, generator, smul_smul]
  congr 1
  ring

def inverseCoeff (coeff : ℕ → B) (n : ℕ) : B :=
  (1 - eigenvalue n / 2)⁻¹ • coeff n

lemma inverse_denominator_bound (n : ℕ) : |(1 - eigenvalue n / 2)⁻¹| ≤ 1 / 2 := by
  have he := eigenvalue_ge_six n
  have hd : 2 ≤ |1 - eigenvalue n / 2| := by
    rw [abs_of_neg (by linarith)]
    linarith
  rw [abs_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd

omit [CompleteSpace B] in
lemma inverseCoeff_rapid [CompleteSpace B] (coeff : ℕ → B) (h : Rapid coeff) : Rapid (inverseCoeff coeff) := by
  intro b
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (eigenvalue_pos n).le _) (norm_nonneg _))
    _ ((h b).mul_left (1 / 2))
  intro n
  rw [inverseCoeff, norm_smul, Real.norm_eq_abs]
  calc
    eigenvalue n ^ b * (|(1 - eigenvalue n / 2)⁻¹| * ‖coeff n‖) ≤
      eigenvalue n ^ b * ((1 / 2) * ‖coeff n‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (inverse_denominator_bound n) (norm_nonneg _))
          (pow_nonneg (eigenvalue_pos n).le _)
    _ = (1 / 2) * (eigenvalue n ^ b * ‖coeff n‖) := by ring

theorem heat_and_potential (coeff : ℕ → B) (h : Rapid coeff) :
    ContDiff ℝ ∞ (heat coeff) ∧ ContDiff ℝ ∞ (heat (inverseCoeff coeff)) ∧
    heat coeff 0 = ∑' n, coeff n ∧
    (∀ t, 0 ≤ t → deriv (heat coeff) t = heat (generator coeff) t) ∧
    (∀ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t →
      ‖iteratedDeriv b (heat coeff) t‖ +
        ‖iteratedDeriv b (heat (inverseCoeff coeff)) t‖ ≤ C * exp (-6 * t)) := by
  refine ⟨heat_smooth coeff h, heat_smooth _ (inverseCoeff_rapid coeff h),
    heat_initial coeff, fun t ht => spectral_heat_equation coeff h ht, ?_⟩
  intro b
  let C := (∑' n, eigenvalue n ^ b * ‖coeff n‖) +
    (∑' n, eigenvalue n ^ b * ‖inverseCoeff coeff n‖)
  have hC : 0 ≤ C := by
    apply add_nonneg <;>
      exact tsum_nonneg (fun n => mul_nonneg (pow_nonneg (eigenvalue_pos n).le _) (norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h1 := heat_decay coeff h b ht
  have h2 := heat_decay (inverseCoeff coeff) (inverseCoeff_rapid coeff h) b ht
  dsimp only [C]
  nlinarith

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

omit [CompleteSpace C] in
lemma heat_map [CompleteSpace C] (L : B →L[ℝ] C) (coeff : ℕ → B) (h : Rapid coeff) (t : ℝ) :
    heat (fun n => L (coeff n)) t = L (heat coeff t) := by
  unfold heat
  rw [L.map_tsum (term_summable coeff h t)]
  congr 1
  funext n
  simp [term]

end
end CKSSpectralHeat

end

end OAI
