import OAI.Analysis.TracialSplitting.TraceEstimates

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FiniteSpectralResolution

variable {D : Type uD} [CStarAlgebra D]

lemma realSpectrum_finite {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℂ a).Finite) : (spectrum ℝ a).Finite := by
  rw [← ha.spectrumRestricts.image]
  exact hfinite.image _

def spectralAtom (a : D) (t : ℝ) : D :=
  cfc (fun x : ℝ => if x = t then (1 : ℝ) else 0) a

lemma spectralAtom_projection {a : D} (hfinite : (spectrum ℝ a).Finite) (t : ℝ) :
    IsStarProjection (spectralAtom a t) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc _ a * cfc _ a = cfc _ a
  rw [← cfc_mul _ _ a (hfinite.continuousOn _) (hfinite.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma spectralAtom_orthogonal {a : D} (hfinite : (spectrum ℝ a).Finite)
    {s t : ℝ} (hst : s ≠ t) : spectralAtom a s * spectralAtom a t = 0 := by
  change cfc _ a * cfc _ a = 0
  rw [← cfc_mul _ _ a (hfinite.continuousOn _) (hfinite.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 0) a := by
      apply cfc_congr
      intro x _
      by_cases hxs : x = s
      · subst x
        simp [hst]
      · simp [hxs]
    _ = 0 := cfc_zero ℝ a

lemma spectralAtom_sum {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℝ a).Finite) : ∑ t ∈ hfinite.toFinset, spectralAtom a t = 1 := by
  classical
  simp only [spectralAtom]
  rw [← cfc_sum _ a hfinite.toFinset (fun _ _ => hfinite.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 1) a := by
      apply cfc_congr
      intro x hx
      simp only [Finset.sum_apply]
      simp [Set.Finite.mem_toFinset, hx]
    _ = 1 := cfc_one ℝ a ha

lemma spectralAtom_resolution {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℝ a).Finite) :
    ∑ t ∈ hfinite.toFinset, t • spectralAtom a t = a := by
  classical
  simp only [spectralAtom, ← cfc_smul _ _ a (hfinite.continuousOn _)]
  rw [← cfc_sum _ a hfinite.toFinset (fun _ _ => hfinite.continuousOn _)]
  calc
    _ = cfc (fun x : ℝ => x) a := by
      apply cfc_congr
      intro x hx
      simp only [Finset.sum_apply, smul_eq_mul]
      simp [Set.Finite.mem_toFinset, hx]
    _ = a := cfc_id ℝ a ha

lemma spectralAtom_eigenvalue {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℝ a).Finite) (t : ℝ) : a * spectralAtom a t = t • spectralAtom a t := by
  change a * cfc (fun x : ℝ => if x = t then (1 : ℝ) else 0) a =
    t • cfc (fun x : ℝ => if x = t then (1 : ℝ) else 0) a
  nth_rw 1 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a continuous_id.continuousOn (hfinite.continuousOn _),
    ← cfc_smul _ _ a (hfinite.continuousOn _)]
  apply cfc_congr
  intro x _
  by_cases hxt : x = t <;> simp [hxt]

end FiniteSpectralResolution

section ProjectionCorners

variable {D : Type uD} [CStarAlgebra D]

def projectionCornerSubalgebra {p : D} (hp : IsStarProjection p) :
    NonUnitalStarSubalgebra ℂ D where
  carrier := {a | p * a = a ∧ a * p = a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    simp [mul_add, add_mul, ha, ha', hb, hb']
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [← mul_assoc, ha], by rw [mul_assoc, hb']⟩
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    simp [ha, ha']
  star_mem' := by
    rintro a ⟨ha, ha'⟩
    constructor
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha

abbrev ProjectionCorner {p : D} (hp : IsStarProjection p) := projectionCornerSubalgebra hp

namespace ProjectionCorner

variable {p : D} (hp : IsStarProjection p)

instance : Semiring (ProjectionCorner hp) where
  __ : NonUnitalSemiring (ProjectionCorner hp) := inferInstance
  one := ⟨p, hp.isIdempotentElem, hp.isIdempotentElem⟩
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

instance : Ring (ProjectionCorner hp) where
  __ : Semiring (ProjectionCorner hp) := inferInstance
  __ : NonUnitalRing (ProjectionCorner hp) := inferInstance

@[simp] lemma coe_one : ((1 : ProjectionCorner hp) : D) = p := rfl

instance : Algebra ℂ (ProjectionCorner hp) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance : NormedRing (ProjectionCorner hp) where
  __ : Ring (ProjectionCorner hp) := inferInstance
  __ : NonUnitalNormedRing (ProjectionCorner hp) := inferInstance

instance : NormedAlgebra ℂ (ProjectionCorner hp) where
  __ : Algebra ℂ (ProjectionCorner hp) := inferInstance
  norm_smul_le r x := norm_smul_le r x

lemma isClosed : IsClosed (projectionCornerSubalgebra hp : Set D) :=
  (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance : CompleteSpace (ProjectionCorner hp) := (isClosed hp).completeSpace_coe

instance : CStarAlgebra (ProjectionCorner hp) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le (x : D)

def inclusion : ProjectionCorner hp →⋆ₙₐ[ℂ] D := NonUnitalStarSubalgebraClass.subtype (projectionCornerSubalgebra hp)

lemma inclusion_isometric : Isometry (inclusion hp) := fun _ _ => rfl

lemma isSelfAdjoint_coe {a : ProjectionCorner hp} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (a : D) := congrArg Subtype.val ha

lemma coe_cfc {a : ProjectionCorner hp} (ha : IsSelfAdjoint a)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    ((cfc f a : ProjectionCorner hp) : D) = cfc f (a : D) := by
  rw [← cfcₙ_eq_cfc hf.continuousOn hf0, ← cfcₙ_eq_cfc hf.continuousOn hf0]
  exact (inclusion hp).map_cfcₙ f a hf.continuousOn hf0
    (inclusion_isometric hp).continuous ha (isSelfAdjoint_coe hp ha)

lemma spectrum_coe_subset (a : ProjectionCorner hp) :
    spectrum ℝ (a : D) ⊆ spectrum ℝ a ∪ {0} := by
  apply Set.Subset.trans (spectrum_subset_quasispectrum ℝ (a : D))
  rw [← quasispectrum_eq_spectrum_union_zero]
  exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ (inclusion hp) a

def compress (a : D) : ProjectionCorner hp :=
  ⟨p * a * p, by
    constructor
    · simp only [← mul_assoc, hp.isIdempotentElem.eq]
    · simp only [mul_assoc, hp.isIdempotentElem.eq]⟩

@[simp] lemma coe_compress (a : D) : ((compress hp a : ProjectionCorner hp) : D) = p * a * p := rfl

lemma coe_algebraMap (t : ℂ) : ((algebraMap ℂ (ProjectionCorner hp) t : ProjectionCorner hp) : D) =
    t • p := rfl

lemma spectrum_subset_coe (a : ProjectionCorner hp) :
    spectrum ℂ a ⊆ spectrum ℂ (a : D) := by
  intro t ht
  rw [spectrum.mem_iff] at ht ⊢
  intro hu
  obtain ⟨u, hu⟩ := hu
  let x : ProjectionCorner hp := algebraMap ℂ (ProjectionCorner hp) t - a
  have hx : (x : D) = p * (u : D) := by
    rw [hu]
    change t • p - (a : D) = p * (algebraMap ℂ D t - (a : D))
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, a.property.1]
  have hx' : (x : D) = (u : D) * p := by
    rw [hu]
    change t • p - (a : D) = (algebraMap ℂ D t - (a : D)) * p
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, a.property.2]
  apply ht
  refine ⟨⟨x, compress hp (u⁻¹ : Dˣ), ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change (x : D) * (p * (↑u⁻¹ : D) * p) = p
    rw [← mul_assoc (x : D) _ p, ← mul_assoc (x : D) p, x.property.2, hx,
      mul_assoc p, Units.mul_inv, mul_one, hp.isIdempotentElem.eq]
  · apply Subtype.ext
    change p * (↑u⁻¹ : D) * p * (x : D) = p
    rw [mul_assoc, x.property.1, hx', ← mul_assoc, mul_assoc p, Units.inv_mul,
      mul_one, hp.isIdempotentElem.eq]

lemma finite_spectrum_of_coe {a : ProjectionCorner hp} (ha : (spectrum ℂ (a : D)).Finite) :
    (spectrum ℂ a).Finite := ha.subset (spectrum_subset_coe hp a)

end ProjectionCorner

end ProjectionCorners

section ProjectionPolars

open scoped NNReal

open Topology

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def unitaryPolar (z : D) : D := z * Ring.inverse (CFC.sqrt (star z * z))

lemma unitaryPolar_mem {z : D} (hz : IsUnit z) : unitaryPolar z ∈ unitary D := by
  let s := CFC.sqrt (star z * z)
  have hs : IsUnit s := (CFC.isUnit_sqrt_iff _).mpr (hz.star.mul hz)
  have hss : s * s = star z * z := CFC.sqrt_mul_sqrt_self _
  have hsa : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hsi : star (Ring.inverse s) = Ring.inverse s := by
    rw [← Ring.inverse_star, hsa]
  have hleft : star (unitaryPolar z) * unitaryPolar z = 1 := by
    change star (z * Ring.inverse s) * (z * Ring.inverse s) = 1
    rw [star_mul, hsi]
    calc
      _ = Ring.inverse s * (star z * z) * Ring.inverse s := by simp only [mul_assoc]
      _ = Ring.inverse s * (s * s) * Ring.inverse s := by rw [hss]
      _ = 1 := by rw [← mul_assoc, Ring.inverse_mul_cancel s hs, one_mul,
        Ring.mul_inverse_cancel s hs]
  have hu : IsUnit (unitaryPolar z) := hz.mul (hs.ringInverse)
  exact ⟨hleft, hu.mul_left_inj.mp (by simp only [mul_assoc, hleft, mul_one, one_mul])⟩

@[simp] lemma unitaryPolar_one : unitaryPolar (1 : D) = 1 := by
  simp [unitaryPolar]

lemma continuousAt_unitaryPolar_one : ContinuousAt (unitaryPolar : D → D) 1 := by
  have hs : Continuous (fun z : D => CFC.sqrt (star z * z)) :=
    CFC.continuousOn_sqrt.comp_continuous (continuous_star.mul continuous_id)
      (fun z => star_mul_self_nonneg z)
  have hi : ContinuousAt (fun z : D => Ring.inverse (CFC.sqrt (star z * z))) 1 := by
    apply ContinuousAt.comp (g := Ring.inverse) (f := fun z : D => CFC.sqrt (star z * z))
    · simpa using (NormedRing.inverse_continuousAt (1 : Dˣ))
    · exact hs.continuousAt
  exact continuousAt_id.mul hi

omit [PartialOrder D] [StarOrderedRing D] in
lemma commute_ring_inverse {a b : D} (h : Commute a b) (ha : IsUnit a) :
    Commute (Ring.inverse a) b := by
  apply ha.mul_right_inj.mp
  change a * (Ring.inverse a * b) = a * (b * Ring.inverse a)
  rw [← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul, ← mul_assoc, h.eq,
    mul_assoc, Ring.mul_inverse_cancel a ha, mul_one]

omit [PartialOrder D] [StarOrderedRing D] in
def projectionIntertwiner (p q : D) : D := p * q + (1 - p) * (1 - q)

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_self {p : D} (hp : IsStarProjection p) :
    projectionIntertwiner p p = 1 := by
  have hpp : p * p = p := hp.isIdempotentElem
  simp only [projectionIntertwiner, sub_mul, mul_sub, one_mul, mul_one, hpp]
  abel

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_mul {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : projectionIntertwiner p q * q = p * projectionIntertwiner p q := by
  have hpp : p * p = p := hp.isIdempotentElem
  have hqq : q * q = q := hq.isIdempotentElem
  have hz : projectionIntertwiner p q = 1 - p - q + 2 • (p * q) := by
    dsimp [projectionIntertwiner]
    noncomm_ring
  rw [hz]
  simp only [add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm]
  rw [mul_assoc p q q, hqq, ← mul_assoc p p q, hpp]
  abel

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_star {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : star (projectionIntertwiner p q) = projectionIntertwiner q p := by
  simp [projectionIntertwiner, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_square_commute {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    Commute (star (projectionIntertwiner p q) * projectionIntertwiner p q) q := by
  rw [projectionIntertwiner_star hp hq]
  show projectionIntertwiner q p * projectionIntertwiner p q * q =
    q * (projectionIntertwiner q p * projectionIntertwiner p q)
  rw [mul_assoc, projectionIntertwiner_mul hp hq, ← mul_assoc,
    projectionIntertwiner_mul hq hp, mul_assoc]

lemma unitaryPolar_intertwines {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hz : IsUnit (projectionIntertwiner p q)) :
    unitaryPolar (projectionIntertwiner p q) * q =
      p * unitaryPolar (projectionIntertwiner p q) := by
  let z := projectionIntertwiner p q
  have hs : Commute (CFC.sqrt (star z * z)) q :=
    (projectionIntertwiner_square_commute hp hq).cfcₙ_nnreal NNReal.sqrt
  have hi := commute_ring_inverse hs ((CFC.isUnit_sqrt_iff _).mpr (hz.star.mul hz))
  change z * Ring.inverse (CFC.sqrt (star z * z)) * q =
    p * (z * Ring.inverse (CFC.sqrt (star z * z)))
  rw [mul_assoc, hi.eq, ← mul_assoc, projectionIntertwiner_mul hp hq, mul_assoc]

lemma unitaryPolar_conjugates {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hz : IsUnit (projectionIntertwiner p q)) :
    unitaryPolar (projectionIntertwiner p q) * q *
      star (unitaryPolar (projectionIntertwiner p q)) = p := by
  rw [unitaryPolar_intertwines hp hq hz, mul_assoc, (unitaryPolar_mem hz).2, mul_one]

end ProjectionPolars

section SpectralCutoffs

variable {D : Type uD} [CStarAlgebra D]

def gapCutoff (t : ℝ) : ℝ := max 0 (min 1 (t - 1))

lemma gapCutoff_continuous : Continuous gapCutoff := by
  unfold gapCutoff
  fun_prop

lemma gapCutoff_eq_zero {t : ℝ} (h : t ≤ 1) : gapCutoff t = 0 := by
  unfold gapCutoff
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

lemma gapCutoff_eq_one {t : ℝ} (h : 2 ≤ t) : gapCutoff t = 1 := by
  unfold gapCutoff
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

@[simp] lemma gapCutoff_zero : gapCutoff 0 = 0 := gapCutoff_eq_zero (by norm_num)

lemma spectralCut_isProjection {a : D}
    (hgap : ∀ t ∈ spectrum ℝ a, t ≤ 1 ∨ 2 ≤ t) :
    IsStarProjection (cfc gapCutoff a) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc gapCutoff a * cfc gapCutoff a = cfc gapCutoff a
  rw [← cfc_mul gapCutoff gapCutoff a gapCutoff_continuous.continuousOn
    gapCutoff_continuous.continuousOn]
  apply cfc_congr
  intro t ht
  rcases hgap t ht with h | h
  · simp [gapCutoff_eq_zero h]
  · simp [gapCutoff_eq_one h]

lemma complexSpectrum_finite {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℝ a).Finite) : (spectrum ℂ a).Finite := by
  rw [← ha.spectrumRestricts.algebraMap_image]
  exact hfinite.image _

lemma finite_spectrum_cfc {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℂ a).Finite) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a)) :
    (spectrum ℂ (cfc f a)).Finite := by
  apply complexSpectrum_finite (cfc_predicate _ _)
  rw [cfc_map_spectrum f a ha hf]
  exact (realSpectrum_finite ha hfinite).image f

lemma spectrum_shift_lower {a : D} {R t : ℝ} (hR : ‖a‖ + 2 < R)
    (ht : t ∈ spectrum ℝ (a + R • (1 : D))) : 2 < t := by
  cases subsingleton_or_nontrivial D with
  | inl hsubsingleton =>
    let := hsubsingleton
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at ht
  | inr hnontrivial =>
    let := hnontrivial
    have hmem : t - R ∈ spectrum ℝ a := by
      apply (spectrum.add_mem_add_iff (r := t - R) (s := R)).mp
      simpa [Algebra.algebraMap_eq_smul_one, add_comm] using ht
    have hn := spectrum.norm_le_norm_of_mem hmem
    rw [Real.norm_eq_abs] at hn
    have := (abs_le.mp hn).1
    linarith

lemma cutoff_shift_corner {p : D} (hp : IsStarProjection p)
    {a : ProjectionCorner hp} (ha : IsSelfAdjoint a) {R : ℝ} (hR : ‖a‖ + 2 < R) :
    cfc gapCutoff ((a : D) + R • p) = p := by
  let b : ProjectionCorner hp := a + R • 1
  have hb : IsSelfAdjoint b := ha.add ((isSelfAdjoint_iff.mpr (star_trivial R)).smul (IsSelfAdjoint.one _))
  have hbval : (b : D) = (a : D) + R • p := rfl
  rw [← hbval, ← ProjectionCorner.coe_cfc hp hb gapCutoff gapCutoff_continuous gapCutoff_zero]
  have he : cfc gapCutoff b = (1 : ProjectionCorner hp) := by
    rw [← cfc_one ℝ b hb]
    apply cfc_congr
    intro t ht
    exact gapCutoff_eq_one (spectrum_shift_lower hR ht).le
  rw [he, ProjectionCorner.coe_one]

lemma cutoff_shift_corner_gap {p : D} (hp : IsStarProjection p)
    (a : ProjectionCorner hp) {R : ℝ} (hR : ‖a‖ + 2 < R) :
    spectrum ℝ ((a : D) + R • p) ⊆ {t : ℝ | t < 1 ∨ 2 < t} := by
  intro t ht
  have ht' := ProjectionCorner.spectrum_coe_subset hp (a + R • 1) ht
  rcases ht' with ht' | ht'
  · exact Or.inr (spectrum_shift_lower hR ht')
  · exact Or.inl (by simpa only [Set.mem_singleton_iff.mp ht'] using (show (0 : ℝ) < 1 by norm_num))

lemma realRankZero_dense (hD : RealRankZero D) :
    Dense {a : selfAdjoint D | (spectrum ℂ (a : D)).Finite} := by
  intro a
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨b, hb, hbf, hab⟩ := hD a a.property ε hε
  refine ⟨⟨b, hb⟩, hbf, ?_⟩
  rw [dist_eq_norm]
  change ‖(a : D) - b‖ < ε
  exact hab

lemma spectrum_conjugate_unitary {u a : D} (hu : u ∈ unitary D) :
    spectrum ℂ (u * a * star u) = spectrum ℂ a :=
  spectrum.units_conjugate (u := Unitary.toUnits ⟨u, hu⟩)

lemma projection_conjugate_compress {u p q a : D}
    (hq : IsStarProjection q) (hqa : Commute q a)
    (hpu : p * u = u * q) (hup : star u * p = q * star u) :
    p * (u * a * star u) * p = u * (a * q) * star u := by
  calc
    p * (u * a * star u) * p = (p * u) * a * (star u * p) := by simp only [mul_assoc]
    _ = (u * q) * a * (q * star u) := by rw [hpu, hup]
    _ = u * (a * q) * star u := by
      rw [mul_assoc u q a, hqa.eq]
      simp only [mul_assoc, ← mul_assoc q q, hq.isIdempotentElem.eq]

lemma finite_spectrum_cut {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℂ a).Finite) :
    (spectrum ℂ (a * cfc gapCutoff a)).Finite := by
  have he : a * cfc gapCutoff a = cfc (fun t : ℝ => t * gapCutoff t) a := by
    rw [cfc_mul (fun t : ℝ => t) gapCutoff a continuous_id.continuousOn gapCutoff_continuous.continuousOn,
      cfc_id' ℝ a ha]
  rw [he]
  exact finite_spectrum_cfc ha hf _ (continuous_id.mul gapCutoff_continuous).continuousOn

lemma realRankZero_corner (hD : RealRankZero D) {p : D} (hp : IsStarProjection p) :
    RealRankZero (ProjectionCorner hp) := by
  let := CStarAlgebra.spectralOrder D
  let := CStarAlgebra.spectralOrderedRing D
  intro h hh ε hε
  let R : ℝ := ‖h‖ + 3
  have hR : ‖h‖ + 2 < R := by dsimp [R]; linarith
  let b : selfAdjoint D := ⟨(h : D) + R • p,
    (ProjectionCorner.isSelfAdjoint_coe hp hh).add ((isSelfAdjoint_iff.mpr (star_trivial R)).smul hp.isSelfAdjoint)⟩
  let q : selfAdjoint D → D := fun a => cfc gapCutoff (a : D)
  let z : selfAdjoint D → D := fun a => projectionIntertwiner p (q a)
  let u : selfAdjoint D → D := fun a => unitaryPolar (z a)
  let F : selfAdjoint D → D := fun a => p * (u a * (a : D) * star (u a)) * p
  have hqb : q b = p := cutoff_shift_corner hp hh hR
  have hzb : z b = 1 := by dsimp [z]; rw [hqb, projectionIntertwiner_self hp]
  have hub : u b = 1 := by dsimp [u]; rw [hzb, unitaryPolar_one]
  have hFb : F b = (b : D) := by
    dsimp [F]
    rw [hub, star_one, one_mul, mul_one]
    change p * ((h : D) + R • p) * p = (h : D) + R • p
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      h.property.1, h.property.2, hp.isIdempotentElem.eq]
  have hqcont : Continuous q :=
    Continuous.cfc_of_mem_nhdsSet gapCutoff Filter.univ_mem continuous_subtype_val
      (fun a => a.property) gapCutoff_continuous.continuousOn
  have hzcont : Continuous z := by
    dsimp [z, projectionIntertwiner]
    fun_prop
  have hucont : ContinuousAt u b := by
    apply ContinuousAt.comp (f := z) (g := unitaryPolar)
    · rw [hzb]
      exact continuousAt_unitaryPolar_one
    · exact hzcont.continuousAt
  have hFcont : ContinuousAt F b := by
    exact (continuousAt_const.mul ((hucont.mul continuous_subtype_val.continuousAt).mul
      hucont.star)).mul continuousAt_const
  have hnear : ∀ᶠ a in nhds b, ‖F a - (b : D)‖ < ε := by
    simpa only [hFb, dist_eq_norm] using Metric.tendsto_nhds.mp hFcont ε hε
  have hunit : ∀ᶠ a : selfAdjoint D in nhds b, IsUnit (z a) := by
    change z ⁻¹' {x : D | IsUnit x} ∈ nhds b
    apply hzcont.continuousAt.preimage_mem_nhds
    rw [hzb]
    exact Units.nhds (1 : Dˣ)
  let S : Set ℝ := {t | t < 1 ∨ 2 < t}
  have hS : IsOpen S := isOpen_lt continuous_id continuous_const |>.union
    (isOpen_lt continuous_const continuous_id)
  have hgap : ∀ᶠ a : selfAdjoint D in nhds b, ∀ t ∈ spectrum ℝ (a : D), t ≤ 1 ∨ 2 ≤ t := by
    have hbS : S ∈ nhdsSet (spectrum ℝ (b : D)) :=
      hS.mem_nhdsSet.mpr (cutoff_shift_corner_gap hp h hR)
    have he := (upperHemicontinuous_spectrum ℝ D).upperHemicontinuousAt (b : D) S hbS
    have he' := continuous_subtype_val.continuousAt.tendsto.eventually he
    filter_upwards [he'] with a ha
    intro t ht
    exact (subset_of_mem_nhdsSet ha ht).imp le_of_lt le_of_lt
  obtain ⟨a, hfinite, hgap, hunit, hnear⟩ :=
    (realRankZero_dense hD).inter_nhds_nonempty (hgap.and (hunit.and hnear))
  have hqa : IsStarProjection (q a) := spectralCut_isProjection hgap
  have hpu : p * u a = u a * q a := (unitaryPolar_intertwines hp hqa hunit).symm
  have hup : star (u a) * p = q a * star (u a) := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hqa.isSelfAdjoint.star_eq] using
      congrArg star hpu
  have hcomm : Commute (q a) (a : D) := a.property.commute_cfc (Commute.refl _) gapCutoff
  have hFeq : F a = u a * ((a : D) * q a) * star (u a) :=
    projection_conjugate_compress hqa hcomm hpu hup
  let c : ProjectionCorner hp := ProjectionCorner.compress hp (u a * (a : D) * star (u a))
  have hc : IsSelfAdjoint c := by
    apply Subtype.ext
    change star (p * (u a * (a : D) * star (u a)) * p) =
      p * (u a * (a : D) * star (u a)) * p
    simpa only [hp.isSelfAdjoint.star_eq] using
      (a.property.conjugate (u a) |>.conjugate p).star_eq
  have hcf : (spectrum ℂ c).Finite := by
    apply ProjectionCorner.finite_spectrum_of_coe hp
    change (spectrum ℂ (F a)).Finite
    rw [hFeq, spectrum_conjugate_unitary (unitaryPolar_mem hunit)]
    exact finite_spectrum_cut a.property hfinite
  refine ⟨c - R • 1, hc.sub ((isSelfAdjoint_iff.mpr (star_trivial R)).smul (IsSelfAdjoint.one _)), ?_, ?_⟩
  · apply complexSpectrum_finite (hc.sub ((isSelfAdjoint_iff.mpr (star_trivial R)).smul (IsSelfAdjoint.one _)))
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq]
    exact (realSpectrum_finite hc hcf).sub (Set.finite_singleton R)
  · have he : ((h - (c - R • 1) : ProjectionCorner hp) : D) = (b : D) - F a := by
      change (h : D) - (F a - R • p) = (h : D) + R • p - F a
      abel
    change ‖((h - (c - R • 1) : ProjectionCorner hp) : D)‖ < ε
    rw [he, norm_sub_rev]
    exact hnear

end SpectralCutoffs

end CurrentMain

end

end

end OAI
