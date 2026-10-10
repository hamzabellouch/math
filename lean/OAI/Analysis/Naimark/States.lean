import OAI.Analysis.Naimark.Basic

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

def cornerSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | e * a = a ∧ a * e = a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    simp [mul_add, add_mul, ha, hb, ha', hb']
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [← mul_assoc, ha], by rw [mul_assoc, hb']⟩
  smul_mem' := by
    rintro z a ⟨ha,ha'⟩
    exact ⟨by rw [mul_smul_comm, ha], by rw [smul_mul_assoc, ha']⟩
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha

instance cornerClosed : IsClosed (cornerSubalgebra e he : Set A) := by
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

abbrev CStarCorner := cornerSubalgebra e he

instance cornerOne : One (CStarCorner e he) :=
  ⟨⟨e, he.isIdempotentElem.eq, he.isIdempotentElem.eq⟩⟩

@[simp] theorem corner_coe_one : ((1 : CStarCorner e he) : A) = e := rfl

instance cornerRing : Ring (CStarCorner e he) := {
  (inferInstance : NonUnitalRing (CStarCorner e he)) with
  one := 1
  one_mul a := Subtype.ext a.2.1
  mul_one a := Subtype.ext a.2.2
  natCast n := n • (1 : CStarCorner e he)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast z := z • (1 : CStarCorner e he)
  intCast_ofNat n := ofNat_zsmul _ _
  intCast_negSucc n := by
    change (Int.negSucc n) • (1 : CStarCorner e he) = -((n+1) • (1 : CStarCorner e he))
    rw [Int.negSucc_eq, neg_zsmul]
    congr 1
    exact ofNat_zsmul (1 : CStarCorner e he) (n+1) }

instance cornerNormedRing : NormedRing (CStarCorner e he) := {
  (inferInstance : NonUnitalNormedRing (CStarCorner e he)), cornerRing e he with }

instance cornerAlgebra : Algebra ℂ (CStarCorner e he) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance cornerCStarAlgebra : CStarAlgebra (CStarCorner e he) := {
  (inferInstance : NonUnitalCStarAlgebra (CStarCorner e he)),
  cornerNormedRing e he, cornerAlgebra e he with }

instance cornerPartialOrder : PartialOrder (CStarCorner e he) :=
  CStarAlgebra.spectralOrder _

instance cornerStarOrderedRing : StarOrderedRing (CStarCorner e he) :=
  CStarAlgebra.spectralOrderedRing _

def cornerCompression : A →L[ℂ] CStarCorner e he where
  toFun a := ⟨e*a*e, by
    constructor
    · rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq]
    · rw [mul_assoc (e*a), he.isIdempotentElem.eq]⟩
  map_add' a b := Subtype.ext (by
    change e*(a+b)*e = e*a*e+e*b*e
    simp only [mul_add, add_mul])
  map_smul' z a := Subtype.ext (by
    change e*(z • a)*e = z • (e*a*e)
    simp only [mul_smul_comm, smul_mul_assoc])
  cont := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).mul continuous_const

@[simp] theorem cornerCompression_coe (a : A) :
    (cornerCompression e he a : A) = e*a*e := rfl

@[simp] theorem cornerCompression_corner (a : CStarCorner e he) :
    cornerCompression e he (a : A) = a := by
  apply Subtype.ext
  exact (congrArg (· * e) a.2.1).trans a.2.2

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def weakStates (A : Type*) [CStarAlgebra A] : Set (WeakDual ℂ A) :=
  {f | IsState f.toStrongDual}

theorem isClosed_weakStates : IsClosed (weakStates A) := by
  have hone : IsClosed {f : WeakDual ℂ A | f 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  have hpos (a : A) : IsClosed {f : WeakDual ℂ A |
      (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re} :=
    (isClosed_eq (Complex.continuous_im.comp (WeakDual.eval_continuous _)) continuous_const).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous _)))
  have h := hone.inter (isClosed_iInter hpos)
  simpa only [weakStates, isState_iff, WeakDual.toStrongDual_apply, Set.ofPred_and,
    Set.ofPred_forall] using h

theorem isCompact_weakStates : IsCompact (weakStates A) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).of_isClosed_subset
    isClosed_weakStates
  intro f hf
  change f.toStrongDual ∈ Metric.closedBall 0 1
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq hf.1

theorem state_eq_one_of_projection_le (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p q : A) (hq : IsStarProjection q) (hpq : p ≤ q) (hfp : f p = 1) : f q = 1 := by
  have hmono := (positiveOfSquares f hf.2).monotone
  apply le_antisymm
  · have hh := hmono hq.le_one
    change f q ≤ f 1 at hh
    rwa [((isState_iff f).mp hf).1] at hh
  · have hh := hmono hpq
    change f p ≤ f q at hh
    rwa [hfp] at hh

theorem Peaks.tendsto_supported {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (g : ℕ → A →L[ℂ] ℂ) (hg : ∀ n, IsState (g n)) (hgn : ∀ n, g n (p n) = 1) :
    Tendsto (fun n => StrongDual.toWeakDual (g n)) atTop (𝓝 (StrongDual.toWeakDual f)) := by
  apply isCompact_weakStates.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall hg)
  intro k hk hcluster
  apply WeakDual.toStrongDual.injective
  apply hp.2.2.2.2 _ hk
  intro m
  have hclosed : IsClosed {z : WeakDual ℂ A | z (p m) = 1} :=
    isClosed_eq (WeakDual.eval_continuous _) continuous_const
  apply hclosed.mem_of_mapClusterPt hcluster
  filter_upwards [eventually_ge_atTop m] with n hn
  exact state_eq_one_of_projection_le (g n) (hg n) (p n) (p m) (hp.1 m) (hp.2.1 hn) (hgn n)

theorem Peaks.tendsto_supported_apply {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (g : ℕ → A →L[ℂ] ℂ) (hg : ∀ n, IsState (g n)) (hgn : ∀ n, g n (p n) = 1) (a : A) :
    Tendsto (fun n => g n a) atTop (𝓝 (f a)) :=
  ((WeakDual.eval_continuous a).tendsto _).comp (hp.tendsto_supported g hg hgn)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def cornerFunctional (f : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  f.comp (ContinuousLinearMap.mulLeftRight ℂ A p p)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerFunctional_apply (f : A →L[ℂ] ℂ) (p a : A) :
    cornerFunctional f p a = f (p * a * p) := rfl

def cornerState (f : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  (f p).re⁻¹ • cornerFunctional f p

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerState_apply (f : A →L[ℂ] ℂ) (p a : A) :
    cornerState f p a = (f p).re⁻¹ • f (p * a * p) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem state_projection_real (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) : f p = ((f p).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, Complex.ofReal_im]
      using (hf.2 p).1

theorem cornerState_isState (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) (hpos : 0 < (f p).re) : IsState (cornerState f p) := by
  apply (isState_iff _).mpr
  constructor
  · rw [cornerState_apply, mul_one, hp.isIdempotentElem.eq, state_projection_real f hf p hp]
    simp only [Complex.ofReal_re]
    rw [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]
  · intro a
    have heq : p * (star a * a) * p = star (a * p) * (a * p) := by
      rw [star_mul, hp.isSelfAdjoint.star_eq]
      noncomm_ring
    rw [cornerState_apply, heq]
    simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul,
      (hf.2 (a * p)).1, mul_zero, true_and]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hpos)) (hf.2 (a * p)).2

theorem cornerState_eq_one (f : A →L[ℂ] ℂ) (hf : IsState f)
    (q p : A) (hq : IsStarProjection q) (hp : IsStarProjection p) (hqp : q ≤ p)
    (hpos : 0 < (f q).re) : cornerState f q p = 1 := by
  rw [cornerState_apply, (hq.le_iff_mul_eq_left hp).mp hqp, hq.isIdempotentElem.eq,
    state_projection_real f hf q hq]
  simp only [Complex.ofReal_re]
  rw [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]

def peakAtom (p : ℕ → A) (n : ℕ) : A := p n - p (n + 1)

theorem Peaks.peakAtom_projection {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    IsStarProjection (peakAtom p n) :=
  ((hp.1 (n+1)).le_iff_sub (hp.1 n)).mp (hp.2.1 (Nat.le_succ n))

theorem Peaks.peakAtom_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    peakAtom p n ≤ p n := by
  exact sub_le_self _ (hp.1 (n+1)).nonneg

theorem Peaks.tendsto_atomState {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    Tendsto (fun n => cornerState τ (peakAtom p n) a) atTop (𝓝 (f a)) := by
  apply hp.tendsto_supported_apply
  · intro n
    exact cornerState_isState τ hτ _ (hp.peakAtom_projection n) (hpos n)
  · intro n
    exact cornerState_eq_one τ hτ _ _ (hp.peakAtom_projection n) (hp.1 n)
      (hp.peakAtom_le n) (hpos n)

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem selfAdjoint_nonneg_of_norm_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ g a := by
  have hau : (a : A) ≤ ‖a‖ • (1 : A) := by
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap (a : A) (norm_nonneg _) ha).mp le_rfl
  have hpos : 0 ≤ ‖a‖ • (1 : A) - (a : A) := sub_nonneg.mpr hau
  have hnorm : ‖‖a‖ • (1 : selfAdjoint A) - a‖ ≤ ‖a‖ := by
    change ‖‖a‖ • (1 : A) - (a : A)‖ ≤ ‖a‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hpos).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_le_self (‖a‖ • (1 : A)) ha
  have hb := g.le_opNorm (‖a‖ • (1 : selfAdjoint A) - a)
  have hc : ‖g (‖a‖ • (1 : selfAdjoint A) - a)‖ ≤ ‖a‖ :=
    hb.trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans (by simpa using hnorm))
  rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, Real.norm_eq_abs] at hc
  have h := (le_abs_self _).trans hc
  linarith

def selfAdjointComplexify (g : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (g (realPart a) : ℂ) + Complex.I * (g (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add, mul_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem selfAdjointComplexify_coe (g : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    selfAdjointComplexify g (a : A) = (g a : ℂ) := by
  simp [selfAdjointComplexify]

def selfAdjointPositive (g : selfAdjoint A →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (selfAdjointComplexify g.toLinearMap) fun a ha => by
    let x : selfAdjoint A := ⟨a, ha.isSelfAdjoint⟩
    change 0 ≤ selfAdjointComplexify g.toLinearMap (x : A)
    rw [selfAdjointComplexify_coe]
    exact ⟨selfAdjoint_nonneg_of_norm_one g hg h1 x ha, by simp⟩

@[simp] theorem selfAdjointPositive_coe (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) :
    selfAdjointPositive g hg h1 (a : A) = (g a : ℂ) :=
  selfAdjointComplexify_coe _ _

@[simp] theorem selfAdjointPositive_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) : selfAdjointPositive g hg h1 1 = 1 := by
  simpa only [selfAdjoint.val_one, h1, Complex.ofReal_one] using selfAdjointPositive_coe g hg h1 1

def selfAdjointSubspace (S : StarSubalgebra ℂ A) : Submodule ℝ A :=
  (S.toSubalgebra.toSubmodule.restrictScalars ℝ) ⊓ selfAdjoint.submodule ℝ A

def selfAdjointSubspaceInclusion (S : StarSubalgebra ℂ A) :
    selfAdjointSubspace S →L[ℝ] S :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨a.val, a.property.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun a => by simp [one_mul])

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_state_extension_subalgebra
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (f : S →L[ℂ] ℂ) (hf : IsState f) :
    ∃ F : A →L[ℂ] ℂ, IsState F ∧ ∀ a : S, F (a : A) = f a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let g : selfAdjointSubspace S →L[ℝ] ℝ :=
    Complex.reCLM.comp ((f.restrictScalars ℝ).comp (selfAdjointSubspaceInclusion S))
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro a
    change ‖(f (selfAdjointSubspaceInclusion S a)).re‖ ≤ 1 * ‖a‖
    calc
      _ ≤ ‖f (selfAdjointSubspaceInclusion S a)‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
      _ ≤ ‖selfAdjointSubspaceInclusion S a‖ := state_norm_apply_le f hf _
      _ = 1 * ‖a‖ := by simp [selfAdjointSubspaceInclusion]; rfl
  obtain ⟨G₀, hG₀, hnG₀⟩ := exists_extension_norm_eq (selfAdjointSubspace S) g
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let G := G₀.comp sa
  have hGn : ‖G‖ ≤ 1 := by
    apply G.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖G a‖ ≤ ‖G₀‖ * ‖sa a‖ := G₀.le_opNorm _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hnG₀.trans_le hg) (norm_nonneg _)
  have hG1 : G 1 = 1 := by
    let e : selfAdjointSubspace S := ⟨1, S.one_mem, IsSelfAdjoint.one A⟩
    have he := hG₀ e
    change G 1 = (f 1).re at he
    simpa only [(isState_iff f).mp hf |>.1, Complex.one_re] using he
  let F := positiveCLM (selfAdjointPositive G hGn hG1)
  have hF : IsState F := by
    apply (isState_iff _).mpr
    refine ⟨selfAdjointPositive_one G hGn hG1, fun a => ?_⟩
    exact ⟨((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).2.symm,
      ((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).1⟩
  refine ⟨F, hF, ?_⟩
  have hs (a : S) (ha : IsSelfAdjoint a) : F (a : A) = f a := by
    let b : selfAdjointSubspace S := ⟨(a : A), a.property, by
      change star (a : A) = (a : A)
      exact congrArg Subtype.val ha.star_eq⟩
    let bsa : selfAdjoint A := ⟨(a : A), b.property.2⟩
    have hfb : (f a).im = 0 := by
      have hh := state_map_star f hf a
      rw [ha.star_eq] at hh
      exact Complex.conj_eq_iff_im.mp hh.symm
    change selfAdjointPositive G hGn hG1 (bsa : A) = f a
    rw [selfAdjointPositive_coe]
    change (G₀ b : ℂ) = f a
    rw [hG₀ b]
    change ((f a).re : ℂ) = f a
    exact Complex.ext (by simp) (by simpa using hfb.symm)
  intro a
  have hdecomp := realPart_add_I_smul_imaginaryPart a
  rw [← hdecomp]
  change F (((realPart a : S) : A) + Complex.I • ((imaginaryPart a : S) : A)) = _
  simp only [map_add, map_smul]
  rw [hs _ (realPart a).property, hs _ (imaginaryPart a).property]

omit [PartialOrder A] [StarOrderedRing A] in

theorem character_isState (φ : WeakDual.characterSpace ℂ A) :
    IsState (WeakDual.toStrongDual (φ : WeakDual ℂ A)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  apply (isState_iff _).mpr
  refine ⟨map_one φ, fun a => ?_⟩
  change (φ (star a * a)).im = 0 ∧ 0 ≤ (φ (star a * a)).re
  rw [map_mul, map_star]
  have h := star_mul_self_nonneg (φ a)
  exact ⟨h.2.symm, h.1⟩

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_norming_state [Nontrivial A] (a : A) [IsStarNormal a] :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ ‖f a‖ = ‖a‖ := by
  let S := StarAlgebra.elemental ℂ a
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ a
  let b : S := ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  obtain ⟨z, hz, hnz⟩ :=
    (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℂ) b).1
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  obtain ⟨f, hf, hrest⟩ := exists_state_extension_subalgebra S
    (WeakDual.toStrongDual (φ : WeakDual ℂ S)) (character_isState φ)
  refine ⟨f, hf, ?_⟩
  change ‖f (b : A)‖ = ‖b‖
  rw [hrest b]
  change ‖φ b‖ = ‖b‖
  rw [hφ]
  exact hnz

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

variable {A : Type*} [CStarAlgebra A] {ι : Type*}

theorem orthogonalProjection_commute (p : ι → A)
    (horth : Pairwise (fun i j => p i * p j = 0)) (i j : ι) : Commute (p i) (p j) := by
  by_cases h : i = j
  · subst j; exact Commute.refl _
  · exact (horth h).trans (horth (Ne.symm h)).symm

theorem normal_orthogonalProjection_sum (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ι → ℂ) (s : Finset ι) :
    IsStarNormal (∑ i ∈ s, c i • p i) := by
  constructor
  rw [star_sum]
  apply Commute.sum_left
  intro i hi
  apply Commute.sum_right
  intro j hj
  rw [star_smul, (hp i).isSelfAdjoint.star_eq]
  exact (orthogonalProjection_commute p horth i j).smul_left (star (c i)) |>.smul_right (c j)

theorem norm_orthogonalProjection_sum_le (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ι → ℂ) (s : Finset ι)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i ∈ s, ‖c i‖ ≤ C) : ‖∑ i ∈ s, c i • p i‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hC
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    have hn : IsStarNormal (c i • p i) := by
      let : IsStarNormal (p i) := (hp i).isSelfAdjoint.isStarNormal
      infer_instance
    have hs := normal_orthogonalProjection_sum p hp horth c s
    have hab : (c i • p i) * (∑ j ∈ s, c j • p j) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [smul_mul_assoc, mul_smul_comm, horth (ne_of_mem_of_not_mem hj his).symm,
        smul_zero]
    have hcomm : Commute (c i • p i) (∑ j ∈ s, c j • p j) := by
      apply Commute.sum_right
      intro j hj
      exact (orthogonalProjection_commute p horth i j).smul_left _ |>.smul_right _
    rw [hn.norm_add_eq_max hs hcomm hab]
    apply max_le
    · calc
        ‖c i • p i‖ = ‖c i‖ * ‖p i‖ := norm_smul _ _
        _ ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left ((hp i).norm_le _) (norm_nonneg _)
        _ ≤ C := by simpa using hc i (Finset.mem_insert_self _ _)
    · exact ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))

theorem summable_orthogonalProjection (p : ℕ → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ℕ → ℂ)
    (hc : Tendsto c atTop (𝓝 0)) : Summable (fun i => c i • p i) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hsmall := (tendsto_zero_iff_norm_tendsto_zero.mp hc).eventually
    (Iio_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨Finset.range N, fun s hs => ?_⟩
  apply lt_of_le_of_lt (norm_orthogonalProjection_sum_le p hp horth c s (ε/2)
    (le_of_lt (half_pos hε)) ?_) (half_lt_self hε)
  intro i hi
  apply le_of_lt (hN i _)
  by_contra h
  have hin : i ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge h)
  exact Finset.disjoint_left.mp hs hi hin

theorem orthogonalProjection_mul_tsum (p : ℕ → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ℕ → ℂ)
    (hc : Tendsto c atTop (𝓝 0)) (k : ℕ) :
    p k * (∑' i, c i • p i) = c k • p k := by
  rw [← (summable_orthogonalProjection p hp horth c hc).tsum_mul_left]
  apply Eq.trans (tsum_eq_single k ?_) ?_
  · intro i hik
    simp only [mul_smul_comm, horth (Ne.symm hik), smul_zero]
  · rw [mul_smul_comm, (hp k).isIdempotentElem.eq]

theorem norm_orthogonalProjection_tsum_le (p : ℕ → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ℕ → ℂ)
    (hc : Tendsto c atTop (𝓝 0)) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, ‖c i‖ ≤ C) :
    ‖∑' i, c i • p i‖ ≤ C := by
  apply le_of_tendsto ((summable_orthogonalProjection p hp horth c hc).hasSum.norm)
  exact Filter.Eventually.of_forall fun s =>
    norm_orthogonalProjection_sum_le p hp horth c s C hC (fun i _ => hbound i)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.peakAtom_mul_peak {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    {i n : ℕ} (hin : i < n) : peakAtom p i * p n = 0 := by
  have h₁ := ((hp.1 n).le_iff_mul_eq_right (hp.1 i)).mp (hp.2.1 (Nat.le_of_lt hin))
  have h₂ := ((hp.1 n).le_iff_mul_eq_right (hp.1 (i+1))).mp (hp.2.1 hin)
  simp only [peakAtom, sub_mul, h₁, h₂, sub_self]

theorem Peaks.peak_mul_peakAtom {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    {i n : ℕ} (hin : i < n) : p n * peakAtom p i = 0 := by
  simpa only [star_mul, (hp.1 n).isSelfAdjoint.star_eq,
    (hp.peakAtom_projection i).isSelfAdjoint.star_eq, star_zero]
    using congrArg star (hp.peakAtom_mul_peak hin)

theorem Peaks.peakAtom_orthogonal {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) :
    Pairwise (fun i j => peakAtom p i * peakAtom p j = 0) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · change peakAtom p i * (p j - p (j+1)) = 0
    rw [mul_sub, hp.peakAtom_mul_peak h, hp.peakAtom_mul_peak (h.trans_le (Nat.le_succ j)),
      sub_self]
  · change (p i - p (i+1)) * peakAtom p j = 0
    rw [sub_mul, hp.peak_mul_peakAtom h, hp.peak_mul_peakAtom (h.trans_le (Nat.le_succ i)),
      sub_self]

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakAtom_sum (p : ℕ → A) (n : ℕ) :
    ∑ i ∈ Finset.range n, peakAtom p i = p 0 - p n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, peakAtom]; abel

def peakDiagonal (p : ℕ → A) (c : ℂ) (b : ℕ → ℂ) : A :=
  c • (1 : A) + ∑' i, (b i - c) • peakAtom p i

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakDiagonal_partial {p : ℕ → A} (hp0 : p 0 = 1)
    (c : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i =
      (∑ i ∈ Finset.range n, b i • peakAtom p i) + c • p n := by
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, peakAtom_sum, hp0, smul_sub]
  abel

theorem Peaks.norm_peakDiagonal_partial_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (c : ℂ) (b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ‖c‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ C) (n : ℕ) :
    ‖c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i‖ ≤ C := by
  rw [peakDiagonal_partial hp0]
  have hs := normal_orthogonalProjection_sum _ hp.peakAtom_projection hp.peakAtom_orthogonal
    b (Finset.range n)
  have hn : IsStarNormal (c • p n) := by
    let : IsStarNormal (p n) := (hp.1 n).isSelfAdjoint.isStarNormal
    infer_instance
  have hzero : (∑ i ∈ Finset.range n, b i • peakAtom p i) * (c • p n) = 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [smul_mul_assoc, mul_smul_comm, hp.peakAtom_mul_peak (Finset.mem_range.mp hi),
      smul_zero]
  have hzero' : (c • p n) * (∑ i ∈ Finset.range n, b i • peakAtom p i) = 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [smul_mul_assoc, mul_smul_comm, hp.peak_mul_peakAtom (Finset.mem_range.mp hi),
      smul_zero]
  rw [hs.norm_add_eq_max hn (hzero.trans hzero'.symm) hzero]
  apply max_le
  · exact norm_orthogonalProjection_sum_le _ hp.peakAtom_projection hp.peakAtom_orthogonal
      b _ C hC (fun i _ => hb i)
  · calc
      ‖c • p n‖ = ‖c‖ * ‖p n‖ := norm_smul _ _
      _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left ((hp.1 n).norm_le _) (norm_nonneg _)
      _ ≤ C := by simpa using hc

theorem Peaks.tendsto_peakDiagonal {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (c : ℂ) (b : ℕ → ℂ) (hb : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun n => c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i)
      atTop (𝓝 (peakDiagonal p c b)) := by
  apply tendsto_const_nhds.add
  exact (summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal
    (fun i => b i - c) (by simpa using hb.sub_const c)).hasSum.tendsto_sum_nat

theorem Peaks.norm_peakDiagonal_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (c : ℂ) (b : ℕ → ℂ) (hb : Tendsto b atTop (𝓝 c))
    (C : ℝ) (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hbc : ∀ i, ‖b i‖ ≤ C) :
    ‖peakDiagonal p c b‖ ≤ C := by
  apply le_of_tendsto (hp.tendsto_peakDiagonal c b hb).norm
  exact Filter.Eventually.of_forall (hp.norm_peakDiagonal_partial_le hp0 c b C hC hc hbc)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.summable_expectationTail {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    Summable (fun n => (cornerState τ (peakAtom p n) a - f a) • peakAtom p n) :=
  summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal _
    (by simpa using (hp.tendsto_atomState τ hτ hpos a).sub_const (f a))

def peakingExpectationFun (p : ℕ → A) (f τ : A →L[ℂ] ℂ) (a : A) : A :=
  peakDiagonal p (f a) (fun n => cornerState τ (peakAtom p n) a)

theorem Peaks.peakingExpectationFun_add {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a b : A) :
    peakingExpectationFun p f τ (a + b) =
      peakingExpectationFun p f τ a + peakingExpectationFun p f τ b := by
  have heq (n : ℕ) :
      (cornerState τ (peakAtom p n) (a+b) - f (a+b)) • peakAtom p n =
        (cornerState τ (peakAtom p n) a - f a) • peakAtom p n +
        (cornerState τ (peakAtom p n) b - f b) • peakAtom p n := by
    rw [map_add, map_add, add_sub_add_comm, add_smul]
  simp only [peakingExpectationFun, peakDiagonal]
  simp_rw [heq]
  rw [(hp.summable_expectationTail τ hτ hpos a).tsum_add
    (hp.summable_expectationTail τ hτ hpos b), map_add, add_smul]
  abel

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakingExpectationFun_smul (p : ℕ → A) (f τ : A →L[ℂ] ℂ) (c : ℂ) (a : A) :
    peakingExpectationFun p f τ (c • a) = c • peakingExpectationFun p f τ a := by
  simp only [peakingExpectationFun, peakDiagonal, map_smul, ← smul_sub]
  simp_rw [smul_assoc]
  rw [tsum_const_smul'', smul_add]

theorem Peaks.norm_peakingExpectationFun_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    ‖peakingExpectationFun p f τ a‖ ≤ ‖a‖ := by
  exact hp.norm_peakDiagonal_le hp0 _ _ (hp.tendsto_atomState τ hτ hpos a) _ (norm_nonneg _)
    (state_norm_apply_le _ hp.2.2.1 _)
    (fun n => state_norm_apply_le _ (cornerState_isState _ hτ _ (hp.peakAtom_projection n)
      (hpos n)) _)

def peakingExpectation {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) : A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := peakingExpectationFun p f τ
      map_add' := hp.peakingExpectationFun_add τ hτ hpos
      map_smul' := peakingExpectationFun_smul p f τ }
    1 (fun a => by
      change ‖peakingExpectationFun p f τ a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using hp.norm_peakingExpectationFun_le hp0 τ hτ hpos a)

@[simp] theorem peakingExpectation_apply {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos a = peakingExpectationFun p f τ a := rfl

theorem peakingExpectation_one {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) :
    peakingExpectation hp hp0 τ hτ hpos 1 = 1 := by
  have hf1 := ((isState_iff f).mp hp.2.2.1).1
  have hc1 (n : ℕ) := ((isState_iff _).mp
    (cornerState_isState _ hτ _ (hp.peakAtom_projection n) (hpos n))).1
  simp only [peakingExpectation_apply, peakingExpectationFun, peakDiagonal, hf1, hc1,
    sub_self, zero_smul, tsum_zero, add_zero, one_smul]

theorem peakingExpectation_nonneg {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) {a : A} (ha : 0 ≤ a) :
    0 ≤ peakingExpectation hp hp0 τ hτ hpos a := by
  apply ge_of_tendsto (hp.tendsto_peakDiagonal (f a)
    (fun n => cornerState τ (peakAtom p n) a) (hp.tendsto_atomState τ hτ hpos a))
  apply Filter.Eventually.of_forall
  intro n
  rw [peakDiagonal_partial hp0]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact smul_nonneg (state_nonneg _
      (cornerState_isState _ hτ _ (hp.peakAtom_projection i) (hpos i)) ha)
      (hp.peakAtom_projection i).nonneg
  · exact smul_nonneg (state_nonneg _ hp.2.2.1 ha) (hp.1 n).nonneg

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cornerFunctional_norm_apply_le (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (q : A) (hq : IsStarProjection q) (a : A) :
    ‖τ (q * a * q)‖ ≤ (τ q).re * ‖a‖ := by
  have hsq (b : A) :
      (cornerFunctional τ q (star b * b)).im = 0 ∧
        0 ≤ (cornerFunctional τ q (star b * b)).re := by
    have heq : q * (star b * b) * q = star (b*q) * (b*q) := by
      rw [star_mul, hq.isSelfAdjoint.star_eq]
      noncomm_ring
    simpa only [cornerFunctional_apply, heq] using hτ.2 (b*q)
  have h := positive_norm_apply_le (positiveOfSquares (cornerFunctional τ q) hsq) a
  simpa only [positiveOfSquares_apply, cornerFunctional_apply, mul_one,
    hq.isIdempotentElem.eq] using h

omit [PartialOrder A] [StarOrderedRing A] in

theorem trace_compression (τ : A →L[ℂ] ℂ) (htr : ∀ a b, τ (a*b) = τ (b*a))
    (q : A) (hq : IsStarProjection q) (a : A) : τ (q*a*q) = τ (q*a) := by
  rw [htr (q*a) q, ← mul_assoc, hq.isIdempotentElem.eq]

omit [PartialOrder A] [StarOrderedRing A] in

theorem trace_cornerState_smul (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (q : A) (hq : IsStarProjection q) (hpos : 0 < (τ q).re) (a : A) :
    τ (cornerState τ q a • q) = τ (q*a*q) := by
  rw [map_smul, cornerState_apply, Complex.real_smul, smul_eq_mul]
  rw [state_projection_real τ hτ q hq]
  have hne : ((τ q).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  simp only [Complex.ofReal_re, Complex.ofReal_inv]
  field_simp

theorem trace_peaking_partial {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b, τ (a*b) = τ (b*a))
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) (n : ℕ) :
    τ (f a • (1:A) + ∑ i ∈ Finset.range n,
      (cornerState τ (peakAtom p i) a - f a) • peakAtom p i) =
      τ a + f a * τ (p n) - τ (p n * a) := by
  rw [peakDiagonal_partial hp0, map_add, map_sum, map_smul]
  simp_rw [trace_cornerState_smul τ hτ _ (hp.peakAtom_projection _) (hpos _),
    trace_compression τ htr _ (hp.peakAtom_projection _)]
  rw [← map_sum, ← Finset.sum_mul, peakAtom_sum, hp0, sub_mul, one_mul, map_sub]
  simp only [smul_eq_mul]
  ring

theorem trace_peak_mul_tendsto_zero {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (htr : ∀ a b, τ (a*b) = τ (b*a))
    (hnull : Tendsto (fun n => τ (p n)) atTop (𝓝 0)) (a : A) :
    Tendsto (fun n => τ (p n * a)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => ‖τ (p n)‖ * ‖a‖) atTop (𝓝 0) from by
      simpa only [norm_zero, zero_mul] using hnull.norm.mul_const ‖a‖)
  rw [← trace_compression τ htr _ (hp.1 n)]
  exact (cornerFunctional_norm_apply_le τ hτ _ (hp.1 n) a).trans
    (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _))

theorem peakingExpectation_trace {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b, τ (a*b) = τ (b*a))
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (hnull : Tendsto (fun n => τ (p n)) atTop (𝓝 0)) (a : A) :
    τ (peakingExpectation hp hp0 τ hτ hpos a) = τ a := by
  have h₁ := τ.continuous.tendsto _ |>.comp
    (hp.tendsto_peakDiagonal (f a) (fun n => cornerState τ (peakAtom p n) a)
      (hp.tendsto_atomState τ hτ hpos a))
  have h₂ : Tendsto (fun n => τ a + f a * τ (p n) - τ (p n * a)) atTop (𝓝 (τ a)) := by
    simpa only [mul_zero, add_zero, sub_zero] using
      (tendsto_const_nhds.add (hnull.const_mul (f a))).sub
        (trace_peak_mul_tendsto_zero hp τ hτ htr hnull a)
  simp only [Function.comp_def] at h₁
  simp_rw [trace_peaking_partial hp hp0 τ hτ htr hpos a] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem peakingExpectation_faithful {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b, τ (a*b) = τ (b*a))
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (hnull : Tendsto (fun n => τ (p n)) atTop (𝓝 0))
    (hfaithful : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A)
    (ha : peakingExpectation hp hp0 τ hτ hpos (star a*a) = 0) : a = 0 := by
  apply hfaithful a
  rw [← peakingExpectation_trace hp hp0 τ hτ htr hpos hnull, ha, map_zero]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.mul_peak {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (m n : ℕ) :
    p m * p n = p (max m n) := by
  rcases le_total m n with h | h
  · rw [max_eq_right h]
    exact ((hp.1 n).le_iff_mul_eq_right (hp.1 m)).mp (hp.2.1 h)
  · rw [max_eq_left h]
    exact ((hp.1 m).le_iff_mul_eq_left (hp.1 n)).mp (hp.2.1 h)

def peakSpanAlgebra {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1) :
    StarSubalgebra ℂ A where
  carrier := Submodule.span ℂ (Set.range p)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨0, hp0⟩
  mul_mem' := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨m, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨n, rfl⟩ := hb
        rw [hp.mul_peak]
        exact Submodule.subset_span (Set.mem_range_self _)
      | zero => simp only [mul_zero]; exact Submodule.zero_mem _
      | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
      | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add a c _ _ ha hc => rw [add_mul]; exact Submodule.add_mem _ ha hc
    | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  star_mem' := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨n, rfl⟩ := ha
      rw [(hp.1 n).isSelfAdjoint.star_eq]
      exact Submodule.subset_span (Set.mem_range_self _)
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [star_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [star_smul]; exact Submodule.smul_mem _ (star c) ha

omit [PartialOrder A] [StarOrderedRing A] in

def peakAlgebra (p : ℕ → A) : StarSubalgebra ℂ A :=
  (StarAlgebra.adjoin ℂ (Set.range p)).topologicalClosure

omit [PartialOrder A] [StarOrderedRing A] in
theorem peak_mem_peakAlgebra (p : ℕ → A) (n : ℕ) : p n ∈ peakAlgebra p :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self n))

omit [PartialOrder A] [StarOrderedRing A] in
theorem peakAtom_mem_peakAlgebra (p : ℕ → A) (n : ℕ) : peakAtom p n ∈ peakAlgebra p :=
  (peakAlgebra p).sub_mem (peak_mem_peakAlgebra p n) (peak_mem_peakAlgebra p (n+1))

theorem peakAlgebra_eq_spanClosure {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) : peakAlgebra p = (peakSpanAlgebra hp hp0).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_mono
    apply StarAlgebra.adjoin_le
    intro a ha
    exact Submodule.subset_span ha
  · apply StarSubalgebra.topologicalClosure_minimal _ (StarSubalgebra.isClosed_topologicalClosure _)
    intro a ha
    have hs : Submodule.span ℂ (Set.range p) ≤ (peakAlgebra p).toSubmodule := by
      apply Submodule.span_le.mpr
      intro x hx
      exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hx)
    exact hs ha

theorem peakingExpectation_mem {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos a ∈ peakAlgebra p := by
  apply (StarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto
    (hp.tendsto_peakDiagonal (f a) (fun n => cornerState τ (peakAtom p n) a)
      (hp.tendsto_atomState τ hτ hpos a))
  apply Filter.Eventually.of_forall
  intro n
  apply (peakAlgebra p).add_mem
  · exact (peakAlgebra p).smul_mem (peakAlgebra p).one_mem _
  · exact (peakAlgebra p).sum_mem fun i _ =>
      (peakAlgebra p).smul_mem (peakAtom_mem_peakAlgebra p i) _

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in

theorem Peaks.apply_peakAtom {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    f (peakAtom p n) = 0 := by
  simp only [peakAtom, map_sub, hp.2.2.2.1, sub_self]

theorem cornerState_peakAtom_of_ne {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) {n m : ℕ} (hnm : n ≠ m) :
    cornerState τ (peakAtom p n) (peakAtom p m) = 0 := by
  simp only [cornerState_apply, hp.peakAtom_orthogonal hnm, zero_mul, map_zero, smul_zero]

theorem peakingExpectation_peakAtom {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) :
    peakingExpectation hp hp0 τ hτ hpos (peakAtom p m) = peakAtom p m := by
  change peakDiagonal p (f (peakAtom p m)) (fun n => cornerState τ (peakAtom p n) (peakAtom p m)) = _
  rw [peakDiagonal, hp.apply_peakAtom]
  simp only [zero_smul, zero_add, sub_zero]
  rw [tsum_eq_single m]
  · rw [cornerState_eq_one τ hτ _ _ (hp.peakAtom_projection m) (hp.peakAtom_projection m) le_rfl (hpos m), one_smul]
  · intro n hnm
    rw [cornerState_peakAtom_of_ne hp τ hnm, zero_smul]

theorem peakingExpectation_peak {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) :
    peakingExpectation hp hp0 τ hτ hpos (p m) = p m := by
  have hm : p m = 1 - ∑ i ∈ Finset.range m, peakAtom p i := by
    rw [peakAtom_sum, hp0]; abel
  calc
    peakingExpectation hp hp0 τ hτ hpos (p m) =
        1 - ∑ i ∈ Finset.range m, peakAtom p i := by
      conv_lhs => rw [hm]
      rw [map_sub, map_sum, peakingExpectation_one hp hp0 τ hτ hpos]
      simp_rw [peakingExpectation_peakAtom hp hp0 τ hτ hpos]
    _ = p m := hm.symm

theorem peakingExpectation_fixes {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) (ha : a ∈ peakAlgebra p) :
    peakingExpectation hp hp0 τ hτ hpos a = a := by
  rw [peakAlgebra_eq_spanClosure hp hp0] at ha
  have hc : IsClosed {a : A | peakingExpectation hp hp0 τ hτ hpos a = a} :=
    isClosed_eq (peakingExpectation hp hp0 τ hτ hpos).continuous continuous_id
  apply closure_minimal (t := {a : A | peakingExpectation hp hp0 τ hτ hpos a = a}) ?_ hc ha
  intro a ha
  change a ∈ Submodule.span ℂ (Set.range p) at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, rfl⟩ := ha
    exact peakingExpectation_peak hp hp0 τ hτ hpos n
  | zero => exact map_zero _
  | add a b _ _ ha hb =>
    change _ = _ at ha hb ⊢
    rw [map_add, ha, hb]
  | smul c a _ ha =>
    change _ = _ at ha ⊢
    rw [map_smul, ha]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem mul_idempotent_compression (f : A →L[ℂ] ℂ) (q : A) (hq : q*q=q)
    (hc : ∀ a, f (q*a*q)=f a) (a : A) : f (q*a)=f a := by
  calc
    f (q*a) = f (q*(q*a)*q) := (hc (q*a)).symm
    _ = f (q*a*q) := by rw [← mul_assoc q q, hq]
    _ = f a := hc a

theorem Peaks.apply_peakAtom_mul {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (n : ℕ) (a : A) : f (peakAtom p n * a) = 0 := by
  have hc := state_compression f hp.2.2.1 (p (n+1)) ((hp.1 _).norm_le _)
    (hp.1 _).isSelfAdjoint (hp.2.2.2.1 _) (peakAtom p n*a)
  have hmul : p (n+1)*peakAtom p n=0 := by
    have h := congrArg star (hp.peakAtom_mul_peak (Nat.lt_succ_self n))
    simpa [(hp.1 _).isSelfAdjoint.star_eq, (hp.peakAtom_projection n).isSelfAdjoint.star_eq] using h
  rw [← hc, ← mul_assoc (p (n+1)), hmul, zero_mul, zero_mul, map_zero]

theorem peakingExpectation_peakAtom_mul {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos (peakAtom p m*a) =
      cornerState τ (peakAtom p m) a • peakAtom p m := by
  change peakDiagonal p (f (peakAtom p m*a)) (fun n => cornerState τ (peakAtom p n) (peakAtom p m*a)) = _
  rw [peakDiagonal, hp.apply_peakAtom_mul]
  simp only [zero_smul, zero_add, sub_zero]
  rw [tsum_eq_single m]
  · congr 1
    simp only [cornerState_apply, ← mul_assoc, (hp.peakAtom_projection m).isIdempotentElem.eq]
  · intro n hnm
    simp only [cornerState_apply, ← mul_assoc, hp.peakAtom_orthogonal hnm, zero_mul, map_zero, smul_zero,
      zero_smul]

theorem peakAtom_mul_peakingExpectation {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) (a : A) :
    peakAtom p m * peakingExpectation hp hp0 τ hτ hpos a =
      cornerState τ (peakAtom p m) a • peakAtom p m := by
  change peakAtom p m * (f a • (1 : A) + ∑' n,
    (cornerState τ (peakAtom p n) a - f a) • peakAtom p n) = _
  rw [mul_add, mul_smul_comm, mul_one]
  have hsum := (hp.summable_expectationTail τ hτ hpos a).hasSum.map
    (ContinuousLinearMap.mul ℂ A (peakAtom p m)) (ContinuousLinearMap.mul ℂ A (peakAtom p m)).continuous
  have heq : peakAtom p m * ∑' n, (cornerState τ (peakAtom p n) a - f a) • peakAtom p n =
      (cornerState τ (peakAtom p m) a - f a) • peakAtom p m := by
    change HasSum (fun n => peakAtom p m * ((cornerState τ (peakAtom p n) a - f a) • peakAtom p n))
      (peakAtom p m * ∑' n, (cornerState τ (peakAtom p n) a - f a) • peakAtom p n) at hsum
    rw [← hsum.tsum_eq, tsum_eq_single m]
    · simp only [mul_smul_comm,
        (hp.peakAtom_projection m).isIdempotentElem.eq]
    · intro n hnm
      simp only [mul_smul_comm,
        hp.peakAtom_orthogonal hnm.symm, smul_zero]
  rw [heq, ← add_smul, add_sub_cancel]

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveFunctional_matrix_square_nonneg (f : A →ₚ[ℂ] ℂ) {n : Type*} [Fintype n]
    (N : CStarMatrix n n A) : 0 ≤ (star N * N).map f := by
  classical
  let Q : Matrix n n ℂ := fun i j => f ((star N * N) i j)
  have hQ : Q.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      change star (f ((star N * N) j i)) = f ((star N * N) i j)
      rw [← map_star]
      congr 1
      have hstar : star (star N * N) = star N * N := by simp
      exact congrFun (congrFun hstar i) j
    · intro x
      have h (k : n) : 0 ≤ f (star (∑ i, x i • N k i) * (∑ j, x j • N k j)) :=
        f.map_nonneg (star_mul_self_nonneg _)
      have heq : star x ⬝ᵥ (Q *ᵥ x) =
          ∑ k, f (star (∑ i, x i • N k i) * (∑ j, x j • N k j)) := by
        simp only [dotProduct, Matrix.mulVec, Q, CStarMatrix.mul_apply,
          CStarMatrix.star_apply, star_sum, Finset.sum_mul, Finset.mul_sum, map_sum,
          star_smul, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, Pi.star_apply]
        conv_rhs =>
          rw [Finset.sum_comm]
          arg 2
          ext i
          rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [heq]
      exact Finset.sum_nonneg fun k _ => h k
  exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hQ.nonneg

theorem positiveFunctional_matrix_nonneg (f : A →ₚ[ℂ] ℂ) {n : Type*} [Fintype n]
    (M : CStarMatrix n n A) (hM : 0 ≤ M) : 0 ≤ M.map f := by
  classical
  have h := StarOrderedRing.nonneg_iff.mp hM
  refine AddSubmonoid.closure_induction (motive := fun M _ => 0 ≤ M.map f) ?_ ?_ ?_ h
  · rintro M ⟨N, rfl⟩
    exact positiveFunctional_matrix_square_nonneg f N
  · simpa only [show (0 : CStarMatrix n n A).map f = 0 from by ext; simp] using
      (le_refl (0 : CStarMatrix n n ℂ))
  · intro M N _ _ hM hN
    have heq : (M + N).map f = M.map f + N.map f := by ext; simp
    rw [heq]
    exact add_nonneg hM hN

def positiveFunctionalCP (f : A →ₚ[ℂ] ℂ) : A →CP ℂ :=
  { f.toLinearMap with map_cstarMatrix_nonneg' := fun _ M hM =>
      positiveFunctional_matrix_nonneg f M hM }

open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

def projectionScalarHom (q : A) (hq : IsStarProjection q) : ℂ →⋆ₙₐ[ℂ] A where
  toFun z := z • q
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b q
  map_mul' a b := by
    simp only [smul_mul_assoc, mul_smul_comm, hq.isIdempotentElem.eq, smul_smul]
    exact congrArg (fun c : ℂ => c • q) (mul_comm a b)
  map_smul' a b := (smul_smul a b q).symm
  map_star' a := by simp only [star_smul, hq.isSelfAdjoint.star_eq]

def projectionFunctionalCP (f : A →ₚ[ℂ] ℂ) (q : A) (hq : IsStarProjection q) : A →CP A where
  toLinearMap := (projectionScalarHom q hq : ℂ →ₗ[ℂ] A).comp f.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have h := (projectionScalarHom q hq : ℂ →CP A).map_cstarMatrix_nonneg (M.map f)
      (positiveFunctional_matrix_nonneg f M hM)
    exact h

theorem peaking_partial_matrix_nonneg {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (N : ℕ) {n : Type*} [Fintype n] (M : CStarMatrix n n A) (hM : 0 ≤ M) :
    0 ≤ M.map (fun a => (∑ i ∈ Finset.range N, cornerState τ (peakAtom p i) a • peakAtom p i) + f a • p N) := by
  classical
  have hf := (projectionFunctionalCP (positiveOfSquares f hp.2.2.1.2) (p N) (hp.1 N)).map_cstarMatrix_nonneg M hM
  have hc (i : ℕ) := (projectionFunctionalCP
    (positiveOfSquares (cornerState τ (peakAtom p i))
      (cornerState_isState τ hτ _ (hp.peakAtom_projection i) (hpos i)).2)
    (peakAtom p i) (hp.peakAtom_projection i)).map_cstarMatrix_nonneg M hM
  convert add_nonneg (Finset.sum_nonneg (s := Finset.range N) (fun i _ => hc i)) hf using 1
  ext i j
  have hs (s : Finset ℕ) (g : ℕ → CStarMatrix n n A) :
      (∑ k ∈ s, g k) i j = ∑ k ∈ s, g k i j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih => simp only [Finset.sum_insert hk, CStarMatrix.add_apply, ih]
  simp only [CStarMatrix.add_apply, hs, CStarMatrix.map_apply]
  rfl

def peakingExpectationCP {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) : A →CP A where
  toLinearMap := (peakingExpectation hp hp0 τ hτ hpos).toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    let L (n : ℕ) := M.map (fun a => f a • (1 : A) +
      ∑ i ∈ Finset.range n, (cornerState τ (peakAtom p i) a - f a) • peakAtom p i)
    have hlim : Filter.Tendsto L Filter.atTop
        (𝓝 (M.map (peakingExpectation hp hp0 τ hτ hpos))) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      exact hp.tendsto_peakDiagonal (f (M i j))
        (fun n => cornerState τ (peakAtom p n) (M i j))
        (hp.tendsto_atomState τ hτ hpos (M i j))
    apply ge_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    simpa only [L, peakDiagonal_partial hp0] using peaking_partial_matrix_nonneg hp τ hτ hpos n M hM

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem peakingExpectation_peak_mul {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos (p m*a) =
      p m*peakingExpectation hp hp0 τ hτ hpos a := by
  have hm : p m = 1 - ∑ i ∈ Finset.range m, peakAtom p i := by
    rw [peakAtom_sum, hp0]; abel
  have hq (n : ℕ) : peakingExpectation hp hp0 τ hτ hpos (peakAtom p n*a) =
      peakAtom p n*peakingExpectation hp hp0 τ hτ hpos a := by
    rw [peakingExpectation_peakAtom_mul, peakAtom_mul_peakingExpectation]
  rw [hm, sub_mul, sub_mul, one_mul, one_mul, Finset.sum_mul, Finset.sum_mul, map_sub, map_sum]
  simp_rw [hq]

theorem peakingExpectation_leftBimodule {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (d a : A) (hd : d ∈ peakAlgebra p) :
    peakingExpectation hp hp0 τ hτ hpos (d*a) =
      d*peakingExpectation hp hp0 τ hτ hpos a := by
  rw [peakAlgebra_eq_spanClosure hp hp0] at hd
  have hc : IsClosed {d : A | peakingExpectation hp hp0 τ hτ hpos (d*a) =
      d*peakingExpectation hp hp0 τ hτ hpos a} := isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (t := {d : A | peakingExpectation hp hp0 τ hτ hpos (d*a) =
      d*peakingExpectation hp hp0 τ hτ hpos a}) ?_ hc hd
  intro d hd
  change d ∈ Submodule.span ℂ (Set.range p) at hd
  induction hd using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨n, rfl⟩ := hd
    exact peakingExpectation_peak_mul hp hp0 τ hτ hpos n a
  | zero => simp only [Set.mem_ofPred_eq, zero_mul, map_zero]
  | add d e _ _ hd he =>
    change _ = _ at hd he ⊢
    rw [add_mul, add_mul, map_add, hd, he]
  | smul c d _ hd =>
    change _ = _ at hd ⊢
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, hd]

theorem peakingExpectation_star {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos (star a) = star (peakingExpectation hp hp0 τ hτ hpos a) :=
  map_star (PositiveLinearMap.mk₀ (peakingExpectation hp hp0 τ hτ hpos).toLinearMap
    (fun _ hx => peakingExpectation_nonneg hp hp0 τ hτ hpos hx)) a

theorem peakingExpectation_rightBimodule {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a d : A) (hd : d ∈ peakAlgebra p) :
    peakingExpectation hp hp0 τ hτ hpos (a*d) =
      peakingExpectation hp hp0 τ hτ hpos a*d := by
  have h := peakingExpectation_leftBimodule hp hp0 τ hτ hpos (star d) (star a)
    (star_mem hd)
  have hs := congrArg star h
  simpa only [← star_mul, peakingExpectation_star, star_star] using hs

theorem peakingExpectation_idempotent {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos (peakingExpectation hp hp0 τ hτ hpos a) =
      peakingExpectation hp hp0 τ hτ hpos a :=
  peakingExpectation_fixes hp hp0 τ hτ hpos _ (peakingExpectation_mem hp hp0 τ hτ hpos a)

open Filter Topology
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem nontrivial_of_state (f : A →L[ℂ] ℂ) (hf : IsState f) : Nontrivial A := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have he := (isState_iff f).mp hf |>.1
  rw [← h, map_zero] at he
  exact zero_ne_one he

theorem state_corner_bound (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) (a : A) :
    ‖f (p * a * p)‖ ≤ (f p).re * ‖a‖ := by
  have hpos : ∀ x : A, ((cornerFunctional f p) (star x * x)).im = 0 ∧
      0 ≤ ((cornerFunctional f p) (star x * x)).re := by
    intro x
    have he : p * (star x * x) * p = star (x * p) * (x * p) := by
      rw [star_mul, hp.isSelfAdjoint.star_eq]
      noncomm_ring
    simpa only [cornerFunctional_apply, he] using hf.2 (x * p)
  have hh := positive_norm_apply_le (positiveOfSquares (cornerFunctional f p) hpos) a
  simpa only [positiveOfSquares_apply, cornerFunctional_apply, mul_one,
    hp.isIdempotentElem.eq] using hh

theorem exists_supported_norming_state (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) (hfp : f p = 1)
    (a : A) (ha : IsSelfAdjoint a) :
    ∃ g : A →L[ℂ] ℂ, IsState g ∧ g p = 1 ∧ ‖g a‖ = ‖p * a * p‖ := by
  have : Nontrivial A := nontrivial_of_state f hf
  let b := p * a * p
  have hb : IsSelfAdjoint b := by
    change star (p * a * p) = p * a * p
    rw [star_mul, star_mul, hp.isSelfAdjoint.star_eq, ha.star_eq, mul_assoc]
  by_cases hz : b = 0
  · refine ⟨f, hf, hfp, ?_⟩
    rw [← state_compression f hf p (hp.norm_le _) hp.isSelfAdjoint hfp a]
    change ‖f b‖ = ‖b‖
    simp only [hz, map_zero, norm_zero]
  · let : IsStarNormal b := hb.isStarNormal
    obtain ⟨g, hg, hgn⟩ := exists_norming_state b
    have hpb : p * b * p = b := by
      calc
        p * b * p = (p * p) * a * (p * p) := by dsimp [b]; noncomm_ring
        _ = b := by rw [hp.isIdempotentElem.eq]
    have hbound := state_corner_bound g hg p hp b
    rw [hpb, hgn] at hbound
    have hpos : 0 < ‖b‖ := norm_pos_iff.mpr hz
    have hle : (g p).re ≤ 1 := (Complex.re_le_norm _).trans
      ((state_norm_apply_le g hg p).trans (hp.norm_le _))
    have heqr : (g p).re = 1 := by nlinarith
    have hgp : g p = 1 := by
      rw [state_projection_real g hg p hp, heqr, Complex.ofReal_one]
    refine ⟨g, hg, hgp, ?_⟩
    rw [← state_compression g hg p (hp.norm_le _) hp.isSelfAdjoint hgp a]
    exact hgn

theorem Peaks.excision_selfAdjoint {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (a : A) (ha : IsSelfAdjoint a) :
    Tendsto (fun n => ‖p n * (a - f a • (1 : A)) * p n‖) atTop (𝓝 0) := by
  let b := a - f a • (1 : A)
  have hb : IsSelfAdjoint b := by
    change star (a - f a • (1 : A)) = a - f a • (1 : A)
    rw [star_sub, ha.star_eq, star_smul, star_one, ← state_map_star f hp.2.2.1 a,
      ha.star_eq]
  have hfb : f b = 0 := by
    simp only [b, map_sub, map_smul, (isState_iff f).mp hp.2.2.1 |>.1,
      smul_eq_mul, mul_one, sub_self]
  choose g hg hgp hgn using fun n => exists_supported_norming_state f hp.2.2.1
    (p n) (hp.1 n) (hp.2.2.2.1 n) b hb
  have ht := (hp.tendsto_supported_apply g hg hgp b).norm
  simpa only [hfb, norm_zero, hgn] using ht

theorem Peaks.excision {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (a : A) :
    Tendsto (fun n => ‖p n * (a - f a • (1 : A)) * p n‖) atTop (𝓝 0) := by
  let r : A := realPart a
  let s : A := imaginaryPart a
  have hr := hp.excision_selfAdjoint r (realPart a).property
  have hs := hp.excision_selfAdjoint s (imaginaryPart a).property
  have ha : a = r + Complex.I • s := (realPart_add_I_smul_imaginaryPart a).symm
  have hdecomp (n : ℕ) : p n * (a - f a • (1 : A)) * p n =
      p n * (r - f r • (1 : A)) * p n +
      Complex.I • (p n * (s - f s • (1 : A)) * p n) := by
    conv_lhs => rw [ha]
    simp only [map_add, map_smul, add_smul, smul_smul, mul_add, add_mul,
      mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub, mul_one]
    module
  have hbound (n : ℕ) : ‖p n * (a - f a • (1 : A)) * p n‖ ≤
      ‖p n * (r - f r • (1 : A)) * p n‖ +
      ‖p n * (s - f s • (1 : A)) * p n‖ := by
    rw [hdecomp n]
    simpa only [norm_smul, Complex.norm_I, one_mul] using norm_add_le
      (p n * (r - f r • (1 : A)) * p n)
      (Complex.I • (p n * (s - f s • (1 : A)) * p n))
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using hr.add hs)

end NaimarkZFC

end

end OAI
