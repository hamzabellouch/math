import OAI.Analysis.NuclearUltrapower.FullGroupAlgebra

namespace OAI

section

noncomputable section
universe u
open scoped ComplexOrder ENNReal
namespace NuclearUltrapower
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
local instance gnsSpectralOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance gnsSpectralOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The disk estimate which exposes a positive element to Hahn--Banach. -/
theorem norm_positive_center (a : A) (ha : 0 ≤ a) :
    ‖a - (‖a‖ / 2 : ℝ) • (1 : A)‖ ≤ ‖a‖ / 2 := by
  have hsa := IsSelfAdjoint.of_nonneg ha
  have he : cfc (fun x : ℝ => x - ‖a‖ / 2) a = a - (‖a‖ / 2 : ℝ) • (1 : A) := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ => ‖a‖ / 2) a,
      cfc_id' ℝ a hsa, cfc_const _ a hsa]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← he]
  apply norm_cfc_le (by positivity)
  intro x hx
  have hx0 : 0 ≤ x := (spectrum_nonneg_of_nonneg ha) hx
  have hxN : x ≤ ‖a‖ := (Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Elementary disk intersection, used to retain the unit under norm-preserving extension. -/
theorem complex_disk_intersection (z : ℂ) (h0 : ‖z‖ ≤ 1) (h2 : ‖2-z‖ ≤ 1) : z = 1 := by
  have hr := Complex.abs_re_le_norm z
  have hr2 := Complex.abs_re_le_norm (2-z)
  have hzre : z.re = 1 := by
    have := (le_abs_self z.re).trans (hr.trans h0)
    have := (le_abs_self (2-z).re).trans (hr2.trans h2)
    norm_num [Complex.sub_re] at *
    linarith
  have hz : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    nlinarith [Complex.sq_norm z, Complex.normSq_apply z, norm_nonneg z]
  apply Complex.ext
  · simpa using hzre
  · simp only [Complex.one_im]
    nlinarith [sq_nonneg z.im]

/-- Hahn--Banach norms a positive element by a unital contraction. -/
theorem exists_unital_norming_functional (a : A) (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ f : A →L[ℂ] ℂ, ‖f‖ = 1 ∧ f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  obtain ⟨f, hf, hfa⟩ := exists_dual_vector ℂ a (norm_ne_zero_iff.mpr ha0)
  refine ⟨f, hf, ?_, hfa⟩
  apply complex_disk_intersection
  · simpa [hf] using f.le_opNorm (1 : A)
  · have h := (f.le_opNorm (a - (‖a‖ / 2 : ℝ) • (1 : A))).trans
        (by simpa [hf] using norm_positive_center a ha)
    have hn : 0 < ‖a‖ / 2 := by positivity
    have he : f (a - (‖a‖ / 2 : ℝ) • (1 : A)) = (‖a‖ / 2 : ℂ) * (2-f 1) := by
      rw [map_sub, ContinuousLinearMap.map_smul_of_tower, hfa]
      simp only [Complex.real_smul]
      push_cast
      ring_nf
      simp
    rw [he, norm_mul] at h
    have he' : ‖(‖a‖ / 2 : ℂ)‖ = ‖a‖ / 2 := by
      rw [norm_div, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [he'] at h
    nlinarith

/-- A contractive unital functional is real on self-adjoint elements. -/
theorem contractive_unital_real (f : A →L[ℂ] ℂ) (hf : ‖f‖ ≤ 1) (h1 : f 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) : (f a).im = 0 := by
  have hbound (t : ℝ) : ‖(1 : A) + ((t : ℂ)*Complex.I) • a‖ ^ 2 ≤ 1 + t^2 * ‖a‖^2 := by
    have he : star ((1 : A) + ((t : ℂ)*Complex.I) • a) *
        ((1 : A) + ((t : ℂ)*Complex.I) • a) = 1 + (t^2 : ℝ) • (a*a) := by
      have hc : star (((t : ℂ)*Complex.I) • a) = -(((t : ℂ)*Complex.I) • a) := by
        simp [ha.star_eq, mul_comm]
      rw [star_add, star_one, hc]
      have hprod : (((t : ℂ)*Complex.I) • a) * (((t : ℂ)*Complex.I) • a) =
          -(t^2 : ℝ) • (a*a) := by
        rw [smul_mul_smul]
        have hcoeff : ((t : ℂ)*Complex.I)*((t : ℂ)*Complex.I) = -(t^2 : ℝ) := by
          push_cast
          calc ((t : ℂ)*Complex.I)*((t : ℂ)*Complex.I) = (t:ℂ)^2*Complex.I^2 := by ring
               _ = -(t:ℂ)^2 := by rw [Complex.I_sq]; ring
        rw [hcoeff]
        rw [← Complex.ofReal_neg]
        exact Complex.coe_smul _ _
      calc (1 + -(((t:ℂ)*Complex.I) • a)) * (1 + ((t:ℂ)*Complex.I) • a) =
          1 - (((t:ℂ)*Complex.I) • a) * (((t:ℂ)*Complex.I) • a) := by
            generalize ((t:ℂ)*Complex.I) • a = x
            noncomm_ring
           _ = 1 + (t^2 : ℝ) • (a*a) := by rw [hprod]; simp
    rw [sq, ← CStarRing.norm_star_mul_self, he]
    calc ‖(1 : A) + (t^2 : ℝ) • (a*a)‖ ≤ ‖(1 : A)‖ + ‖(t^2 : ℝ) • (a*a)‖ := norm_add_le _ _
         _ ≤ 1 + t^2 * ‖a‖^2 := by
           rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t), ha.norm_mul_self]
           simp
  have hscalar (t : ℝ) : -2*t*(f a).im ≤ t^2*‖a‖^2 := by
    have hc : ‖f ((1 : A) + ((t:ℂ)*Complex.I) • a)‖ ≤ ‖(1 : A) + ((t:ℂ)*Complex.I) • a‖ :=
      (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hf)
    rw [map_add, map_smul, h1] at hc
    simp only [smul_eq_mul] at hc
    have hs := hbound t
    have hc2 : ‖1 + ((t:ℂ)*Complex.I) * f a‖^2 ≤ 1 + t^2*‖a‖^2 := by
      exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hc).trans hs
    rw [Complex.sq_norm, Complex.normSq_apply] at hc2
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_zero, zero_sub, mul_one, zero_add, add_zero,
      Complex.add_im, Complex.one_im] at hc2
    nlinarith [sq_nonneg (t * (f a).re), sq_nonneg (t * (f a).im)]
  have h := hscalar (-(f a).im / (‖a‖^2+1))
  have hp : 0 < ‖a‖^2+1 := by positivity
  have h' := (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).mpr h
  field_simp at h'
  nlinarith [sq_nonneg (f a).im, sq_nonneg (‖a‖ * (f a).im)]

/-- The norm-one / unit-preserving criterion for positivity. -/
theorem contractive_unital_positive (f : A →L[ℂ] ℂ) (hf : ‖f‖ ≤ 1) (h1 : f 1 = 1)
    (a : A) (ha : 0 ≤ a) : 0 ≤ f a := by
  apply RCLike.nonneg_iff.mpr
  constructor
  · have h := (f.le_opNorm (a - (‖a‖ / 2 : ℝ) • (1:A))).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hf).trans (norm_positive_center a ha))
    rw [map_sub, ContinuousLinearMap.map_smul_of_tower, h1] at h
    have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans h)).1
    simp only [Complex.sub_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at hr
    change 0 ≤ (f a).re
    linarith
  · exact contractive_unital_real f hf h1 a (IsSelfAdjoint.of_nonneg ha)

/-- Sufficiently many states, proved rather than assumed. -/
theorem exists_norming_state (a : A) (ha : 0 ≤ a) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  have hex : ∃ f : A →L[ℂ] ℂ, ‖f‖ = 1 ∧ f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
    by_cases ha0 : a = 0
    · obtain ⟨f, hf, h1⟩ := exists_dual_vector ℂ (1:A) (by simp)
      refine ⟨f, hf, ?_, ?_⟩
      · simpa using h1
      · simp [ha0]
    · exact exists_unital_norming_functional a ha ha0
  obtain ⟨f, hf, h1, hfa⟩ := hex
  let p : A →ₚ[ℂ] ℂ := { f.toLinearMap with
    monotone' := by
      intro x y hxy
      change f x ≤ f y
      have : 0 ≤ f (y-x) := contractive_unital_positive f hf.le h1 (y-x) (sub_nonneg.mpr hxy)
      simpa only [map_sub, sub_nonneg] using this }
  exact ⟨p, h1, hfa⟩

omit [Nontrivial A] in
/-- The GNS cyclic vector for a state has norm one. -/
theorem gns_unit_norm (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    ‖(f.toPreGNS 1 : f.GNS)‖ = 1 := by
  rw [UniformSpace.Completion.norm_coe, f.preGNS_norm_def]
  simp [h1]

/-- Every C*-algebra element attains its norm in one of its GNS representations.
This supplies norm-separation with no external faithful-representation axiom. -/
theorem exists_norming_gns (a : A) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ ‖f.gnsStarAlgHom a‖ = ‖a‖ := by
  obtain ⟨f, h1, hf⟩ := exists_norming_state (star a * a) (star_mul_self_nonneg a)
  refine ⟨f, h1, le_antisymm (NonUnitalStarAlgHom.norm_apply_le _ _) ?_⟩
  let ξ : f.GNS := f.toPreGNS 1
  have hξ : ‖ξ‖ = 1 := gns_unit_norm f h1
  have hact : f.gnsStarAlgHom a ξ = (f.toPreGNS a : f.GNS) := by
    change f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1) = _
    rw [f.gnsNonUnitalStarAlgHom_apply_coe]
    simp [PositiveLinearMap.leftMulMapPreGNS]
  have hn : ‖f.gnsStarAlgHom a ξ‖ = ‖a‖ := by
    rw [hact, UniformSpace.Completion.norm_coe, f.preGNS_norm_def]
    simp only [PositiveLinearMap.ofPreGNS_toPreGNS, hf, Complex.ofReal_re,
      CStarRing.norm_star_mul_self]
    rw [Real.sqrt_mul_self (norm_nonneg _)]
  have h := (f.gnsStarAlgHom a).le_opNorm ξ
  rwa [hξ, mul_one, hn] at h

/-- Testing on all Hilbert space representations detects the original norm. -/
theorem norm_le_of_all_hilbert_representations (a : A) (M : ℝ)
    (h : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)), ‖ρ a‖ ≤ M) : ‖a‖ ≤ M := by
  obtain ⟨f, _, hf⟩ := exists_norming_gns a
  rw [← hf]
  exact h f.GNS f.gnsStarAlgHom

section DirectSum
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

/-- A uniformly bounded diagonal family acts on the Hilbert direct sum. -/
def hilbertDiagonal (T : ∀ i, E i →L[ℂ] E i) (M : ℝ) (hM : 0 ≤ M)
    (hT : ∀ i, ‖T i‖ ≤ M) : lp E 2 →L[ℂ] lp E 2 := by
  have hb (x : lp E 2) (i : ι) : ‖T i (x i)‖ ≤ ‖((M:ℂ) • x) i‖ := by
    change ‖T i (x i)‖ ≤ ‖(M:ℂ) • x i‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    exact ((T i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
  let L : lp E 2 →ₗ[ℂ] lp E 2 := {
    toFun x := ⟨fun i => T i (x i), (lp.memℓp ((M:ℂ) • x)).norm.mono (hb x)⟩
    map_add' x y := by ext i; exact map_add (T i) _ _
    map_smul' c x := by ext i; exact map_smul (T i) _ _ }
  refine L.mkContinuous M fun x => ?_
  have h := lp.norm_mono (x := L x) (y := (M:ℂ) • x) (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hb x)
  simpa only [L, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM] using h

@[simp] theorem hilbertDiagonal_apply (T : ∀ i, E i →L[ℂ] E i) (M : ℝ) (hM : 0 ≤ M)
    (hT : ∀ i, ‖T i‖ ≤ M) (x : lp E 2) (i : ι) :
    hilbertDiagonal T M hM hT x i = T i (x i) := rfl
end DirectSum

/-- Universal GNS Hilbert space, with all positive functionals as coordinates. -/
abbrev UniversalGNS (A : Type u) [CStarAlgebra A] :=
  lp (fun f : A →ₚ[ℂ] ℂ => f.GNS) 2

/-- The faithful unital Hilbert representation obtained by summing the GNS
representations of all positive functionals. -/
def universalGNS : A →⋆ₐ[ℂ] (UniversalGNS A →L[ℂ] UniversalGNS A) where
  toFun a := hilbertDiagonal (fun f : A →ₚ[ℂ] ℂ => f.gnsStarAlgHom a) ‖a‖
    (norm_nonneg a) (fun f => NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a)
  map_zero' := by ext x f; simp
  map_one' := by ext x f; simp
  map_add' a b := by ext x f; simp
  map_mul' a b := by ext x f; simp
  commutes' c := by
    ext x f
    change f.gnsStarAlgHom (algebraMap ℂ A c) (x f) = c • x f
    exact congrArg (fun T : f.GNS →L[ℂ] f.GNS => T (x f)) (f.gnsStarAlgHom.commutes c)
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [lp.inner_eq_tsum, hilbertDiagonal_apply]
    apply tsum_congr
    intro f
    calc
      _ = inner ℂ ((star (f.gnsStarAlgHom a)) (x f)) (y f) :=
        congrArg (fun T : f.GNS →L[ℂ] f.GNS => inner ℂ (T (x f)) (y f)) (map_star f.gnsStarAlgHom a)
      _ = _ := ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] theorem universalGNS_apply (a : A) (x : UniversalGNS A) (f : A →ₚ[ℂ] ℂ) :
    universalGNS a x f = f.gnsStarAlgHom a (x f) := rfl

theorem universalGNS_injective : Function.Injective (universalGNS (A := A)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨f, h1, hf⟩ := exists_norming_gns a
  have hz : f.gnsStarAlgHom a = 0 := by
    ext ξ
    have he := congrArg (fun T : UniversalGNS A →L[ℂ] UniversalGNS A =>
      T (lp.single 2 f ξ) f) ha
    simpa only [universalGNS_apply, lp.single_apply, Pi.single_eq_same, dite_true,
      zero_apply, lp.coeFn_zero, Pi.zero_apply] using he
  rw [hz, norm_zero] at hf
  exact norm_eq_zero.mp hf.symm

/-- The representation loses neither norm nor spectrum. -/
theorem universalGNS_isometry : Isometry (universalGNS (A := A)) :=
  NonUnitalStarAlgHom.isometry (universalGNS (A := A)) (universalGNS_injective (A := A))

end NuclearUltrapower
end
end

end OAI
