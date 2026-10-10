import OAI.Geometry.Arnold.ThreePoints

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample
namespace ThreePoints

open scoped Matrix

open scoped Manifold RealInnerProductSpace

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 := Metric.sphere (0 : E3) 1

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

def coords : E3 ≃L[ℝ] R3 := EuclideanSpace.equiv (Fin 3) ℝ

def sphereEmbed (x : S2) : R3 := coords (x : E3)

def spherePairEmbed : S2 × S2 → Pair := Prod.map sphereEmbed sphereEmbed

def sphereF : S2 × S2 → ℝ := f ∘ spherePairEmbed

lemma inner_coords (x y : E3) : inner ℝ x y = coords x ⬝ᵥ coords y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [coords, EuclideanSpace.equiv, star_trivial]
  exact dotProduct_comm _ _

lemma norm_sq_coords (x : E3) : ‖x‖ ^ 2 = sqNorm (coords x) := by
  rw [← real_inner_self_eq_norm_sq, inner_coords, dot_self]

lemma sphereEmbed_mem (x : S2) : sqNorm (sphereEmbed x) = 1 := by
  rw [sphereEmbed, ← norm_sq_coords]
  have h : ‖(x : E3)‖ = 1 := norm_eq_of_mem_sphere x
  rw [h]; norm_num

lemma spherePairEmbed_mem (q : S2 × S2) : spherePairEmbed q ∈ sphereProduct :=
  ⟨sphereEmbed_mem q.1, sphereEmbed_mem q.2⟩

lemma sphereEmbed_injective : Function.Injective sphereEmbed := by
  intro x y h
  exact Subtype.ext (coords.injective h)

lemma spherePairEmbed_injective : Function.Injective spherePairEmbed :=
  Function.Injective.prodMap sphereEmbed_injective sphereEmbed_injective

lemma exists_sphereEmbed {v : R3} (hv : sqNorm v = 1) :
    ∃ x : S2, sphereEmbed x = v := by
  have hn : ‖coords.symm v‖ = 1 := by
    have hs : ‖coords.symm v‖ ^ 2 = 1 := by
      rw [norm_sq_coords, coords.apply_symm_apply, hv]
    nlinarith [norm_nonneg (coords.symm v)]
  refine ⟨⟨coords.symm v, ?_⟩, coords.apply_symm_apply v⟩
  simpa using hn

lemma range_spherePairEmbed : Set.range spherePairEmbed = sphereProduct := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact spherePairEmbed_mem x
  · rintro ⟨hx, hy⟩
    obtain ⟨x, hx⟩ := exists_sphereEmbed hx
    obtain ⟨y, hy⟩ := exists_sphereEmbed hy
    exact ⟨(x, y), Prod.ext hx hy⟩

lemma sphereEmbed_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, R3) ∞ sphereEmbed :=
  coords.contDiff.contMDiff.comp contMDiff_coe_sphere

lemma spherePairEmbed_smooth :
    ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, Pair) ∞ spherePairEmbed := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact sphereEmbed_smooth.prodMap sphereEmbed_smooth

theorem sphereF_smooth : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ sphereF :=
  f_contDiff.contMDiff.comp spherePairEmbed_smooth

def sphereEmbedDeriv (x : S2) : TangentSpace (𝓡 2) x →L[ℝ] R3 :=
  coords.toContinuousLinearMap.comp
    (mvfderiv (𝓡 2) (Subtype.val : S2 → E3) x)

lemma sphereEmbed_mfderiv (x : S2) :
    mfderiv (𝓡 2) 𝓘(ℝ, R3) sphereEmbed x = sphereEmbedDeriv x := by
  change mfderiv (𝓡 2) 𝓘(ℝ, R3)
    ((coords : E3 → R3) ∘ (Subtype.val : S2 → E3)) x = _
  rw [mfderiv_comp x (coords.contDiff.contMDiff.mdifferentiable (n := ∞) (by norm_num)).mdifferentiableAt
    (((contMDiff_coe_sphere (m := ∞) (n := 2)).mdifferentiable (by norm_num))).mdifferentiableAt,
    mfderiv_eq_fderiv, coords.fderiv]
  rfl

lemma sphereEmbedDeriv_range (x : S2) (v : R3) :
    v ∈ (sphereEmbedDeriv x).range ↔ sphereEmbed x ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    have hw : mvfderiv (𝓡 2) (Subtype.val : S2 → E3) x w ∈ (ℝ ∙ (x : E3))ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := 2) x]
      exact ⟨w, rfl⟩
    have := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
    change coords (x : E3) ⬝ᵥ coords (mvfderiv (𝓡 2) (Subtype.val : S2 → E3) x w) = 0
    rwa [← inner_coords]
  · intro hv
    have hw : coords.symm v ∈ (ℝ ∙ (x : E3))ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_coords,
        coords.apply_symm_apply]
      exact hv
    rw [← range_mvfderiv_subtypeVal (n := 2) x] at hw
    obtain ⟨w, hw⟩ := hw
    refine ⟨w, ?_⟩
    change coords (mvfderiv (𝓡 2) (Subtype.val : S2 → E3) x w) = v
    exact (congrArg coords hw).trans (coords.apply_symm_apply v)

lemma spherePairEmbed_mfderiv (q : S2 × S2) :
    mfderiv ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, Pair) spherePairEmbed q =
      (sphereEmbedDeriv q.1).prodMap (sphereEmbedDeriv q.2) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  change mfderiv ((𝓡 2).prod (𝓡 2)) (𝓘(ℝ, R3).prod 𝓘(ℝ, R3))
    (Prod.map sphereEmbed sphereEmbed) q = _
  rw [mfderiv_prodMap
    (sphereEmbed_smooth.mdifferentiable (by norm_num)).mdifferentiableAt
    (sphereEmbed_smooth.mdifferentiable (by norm_num)).mdifferentiableAt,
    sphereEmbed_mfderiv, sphereEmbed_mfderiv]
  rfl

lemma sphereF_mfderiv (q : S2 × S2) :
    mfderiv ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) sphereF q =
      (df (spherePairEmbed q)).comp
        ((sphereEmbedDeriv q.1).prodMap (sphereEmbedDeriv q.2)) := by
  unfold sphereF
  rw [mfderiv_comp q
    (f_contDiff.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    (spherePairEmbed_smooth.mdifferentiable (by norm_num)).mdifferentiableAt,
    mfderiv_eq_fderiv, (f_hasFDerivAt _).fderiv]
  rw [spherePairEmbed_mfderiv]
  rfl

lemma sphereF_critical_iff (q : S2 × S2) :
    mfderiv ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) sphereF q = 0 ↔
      TangentCritical (spherePairEmbed q) := by
  rw [sphereF_mfderiv]
  constructor
  · intro h
    refine ⟨spherePairEmbed_mem q, ?_⟩
    intro u v hu hv
    obtain ⟨a, ha⟩ := (sphereEmbedDeriv_range q.1 u).mpr hu
    obtain ⟨b, hb⟩ := (sphereEmbedDeriv_range q.2 v).mpr hv
    have hh := DFunLike.congr_fun h (a, b)
    change df (spherePairEmbed q) (sphereEmbedDeriv q.1 a, sphereEmbedDeriv q.2 b) = 0 at hh
    change sphereEmbedDeriv q.1 a = u at ha
    change sphereEmbedDeriv q.2 b = v at hb
    rw [ha, hb] at hh
    simpa only [(f_hasFDerivAt _).fderiv] using hh
  · rintro ⟨_, h⟩
    apply ContinuousLinearMap.ext
    intro w
    change df (spherePairEmbed q) (sphereEmbedDeriv q.1 w.1, sphereEmbedDeriv q.2 w.2) = 0
    rw [← (f_hasFDerivAt _).fderiv]
    exact h _ _ ((sphereEmbedDeriv_range q.1 _).mp ⟨w.1, rfl⟩)
      ((sphereEmbedDeriv_range q.2 _).mp ⟨w.2, rfl⟩)

/-- The critical count on the smooth sphere-product manifold. -/
theorem sphereF_critical_encard :
    {q : S2 × S2 | mfderiv ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) sphereF q = 0}.encard = 3 := by
  have he : {q : S2 × S2 | mfderiv ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) sphereF q = 0} =
      spherePairEmbed ⁻¹' {q : Pair | TangentCritical q} := by
    ext q
    exact sphereF_critical_iff q
  rw [he, Set.encard_preimage_of_injective_subset_range spherePairEmbed_injective]
  · exact tangentCritical_encard
  · rw [range_spherePairEmbed]
    exact fun _ h ↦ h.1

end ThreePoints
end ArnoldCounterexample

end

end OAI
