import OAI.Analysis.LiebThirring.BoundaryParity

namespace OAI

universe u143 u144 u145 u146 u147

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

/-- A continuous cutoff equal to one on the inner half ball. -/
def radialCut (R t : ℝ) : ℝ := max 0 (min 1 (2 - 2*t/R))

lemma radialCut_nonneg (R t : ℝ) : 0 ≤ radialCut R t := le_max_left _ _
lemma radialCut_le_one (R t : ℝ) : radialCut R t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
lemma radialCut_eq_zero (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : R ≤ t) : radialCut R t = 0 := by
  classical
  apply max_eq_left
  apply (min_le_right _ _).trans
  have hd : 2 ≤ 2*t/R := (le_div_iff₀ hR).mpr (by linarith)
  linarith
lemma radialCut_eq_one (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ≤ R/2) : radialCut R t = 1 := by
  classical
  have hd : 2*t/R ≤ 1 := (div_le_iff₀ hR).mpr (by linarith)
  simp only [radialCut, min_eq_left (by linarith : 1 ≤ 2 - 2*t/R), max_eq_right zero_le_one]
lemma continuous_radialCut (R : ℝ) : Continuous (radialCut R) := by
  classical
  unfold radialCut
  fun_prop

section Flatten
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u143} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin d → ℝ) (R : ℝ) (f : (Fin (d + 1) → ℝ) → V)

def localAffine (s : H) (x : Fin (d + 1) → ℝ) : V :=
  ρ s (L (spatial (s⁻¹ • x) - p))

def flattenTerm (s : H) (x : Fin (d + 1) → ℝ) : V :=
  radialCut R (dist x (s • embedSpatial p)) • (localAffine H ρ L p s x - f x)

def flattenInitial (x : Fin (d + 1) → ℝ) : V := by
  classical
  exact f x + ∑ s : H, flattenTerm H ρ L p R f s x

lemma localAffine_smul (s g : H) (x : Fin (d + 1) → ℝ) :
    localAffine H ρ L p (g*s) (g • x) = ρ g (localAffine H ρ L p s x) := by
  classical
  simp only [localAffine,mul_inv_rev,mul_smul,inv_smul_smul,map_mul,LinearEquiv.mul_apply]

lemma continuous_localAffine [FiniteDimensional ℝ V] (s : H) : Continuous (localAffine H ρ L p s) := by
  classical
  unfold localAffine
  exact (ρ s).toContinuousLinearEquiv.continuous.comp
    (L.toContinuousLinearEquiv.continuous.comp
      ((spatial.continuous_of_finiteDimensional.comp (continuous_const_smul s⁻¹)).sub continuous_const))

lemma continuous_flattenInitial [FiniteDimensional ℝ V] (hf : Continuous f) : Continuous (flattenInitial H ρ L p R f) := by
  classical
  apply hf.add
  apply continuous_finsetSum
  intro s _
  exact ((continuous_radialCut R).comp (continuous_id.dist continuous_const)).smul
    ((continuous_localAffine H ρ L p s).sub hf)

lemma flattenInitial_equivariant (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (g : H) (x : Fin (d + 1) → ℝ) :
    flattenInitial H ρ L p R f (g • x) = ρ g (flattenInitial H ρ L p R f x) := by
  classical
  have ht (s : H) : flattenTerm H ρ L p R f (g*s) (g • x) =
      ρ g (flattenTerm H ρ L p R f s x) := by
    simp only [flattenTerm,mul_smul,dist_smul,localAffine_smul,hfe,map_smul,map_sub]
  have he := Fintype.sum_equiv (Equiv.mulLeft g)
    (fun s : H ↦ ρ g (flattenTerm H ρ L p R f s x))
    (fun s : H ↦ flattenTerm H ρ L p R f s (g • x)) (fun s ↦ (ht s).symm)
  simp only [flattenInitial,hfe,map_add,map_sum]
  exact congrArg (ρ g (f x) + ·) he.symm

lemma flattenInitial_eq_self {x : Fin (d + 1) → ℝ} (hR : 0 < R)
    (hx : x ∉ orbitBall (G := H) (embedSpatial p) R) :
    flattenInitial H ρ L p R f x = f x := by
  classical
  have ht : ∀ s : H, R ≤ dist x (s • embedSpatial p) :=
    fun s ↦ le_of_not_gt (fun hs ↦ hx ⟨s,hs⟩)
  unfold flattenInitial
  have hz : ∀ s : H, flattenTerm H ρ L p R f s x = 0 := by
    intro s
    unfold flattenTerm
    rw [radialCut_eq_zero R hR (ht s),zero_smul]
  simp only [hz,Finset.sum_const_zero,add_zero]

lemma flattenInitial_in_ball (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    {x : Fin (d + 1) → ℝ} (hx : x ∈ orbitBall (G := H) (embedSpatial p) R) :
    flattenInitial H ρ L p R f x = f x +
      radialCut R (dist x (ballLabel (G := H) (embedSpatial p) R x • embedSpatial p)) •
        (affineOrbitModel H ρ L (embedSpatial p) R p x - f x) := by
  classical
  let s := ballLabel (G := H) (embedSpatial p) R x
  have hs := ballLabel_dist (embedSpatial p) R hx
  have ht (k : H) (hk : k ≠ s) : flattenTerm H ρ L p R f k x = 0 := by
    have hd := hsep s k hk.symm
    have he := dist_triangle (s • embedSpatial p) x (k • embedSpatial p)
    rw [dist_comm (s • embedSpatial p) x] at he
    have hdk : R ≤ dist x (k • embedSpatial p) := by
      change dist x (s • embedSpatial p) < R at hs
      linarith
    simp only [flattenTerm,radialCut_eq_zero R hR hdk,zero_smul]
  have hsum : ∑ k : H, flattenTerm H ρ L p R f k x = flattenTerm H ρ L p R f s x := by
    apply Finset.sum_eq_single s
    · intro k _ hk
      exact ht k hk
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  rw [flattenInitial,hsum]
  rfl

lemma flattenInitial_inner (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    {x : Fin (d + 1) → ℝ} (hx : x ∈ orbitBall (G := H) (embedSpatial p) (R/2)) :
    flattenInitial H ρ L p R f x = affineOrbitModel H ρ L (embedSpatial p) (R/2) p x := by
  classical
  obtain ⟨s,hs⟩ := hx
  have hsR : dist x (s • embedSpatial p) < R := by linarith
  have hlR := ballLabel_eq (embedSpatial p) R hR hsep hsR
  have hsep' : ∀ g k : H, g ≠ k → 8 * (R/2) < dist (g • embedSpatial p) (k • embedSpatial p) := by
    intro g k hgk
    linarith [hsep g k hgk]
  have hlhalf := ballLabel_eq (embedSpatial p) (R/2) (by positivity) hsep' hs
  rw [flattenInitial_in_ball H ρ L p R f hR hsep ⟨s,hsR⟩,hlR,
    radialCut_eq_one R hR hs.le,one_smul]
  simp only [affineOrbitModel,hlR,hlhalf]
  abel

lemma affineOrbitModel_zero_bottom
    {x : Fin (d + 1) → ℝ} (ht : x (Fin.last d) = 0)
    (hz : affineOrbitModel H ρ L (embedSpatial p) R p x = 0) :
    ∃ s : H, s • embedSpatial p = x := by
  classical
  let s := ballLabel (G := H) (embedSpatial p) R x
  have hu : spatial (s⁻¹ • x) - p = 0 := by
    apply L.injective
    apply (ρ s).injective
    simpa only [affineOrbitModel,map_zero,s] using hz
  have he := embed_spatial_of_time_zero (s⁻¹ • x) ((s⁻¹).val.smul_time_zero x ht)
  rw [sub_eq_zero.mp hu] at he
  refine ⟨s,?_⟩
  rw [he,smul_inv_smul]

lemma flattenInitial_zero_bottom (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (herr : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      ‖f x - affineOrbitModel H ρ L (embedSpatial p) R p x‖ ≤
        ‖affineOrbitModel H ρ L (embedSpatial p) R p x‖ / 2)
    {x : Fin (d + 1) → ℝ} (ht : x (Fin.last d) = 0)
    (hz : flattenInitial H ρ L p R f x = 0) : ∃ s : H, s • embedSpatial p = x := by
  classical
  by_cases hx : x ∈ orbitBall (G := H) (embedSpatial p) R
  · let m := affineOrbitModel H ρ L (embedSpatial p) R p x
    let a := radialCut R (dist x (ballLabel (G := H) (embedSpatial p) R x • embedSpatial p))
    have hz' : f x + a • (m - f x) = 0 := by
      rw [flattenInitial_in_ball H ρ L p R f hR hsep hx] at hz
      exact hz
    have ha : 0 ≤ a := radialCut_nonneg _ _
    have ha1 : a ≤ 1 := radialCut_le_one _ _
    have he : f x + a • (m - f x) = m + (1-a) • (f x-m) := by
      rw [sub_smul,one_smul,smul_sub,smul_sub]
      abel
    rw [he] at hz'
    have hn : ‖m‖ ≤ ‖f x-m‖ := by
      have hm : m = -((1-a) • (f x-m)) := eq_neg_of_add_eq_zero_left hz'
      have heN := congrArg norm hm
      rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 1-a)] at heN
      nlinarith [norm_nonneg (f x-m)]
    have hm0 : m = 0 := norm_eq_zero.mp (by linarith [herr x ht hx,norm_nonneg m])
    exact affineOrbitModel_zero_bottom H ρ L p R ht hm0
  · exact hz0 x ht ((flattenInitial_eq_self H ρ L p R f hR hx).symm.trans hz)

lemma flattenInitial_final (hR : 0 < R) (hR1 : R ≤ 1) {x : Fin (d + 1) → ℝ} (ht : x (Fin.last d) = 1) :
    flattenInitial H ρ L p R f x = f x := by
  classical
  apply flattenInitial_eq_self H ρ L p R f hR
  rintro ⟨s,hs⟩
  have hd := dist_le_pi_dist x (s • embedSpatial p) (Fin.last d)
  have hst : (s • embedSpatial p) (Fin.last d) = 0 :=
    s.val.smul_time_zero _ (by change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) p 0 (Fin.last d) = 0; simp only [Fin.snoc_last])
  rw [ht,hst] at hd
  norm_num at hd
  linarith

end Flatten
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
section FlattenCompact
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u144} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin d → ℝ) (R : ℝ) (f : (Fin (d + 1) → ℝ) → V)

lemma compact_zeros_flattenInitial (hR : 0 < R) (hf : Continuous f)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0}) :
    IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ flattenInitial H ρ L p R f x = 0} := by
  classical
  have hc := hK.union (isCompact_iUnion
    (fun s : H ↦ isCompact_closedBall (s • embedSpatial p) R))
  apply hc.of_isClosed_subset
  · exact (isClosed_Icc.preimage (continuous_apply _)).inter
      (isClosed_eq (continuous_flattenInitial H ρ L p R f hf) continuous_const)
  · intro x hx
    by_cases hb : x ∈ orbitBall (G := H) (embedSpatial p) R
    · obtain ⟨s,hs⟩ := hb
      exact Or.inr (Set.mem_iUnion.mpr ⟨s,hs.le⟩)
    · exact Or.inl ⟨hx.1,(flattenInitial_eq_self H ρ L p R f hR hb).symm.trans hx.2⟩

/-- A simple initial zero need only agree with its invertible linearization up
to a relative error of one half. Compactly supported flattening turns this
into the affine continuation theorem, without adding any new final zeros. -/
theorem exists_terminal_zero_local
    (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (hball : orbitBall (G := H) (embedSpatial p) R ⊆ freeLocus (G := H))
    (hf : Continuous f) (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (herr : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      ‖f x - affineOrbitModel H ρ L (embedSpatial p) R p x‖ ≤
        ‖affineOrbitModel H ρ L (embedSpatial p) R p x‖ / 2)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0})
    (hfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → f x = 0 →
      ∀ s : H, s • x = x → s = 1) :
    ∃ x : Fin (d + 1) → ℝ, x (Fin.last d) = 1 ∧ f x = 0 := by
  classical
  let g := flattenInitial H ρ L p R f
  have hsep' : ∀ s t : H, s ≠ t → 8 * (R/2) < dist (s • embedSpatial p) (t • embedSpatial p) := by
    intro s t hst
    linarith [hsep s t hst]
  have hgfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → g x = 0 →
      ∀ s : H, s • x = x → s = 1 := by
    intro x hx hz s hs
    by_cases hb : x ∈ orbitBall (G := H) (embedSpatial p) R
    · exact hball hb s hs
    · apply hfree x hx _ s hs
      exact (flattenInitial_eq_self H ρ L p R f hR hb).symm.trans hz
  obtain ⟨x,hxt,hxg⟩ := exists_terminal_zero_affine H hHt ρ L hρ p (R/2) (by positivity)
    hsep' g (continuous_flattenInitial H ρ L p R f hf).continuousOn
    (flattenInitial_equivariant H ρ L p R f hfe)
    (fun x _ hx ↦ flattenInitial_inner H ρ L p R f hR hsep hx)
    (fun x ht hz ↦ flattenInitial_zero_bottom H ρ L p R f hR hsep hz0 herr ht hz)
    (compact_zeros_flattenInitial H ρ L p R f hR hf hK) hgfree
  refine ⟨x,hxt,?_⟩
  exact (flattenInitial_final H ρ L p R f hR hR1 hxt).symm.trans hxg

end FlattenCompact
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
lemma hasFDerivAt_relative_error {E : Type u145} {V : Type u146}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (p : E) (L : E ≃L[ℝ] V) (hf0 : f p = 0)
    (hd : HasFDerivAt f L.toContinuousLinearMap p) :
    ∃ δ > 0, ∀ u : E, dist u p < δ → ‖f u - L (u-p)‖ ≤ ‖L (u-p)‖ / 2 := by
  let M := ‖L.symm.toContinuousLinearMap‖
  have hM : 0 ≤ M := norm_nonneg _
  let c := 1 / (2*(M+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcM : c*M ≤ 1/2 := by
    dsimp [c]
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 2*(M+1))]
    linarith
  obtain ⟨δ,hδ,he⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.def hc)
  refine ⟨δ,hδ,fun u hu ↦ ?_⟩
  have hsmall : ‖f u - L (u-p)‖ ≤ c * ‖u-p‖ := by simpa only [hf0,sub_zero,ContinuousLinearEquiv.coe_coe] using he hu
  have hnorm : ‖u-p‖ ≤ M * ‖L (u-p)‖ := by
    have h := L.symm.toContinuousLinearMap.le_opNorm (L (u-p))
    simpa only [ContinuousLinearEquiv.coe_coe,L.symm_apply_apply] using h
  calc
    ‖f u - L (u-p)‖ ≤ c*‖u-p‖ := hsmall
    _ ≤ c*(M*‖L (u-p)‖) := mul_le_mul_of_nonneg_left hnorm hc.le
    _ = (c*M)*‖L (u-p)‖ := by ring
    _ ≤ (1/2)*‖L (u-p)‖ := mul_le_mul_of_nonneg_right hcM (norm_nonneg _)
    _ = ‖L (u-p)‖/2 := by ring
end SharpLiebThirring.CubeFlags


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

/-- A continuous equivariant homotopy with compact free zero set and one simple
initial zero orbit must have a terminal zero. No smoothness is required away
from the distinguished initial point. -/
theorem exists_terminal_zero_simple {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    {V : Type u147} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (p : Fin d → ℝ) (f : (Fin (d + 1) → ℝ) → V)
    (hf : Continuous f) (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hp0 : f (embedSpatial p) = 0)
    (hd : HasFDerivAt (fun u : Fin d → ℝ ↦ f (embedSpatial u))
      L.toContinuousLinearEquiv.toContinuousLinearMap p)
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0})
    (hfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → f x = 0 →
      ∀ s : H, s • x = x → s = 1) :
    ∃ x : Fin (d + 1) → ℝ, x (Fin.last d) = 1 ∧ f x = 0 := by
  classical
  have ht0 : (embedSpatial p) (Fin.last d) = 0 := by
    change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) p 0 (Fin.last d) = 0
    simp only [Fin.snoc_last]
  have hpFree : embedSpatial p ∈ freeLocus (G := H) :=
    hfree _ (by rw [ht0]; exact ⟨le_refl _,zero_le_one⟩) hp0
  obtain ⟨R₁,hR₁,hsep⟩ := orbit_separation (G := H) (embedSpatial p) hpFree
  obtain ⟨R₂,hR₂,hball⟩ := Metric.isOpen_iff.mp (isOpen_freeLocus (G := H)) _ hpFree
  obtain ⟨δ,hδ,herr⟩ := hasFDerivAt_relative_error (fun u : Fin d → ℝ ↦ f (embedSpatial u))
    p L.toContinuousLinearEquiv hp0 hd
  let R := min 1 (min R₁ (min R₂ δ))
  have hR : 0 < R := lt_min zero_lt_one (lt_min hR₁ (lt_min hR₂ hδ))
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRR₁ : R ≤ R₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hRR₂ : R ≤ R₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRδ : R ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsep' : ∀ s t : H, s ≠ t → 8*R < dist (s • embedSpatial p) (t • embedSpatial p) := by
    intro s t hst
    linarith [hsep s t hst]
  have hball' : orbitBall (G := H) (embedSpatial p) R ⊆ freeLocus (G := H) := by
    rintro x ⟨s,hs⟩
    have hx : dist (s⁻¹ • x) (embedSpatial p) < R₂ := by
      have he := dist_smul s⁻¹ x (s • embedSpatial p)
      rw [inv_smul_smul] at he
      rw [he]
      exact hs.trans_le hRR₂
    have hb := freeLocus_smul s (hball hx)
    simpa only [smul_inv_smul] using hb
  apply exists_terminal_zero_local H ρ L p R f hHt hρ hR hR1 hsep' hball' hf hfe hz0
  · intro x ht hx
    let s := ballLabel (G := H) (embedSpatial p) R x
    let y := s⁻¹ • x
    let u := spatial y
    have htY : y (Fin.last d) = 0 := (s⁻¹).val.smul_time_zero x ht
    have hY : embedSpatial u = y := embed_spatial_of_time_zero y htY
    have hdist : dist u p < δ := by
      have hs := ballLabel_dist (embedSpatial p) R hx
      have he := dist_smul s⁻¹ x (s • embedSpatial p)
      rw [inv_smul_smul] at he
      have hdu := dist_spatial_le y (embedSpatial p)
      rw [spatial_embed] at hdu
      exact hdu.trans_lt ((he ▸ hs).trans_le hRδ)
    have her := herr u hdist
    have hfx : f x = ρ s (f (embedSpatial u)) := by
      rw [hY,← hfe,smul_inv_smul]
    change ‖f x - ρ s (L (u-p))‖ ≤ ‖ρ s (L (u-p))‖ / 2
    rw [hfx,← map_sub,hρ,hρ]
    exact her
  · exact hK
  · exact hfree

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
