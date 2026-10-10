import OAI.Analysis.NodalLength.MassComparison

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set

namespace SharpNodal.Profiles
open Carleman

structure WeightedProfileBounds (Ω : Set Plane) (S : ℕ → ℝ) (B : ℕ → Plane)
    (U : ℕ → Plane → ℝ) (c : ℕ → ℝ) (V : Plane → EReal) : Prop where
  upper : ∀ (f : Plane → ℝ), ContinuousOn f Ω → ∀ F : Set Plane,
    IsCompact F → F⊆Ω →
    limsup (fun j => logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f F)) atTop ≤
      ⨆ x∈F, V x+(f x:EReal)
  lower : ∀ (f : Plane → ℝ), ContinuousOn f Ω → ∀ G : Set Plane,
    IsOpen G → G⊆Ω →
    (⨆ x∈G, V x+(f x:EReal)) ≤
      liminf (fun j => logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f G)) atTop

lemma upperSemicontinuousOn_add_real {Ω : Set Plane} {V : Plane → EReal}
    {f : Plane → ℝ} (hV : UpperSemicontinuousOn V Ω) (hf : ContinuousOn f Ω) :
    UpperSemicontinuousOn (fun x => V x+(f x:EReal)) Ω := by
  apply hV.add' (continuous_coe_real_ereal.comp_continuousOn hf).upperSemicontinuousOn
  intro x hx
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

lemma compact_strict_gap {F : Set Plane} {W : Plane → EReal} (hF : IsCompact F)
    (hW : UpperSemicontinuousOn W F) (hneg : ∀ x∈F, W x<0) :
    (⨆ x∈F, W x)<0 := by
  rcases F.eq_empty_or_nonempty with h | h
  · simp [h]
  · obtain ⟨x, hx, hmax⟩ := hW.exists_isMaxOn h hF
    apply lt_of_le_of_lt _ (hneg x hx)
    exact iSup_le fun y => iSup_le fun hy => hmax hy

theorem strict_contact_mass_contradiction
    {Ω F G : Set Plane} {S c : ℕ → ℝ} {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    {V : Plane → EReal} {f : Plane → ℝ} {x₀ : Plane} {C : ℝ}
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop) (hC : 0<C)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V)
    (hf : ContinuousOn f Ω) (hF : IsCompact F) (hFΩ : F⊆Ω)
    (hG : IsOpen G) (hGΩ : G⊆Ω) (hx₀ : x₀∈G)
    (hneg : ∀ x∈F, V x+(f x:EReal)<0) (hzero : V x₀+(f x₀:EReal)=0)
    (hcomp : ∀ᶠ j in atTop, tiltedMass (S j) (B j) (U j) (c j) f G ≤
      ENNReal.ofReal C*tiltedMass (S j) (B j) (U j) (c j) f F) : False := by
  have hW := (upperSemicontinuousOn_add_real hV hf).mono hFΩ
  have hgap := compact_strict_gap hF hW hneg
  obtain ⟨a, hsa, ha⟩ := EReal.lt_iff_exists_real_btwn.mp hgap
  have ha' : a<0 := by exact_mod_cast ha
  let b := a/2
  have hab : a<b := by dsimp [b]; linarith
  have hb : b<0 := by dsimp [b]; linarith
  have hupper := hprofile.upper f hf F hF hFΩ
  have hlower := hprofile.lower f hf G hG hGΩ
  have hlow0 : (0:EReal)≤⨆ x∈G, V x+(f x:EReal) := by
    rw [← hzero]
    exact le_iSup_of_le x₀ (le_iSup_of_le hx₀ le_rfl)
  have hA := eventually_lt_of_limsup_lt (hupper.trans_lt hsa)
  have hB := eventually_lt_of_lt_liminf
    ((show (b:EReal)<0 by exact_mod_cast hb).trans_le (hlow0.trans hlower))
  apply no_exponential_gap hS hab hC _ _ hcomp
  · filter_upwards [hA] with j hj
    exact ((logRate_lt_iff (hSpos j) _).mp hj).le
  · filter_upwards [hB] with j hj
    exact ((lt_logRate_iff (hSpos j) _).mp hj).le

theorem laplacian_nonneg_of_strict_contact
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S D K e c : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω) (hball : Metric.ball x₀ r₀⊆Ω)
    (hχ : ContDiffOn ℝ ∞ χ Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω) (hr₀ : 0<r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0<c j) (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V)
    (hcontact : V x₀+(-χ x₀:EReal)=0)
    (hstrict : ∀ x∈Metric.ball x₀ r₀, x≠x₀ → V x+(-χ x:EReal)<0) :
    0≤euclideanLaplacian χ x₀ := by
  by_contra hn
  have htrace := lt_of_not_ge hn
  obtain ⟨F, G, C, hF, hG, hC, hFsub, hGsub, hFaway, hxG, hcomp⟩ :=
    tilted_mass_comparison_on hΩ hx₀ hball hχ hp hU hr₀ hSpos hS hc hDdef hb hd hK
      hpbound he hpgrad hPDE htrace ha
  apply strict_contact_mass_contradiction hSpos hS hC hV hprofile hχ.continuousOn.neg
    hF (hFsub.trans hball) hG (hGsub.trans hball) hxG _ hcontact hcomp
  intro x hx
  apply hstrict x (hFsub hx)
  intro heq
  exact hFaway (heq ▸ hx)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

def radiusSquare (x₀ x : Plane) : ℝ := ‖x-x₀‖^2

def contactQuartic (x₀ x : Plane) : ℝ := radiusSquare x₀ x*radiusSquare x₀ x

lemma smooth_radiusSquare (x₀ : Plane) : Smooth (radiusSquare x₀) :=
  (contDiff_id.sub contDiff_const).norm_sq ℝ

lemma radiusSquare_self (x₀ : Plane) : radiusSquare x₀ x₀=0 := by simp [radiusSquare]

lemma radiusSquare_pos {x₀ x : Plane} (hx : x≠x₀) : 0<radiusSquare x₀ x := by
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) 2

lemma radiusSquare_partial_self (x₀ : Plane) (i : Fin 2) :
    coordPartial (radiusSquare x₀) i x₀=0 := by
  have hq : HasFDerivAt (𝕜:=ℝ) (radiusSquare x₀) 0 x₀ := by
    convert! ((hasFDerivAt_id (𝕜:=ℝ) x₀).sub_const x₀).norm_sq using 1
    simp
  simp [coordPartial, hq.fderiv]

lemma smooth_contactQuartic (x₀ : Plane) : Smooth (contactQuartic x₀) :=
  (smooth_radiusSquare x₀).mul (smooth_radiusSquare x₀)

lemma contactQuartic_self (x₀ : Plane) : contactQuartic x₀ x₀=0 := by
  simp [contactQuartic, radiusSquare_self]

lemma contactQuartic_pos {x₀ x : Plane} (hx : x≠x₀) : 0<contactQuartic x₀ x :=
  mul_pos (radiusSquare_pos hx) (radiusSquare_pos hx)

lemma contactQuartic_partial_self (x₀ : Plane) (i : Fin 2) :
    coordPartial (contactQuartic x₀) i x₀=0 := by
  unfold contactQuartic
  rw [partial_mul (smooth_radiusSquare x₀) (smooth_radiusSquare x₀)]
  simp [radiusSquare_self]

lemma contactQuartic_laplacian_self (x₀ : Plane) :
    euclideanLaplacian (contactQuartic x₀) x₀=0 := by
  unfold contactQuartic
  rw [laplacian_mul (smooth_radiusSquare x₀) (smooth_radiusSquare x₀)]
  simp [radiusSquare_self, radiusSquare_partial_self]

lemma laplacian_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g) (x : Plane) :
    euclideanLaplacian (fun y => f y+g y) x=euclideanLaplacian f x+euclideanLaplacian g x := by
  unfold euclideanLaplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show coordPartial (fun y => f y+g y) i = fun y => coordPartial f i y+coordPartial g i y
    from funext (partial_add hf hg i)]
  exact partial_add (smooth_partial hf i) (smooth_partial hg i) i x

lemma strictify_gradient {χ : Plane → ℝ} (hχ : Smooth χ) (x₀ : Plane) :
    coordinateGradient (fun x => χ x+contactQuartic x₀ x) x₀=coordinateGradient χ x₀ := by
  ext i
  simp only [coordinateGradient_apply, partial_add hχ (smooth_contactQuartic x₀),
    contactQuartic_partial_self, add_zero]

lemma strictify_laplacian {χ : Plane → ℝ} (hχ : Smooth χ) (x₀ : Plane) :
    euclideanLaplacian (fun x => χ x+contactQuartic x₀ x) x₀=euclideanLaplacian χ x₀ := by
  rw [laplacian_add hχ (smooth_contactQuartic x₀), contactQuartic_laplacian_self, add_zero]

lemma strictify_contact {V : Plane → EReal} {χ : Plane → ℝ} {x₀ : Plane}
    (hcontact : V x₀=(χ x₀:EReal)) :
    V x₀+((-(χ x₀+contactQuartic x₀ x₀):ℝ):EReal)=0 := by
  rw [contactQuartic_self, add_zero, hcontact, ← EReal.coe_add]
  simp

lemma strictify_strict {V : Plane → EReal} {χ : Plane → ℝ} {x₀ x : Plane}
    (hdom : V x≤(χ x:EReal)) (hx : x≠x₀) :
    V x+((-(χ x+contactQuartic x₀ x):ℝ):EReal)<0 := by
  apply lt_of_le_of_lt (add_le_add hdom le_rfl) _
  rw [← EReal.coe_add]
  norm_cast
  have hq := contactQuartic_pos hx
  linarith

theorem smooth_extension_near {Ω : Set Plane} {f : Plane → ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω) (hf : ContDiffOn ℝ ∞ f Ω) :
    ∃ (g : Plane → ℝ) (r : ℝ), Smooth g ∧ 0<r ∧ Metric.ball x₀ r⊆Ω ∧
      ∀ x∈Metric.ball x₀ r, g x=f x := by
  obtain ⟨ζ, r, hr, hζ, hcζ, hζΩ, hζ1⟩ := exists_smooth_cutoff (hΩ.mem_nhds hx₀)
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  refine ⟨fun x => ζ x*f x, min r R, smooth_cutoff_mul hΩ hζ hζΩ hf,
    lt_min hr hR, (Metric.ball_subset_ball (min_le_right _ _)).trans hRΩ, ?_⟩
  intro x hx
  dsimp only
  rw [hζ1 x (Metric.ball_subset_ball (min_le_left _ _) hx), one_mul]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

abbrev BilinearForm := Plane →L[ℝ] Plane →L[ℝ] ℝ

def SymmetricForm (A : BilinearForm) : Prop := ∀ x y, A x y=A y x

def centeredQuadratic (A : BilinearForm) (x₀ x : Plane) : ℝ :=
  (1/2:ℝ)*A (x-x₀) (x-x₀)

lemma smooth_centeredQuadratic (A : BilinearForm) (x₀ : Plane) :
    Smooth (centeredQuadratic A x₀) := by
  exact contDiff_const.mul ((contDiff_const.clm_apply (contDiff_id.sub contDiff_const)).clm_apply
    (contDiff_id.sub contDiff_const))

lemma hasFDerivAt_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : HasFDerivAt (centeredQuadratic A x₀) (A (x-x₀)) x := by
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hAt : HasFDerivAt (fun y => A (y-x₀)) A x := by
    convert! A.hasFDerivAt.comp x ht using 1
  convert! (hAt.clm_apply ht).const_mul (1/2:ℝ) using 1
  ext y
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, id_eq]
  rw [hA y (x-x₀)]
  ring

lemma fderiv_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A) (x₀ : Plane) :
    fderiv ℝ (centeredQuadratic A x₀) = fun x => A (x-x₀) :=
  funext fun x => (hasFDerivAt_centeredQuadratic hA x₀ x).fderiv

lemma partial_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i : Fin 2) (x : Plane) :
    coordPartial (centeredQuadratic A x₀) i x=A (x-x₀) (EuclideanSpace.single i 1) := by
  rw [coordPartial, fderiv_centeredQuadratic hA]

lemma partial2_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial (centeredQuadratic A x₀) i) j x=
      A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  rw [show coordPartial (centeredQuadratic A x₀) i =
    fun y => A (y-x₀) (EuclideanSpace.single i 1) from funext (partial_centeredQuadratic hA x₀ i)]
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hh : HasFDerivAt (fun y => A (y-x₀) (EuclideanSpace.single i 1))
      (A.flip (EuclideanSpace.single i 1)) x := by
    convert! (A.flip (EuclideanSpace.single i 1)).hasFDerivAt.comp x ht using 1
  simp only [coordPartial, hh.fderiv, ContinuousLinearMap.flip_apply]

lemma laplacian_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : euclideanLaplacian (centeredQuadratic A x₀) x=
      ∑ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  simp only [euclideanLaplacian, partial2_centeredQuadratic hA]

lemma symmetric_hessian {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    SymmetricForm (fderiv ℝ (fderiv ℝ f) x₀) := by
  intro x y
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞)≤⊤))).eq x y

lemma hessian_on_basis {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ f) x₀ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)=
      coordPartial (coordPartial f i) j x₀ := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
  simp

def secondTaylorPolynomial (f : Plane → ℝ) (x₀ x : Plane) : ℝ :=
  f x₀+fderiv ℝ f x₀ (x-x₀)+centeredQuadratic (fderiv ℝ (fderiv ℝ f) x₀) x₀ x

lemma smooth_secondTaylorPolynomial (f : Plane → ℝ) (x₀ : Plane) :
    Smooth (secondTaylorPolynomial f x₀) :=
  (contDiff_const.add (contDiff_const.clm_apply (contDiff_id.sub contDiff_const))).add
    (smooth_centeredQuadratic _ _)

lemma secondTaylorPolynomial_self (f : Plane → ℝ) (x₀ : Plane) :
    secondTaylorPolynomial f x₀ x₀=f x₀ := by
  simp [secondTaylorPolynomial, centeredQuadratic]

lemma hasFDerivAt_secondTaylorPolynomial {f : Plane → ℝ} (hf : Smooth f) (x₀ x : Plane) :
    HasFDerivAt (secondTaylorPolynomial f x₀)
      (fderiv ℝ f x₀+fderiv ℝ (fderiv ℝ f) x₀ (x-x₀)) x := by
  apply HasFDerivAt.add _ (hasFDerivAt_centeredQuadratic (symmetric_hessian hf x₀) x₀ x)
  apply HasFDerivAt.const_add
  convert! (fderiv ℝ f x₀).hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀) using 1

theorem secondTaylorPolynomial_remainder {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    (fun x => f x-secondTaylorPolynomial f x₀ x) =o[𝓝 x₀] (fun x => ‖x-x₀‖^2) := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  have hd := (hdf x₀).hasFDerivAt.isLittleO.norm_right
  have hder (x : Plane) : HasFDerivAt (fun y => f y-secondTaylorPolynomial f x₀ y)
      (fderiv ℝ f x-fderiv ℝ f x₀-fderiv ℝ (fderiv ℝ f) x₀ (x-x₀)) x := by
    convert! ((hf.differentiable (by simp) x).hasFDerivAt).sub
      (hasFDerivAt_secondTaylorPolynomial hf x₀ x) using 1
    abel
  have hh := (convex_univ : Convex ℝ (Set.univ : Set Plane)).isLittleO_pow_succ
    (mem_univ x₀) (fun x _ => (hder x).hasFDerivWithinAt) (n:=1)
      (by simpa only [nhdsWithin_univ, pow_one] using hd)
  simpa only [nhdsWithin_univ, secondTaylorPolynomial_self, sub_self, sub_zero] using hh

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

def IsUpperTest (V : Plane → EReal) (f : Plane → ℝ) (x₀ : Plane) : Prop :=
  V x₀=(f x₀:EReal) ∧ ∀ᶠ x in 𝓝 x₀, V x≤(f x:EReal)

def NonexceptionalTestProperty (Ω : Set Plane) (V : Plane → EReal) : Prop :=
  ∀ (f : Plane → ℝ), Smooth f → ∀ x₀∈Ω, IsUpperTest V f x₀ →
    coordinateGradient f x₀≠0 → 0≤euclideanLaplacian f x₀

def FullTestProperty (Ω : Set Plane) (V : Plane → EReal) : Prop :=
  ∀ (f : Plane → ℝ), Smooth f → ∀ x₀∈Ω, IsUpperTest V f x₀ →
    0≤euclideanLaplacian f x₀

def formTrace (A : BilinearForm) : ℝ :=
  ∑ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

def quadraticAffine (c : ℝ) (L : Plane →L[ℝ] ℝ) (A : BilinearForm)
    (x₀ x : Plane) : ℝ := c+L (x-x₀)+centeredQuadratic A x₀ x

lemma smooth_quadraticAffine (c : ℝ) (L : Plane →L[ℝ] ℝ) (A : BilinearForm)
    (x₀ : Plane) : Smooth (quadraticAffine c L A x₀) :=
  (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))).add
    (smooth_centeredQuadratic A x₀)

lemma partial_clm_shift (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (fun y => L (y-x₀)) i x=L (EuclideanSpace.single i 1) := by
  have hd : HasFDerivAt (fun y => L (y-x₀)) L x := by
    convert! L.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀) using 1
  simp only [coordPartial, hd.fderiv]

lemma partial_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (quadraticAffine c L A x₀) i x=
      L (EuclideanSpace.single i 1)+A (x-x₀) (EuclideanSpace.single i 1) := by
  have hL : Smooth (fun y => L (y-x₀)) :=
    contDiff_const.clm_apply (contDiff_id.sub contDiff_const)
  unfold quadraticAffine
  rw [partial_add (contDiff_const.add hL)
    (smooth_centeredQuadratic A x₀), partial_add contDiff_const hL, partial_const,
    partial_clm_shift, partial_centeredQuadratic hA, zero_add]

lemma laplacian_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) :
    euclideanLaplacian (quadraticAffine c L A x₀) x=formTrace A := by
  unfold euclideanLaplacian formTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (quadraticAffine c L A x₀) i =
    fun y => L (EuclideanSpace.single i 1)+coordPartial (centeredQuadratic A x₀) i y by
      ext y; rw [partial_quadraticAffine hA, partial_centeredQuadratic hA]]
  rw [partial_add contDiff_const (smooth_partial (smooth_centeredQuadratic A x₀) i),
    partial_const, zero_add, partial2_centeredQuadratic hA]

lemma quadraticAffine_self (c : ℝ) (L : Plane →L[ℝ] ℝ) (A : BilinearForm) (x₀ : Plane) :
    quadraticAffine c L A x₀ x₀=c := by simp [quadraticAffine, centeredQuadratic]

def innerForm : BilinearForm := innerSL ℝ

lemma innerForm_apply (x y : Plane) : innerForm x y=inner ℝ x y := rfl

lemma symmetric_innerForm : SymmetricForm innerForm := by
  intro x y
  exact real_inner_comm y x

lemma formTrace_innerForm : formTrace innerForm=2 := by
  simp [formTrace, innerForm_apply]

lemma formTrace_add (A B : BilinearForm) : formTrace (A+B)=formTrace A+formTrace B := by
  simp [formTrace, Finset.sum_add_distrib]

lemma formTrace_smul (c : ℝ) (A : BilinearForm) : formTrace (c • A)=c*formTrace A := by
  simp only [formTrace, smul_apply, smul_eq_mul, Finset.mul_sum]

lemma formTrace_hessian {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    formTrace (fderiv ℝ (fderiv ℝ f) x₀)=euclideanLaplacian f x₀ := by
  simp only [formTrace, euclideanLaplacian, hessian_on_basis hf]

lemma centeredQuadratic_add (A B : BilinearForm) (x₀ x : Plane) :
    centeredQuadratic (A+B) x₀ x=centeredQuadratic A x₀ x+centeredQuadratic B x₀ x := by
  simp [centeredQuadratic]; ring

lemma centeredQuadratic_inner_smul (δ : ℝ) (x₀ x : Plane) :
    centeredQuadratic ((2*δ) • innerForm) x₀ x=δ*‖x-x₀‖^2 := by
  simp only [centeredQuadratic, smul_apply, smul_eq_mul, innerForm_apply,
    real_inner_self_eq_norm_sq]
  ring

theorem exists_strict_quadratic_test {Ω : Set Plane} {V : Plane → EReal}
    {f : Plane → ℝ} {x₀ : Plane} (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω)
    (hf : Smooth f) (htest : IsUpperTest V f x₀) (hΔ : euclideanLaplacian f x₀<0) :
    ∃ (A : BilinearForm) (r : ℝ), SymmetricForm A ∧ formTrace A<0 ∧ 0<r ∧
      Metric.closedBall x₀ r⊆Ω ∧
      (∀ x∈Metric.closedBall x₀ r,
        V x≤(quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀ x:EReal)) ∧
      (∀ x∈Metric.closedBall x₀ r, x≠x₀ →
        V x<(quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀ x:EReal)) := by
  let δ := -euclideanLaplacian f x₀/8
  have hδ : 0<δ := by dsimp [δ]; linarith
  let A : BilinearForm := fderiv ℝ (fderiv ℝ f) x₀+(2*δ) • innerForm
  have hA : SymmetricForm A := by
    intro x y
    dsimp [A]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [symmetric_hessian hf x₀ x y, symmetric_innerForm x y]
  have htrace : formTrace A<0 := by
    dsimp [A]
    rw [formTrace_add, formTrace_smul, formTrace_innerForm, formTrace_hessian hf]
    dsimp [δ]
    linarith
  have heq (x : Plane) : quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀ x=
      secondTaylorPolynomial f x₀ x+δ*‖x-x₀‖^2 := by
    dsimp only [quadraticAffine, A, secondTaylorPolynomial]
    rw [centeredQuadratic_add, centeredQuadratic_inner_smul]
    ring
  have hrem := (secondTaylorPolynomial_remainder hf x₀).bound (half_pos hδ)
  have hevent : ∀ᶠ x in 𝓝 x₀, x∈Ω ∧ V x≤(f x:EReal) ∧
      ‖f x-secondTaylorPolynomial f x₀ x‖≤δ/2*‖x-x₀‖^2 := by
    filter_upwards [hΩ.mem_nhds hx₀, htest.2, hrem] with x hx hd hr
    refine ⟨hx, hd, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x-x₀‖)] using hr
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨A, r/2, hA, htrace, half_pos hr, ?_, ?_, ?_⟩
  · intro x hx
    exact (hsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))).1
  · intro x hx
    obtain ⟨_, hd, hb⟩ := hsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))
    apply hd.trans
    apply EReal.coe_le_coe_iff.mpr
    rw [heq]
    rw [Real.norm_eq_abs] at hb
    have hm := le_trans (le_abs_self (f x-secondTaylorPolynomial f x₀ x)) hb
    have hp := sq_nonneg ‖x-x₀‖
    nlinarith
  · intro x hx hne
    obtain ⟨_, hd, hb⟩ := hsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))
    apply hd.trans_lt
    apply EReal.coe_lt_coe_iff.mpr
    rw [heq]
    rw [Real.norm_eq_abs] at hb
    have hm := le_trans (le_abs_self (f x-secondTaylorPolynomial f x₀ x)) hb
    have hp : 0<‖x-x₀‖^2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _
    nlinarith

end SharpNodal.Profiles

end
end
end
end

end OAI
