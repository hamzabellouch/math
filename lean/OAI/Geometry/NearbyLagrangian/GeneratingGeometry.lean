import Mathlib

namespace OAI

/-! Exactness, isotropy and immersion of generating maps. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Generating

variable {Q W : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def vertical (f : Q × W → ℝ) (x : Q × W) : W →L[ℝ] ℝ :=
  (fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ Q W)

def momentum (f : Q × W → ℝ) (x : Q × W) : Q →L[ℝ] ℝ :=
  (fderiv ℝ f x).comp (ContinuousLinearMap.inl ℝ Q W)

def generatingMap (f : Q × W → ℝ) (x : Q × W) : Q × (Q →L[ℝ] ℝ) :=
  (x.1, momentum f x)

def localLiouville (z v : Q × (Q →L[ℝ] ℝ)) : ℝ := z.2 v.1

def localSymplectic (u v : Q × (Q →L[ℝ] ℝ)) : ℝ := u.2 v.1 - v.2 u.1

lemma vertical_hasFDerivAt {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    HasFDerivAt (vertical f)
      (((ContinuousLinearMap.compL ℝ W (Q × W) ℝ).flip
        (ContinuousLinearMap.inr ℝ Q W)).comp (fderiv ℝ (fderiv ℝ f) x)) x := by
  unfold vertical
  exact ((ContinuousLinearMap.compL ℝ W (Q × W) ℝ).flip
    (ContinuousLinearMap.inr ℝ Q W)).hasFDerivAt.comp x hf.hasFDerivAt

lemma momentum_hasFDerivAt {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    HasFDerivAt (momentum f)
      (((ContinuousLinearMap.compL ℝ Q (Q × W) ℝ).flip
        (ContinuousLinearMap.inl ℝ Q W)).comp (fderiv ℝ (fderiv ℝ f) x)) x := by
  unfold momentum
  exact ((ContinuousLinearMap.compL ℝ Q (Q × W) ℝ).flip
    (ContinuousLinearMap.inl ℝ Q W)).hasFDerivAt.comp x hf.hasFDerivAt

lemma vertical_fderiv_apply {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v : Q × W) (w : W) :
    fderiv ℝ (vertical f) x v w = fderiv ℝ (fderiv ℝ f) x v (0, w) := by
  rw [(vertical_hasFDerivAt hf).fderiv]
  rfl

lemma momentum_fderiv_apply {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v : Q × W) (q : Q) :
    fderiv ℝ (momentum f) x v q = fderiv ℝ (fderiv ℝ f) x v (q, 0) := by
  rw [(momentum_hasFDerivAt hf).fderiv]
  rfl

lemma generatingMap_hasFDerivAt {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    HasFDerivAt (generatingMap f)
      ((ContinuousLinearMap.fst ℝ Q W).prod (fderiv ℝ (momentum f) x)) x := by
  exact (ContinuousLinearMap.fst ℝ Q W).hasFDerivAt.prodMk
    (momentum_hasFDerivAt hf).differentiableAt.hasFDerivAt

lemma generatingMap_fderiv {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v : Q × W) :
    fderiv ℝ (generatingMap f) x v = (v.1, fderiv ℝ (momentum f) x v) := by
  rw [(generatingMap_hasFDerivAt hf).fderiv]
  rfl

theorem liouville_eq_differential {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (hcrit : vertical f x = 0)
    (v : Q × W) :
    localLiouville (generatingMap f x) (fderiv ℝ (generatingMap f) x v) =
      fderiv ℝ f x v := by
  rw [generatingMap_fderiv hf]
  change fderiv ℝ f x (v.1, 0) = fderiv ℝ f x v
  have hz : fderiv ℝ f x (0, v.2) = 0 := by
    exact congrArg (fun A : W →L[ℝ] ℝ => A v.2) hcrit
  calc
    _ = fderiv ℝ f x (v.1, 0) + fderiv ℝ f x (0, v.2) := by rw [hz, add_zero]
    _ = fderiv ℝ f x ((v.1, 0) + (0, v.2)) := (map_add _ _ _).symm
    _ = _ := by simp

theorem symplectic_eq_zero {f : Q × W → ℝ} {x : Q × W}
    (hf : ContDiffAt ℝ ∞ f x) {v w : Q × W}
    (hv : fderiv ℝ (vertical f) x v = 0)
    (hw : fderiv ℝ (vertical f) x w = 0) :
    localSymplectic (fderiv ℝ (generatingMap f) x v)
      (fderiv ℝ (generatingMap f) x w) = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hv' : fderiv ℝ (fderiv ℝ f) x v (0, w.2) = 0 := by
    rw [← vertical_fderiv_apply hd, hv, zero_apply]
  have hw' : fderiv ℝ (fderiv ℝ f) x w (0, v.2) = 0 := by
    rw [← vertical_fderiv_apply hd, hw, zero_apply]
  have hsplit (A : Q × W →L[ℝ] ℝ) (z : Q × W) : A z = A (z.1, 0) + A (0, z.2) := by
    rw [← map_add]; congr 1; ext <;> simp
  have hs := (hf.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)).eq v w
  rw [hsplit _ w, hsplit _ v, hv', hw', add_zero, add_zero] at hs
  simp only [generatingMap_fderiv hd, localSymplectic, momentum_fderiv_apply hd]
  exact sub_eq_zero.mpr hs

theorem generatingMap_ker_injective {f : Q × W → ℝ} {x : Q × W}
    (hf : ContDiffAt ℝ ∞ f x)
    (hreg : Function.Surjective (fderiv ℝ (vertical f) x)) :
    Function.Injective (fun v : LinearMap.ker (fderiv ℝ (vertical f) x).toLinearMap =>
      fderiv ℝ (generatingMap f) x v) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hzero (v : Q × W) (hv : fderiv ℝ (vertical f) x v = 0)
      (hgen : fderiv ℝ (generatingMap f) x v = 0) : v = 0 := by
    rw [generatingMap_fderiv hd] at hgen
    have hq : v.1 = 0 := congrArg Prod.fst hgen
    have hp : fderiv ℝ (momentum f) x v = 0 := congrArg Prod.snd hgen
    have hall (z : Q × W) : fderiv ℝ (fderiv ℝ f) x v z = 0 := by
      have hsplit : z = (z.1, 0) + (0, z.2) := by ext <;> simp
      rw [hsplit, map_add, ← momentum_fderiv_apply hd, ← vertical_fderiv_apply hd, hp, hv]
      simp
    have hw : v.2 = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) (by
      intro ℓ
      obtain ⟨z, hz⟩ := hreg ℓ
      have hs := (hf.isSymmSndFDerivAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr le_top)).eq z v
      rw [hall] at hs
      have hv' : v = (0, v.2) := by ext <;> simp [hq]
      rw [hv', ← vertical_fderiv_apply hd, hz] at hs
      exact hs)
    exact Prod.ext hq hw
  intro v w heq
  dsimp only at heq
  apply Subtype.ext
  apply sub_eq_zero.mp
  exact hzero (v.val - w.val) (by
    rw [map_sub, show fderiv ℝ (vertical f) x v.val = 0 from v.property,
      show fderiv ℝ (vertical f) x w.val = 0 from w.property, sub_self]) (by
    rw [map_sub, heq, sub_self])

section Parametrized

open scoped Manifold
variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace N] [ChartedSpace E N]

theorem generatingMap_mfderiv_injective {f : Q × W → ℝ} {j : N → Q × W} {x : N}
    (hf : ContDiffAt ℝ ∞ f (j x))
    (hj : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Q × W) ∞ j x)
    (hcrit : ∀ᶠ y in 𝓝 x, vertical f (j y) = 0)
    (hreg : Function.Surjective (fderiv ℝ (vertical f) (j x)))
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × W) j x)) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × (Q →L[ℝ] ℝ))
      (generatingMap f ∘ j) x) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (j x) :=
    (hf.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hv := (vertical_hasFDerivAt hdf).differentiableAt
  have hg := (generatingMap_hasFDerivAt hdf).differentiableAt
  have hjd := hj.mdifferentiableAt (by simp)
  have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, W →L[ℝ] ℝ) (vertical f ∘ j) x = 0 := by
    have he : (vertical f ∘ j) =ᶠ[𝓝 x] (fun _ : N => (0 : W →L[ℝ] ℝ)) := hcrit
    rw [he.mfderiv_eq]
    exact mfderiv_const (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, W →L[ℝ] ℝ))
      (x := x) (c := (0 : W →L[ℝ] ℝ))
  have hcompv := mfderiv_comp x hv.mdifferentiableAt hjd
  erw [mfderiv_eq_fderiv] at hcompv
  rw [hz] at hcompv
  have hker (a : TangentSpace 𝓘(ℝ, E) x) :
      fderiv ℝ (vertical f) (j x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × W) j x a) = 0 := by
    exact (congrArg (fun A : E →L[ℝ] W →L[ℝ] ℝ => A a) hcompv).symm
  have hcompg := mfderiv_comp x hg.mdifferentiableAt hjd
  erw [mfderiv_eq_fderiv] at hcompg
  intro a b hab
  apply hinj
  have ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × W) j x a ∈
      LinearMap.ker (fderiv ℝ (vertical f) (j x)).toLinearMap := hker a
  have hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × W) j x b ∈
      LinearMap.ker (fderiv ℝ (vertical f) (j x)).toLinearMap := hker b
  have he := generatingMap_ker_injective hf hreg (a₁ := ⟨_, ha⟩) (a₂ := ⟨_, hb⟩)
  apply congrArg Subtype.val (he ?_)
  erw [hcompg] at hab
  exact hab

theorem generatingMap_mfderiv_isotropic {f : Q × W → ℝ} {j : N → Q × W} {x : N}
    (hf : ContDiffAt ℝ ∞ f (j x))
    (hj : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Q × W) ∞ j x)
    (hcrit : ∀ᶠ y in 𝓝 x, vertical f (j y) = 0)
    (a b : TangentSpace 𝓘(ℝ, E) x) :
    localSymplectic
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × (Q →L[ℝ] ℝ)) (generatingMap f ∘ j) x a)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × (Q →L[ℝ] ℝ)) (generatingMap f ∘ j) x b) = 0 := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (j x) :=
    (hf.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hv := (vertical_hasFDerivAt hdf).differentiableAt
  have hg := (generatingMap_hasFDerivAt hdf).differentiableAt
  have hjd := hj.mdifferentiableAt (by simp)
  have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, W →L[ℝ] ℝ) (vertical f ∘ j) x = 0 := by
    have he : (vertical f ∘ j) =ᶠ[𝓝 x] (fun _ : N => (0 : W →L[ℝ] ℝ)) := hcrit
    rw [he.mfderiv_eq]
    exact mfderiv_const (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, W →L[ℝ] ℝ))
      (x := x) (c := (0 : W →L[ℝ] ℝ))
  have hcompv := mfderiv_comp x hv.mdifferentiableAt hjd
  erw [mfderiv_eq_fderiv] at hcompv
  rw [hz] at hcompv
  have hker (v : TangentSpace 𝓘(ℝ, E) x) :
      fderiv ℝ (vertical f) (j x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Q × W) j x v) = 0 := by
    exact (congrArg (fun A : E →L[ℝ] W →L[ℝ] ℝ => A v) hcompv).symm
  have hcompg := mfderiv_comp x hg.mdifferentiableAt hjd
  erw [mfderiv_eq_fderiv] at hcompg
  rw [hcompg]
  exact symplectic_eq_zero hf (hker a) (hker b)

end Parametrized

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem isotropic_of_exact_coordinates {q : S → Q} {p : S → Q →L[ℝ] ℝ}
    {f : S → ℝ} {x : S} (hq : ContDiffAt ℝ ∞ q x)
    (hp : DifferentiableAt ℝ p x) (hf : ContDiffAt ℝ ∞ f x)
    (hex : (fun y => (p y).comp (fderiv ℝ q y)) =ᶠ[𝓝 x] fderiv ℝ f)
    (v w : S) :
    fderiv ℝ p x v (fderiv ℝ q x w) - fderiv ℝ p x w (fderiv ℝ q x v) = 0 := by
  have hqd : DifferentiableAt ℝ (fderiv ℝ q) x :=
    (hq.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hde := hex.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_clm_comp hp hqd] at hde
  have h₁ := congrArg (fun A : S →L[ℝ] (S →L[ℝ] ℝ) => A v w) hde
  have h₂ := congrArg (fun A : S →L[ℝ] (S →L[ℝ] ℝ) => A w v) hde
  change p x (fderiv ℝ (fderiv ℝ q) x v w) +
    fderiv ℝ p x v (fderiv ℝ q x w) = fderiv ℝ (fderiv ℝ f) x v w at h₁
  change p x (fderiv ℝ (fderiv ℝ q) x w v) +
    fderiv ℝ p x w (fderiv ℝ q x v) = fderiv ℝ (fderiv ℝ f) x w v at h₂
  have hqs := (hq.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)).eq v w
  have hfs := (hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)).eq v w
  rw [hqs, hfs] at h₁
  linarith

end NearbyLagrangian.Generating

end

end OAI
