import OAI.Analysis.BoundedHochschild.PositiveKernelSpace

namespace OAI

/-! Transport of finite kernel vectors and the corresponding bounded maps
on their pre-Hilbert spaces. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

lemma kernelForm_mapDomain_left (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) y = kernelForm (fun i j => K (f i) j) x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_mapDomain_index]
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_mapDomain_right (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K x (Finsupp.mapDomain f y) = kernelForm (fun i j => K i (f j)) x y := by
  classical
  unfold kernelForm
  apply Finsupp.sum_congr
  intro i hi
  rw [Finsupp.sum_mapDomain_index]
  · intro j
    simp
  · intro j a b
    exact mul_add _ _ _

lemma kernelForm_mapDomain (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f y) =
      kernelForm (fun i j => K (f i) (f j)) x y := by
  rw [kernelForm_mapDomain_left]
  exact kernelForm_mapDomain_right (K := (fun i j => K (f i) j)) f x y

lemma kernelPre_norm_sq (K : Matrix I I ℂ) (hK : K.PosSemidef)
    (x : PositiveKernelPreSpace K hK) : ‖x‖ ^ 2 = (kernelForm K x x).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) x

/-- A map of labels bounded for the kernel quadratic form induces a bounded
linear map on the finite kernel vectors. -/
def kernelPreMap (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) :
    PositiveKernelPreSpace K hK →L[ℂ] PositiveKernelPreSpace K hK :=
  let L : PositiveKernelPreSpace K hK →ₗ[ℂ] PositiveKernelPreSpace K hK :=
    { toFun := Finsupp.mapDomain f
      map_add' _ _ := Finsupp.mapDomain_add
      map_smul' r x := Finsupp.mapDomain_smul r x }
  L.mkContinuous C (fun x => by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    rw [mul_pow, kernelPre_norm_sq K hK, kernelPre_norm_sq K hK]
    change (kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f x)).re ≤
      C ^ 2 * (kernelForm K x x).re
    exact (congrArg Complex.re (kernelForm_mapDomain K f
      (show I →₀ ℂ from x) (show I →₀ ℂ from x))).trans_le (hf x))

@[simp] lemma kernelPreMap_apply (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) (x : PositiveKernelPreSpace K hK) :
    kernelPreMap K hK f C hC hf x = Finsupp.mapDomain f x := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
