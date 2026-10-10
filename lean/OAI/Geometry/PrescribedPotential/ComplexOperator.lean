import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalPartition
import OAI.Geometry.PrescribedPotential.GlobalOperator

namespace OAI

/-! Complex Operator. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel FrozenPoisson
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_postcomp {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (p : ℂ →L[ℝ] ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (p ∘ f)) x v w = p (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hN : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [(hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have he : fderiv ℝ (p ∘ f) =ᶠ[𝓝 x] (fun y => p.comp (fderiv ℝ f y)) := by
    filter_upwards [hN] with y hy
    exact (p.hasFDerivAt.comp y hy.hasFDerivAt).fderiv
  rw [he.fderiv_eq, fderiv_clm_comp (differentiableAt_const p)
    ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
  simp

lemma second_add {f h : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hh : ContDiffAt ℝ ∞ h x) :
    fderiv ℝ (fderiv ℝ (fun y => f y + h y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ h) x := by
  have hN (u : E → ℂ) (hu : ContDiffAt ℝ ∞ u x) :
      ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y := by
    filter_upwards [(hu.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have he : fderiv ℝ (fun y => f y + h y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y + fderiv ℝ h y) := by
    filter_upwards [hN f hf, hN h hh] with y hy hz
    exact fderiv_add hy hz
  rw [he.fderiv_eq]
  exact fderiv_add ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    ((hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))

lemma second_real_smul {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => c • f y)) x =
      c • fderiv ℝ (fderiv ℝ f) x := by
  have hN : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [(hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have he : fderiv ℝ (fun y => c • f y) =ᶠ[𝓝 x]
      (fun y => c • fderiv ℝ f y) := by
    filter_upwards [hN] with y hy
    exact fderiv_const_smul hy c
  rw [he.fderiv_eq]
  exact fderiv_const_smul ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)) c

variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 
def Smooth.part (f : Smooth A) (p : ℂ →L[ℝ] ℝ) : SmoothRealFunction A where
  value x := p (f x)
  smooth i := by
    have hh := p.contDiff.comp_contDiffOn (f.smooth i)
    have hc := hh.comp (coordinateEquiv d).symm.contDiff.contDiffOn (by
      intro z hz
      simpa only [ComplexAtlas.euclideanChart_target, mem_preimage,
        ContinuousLinearEquiv.apply_symm_apply] using hz)
    convert hc using 1
    ext z
    simp only [Function.comp_apply, ComplexAtlas.euclideanChart_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]

@[simp] lemma Smooth.part_value (f : Smooth A) (p : ℂ →L[ℝ] ℝ) (x : X) :
    (f.part p).value x = p (f x) := rfl

 
def complexLValue (g : KaehlerMetric A) (f : Smooth A) : Smooth A :=
  Smooth.ofReal (g.laplacian (f.part Complex.reCLM)) +
    Smooth.mul (Smooth.const Complex.I) (Smooth.ofReal (g.laplacian (f.part Complex.imCLM)))

 
def localL (g : KaehlerMetric A) (i : Fin A.count) (f : EC d → ℂ) (y : EC d) : ℂ :=
  ∑ k, ∑ l, (traceBilin (g.matrix i (coordinateEquiv d y))
    (rankTwo (stdOrthonormalBasis ℝ (EC d) k) (stdOrthonormalBasis ℝ (EC d) l)) : ℂ) *
      fderiv ℝ (fderiv ℝ f) y (stdOrthonormalBasis ℝ (EC d) k) (stdOrthonormalBasis ℝ (EC d) l)

lemma part_laplacian (g : KaehlerMetric A) (f : Smooth A)
    (p : ℂ →L[ℝ] ℝ) (i : Fin A.count) {x : X} (hx : x ∈ (A.euclideanChart i).source) :
    (g.laplacian (f.part p)).value x =
      ∑ k, ∑ l, traceBilin (g.matrix i (coordinateEquiv d (A.euclideanChart i x)))
        (rankTwo (stdOrthonormalBasis ℝ (EC d) k) (stdOrthonormalBasis ℝ (EC d) l)) *
        p (fderiv ℝ (fderiv ℝ (f ∘ (A.euclideanChart i).symm))
          (A.euclideanChart i x) (stdOrthonormalBasis ℝ (EC d) k) (stdOrthonormalBasis ℝ (EC d) l)) := by
  have hxc : x ∈ (A.chart i).source := by simpa using hx
  change g.laplacianValue (f.part p) x = _
  rw [g.laplacianValue_local (f.part p) i hxc]
  have hy : coordinateEquiv d (A.euclideanChart i x) ∈ (A.chart i).target := by
    simpa only [ComplexAtlas.euclideanChart_apply, ContinuousLinearEquiv.apply_symm_apply]
      using (A.chart i).mapsTo hxc
  have ht := g.traceBilin_localExpression (f.part p) i hy
  rw [ComplexAtlas.euclideanChart_apply, ContinuousLinearEquiv.apply_symm_apply] at ht
  rw [← ht]
  rw [bilin_expansion (stdOrthonormalBasis ℝ (EC d))
    (fderiv ℝ (fderiv ℝ ((f.part p).localExpression i ∘ coordinateEquiv d))
      ((coordinateEquiv d).symm (A.chart i x))) ]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_comm]
  congr 1
  exact second_postcomp ((f.smooth i).contDiffAt
    ((A.euclideanChart i).open_target.mem_nhds ((A.euclideanChart i).mapsTo hx))) p _ _

lemma complexLValue_local (g : KaehlerMetric A) (f : Smooth A)
    (i : Fin A.count) {x : X} (hx : x ∈ (A.euclideanChart i).source) :
    complexLValue g f x = localL g i (f ∘ (A.euclideanChart i).symm) (A.euclideanChart i x) := by
  change ((g.laplacian (f.part Complex.reCLM)).value x : ℂ) +
    Complex.I * ((g.laplacian (f.part Complex.imCLM)).value x : ℂ) = _
  rw [part_laplacian g f Complex.reCLM i hx, part_laplacian g f Complex.imCLM i hx]
  simp only [localL, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Complex.reCLM_apply, Complex.imCLM_apply]
  rw [mul_left_comm Complex.I, ← mul_add, mul_comm Complex.I, Complex.re_add_im]

lemma localL_congr (g : KaehlerMetric A) (i : Fin A.count)
    {f h : EC d → ℂ} {x : EC d} (he : f =ᶠ[𝓝 x] h) :
    localL g i f x = localL g i h x := by
  simp only [localL, he.fderiv.fderiv_eq]

lemma complexLValue_add (g : KaehlerMetric A) (f h : Smooth A) :
    complexLValue g (f + h) = complexLValue g f + complexLValue g h := by
  apply Smooth.ext
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  have hx : x ∈ (A.euclideanChart i).source := by simpa using hi
  simp only [Smooth.add_apply, complexLValue_local g _ i hx, localL]
  have hf := (f.smooth i).contDiffAt ((A.euclideanChart i).open_target.mem_nhds
    ((A.euclideanChart i).mapsTo hx))
  have hh := (h.smooth i).contDiffAt ((A.euclideanChart i).open_target.mem_nhds
    ((A.euclideanChart i).mapsTo hx))
  rw [show ((f + h : Smooth A) ∘ (A.euclideanChart i).symm) =
    (fun y => (f ∘ (A.euclideanChart i).symm) y + (h ∘ (A.euclideanChart i).symm) y) from rfl,
    second_add hf hh]
  simp only [add_apply, mul_add, Finset.sum_add_distrib]

lemma complexLValue_smul (g : KaehlerMetric A) (c : ℝ) (f : Smooth A) :
    complexLValue g (c • f) = c • complexLValue g f := by
  apply Smooth.ext
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  have hx : x ∈ (A.euclideanChart i).source := by simpa using hi
  simp only [Smooth.smul_apply, complexLValue_local g _ i hx, localL]
  have hf := (f.smooth i).contDiffAt ((A.euclideanChart i).open_target.mem_nhds
    ((A.euclideanChart i).mapsTo hx))
  rw [show ((c • f : Smooth A) ∘ (A.euclideanChart i).symm) =
    (fun y => c • (f ∘ (A.euclideanChart i).symm) y) from rfl,
    second_real_smul hf c]
  simp only [smul_apply, mul_smul_comm, Finset.smul_sum]

 
def complexL (g : KaehlerMetric A) : Smooth A →ₗ[ℝ] Smooth A where
  toFun := complexLValue g
  map_add' := complexLValue_add g
  map_smul' := complexLValue_smul g

lemma complexL_tsupport (g : KaehlerMetric A) (f : Smooth A) :
    tsupport (complexL g f : X → ℂ) ⊆ tsupport (f : X → ℂ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  obtain ⟨i, hi⟩ := A.covers x
  let e := A.euclideanChart i
  have he : x ∈ e.source := by simpa [e] using hi
  have hzero : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨(tsupport (f : X → ℂ))ᶜ, (isClosed_tsupport _).isOpen_compl.mem_nhds hn,
        fun y hy => image_eq_zero_of_notMem_tsupport hy⟩
  have hz : (f ∘ e.symm) =ᶠ[𝓝 (e x)] (fun _ => 0) := by
    have hc := (e.symm.continuousAt (e.mapsTo he)).tendsto
    rw [e.left_inv he] at hc
    exact hc.eventually hzero
  have hv := complexLValue_local g f i he
  change complexLValue g f x ≠ 0 at hx
  rw [hv, localL_congr g i hz] at hx
  exact hx (by simp [localL])

end GlobalElliptic

end
end

end OAI
