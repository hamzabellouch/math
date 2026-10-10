import OAI.Analysis.RotationWeights.Fibers

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE uι uκ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def pureL2 (f : Lp ℂ 2 μ) (u : E) : Lp E 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℂ u).compLp f

lemma pureL2_coe (f : Lp ℂ 2 μ) (u : E) :
    pureL2 μ f u =ᵐ[μ] fun x ↦ f x • u :=
  (ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp f

lemma pureL2_inner (f g : Lp ℂ 2 μ) (u v : E) :
    inner ℂ (pureL2 μ f u) (pureL2 μ g v) = inner ℂ f g * inner ℂ u v := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [pureL2_coe μ f u,pureL2_coe μ g v] with x h1 h2
  rw [h1,h2,inner_smul_left,inner_smul_right]
  simp only [RCLike.inner_apply, mul_assoc, mul_comm (g x)]

def coordinateL2 (u : E) : Lp E 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (innerSL ℂ u).compLpL 2 μ

lemma coordinateL2_coe (u : E) (g : Lp E 2 μ) :
    coordinateL2 μ u g =ᵐ[μ] fun x ↦ inner ℂ u (g x) :=
  (innerSL ℂ u).coeFn_compLpL g

lemma pureL2_inner_coordinate (f : Lp ℂ 2 μ) (u : E) (g : Lp E 2 μ) :
    inner ℂ (pureL2 μ f u) g = inner ℂ f (coordinateL2 μ u g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pureL2_coe μ f u,coordinateL2_coe μ u g] with x h1 h2
  rw [h1,h2,inner_smul_left]
  simp only [RCLike.inner_apply,mul_comm]

variable {ι : Type uι} {κ : Type uκ}

lemma hilbertBasis_ext (b : HilbertBasis ι ℂ E) {u v : E}
    (h : ∀ i, inner ℂ (b i) u = inner ℂ (b i) v) : u=v := by
  apply b.repr.injective
  ext i
  simpa only [b.repr_apply_apply] using h i

lemma orthonormal_pureL2 (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) :
    Orthonormal ℂ (fun z : ι × κ ↦ pureL2 μ (c z.2) (b z.1)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [pureL2_inner,orthonormal_iff_ite.mp c.orthonormal,
    orthonormal_iff_ite.mp b.orthonormal]
  by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;> simp [h1,h2,Prod.ext_iff]

lemma pureL2_orthogonal_eq_bot [Countable ι] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) :
    (span ℂ (range (fun z : ι × κ ↦ pureL2 μ (c z.2) (b z.1))))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  have hcoord (a : ι) : coordinateL2 μ (b a) f = 0 := by
    apply hilbertBasis_ext c
    intro n
    rw [inner_zero_right,← pureL2_inner_coordinate]
    exact (mem_orthogonal _ _).mp hf _ (subset_span ⟨(a,n),rfl⟩)
  have hh : ∀ᵐ x ∂μ, ∀ a : ι, inner ℂ (b a) (f x) = 0 := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [coordinateL2_coe μ (b a) f,Lp.coeFn_zero ℂ 2 μ] with x h1 h2
    rw [hcoord a,h2] at h1
    exact h1.symm
  have he : f=0 := by
    apply Lp.ext
    filter_upwards [hh,Lp.coeFn_zero E 2 μ] with x hx hz
    rw [hz]
    apply hilbertBasis_ext b
    intro a
    simpa only [Pi.zero_apply,inner_zero_right] using hx a
  simp only [he,zero_mem]

variable [CompleteSpace E]

def tensorL2Basis [Countable ι] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) : HilbertBasis (ι×κ) ℂ (Lp E 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_pureL2 μ b c) (pureL2_orthogonal_eq_bot μ b c)

@[simp] lemma tensorL2Basis_apply [Countable ι] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) (z : ι×κ) :
    tensorL2Basis μ b c z = pureL2 μ (c z.2) (b z.1) := by
  simp only [tensorL2Basis,HilbertBasis.coe_mkOfOrthogonalEqBot]
end

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma aestronglyMeasurable_field_simple (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ) (s : SimpleFunc X E) :
    AEStronglyMeasurable (fun x ↦ T x (s x)) μ := by
  classical
  have he : (fun x ↦ T x (s x)) =
      ∑ a ∈ s.range, (s ⁻¹' {a}).indicator (fun x ↦ T x a) := by
    funext x
    simp [Set.indicator, s.mem_range_self]
  rw [he]
  exact s.range.aestronglyMeasurable_sum fun a _ ↦ (hT a).indicator (s.measurableSet_fiber a)

lemma aestronglyMeasurable_field_apply (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (f : X → E) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x ↦ T x (f x)) μ := by
  let f₀ := hf.mk f
  have hf₀ : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  have hm : AEStronglyMeasurable (fun x ↦ T x (f₀ x)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ aestronglyMeasurable_field_simple μ T hT (hf₀.approx n))
    exact Eventually.of_forall fun x ↦ ((T x).continuous.tendsto (f₀ x)).comp
      (hf₀.tendsto_approx x)
  apply hm.congr
  exact hf.ae_eq_mk.symm.mono fun x hx ↦ congrArg (T x) hx

lemma bounded_field_memL2 (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    MemLp (fun x ↦ T x (f x)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (aestronglyMeasurable_field_apply μ T hT f (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with x hx
  exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def fieldMulL2 (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (bounded_field_memL2 μ T hT C hC f).toLp (fun x ↦ T x (f x))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(bounded_field_memL2 μ T hT C hC (f+g)).coeFn_toLp,
          (bounded_field_memL2 μ T hT C hC f).coeFn_toLp,
          (bounded_field_memL2 μ T hT C hC g).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add ((bounded_field_memL2 μ T hT C hC f).toLp _)
            ((bounded_field_memL2 μ T hT C hC g).toLp _)] with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4 h5
        rw [h1,h5,h2,h3,h4,map_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(bounded_field_memL2 μ T hT C hC (c•f)).coeFn_toLp,
          (bounded_field_memL2 μ T hT C hC f).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((bounded_field_memL2 μ T hT C hC f).toLp _)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply] at h3 h4
        simp only [RingHom.id_apply]
        rw [h1,h4,h2,h3,map_smul] }
    C (by
      intro f
      change ‖(bounded_field_memL2 μ T hT C hC f).toLp _‖ ≤ C*‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(bounded_field_memL2 μ T hT C hC f).coeFn_toLp,hC] with x hx hc
      rw [hx]
      exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _)))

lemma fieldMulL2_coe (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    fieldMulL2 μ T hT C hC f =ᵐ[μ] fun x ↦ T x (f x) :=
  (bounded_field_memL2 μ T hT C hC f).coeFn_toLp

lemma fieldMulL2_norm_le (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (hC0 : 0 ≤ C) :
    ‖fieldMulL2 μ T hT C hC‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC0
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldMulL2_coe μ T hT C hC f,hC] with x hx hc
  rw [hx]
  exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))


end ContinuousCircleWeight

end

end OAI
