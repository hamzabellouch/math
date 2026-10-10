import OAI.Analysis.NumericalRange.DilationDensity

namespace OAI

noncomputable section


universe u_215 u_216 u_217 u_218 u_219 u_220 u_221 u_222 u_223 u_224 u_225 u_226 u_227 u_228 u_229 u_230 u_231 u_232 u_233 u_234 u_235 u_236 u_237 u_238 u_239 u_240

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real
namespace CompleteCrouzeix

-- Preserve this module's exported namespaces.
namespace MarkovKernel
end MarkovKernel
namespace AnalyticBidiskKernel
end AnalyticBidiskKernel
namespace FourierResolution
end FourierResolution
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix

open MeasureTheory Set Metric Complex Filter
open scoped Topology
namespace CompleteCrouzeix

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


open MeasureTheory Set Metric Complex Filter
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
namespace CompleteCrouzeix
open MeasureTheory Set Metric Complex ComplexConjugate
open scoped Topology Real
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix

open scoped ComplexConjugate InnerProductSpace

namespace CompleteCrouzeix

section

section

section
open scoped lp
variable {ι : Type u_220} {E : Type u_221} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
end

open MeasureTheory ComplexConjugate
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Complex
open scoped Topology InnerProductSpace ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Complex
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix

open Set Metric Filter Complex
open scoped Topology

namespace CompleteCrouzeix

section
open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Metric Complex
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix


open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology
namespace CompleteCrouzeix
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix

open Set Filter Metric Complex
open scoped Topology

namespace CompleteCrouzeix

section

section
open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix


open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator


namespace CompleteCrouzeix

section
open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {m : Type u_230} [Fintype m] [DecidableEq m]

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {ι : Type u_232} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {ι : Type u_233} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)


end CompleteCrouzeix

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open MeasureTheory

namespace CompleteCrouzeix

section
open MeasureTheory
open scoped Matrix.Norms.L2Operator Kronecker ComplexConjugate InnerProductSpace
variable {T : Type u_236} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_237} {m : Type u_238} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def toHSCLM : Matrix m m ℂ →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun := toHS
    map_add' := by intros; ext ⟨i,j⟩; rfl
    map_smul' := by intros; ext ⟨i,j⟩; rfl }

def fromHSCLM : HSMatrix m →L[ℂ] Matrix m m ℂ :=
  LinearMap.toContinuousLinearMap
  { toFun := fromHS
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def densityField (L : C(T,Matrix n n ℂ)) (X Y : Matrix n m ℂ) :
    Lp (HSMatrix m) 2 μ :=
  ContinuousMap.toLp 2 μ ℂ
    ⟨fun t => toHS (weightedDensity (L t) X Y),
      toHSCLM.continuous.comp (continuous_weightedDensity L.continuous X Y)⟩

lemma densityField_ae (L : C(T,Matrix n n ℂ)) (X Y : Matrix n m ℂ) :
    densityField (μ := μ) L X Y =ᵐ[μ]
      fun t => toHS (weightedDensity (L t) X Y) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ _

lemma densityField_hermitian (L : C(T,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (X : Matrix n m ℂ) : l2Star (densityField (μ := μ) L X X) = densityField L X X := by
  apply hermitian_l2Star
  filter_upwards [densityField_ae (μ := μ) L X X] with t ht
  rw [ht,fromHS_toHS]
  exact (show _ = _ from by rw [weightedDensity_star,(hL t).eq])

lemma densityField_inner_continuous (L : C(T,Matrix n n ℂ))
    (hL : ∀ t, (L t).IsHermitian) (X Y : Matrix n m ℂ)
    (u : C(T,Matrix m m ℂ)) :
    inner ℂ (densityField (μ := μ) L X Y)
      (ContinuousMap.toLp 2 μ ℂ ⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩) =
      ∫ t, inner ℂ (vectorize Y)
        (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (L t ⊗ₖ u t) (vectorize X)) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [densityField_ae (μ := μ) L X Y,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ
      (⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩ : C(T,HSMatrix m))] with t ht hu
  rw [ht,hu]
  change inner ℂ (toHS (weightedDensity (L t) X Y)) (toHS (u t)) = _
  rw [hs_inner,weightedDensity_testing (hL t)]

def tensorTesting (X Y : Matrix n m ℂ) : Matrix (n × m) (n × m) ℂ →L[ℂ] ℂ :=
  (innerSL ℂ (vectorize Y)).comp
    ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (n × m)) (vectorize X)).comp
      (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.toContinuousLinearMap)

lemma densityField_testing (L : C(T,Matrix n n ℂ))
    (hL : ∀ t, (L t).IsHermitian) (X Y : Matrix n m ℂ)
    (u : C(T,Matrix m m ℂ)) :
    inner ℂ (densityField (μ := μ) L X Y)
      (ContinuousMap.toLp 2 μ ℂ ⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩) =
      tensorTesting X Y (∫ t, L t ⊗ₖ u t ∂μ) := by
  rw [densityField_inner_continuous L hL X Y u]
  have hc : Continuous (fun t => L t ⊗ₖ u t) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun t => L t i.1 j.1 * u t i.2 j.2)
    fun_prop
  have hi : Integrable (fun t => L t ⊗ₖ u t) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ t, tensorTesting X Y (L t ⊗ₖ u t) ∂μ) = _
  exact (tensorTesting X Y).integral_comp_comm hi

end

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate Matrix.Norms.L2Operator Kronecker
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {m : Type u_239} {n : Type u_240} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def hsTraceLp (u : C(UnitAddCircle,Matrix m m ℂ)) : MatrixCircleL2 (m := m) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    ⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩

lemma hsTraceLp_ae
    {m : Type u_239} [Fintype m] [DecidableEq m] (u : C(UnitAddCircle,Matrix m m ℂ)) :
    hsTraceLp u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (u t) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle _

lemma hsTraceLp_star (u : C(UnitAddCircle,Matrix m m ℂ)) :
    l2Star (hsTraceLp u) = hsTraceLp ⟨fun t => (u t)ᴴ,by fun_prop⟩ := by
  apply Lp.ext
  filter_upwards [l2StarL_ae (hsTraceLp u),hsTraceLp_ae u,
    hsTraceLp_ae (⟨fun t => (u t)ᴴ,by fun_prop⟩ : C(UnitAddCircle,Matrix m m ℂ))]
    with t ht hu hv
  change l2StarL (hsTraceLp u) t = _
  rw [ht,hu,hv]
  rfl

lemma matrixInner_ext_fourier {u v : MatrixCircleL2 (m := m)}
    (h : ∀ (ij : m × m) (k : ℤ),
      inner ℂ u (l2Embedding ij (fourierLp 2 k)) =
        inner ℂ v (l2Embedding ij (fourierLp 2 k))) : u = v := by
  apply l2Coordinate_injective
  intro ij
  have he : innerSL ℂ (l2Coordinate ij u) = innerSL ℂ (l2Coordinate ij v) := by
    apply circleCLM_ext
    intro k
    simpa only [innerSL_apply_apply,coordinate_inner] using h ij k
  exact innerSL_inj.mp he

def matrixFourierTrace (ij : m × m) (k : ℤ) : C(UnitAddCircle,Matrix m m ℂ) :=
  ⟨fun t => Matrix.single ij.1 ij.2 (fourier k t),by
    apply continuous_matrix
    intro i j
    simp only [Matrix.single_apply]
    split_ifs <;> fun_prop⟩

lemma hsTraceLp_matrixFourierTrace (ij : m × m) (k : ℤ) :
    hsTraceLp (matrixFourierTrace ij k) = l2Embedding ij (fourierLp 2 k) := by
  apply Lp.ext
  filter_upwards [hsTraceLp_ae (matrixFourierTrace ij k),
    l2Embedding_ae ij (fourierLp (T := 1) 2 k),coeFn_fourierLp (T := 1) 2 k]
    with t hu hv hk
  rw [hu,hv,hk]
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [toHS,matrixFourierTrace,ContinuousMap.coe_mk,
    Matrix.single_apply,PiLp.single_apply]
  rcases ij with ⟨i',j'⟩
  simp only [Prod.mk.injEq,eq_comm]

lemma densityInner_ext_fourier {u v : MatrixCircleL2 (m := m)}
    (h : ∀ (ij : m × m) (k : ℤ),
      inner ℂ u (hsTraceLp (matrixFourierTrace ij k)) =
        inner ℂ v (hsTraceLp (matrixFourierTrace ij k))) : u = v :=
  matrixInner_ext_fourier (by simpa only [hsTraceLp_matrixFourierTrace] using h)

lemma l2Star_inner (u v : MatrixCircleL2 (m := m)) :
    inner ℂ (l2Star u) (l2Star v) = conj (inner ℂ u v) := by
  rw [inner_conj_symm]
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2StarL_ae u,l2StarL_ae v] with t hu hv
  change inner ℂ (l2StarL u t) (l2StarL v t) = _
  rw [hu,hv,hsStar_apply,hsStar_apply]
  conv_rhs => rw [← toHS_fromHS (v t),← toHS_fromHS (u t)]
  rw [hs_inner,hs_inner,Matrix.conjTranspose_conjTranspose,Matrix.trace_mul_comm]

theorem density_adjoint_identification (C : MatrixCircleL2 (m := m) →L[ℂ] _)
    (p e : MatrixCircleL2 (m := m)) (a b : ℝ)
    (htest : ∀ ij k,
      inner ℂ e (hsTraceLp (matrixFourierTrace ij k)) =
        (a:ℂ)*inner ℂ p (C (hsTraceLp (matrixFourierTrace ij k))) +
        (b:ℂ)*conj (inner ℂ (l2Star p) (C (l2Star (hsTraceLp (matrixFourierTrace ij k)))))) :
    e = (a:ℂ) • C.adjoint p + (b:ℂ) • l2Star (C.adjoint (l2Star p)) := by
  apply densityInner_ext_fourier
  intro ij k
  rw [htest]
  simp only [inner_add_left,inner_smul_left,Complex.conj_ofReal,
    ContinuousLinearMap.adjoint_inner_left]
  congr 1
  have hj := l2Star_inner (C.adjoint (l2Star p))
    (l2Star (hsTraceLp (matrixFourierTrace ij k)))
  have he : l2Star (l2Star (hsTraceLp (matrixFourierTrace ij k))) =
      hsTraceLp (matrixFourierTrace ij k) := l2StarL_involutive _
  rw [he,ContinuousLinearMap.adjoint_inner_left] at hj
  exact congrArg (fun z : ℂ => (b:ℂ)*z) hj.symm

end CompleteCrouzeix

end

end OAI
