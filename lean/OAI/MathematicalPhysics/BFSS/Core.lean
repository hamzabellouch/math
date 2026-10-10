import Mathlib

namespace OAI

/-! The full-space Hilbert model, exact smooth supercharges and closure of the joint graph. -/

namespace BFSSQuantum
noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate

abbrev colorDim (N : ℕ) : ℕ := N ^ 2 - 1
abbrev ColorIndex (N : ℕ) := Fin (colorDim N)
abbrev SpaceIndex := Fin 9
abbrev SpinIndex := Fin 16
abbrev Boson (N : ℕ) := EuclideanSpace ℝ (SpaceIndex × ColorIndex N)
abbrev Fermion (N : ℕ) := EuclideanSpace ℂ (Fin (2 ^ (8 * colorDim N)))
abbrev ColorMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℂ
abbrev GammaMatrix := Matrix SpinIndex SpinIndex ℝ
abbrev GaugeGroup (N : ℕ) := Matrix.specialUnitaryGroup (Fin N) ℂ
abbrev FullL2 (N : ℕ) := Lp (Fermion N) 2 (volume : Measure (Boson N))
abbrev SmoothCore (N : ℕ) := TestFunction (⊤ : TopologicalSpace.Opens (Boson N)) (Fermion N) ⊤

structure AlgebraData (N : ℕ) where
  color : ColorIndex N → ColorMatrix N
  color_hermitian : ∀ A, (color A).IsHermitian
  color_traceless : ∀ A, Matrix.trace (color A) = 0
  color_orthonormal : ∀ A B, Matrix.trace (color A * color B) = if A = B then 1 else 0
  color_spanning : ∀ x : ColorMatrix N, x.IsHermitian → Matrix.trace x = 0 →
    ∃ a : ColorIndex N → ℝ, x = ∑ A, (a A : ℂ) • color A
  gamma : SpaceIndex → GammaMatrix
  gamma_symmetric : ∀ i, (gamma i).IsSymm
  gamma_clifford : ∀ i j, gamma i * gamma j + gamma j * gamma i =
    (if i = j then 2 else 0) • (1 : GammaMatrix)
  theta : SpinIndex → ColorIndex N → (Fermion N →L[ℂ] Fermion N)
  theta_selfAdjoint : ∀ α A, IsSelfAdjoint (theta α A)
  theta_CAR : ∀ α β A B, theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then 1 else 0) • (1 : Fermion N →L[ℂ] Fermion N)
  theta_irreducible : ∀ W : Submodule ℂ (Fermion N),
    (∀ α A, ∀ w ∈ W, theta α A w ∈ W) → W = ⊥ ∨ W = ⊤

namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)

def bracket (x y : ColorMatrix N) : ColorMatrix N :=
  (-Complex.I) • (x * y - y * x)

def structureConstant (A B C : ColorIndex N) : ℝ :=
  (Matrix.trace (M.color A * bracket (M.color B) (M.color C))).re

def gammaTwo (i j : SpaceIndex) : GammaMatrix :=
  (1 / 2 : ℝ) • (M.gamma i * M.gamma j - M.gamma j * M.gamma i)

def polarization : GammaMatrix := M.gamma 0 * M.gamma 1 * M.gamma 2

def smoothMultiplier (g : Boson N → ℂ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    SmoothCore N →ₗ[ℂ] SmoothCore N where
  toFun f := {
    toFun := fun x => g x • f x
    contDiff' := hg.smul f.contDiff
    hasCompactSupport' := by
      change HasCompactSupport (g • (f : Boson N → Fermion N))
      exact HasCompactSupport.smul_left (f := g) f.hasCompactSupport
    tsupport_subset' := by intro x hx; trivial
  }
  map_add' f k := by
    apply DFunLike.ext
    intro x
    change g x • (f x + k x) = g x • f x + g x • k x
    exact smul_add _ _ _
  map_smul' c f := by
    apply DFunLike.ext
    intro x
    change g x • (c • f x) = c • (g x • f x)
    exact smul_comm _ _ _

def coordinateDerivative (i : SpaceIndex) (A : ColorIndex N) : SmoothCore N →ₗ[ℂ] SmoothCore N :=
  (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single (i, A) 1)).toLinearMap

def coordinate (i : SpaceIndex) (A : ColorIndex N) : Boson N → ℝ := fun x => x (i, A)

lemma coordinate_contDiff (i : SpaceIndex) (A : ColorIndex N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coordinate i A) := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) (i, A)).contDiff

def position (i : SpaceIndex) (A : ColorIndex N) : SmoothCore N →ₗ[ℂ] SmoothCore N :=
  smoothMultiplier (fun x => (coordinate i A x : ℂ))
    (Complex.ofRealCLM.contDiff.comp (coordinate_contDiff i A))

def fermionAction (α : SpinIndex) (A : ColorIndex N) : SmoothCore N →ₗ[ℂ] SmoothCore N :=
  (TestFunction.postcompCLM (M.theta α A)).toLinearMap

def charge (α : SpinIndex) : SmoothCore N →ₗ[ℂ] SmoothCore N :=
  (∑ i : SpaceIndex, ∑ A : ColorIndex N, ∑ β : SpinIndex,
    (-Complex.I * (M.gamma i α β : ℂ)) •
      ((M.fermionAction β A).comp (coordinateDerivative i A))) +
  ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
    ∑ B : ColorIndex N, ∑ C : ColorIndex N, ∑ β : SpinIndex,
    (((1 / 2 : ℝ) * M.structureConstant A B C * M.gammaTwo i j α β : ℝ) : ℂ) •
      ((M.fermionAction β A).comp ((position i B).comp (position j C)))

def coreToL2 : SmoothCore N →ₗ[ℂ] FullL2 N where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := MeasureTheory.MemLp.toLp_add _ _
  map_smul' scalar _ := MeasureTheory.MemLp.toLp_const_smul scalar _

def chargeVector : SmoothCore N →ₗ[ℂ] (SpinIndex → FullL2 N) :=
  LinearMap.pi fun α => coreToL2.comp (M.charge α)

def coreForm (f : SmoothCore N) : ℝ :=
  (1 / 16 : ℝ) * ∑ α : SpinIndex, ‖coreToL2 (M.charge α f)‖ ^ 2

lemma coreForm_nonneg (f : SmoothCore N) : 0 ≤ M.coreForm f := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma coreToL2_ae (f : SmoothCore N) :
    (coreToL2 f : Boson N → Fermion N) =ᵐ[volume] f :=
  MemLp.coeFn_toLp (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

lemma coreToL2_inner (f g : SmoothCore N) :
    inner ℂ (coreToL2 f) (coreToL2 g) = ∫ x, inner ℂ (f x) (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coreToL2_ae f, coreToL2_ae g] with x hf hg
  rw [hf, hg]

lemma coreToL2_dense : DenseRange (coreToL2 (N := N)) := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Boson N)))
    (F := Fermion N) (p := 2) (by norm_num)).mono
  rintro f ⟨g, hfg, hgc, hgd⟩
  let k : SmoothCore N := ⟨g, hgd, hgc, by intro x hx; trivial⟩
  refine ⟨k, Lp.ext ?_⟩
  exact (coreToL2_ae k).trans hfg.symm

lemma coreInner_integrable (f g : SmoothCore N) :
    Integrable (fun x => inner ℂ (f x) (g x)) (volume : Measure (Boson N)) :=
  (f.continuous.inner g.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp₂_left g.hasCompactSupport (by simp))

private def innerRealLinear : Fermion N →ₗ[ℝ] Fermion N →ₗ[ℝ] ℂ where
  toFun f := (innerSL ℂ f).toLinearMap.restrictScalars ℝ
  map_add' f g := by ext x; simp
  map_smul' c f := by
    ext x
    change inner ℂ (c • f) x = c • inner ℂ f x
    exact inner_smul_left_eq_smul f x c

private def innerRealBilin : Fermion N →L[ℝ] Fermion N →L[ℝ] ℂ :=
  LinearMap.mkContinuous₂ innerRealLinear 1 (by
    intro f g
    change ‖inner ℂ f g‖ ≤ 1 * ‖f‖ * ‖g‖
    simpa using norm_inner_le_norm f g)

lemma coordinateDerivative_apply (i : SpaceIndex) (A : ColorIndex N)
    (f : SmoothCore N) (x : Boson N) :
    coordinateDerivative i A f x =
      fderiv ℝ (f : Boson N → Fermion N) x (EuclideanSpace.single (i, A) 1) := by
  change (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single (i, A) 1) f) x = _
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (f.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv

lemma coordinateDerivative_skew (i : SpaceIndex) (A : ColorIndex N)
    (f g : SmoothCore N) :
    inner ℂ (coreToL2 f) (coreToL2 (coordinateDerivative i A g)) =
      - inner ℂ (coreToL2 (coordinateDerivative i A f)) (coreToL2 g) := by
  rw [coreToL2_inner, coreToL2_inner]
  have h1 := coreInner_integrable (coordinateDerivative i A f) g
  have h2 := coreInner_integrable f (coordinateDerivative i A g)
  simp only [coordinateDerivative_apply] at h1 h2 ⊢
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerRealBilin) h1 h2 (coreInner_integrable f g)
    (fun x hx => (f.contDiff.differentiable (by simp)).differentiableAt)
    (fun x hx => (g.contDiff.differentiable (by simp)).differentiableAt)

def CoreSymmetric (A : SmoothCore N →ₗ[ℂ] SmoothCore N) : Prop :=
  ∀ f g, inner ℂ (coreToL2 (A f)) (coreToL2 g) =
    inner ℂ (coreToL2 f) (coreToL2 (A g))

lemma coreSymmetric_add {A B : SmoothCore N →ₗ[ℂ] SmoothCore N}
    (hA : CoreSymmetric A) (hB : CoreSymmetric B) : CoreSymmetric (A + B) := by
  intro f g
  simpa only [LinearMap.add_apply, map_add, inner_add_left, inner_add_right] using
    congrArg₂ (· + ·) (hA f g) (hB f g)

lemma coreSymmetric_real_smul {A : SmoothCore N →ₗ[ℂ] SmoothCore N}
    (hA : CoreSymmetric A) (r : ℝ) : CoreSymmetric ((r : ℂ) • A) := by
  intro f g
  simp only [LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [hA f g]

lemma coreSymmetric_sum {ι : Type*} (s : Finset ι)
    (A : ι → SmoothCore N →ₗ[ℂ] SmoothCore N) (hA : ∀ i ∈ s, CoreSymmetric (A i)) :
    CoreSymmetric (∑ i ∈ s, A i) := by
  intro f g
  simp only [LinearMap.sum_apply, map_sum, inner_sum, sum_inner]
  exact Finset.sum_congr rfl fun i hi => hA i hi f g

lemma coreSymmetric_comp {A B : SmoothCore N →ₗ[ℂ] SmoothCore N}
    (hA : CoreSymmetric A) (hB : CoreSymmetric B) (hAB : A.comp B = B.comp A) :
    CoreSymmetric (A.comp B) := by
  intro f g
  rw [LinearMap.comp_apply, hA, hB]
  congr 2
  exact (LinearMap.congr_fun hAB g).symm

lemma fermionAction_symmetric (α : SpinIndex) (A : ColorIndex N) :
    CoreSymmetric (M.fermionAction α A) := by
  intro f g
  rw [coreToL2_inner, coreToL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (M.theta_selfAdjoint α A).isSymmetric (f x) (g x)

lemma position_symmetric (i : SpaceIndex) (A : ColorIndex N) :
    CoreSymmetric (position i A) := by
  intro f g
  rw [coreToL2_inner, coreToL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  change inner ℂ ((coordinate i A x : ℂ) • f x) (g x) =
    inner ℂ (f x) ((coordinate i A x : ℂ) • g x)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

lemma momentum_symmetric (i : SpaceIndex) (A : ColorIndex N) :
    CoreSymmetric ((-Complex.I) • coordinateDerivative i A) := by
  intro f g
  simp only [LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right,
    map_neg, Complex.conj_I, neg_neg]
  have h := coordinateDerivative_skew i A f g
  rw [h]
  ring

lemma fermionAction_position_commute (α : SpinIndex) (A B : ColorIndex N)
    (i : SpaceIndex) :
    (M.fermionAction α A).comp (position i B) =
      (position i B).comp (M.fermionAction α A) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change M.theta α A ((coordinate i B x : ℂ) • f x) =
    (coordinate i B x : ℂ) • M.theta α A (f x)
  exact map_smul _ _ _

lemma position_commute (i j : SpaceIndex) (A B : ColorIndex N) :
    (position i A).comp (position j B) = (position j B).comp (position i A) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (coordinate i A x : ℂ) • ((coordinate j B x : ℂ) • f x) =
    (coordinate j B x : ℂ) • ((coordinate i A x : ℂ) • f x)
  exact smul_comm _ _ _

lemma fermionAction_derivative_commute (α : SpinIndex) (A B : ColorIndex N)
    (i : SpaceIndex) :
    (M.fermionAction α A).comp (coordinateDerivative i B) =
      (coordinateDerivative i B).comp (M.fermionAction α A) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  simp only [LinearMap.comp_apply, coordinateDerivative_apply]
  change M.theta α A (fderiv ℝ (f : Boson N → Fermion N) x
      (EuclideanSpace.single (i, B) 1)) =
    fderiv ℝ ((M.theta α A).restrictScalars ℝ ∘ (f : Boson N → Fermion N)) x
      (EuclideanSpace.single (i, B) 1)
  rw [fderiv_comp _ ((M.theta α A).restrictScalars ℝ).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

lemma kineticTerm_symmetric (i : SpaceIndex) (A : ColorIndex N) (α β : SpinIndex) :
    CoreSymmetric ((-Complex.I * (M.gamma i α β : ℂ)) •
      ((M.fermionAction β A).comp (coordinateDerivative i A))) := by
  have hcomm : (M.fermionAction β A).comp ((-Complex.I) • coordinateDerivative i A) =
      ((-Complex.I) • coordinateDerivative i A).comp (M.fermionAction β A) := by
    rw [LinearMap.comp_smul, LinearMap.smul_comp, M.fermionAction_derivative_commute]
  have h := coreSymmetric_real_smul
    (coreSymmetric_comp (M.fermionAction_symmetric β A)
      (momentum_symmetric i A) hcomm) (M.gamma i α β)
  simpa only [LinearMap.comp_smul, smul_smul, mul_comm (M.gamma i α β : ℂ)] using h

lemma potentialTerm_symmetric (i j : SpaceIndex) (A B C : ColorIndex N)
    (β : SpinIndex) :
    CoreSymmetric ((M.fermionAction β A).comp ((position i B).comp (position j C))) := by
  apply coreSymmetric_comp (M.fermionAction_symmetric β A)
    (coreSymmetric_comp (position_symmetric i B) (position_symmetric j C)
      (position_commute i j B C))
  rw [← LinearMap.comp_assoc, M.fermionAction_position_commute,
    LinearMap.comp_assoc, M.fermionAction_position_commute, ← LinearMap.comp_assoc]

theorem charge_symmetric (α : SpinIndex) : CoreSymmetric (M.charge α) := by
  unfold charge
  apply coreSymmetric_add
  · apply coreSymmetric_sum
    intro i hi
    apply coreSymmetric_sum
    intro A hA
    apply coreSymmetric_sum
    intro β hβ
    exact M.kineticTerm_symmetric i A α β
  · apply coreSymmetric_sum
    intro i hi
    apply coreSymmetric_sum
    intro j hj
    apply coreSymmetric_sum
    intro A hA
    apply coreSymmetric_sum
    intro B hB
    apply coreSymmetric_sum
    intro C hC
    apply coreSymmetric_sum
    intro β hβ
    exact coreSymmetric_real_smul (M.potentialTerm_symmetric i j A B C β) _

def fullCoreGraph : Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  LinearMap.range (coreToL2.prod M.chargeVector)

def fullClosedGraph : Submodule ℂ (FullL2 N × (SpinIndex → FullL2 N)) :=
  M.fullCoreGraph.topologicalClosure

lemma fullClosedGraph_pairing {p : FullL2 N × (SpinIndex → FullL2 N)}
    (hp : p ∈ M.fullClosedGraph) (α : SpinIndex) (f : SmoothCore N) :
    inner ℂ (coreToL2 (M.charge α f)) p.1 = inner ℂ (coreToL2 f) (p.2 α) := by
  let S : Set (FullL2 N × (SpinIndex → FullL2 N)) :=
    {p | inner ℂ (coreToL2 (M.charge α f)) p.1 = inner ℂ (coreToL2 f) (p.2 α)}
  have hc : IsClosed S := isClosed_eq
    (continuous_const.inner continuous_fst)
    (continuous_const.inner ((continuous_apply α).comp continuous_snd))
  have hs : (M.fullCoreGraph : Set _) ⊆ S := by
    rintro p ⟨g, rfl⟩
    exact M.charge_symmetric α f g
  exact closure_minimal hs hc hp

theorem fullClosedGraph_vertical {y : SpinIndex → FullL2 N}
    (hy : ((0 : FullL2 N), y) ∈ M.fullClosedGraph) : y = 0 := by
  funext α
  apply coreToL2_dense.eq_zero_of_inner_right (𝕜 := ℂ)
  intro f
  have h := M.fullClosedGraph_pairing hy α f
  simpa only [inner_zero_right] using h.symm

lemma fullClosedGraph_unique {x : FullL2 N} {y z : SpinIndex → FullL2 N}
    (hy : (x, y) ∈ M.fullClosedGraph) (hz : (x, z) ∈ M.fullClosedGraph) : y = z := by
  have hd := M.fullClosedGraph.sub_mem hy hz
  have h : ((0 : FullL2 N), y - z) ∈ M.fullClosedGraph := by
    simpa only [Prod.mk_sub_mk, sub_self] using hd
  exact sub_eq_zero.mp (M.fullClosedGraph_vertical h)

end AlgebraData
end
end BFSSQuantum

end OAI
