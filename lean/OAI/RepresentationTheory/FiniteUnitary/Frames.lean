import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.HilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The algebraic Hilbert--Schmidt scalar product, irrespective of the operator
norm on the carrier. A core is used to avoid changing any source norm. -/
def hsInner (T U : E →ₗ[ℂ] E) : ℂ :=
  LinearMap.trace ℂ E (LinearMap.adjoint T ∘ₗ U)

lemma hsInner_basis (T U : E →ₗ[ℂ] E) :
    hsInner T U = ∑ i, inner ℂ (T (stdOrthonormalBasis ℂ E i))
      (U (stdOrthonormalBasis ℂ E i)) := by
  rw [hsInner, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E)]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]

@[instance_reducible]
def endCore : InnerProductSpace.Core ℂ (E →ₗ[ℂ] E) where
  inner := hsInner
  conj_inner_symm T U := by
    simp only [hsInner_basis, map_sum, inner_conj_symm]
  re_inner_nonneg T := by
    rw [hsInner_basis, map_sum]
    exact Finset.sum_nonneg fun _ _ => inner_self_nonneg
  add_left T U V := by
    simp only [hsInner_basis, LinearMap.add_apply, inner_add_left, Finset.sum_add_distrib]
  smul_left T U z := by
    simp only [hsInner_basis, LinearMap.smul_apply, inner_smul_left, Finset.mul_sum]
  definite T h := by
    have hh : ∑ i, ‖T (stdOrthonormalBasis ℂ E i)‖^2 = 0 := by
      have he := congrArg (RCLike.re : ℂ → ℝ) h
      simpa only [hsInner_basis, map_sum, map_zero, inner_self_eq_norm_sq] using he
    have hz (i : Fin (Module.finrank ℂ E)) : T (stdOrthonormalBasis ℂ E i) = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg ‖T (stdOrthonormalBasis ℂ E j)‖)).mp hh i (Finset.mem_univ i)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    apply (stdOrthonormalBasis ℂ E).toBasis.ext
    intro i
    simpa using hz i

lemma adjoint_isometry (u : E ≃ₗᵢ[ℂ] E) :
    LinearMap.adjoint u.toLinearEquiv.toLinearMap = u.symm.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [LinearMap.adjoint_inner_left]
  change inner ℂ x (u y) = inner ℂ (u.symm x) y
  simpa only [u.apply_symm_apply] using u.inner_map_map (u.symm x) y

lemma hsInner_conj (u : E ≃ₗᵢ[ℂ] E) (T V : E →ₗ[ℂ] E) :
    hsInner (u.toLinearEquiv.conj T) (u.toLinearEquiv.conj V) = hsInner T V := by
  rw [hsInner_basis]
  conv_rhs => rw [hsInner, LinearMap.trace_eq_sum_inner _
    ((stdOrthonormalBasis ℂ E).map u.symm)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    OrthonormalBasis.map_apply, LinearEquiv.conj_apply]
  change inner ℂ (u (T (u.symm (stdOrthonormalBasis ℂ E i))))
      (u (V (u.symm (stdOrthonormalBasis ℂ E i)))) = _
  exact u.inner_map_map _ _

end RowColumn.HilbertSchmidt

noncomputable section
open scoped RealInnerProductSpace
namespace RowColumn.UnitaryFrame
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma norm_minimizer_unique [CompleteSpace E] (K : Set E) (hK : Convex ℝ K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    (hxm : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hym : ∀ z ∈ K, ‖y‖ ≤ ‖z‖) : x = y := by
  have he : ‖x‖ = ‖y‖ := le_antisymm (hxm y hy) (hym x hx)
  have hm : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ K :=
    hK hx hy (by norm_num) (by norm_num) (by norm_num)
  have hl := hxm _ hm
  have hn : ‖(1/2 : ℝ) • x + (1/2 : ℝ) • y‖ = (1/2 : ℝ)*‖x+y‖ := by
    rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  rw [hn] at hl
  have hsq := mul_self_le_mul_self (norm_nonneg x) hl
  have hp := parallelogram_law_with_norm ℝ x y
  rw [← he] at hp
  have hd := sq_nonneg ‖x-y‖
  have hz : ‖x-y‖ = 0 := by
    nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Simultaneous fixed point obtained from the unique minimum-norm point of a
closed convex invariant set. Applied to rank-one unitary frames, this replaces
Haar integration by finite-dimensional convex averaging. -/
theorem exists_fixed_minimum (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconv : Convex ℝ K) (L : ι → E →ₗᵢ[ℝ] E)
    (hL : ∀ i x, x ∈ K → L i x ∈ K) :
    ∃ x ∈ K, ∀ i, L i x = x := by
  obtain ⟨x,hx,hm⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv (0 : E)
  have hmin (z : E) (hz : z ∈ K) : ‖x‖ ≤ ‖z‖ := by
    have hh : (⨅ w : K, ‖(0 : E)-w‖) ≤ ‖(0 : E)-z‖ :=
      ciInf_le (f := fun w : K => ‖(0 : E) - (w : E)‖)
        ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨z,hz⟩ : K)
    rw [← hm] at hh
    simpa using hh
  refine ⟨x,hx,fun i => ?_⟩
  exact norm_minimizer_unique K hconv (hL i x hx) hx
    (fun z hz => by rw [(L i).norm_map]; exact hmin z hz) hmin

end RowColumn.UnitaryFrame

noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def quadraticForm (T : E →ₗ[ℂ] E) (x : E) : ℝ := (inner ℂ x (T x)).re

omit [FiniteDimensional ℂ E] in
lemma quadraticForm_real_smul [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (c : ℝ) (x : E) :
    quadraticForm T (c • x) = c^2 * quadraticForm T x := by
  simp only [quadraticForm, ← Complex.coe_smul, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]
  simp [Complex.mul_re, pow_two, mul_assoc]

lemma quadraticForm_continuous (T : E →ₗ[ℂ] E) : Continuous (quadraticForm T) :=
  Complex.continuous_re.comp (continuous_id.inner T.toContinuousLinearMap.continuous)

/-- Strict positivity of a finite-dimensional frame is uniformly coercive. -/
theorem positive_coercive (T : E →ₗ[ℂ] E)
    (hT : ∀ x : E, x ≠ 0 → 0 < quadraticForm T x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε * ‖x‖^2 ≤ quadraticForm T x := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let := h
    refine ⟨1, by norm_num, fun x => ?_⟩
    have he : x = 0 := Subsingleton.elim _ _
    simp [he, quadraticForm]
  | inr h =>
    let := h
    let : ProperSpace E := FiniteDimensional.proper ℂ E
    have hn : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
    obtain ⟨y,hy,hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hn
      (quadraticForm_continuous T).continuousOn
    have hny : ‖y‖ = 1 := by simpa using hy
    have hpy : 0 < quadraticForm T y := hT y (by intro he; simp [he] at hny)
    refine ⟨quadraticForm T y, hpy, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx, quadraticForm]
    · have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, ne_of_gt hp]
      have hm : quadraticForm T y ≤ quadraticForm T (‖x‖⁻¹ • x) := hmin hu
      rw [quadraticForm_real_smul] at hm
      have hh := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖x‖)
      calc
        _ ≤ (‖x‖⁻¹ ^ 2 * quadraticForm T x) * ‖x‖^2 := hh
        _ = _ := by field_simp [ne_of_gt hp]

end RowColumn.UnitaryFrame

namespace RowColumn.UnitaryFrame
open scoped BigOperators ComplexOrder ComplexConjugate
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Group G]

local instance : NormedAddCommGroup (E →ₗ[ℂ] E) := HilbertSchmidt.endCore.toNormedAddCommGroup
local instance : InnerProductSpace ℂ (E →ₗ[ℂ] E) :=
  InnerProductSpace.ofCore { __ := HilbertSchmidt.endCore (E := E) }
local instance : InnerProductSpace ℝ (E →ₗ[ℂ] E) := InnerProductSpace.complexToReal

def conjugationIsometry (u : E ≃ₗᵢ[ℂ] E) :
    (E →ₗ[ℂ] E) →ₗᵢ[ℂ] (E →ₗ[ℂ] E) :=
  u.toLinearEquiv.conj.toLinearMap.isometryOfInner (HilbertSchmidt.hsInner_conj u)

def conjugationReal (u : E ≃ₗᵢ[ℂ] E) :
    (E →ₗ[ℂ] E) →ₗᵢ[ℝ] (E →ₗ[ℂ] E) where
  toLinearMap := (conjugationIsometry u).toLinearMap.restrictScalars ℝ
  norm_map' := (conjugationIsometry u).norm_map

lemma conjugation_apply (u : E ≃ₗᵢ[ℂ] E) (T : E →ₗ[ℂ] E) (x : E) :
    conjugationReal u T x = u (T (u.symm x)) := rfl

lemma conjugation_rankOne (u : E ≃ₗᵢ[ℂ] E) (x : E) :
    conjugationReal u (InnerProductSpace.rankOne ℂ x x).toLinearMap =
      (InnerProductSpace.rankOne ℂ (u x) (u x)).toLinearMap := by
  ext y
  change u (inner ℂ x (u.symm y) • x) = inner ℂ (u x) y • u x
  rw [map_smul]
  congr 1
  simpa only [u.apply_symm_apply] using (u.inner_map_map x (u.symm y)).symm

def matrixEntry (x y : E) : (E →ₗ[ℂ] E) →ₗ[ℂ] ℂ where
  toFun T := inner ℂ x (T y)
  map_add' T V := by simp only [LinearMap.add_apply, inner_add_right]
  map_smul' c T := by simp only [LinearMap.smul_apply, inner_smul_right, smul_eq_mul, RingHom.id_apply]

def quadraticEval (x : E) : (E →ₗ[ℂ] E) →ₗ[ℝ] ℝ where
  toFun T := quadraticForm T x
  map_add' T V := by simp [quadraticForm]
  map_smul' c T := by
    simp only [quadraticForm, LinearMap.smul_apply, ← Complex.coe_smul, inner_smul_right]
    simp [Complex.mul_re]

def coerciveSet (ε : ℝ) : Set (E →ₗ[ℂ] E) :=
  {T | ∀ x, ε * ‖x‖^2 ≤ quadraticForm T x}

lemma coerciveSet_closed (ε : ℝ) : IsClosed (coerciveSet (E := E) ε) := by
  rw [coerciveSet, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  exact isClosed_le continuous_const
    (show Continuous (fun T : E →ₗ[ℂ] E => quadraticForm T x) from
      (quadraticEval x).toContinuousLinearMap.continuous)

omit [FiniteDimensional ℂ E] in
lemma coerciveSet_convex [FiniteDimensional ℂ E] (ε : ℝ) :
    Convex ℝ (coerciveSet (E := E) ε) := by
  intro T hT V hV a b ha hb hab x
  have h₁ := mul_le_mul_of_nonneg_left (hT x) ha
  have h₂ := mul_le_mul_of_nonneg_left (hV x) hb
  change ε * ‖x‖^2 ≤ quadraticEval x (a • T + b • V)
  rw [map_add, map_smul, map_smul]
  change ε * ‖x‖^2 ≤ a * quadraticForm T x + b * quadraticForm V x
  calc
    ε * ‖x‖^2 = (a+b) * (ε * ‖x‖^2) := by rw [hab, one_mul]
    _ = a * (ε * ‖x‖^2) + b * (ε * ‖x‖^2) := add_mul _ _ _
    _ ≤ _ := add_le_add h₁ h₂

lemma positiveSet_closed : IsClosed {T : E →ₗ[ℂ] E | T.IsPositive} := by
  have hs : IsClosed {T : E →ₗ[ℂ] E | T.IsSymmetric} := by
    have he : {T : E →ₗ[ℂ] E | T.IsSymmetric} =
        ⋂ x : E, ⋂ y : E,
        {T | starRingEnd ℂ (matrixEntry y x T) = matrixEntry x y T} := by
      ext T
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, matrixEntry, LinearMap.coe_mk,
        AddHom.coe_mk, inner_conj_symm, LinearMap.IsSymmetric]
    rw [he]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
      (Complex.continuous_conj.comp (matrixEntry y x).toContinuousLinearMap.continuous)
      (matrixEntry x y).toContinuousLinearMap.continuous
  have hn : IsClosed {T : E →ₗ[ℂ] E | ∀ x, 0 ≤ quadraticForm T x} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const
      (show Continuous (fun T : E →ₗ[ℂ] E => quadraticForm T x) from
        (quadraticEval x).toContinuousLinearMap.continuous)
  have he : {T : E →ₗ[ℂ] E | T.IsPositive} =
      {T | T.IsSymmetric} ∩ {T | ∀ x, 0 ≤ quadraticForm T x} := by
    ext T
    constructor
    · intro h; exact ⟨h.isSymmetric, fun x => h.re_inner_nonneg_right x⟩
    · rintro ⟨hs,hn⟩
      refine ⟨hs, fun x => ?_⟩
      rw [inner_re_symm]
      exact hn x
  rw [he]
  exact hs.inter hn

omit [FiniteDimensional ℂ E] in
lemma positiveSet_convex [FiniteDimensional ℂ E] : Convex ℝ {T : E →ₗ[ℂ] E | T.IsPositive} := by
  intro T hT V hV a b ha hb hab
  change (a • T + b • V).IsPositive
  rw [← Complex.coe_smul a T, ← Complex.coe_smul b V]
  exact (hT.smul_of_nonneg (by exact_mod_cast ha)).add
    (hV.smul_of_nonneg (by exact_mod_cast hb))

def frameHull (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E) : Set (E →ₗ[ℂ] E) :=
  closure (convexHull ℝ (Set.range fun g : G =>
    (InnerProductSpace.rankOne ℂ (π g x₀) (π g x₀)).toLinearMap))

lemma frameHull_invariant (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E) (g : G) :
    Set.MapsTo (conjugationReal (π g)) (frameHull π x₀) (frameHull π x₀) := by
  apply Set.MapsTo.closure _ (conjugationReal (π g)).continuous
  rw [Set.mapsTo_iff_image_subset]
  rw [← LinearIsometry.coe_toLinearMap, (conjugationReal (π g)).toLinearMap.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_, ⟨h,rfl⟩, rfl⟩
  refine ⟨g*h, ?_⟩
  change (InnerProductSpace.rankOne ℂ (π (g*h) x₀) (π (g*h) x₀)).toLinearMap =
    conjugationReal (π g) (InnerProductSpace.rankOne ℂ (π h x₀) (π h x₀)).toLinearMap
  rw [conjugation_rankOne, map_mul]
  rfl

lemma quadraticForm_conj (u : E ≃ₗᵢ[ℂ] E) (T : E →ₗ[ℂ] E) (x : E) :
    quadraticForm (conjugationReal u T) x = quadraticForm T (u.symm x) := by
  unfold quadraticForm
  rw [conjugation_apply]
  have hi := u.inner_map_map (u.symm x) (T (u.symm x))
  rw [u.apply_symm_apply] at hi
  exact congrArg Complex.re hi

/-- A genuine invariant strictly positive frame is obtained by convex averaging;
no Haar measure or compact-group orthogonality is taken as a hypothesis. -/
theorem exists_invariant_frame_of_coercive
    (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E)
    (T₀ : E →ₗ[ℂ] E) (hT₀ : T₀ ∈ frameHull π x₀) (hp₀ : T₀.IsPositive)
    (ε : ℝ) (_ : 0 < ε) (hε₀ : T₀ ∈ coerciveSet ε) :
    ∃ T : E →ₗ[ℂ] E, T ∈ frameHull π x₀ ∧ T.IsPositive ∧
      T ∈ coerciveSet ε ∧ ∀ g, conjugationReal (π g) T = T := by
  let K := frameHull π x₀ ∩ ({T | T.IsPositive} ∩ coerciveSet ε)
  have hc : IsClosed K := isClosed_closure.inter (positiveSet_closed.inter (coerciveSet_closed ε))
  have hv : Convex ℝ K := (convex_convexHull ℝ _).closure.inter
    (positiveSet_convex.inter (coerciveSet_convex ε))
  have hL (g : G) (V : E →ₗ[ℂ] E) (hV : V ∈ K) :
      conjugationReal (π g) V ∈ K := by
    refine ⟨frameHull_invariant π x₀ g hV.1, ?_, ?_⟩
    · exact (LinearMap.isPositive_linearIsometryEquiv_conj_iff (π g)).mpr hV.2.1
    · intro x
      rw [quadraticForm_conj]
      simpa only [(π g).symm.norm_map] using hV.2.2 ((π g).symm x)
  obtain ⟨T,hT,hfix⟩ := exists_fixed_minimum K ⟨T₀,hT₀,hp₀,hε₀⟩ hc hv
    (fun g => conjugationReal (π g)) hL
  exact ⟨T,hT.1,hT.2.1,hT.2.2,hfix⟩

end RowColumn.UnitaryFrame
namespace RowColumn.UnitaryFrame
open scoped BigOperators ComplexOrder ComplexConjugate
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Group G]

omit [FiniteDimensional ℂ E] in
lemma rankOne_quadratic [FiniteDimensional ℂ E] (v x : E) :
    quadraticForm (InnerProductSpace.rankOne ℂ v v).toLinearMap x =
      Complex.normSq (inner ℂ v x) := by
  change (inner ℂ x (inner ℂ v x • v)).re = _
  rw [inner_smul_right, ← inner_conj_symm x v, Complex.mul_conj, Complex.ofReal_re]

omit [FiniteDimensional ℂ E] in
lemma finite_frame_strict [FiniteDimensional ℂ E] (s : Finset E)
    (hs : Submodule.span ℂ (s : Set E) = ⊤)
    {x : E} (hx : x ≠ 0) : 0 < ∑ v ∈ s, Complex.normSq (inner ℂ v x) := by
  have hn : 0 ≤ ∑ v ∈ s, Complex.normSq (inner ℂ v x) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  by_contra h
  have hz := le_antisymm (le_of_not_gt h) hn
  have hi (v : E) (hv : v ∈ s) : inner ℂ v x = 0 :=
    Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp hz v hv)
  have hall (v : E) (hv : v ∈ Submodule.span ℂ (s : Set E)) : inner ℂ v x = 0 := by
    induction hv using Submodule.span_induction with
    | mem v hv => exact hi v hv
    | zero => simp
    | add u v hu hv heu hev => simp [heu, hev]
    | smul c v hv hv' => simp [hv']
  exact hx ((inner_self_eq_zero (𝕜 := ℂ)).mp (hall x (by rw [hs]; trivial)))

def finiteFrame (s : Finset E) : E →ₗ[ℂ] E :=
  s.centerMass (fun _ => (1 : ℝ))
    (fun v => (InnerProductSpace.rankOne ℂ v v).toLinearMap)

lemma finiteFrame_quadratic (s : Finset E) (x : E) :
    quadraticForm (finiteFrame s) x = (s.card : ℝ)⁻¹ *
      ∑ v ∈ s, Complex.normSq (inner ℂ v x) := by
  change quadraticEval x (finiteFrame s) = _
  simp only [finiteFrame, Finset.centerMass, one_smul, Finset.sum_const,
    nsmul_eq_mul, mul_one, map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact rankOne_quadratic v x

local instance : NormedAddCommGroup (E →ₗ[ℂ] E) := HilbertSchmidt.endCore.toNormedAddCommGroup
local instance : InnerProductSpace ℂ (E →ₗ[ℂ] E) :=
  InnerProductSpace.ofCore { __ := HilbertSchmidt.endCore (E := E) }
local instance : InnerProductSpace ℝ (E →ₗ[ℂ] E) := InnerProductSpace.complexToReal

lemma finiteFrame_positive (s : Finset E) (hs : s.Nonempty) : (finiteFrame s).IsPositive := by
  change s.centerMass (fun _ => (1 : ℝ))
    (fun v => (InnerProductSpace.rankOne ℂ v v).toLinearMap) ∈
      {T : E →ₗ[ℂ] E | T.IsPositive}
  apply (positiveSet_convex (E := E)).centerMass_mem (fun _ _ => by norm_num)
  · simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      (show (0 : ℝ) < s.card from by exact_mod_cast hs.card_pos)
  · intro v _
    exact (InnerProductSpace.isPositive_rankOne_self v).toLinearMap

/-- Spanning unitary orbits have an invertible positive invariant frame, with
its approximation by finite probability mixtures of the original orbit. -/
theorem exists_invariant_frame (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E)
    (hspan : Submodule.span ℂ (Set.range fun g : G => π g x₀) = ⊤) :
    ∃ T : E →ₗ[ℂ] E, T ∈ frameHull π x₀ ∧ T.IsPositive ∧
      Function.Bijective T ∧ ∀ g, conjugationReal (π g) T = T := by
  classical
  obtain ⟨s,hs,hcard,hss,hindep⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ
    (Set.range fun g : G => π g x₀)
  let t := insert x₀ s
  have htn : t.Nonempty := Finset.insert_nonempty _ _
  have hts : (t : Set E) ⊆ Set.range fun g : G => π g x₀ := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨1, by simp⟩
    · exact hs hx
  have htspan : Submodule.span ℂ (t : Set E) = ⊤ := by
    apply top_unique
    rw [← hspan, ← hss]
    exact Submodule.span_mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
  have hmem : finiteFrame t ∈ frameHull π x₀ := by
    apply subset_closure
    apply t.centerMass_mem_convexHull (fun _ _ => by norm_num)
    · simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        (show (0 : ℝ) < t.card from by exact_mod_cast htn.card_pos)
    · intro v hv
      obtain ⟨g,rfl⟩ := hts hv
      exact ⟨g,rfl⟩
  have hstrict (x : E) (hx : x ≠ 0) : 0 < quadraticForm (finiteFrame t) x := by
    rw [finiteFrame_quadratic]
    exact mul_pos (inv_pos.mpr (by exact_mod_cast htn.card_pos)) (finite_frame_strict t htspan hx)
  obtain ⟨ε,hε,hε₀⟩ := positive_coercive (finiteFrame t) hstrict
  obtain ⟨T,hT,hp,hc,hfix⟩ := exists_invariant_frame_of_coercive π x₀ (finiteFrame t)
    hmem (finiteFrame_positive t htn) ε hε hε₀
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hh := hc x
    change ε * ‖x‖^2 ≤ (inner ℂ x (T x)).re at hh
    rw [hx, inner_zero_right, Complex.zero_re] at hh
    have hn : ‖x‖^2 = 0 := le_antisymm (nonpos_of_mul_nonpos_right hh hε) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact ⟨T,hT,hp,⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩,hfix⟩

end RowColumn.UnitaryFrame

end
end
end
end


section
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder
namespace RowColumn.UnitaryFrame

variable {A G : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [FiniteDimensional ℂ A] [Group G]

/-- Algebraic and convex reconstruction from a spanning unitary group. The
trace is the physical trace, not the trace of the algebra's regular action. -/
theorem exists_density (τ : A →ₗ[ℂ] ℂ) (core : InnerProductSpace.Core ℂ A)
    (hinner : ∀ x y, core.inner x y = τ (star x * y))
    (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤) :
    ∃ D : A, τ D = (Module.finrank ℂ A : ℂ) ∧
      (∀ x : A, 0 ≤ τ (star x * x * D)) ∧
      (∀ (B : A) (ℓ : A →ₗ[ℂ] ℂ) (R : ℝ),
        (∀ g, ‖τ (star (u g : A) * (B*D)) * ℓ (u g : A)‖ ≤ R) → ‖ℓ B‖ ≤ R) := by
  let : NormedAddCommGroup A := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ A := InnerProductSpace.ofCore { __ := core }
  change ∀ x y, inner ℂ x y = τ (star x*y) at hinner
  let π : G →* A ≃ₗᵢ[ℂ] A :=
    { toFun := fun g =>
        (Units.mulLeftLinearEquiv ℂ A (Unitary.toUnits (u g))).isometryOfInner (by
          intro x y
          change inner ℂ ((u g : A)*x) ((u g : A)*y) = inner ℂ x y
          simp only [hinner, star_mul, mul_assoc]
          rw [← mul_assoc (star (u g : A)), Unitary.coe_star_mul_self, one_mul])
      map_one' := by ext x; simp
      map_mul' := by intros g h; ext x; simp }
  have hπ (g : G) (x : A) : π g x = (u g : A)*x := rfl
  obtain ⟨T,hT,hpos,hbij,hfix⟩ := exists_invariant_frame π 1 (by simpa only [hπ, mul_one] using hspan)
  have heq (g : G) (x : A) : T ((u g : A)*x) = (u g : A)*T x := by
    have he := LinearMap.congr_fun (hfix g) (π g x)
    change π g (T ((π g).symm (π g x))) = T (π g x) at he
    rw [(π g).symm_apply_apply] at he
    exact he.symm
  let C := T 1
  have hTm (x : A) : T x = x*C := by
    have hx : x ∈ Submodule.span ℂ (Set.range fun g : G => (u g : A)) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g,rfl⟩ := hx; simpa only [mul_one] using heq g 1
    | zero => simp
    | add x y hx hy hxt hyt => simp only [map_add, add_mul, hxt, hyt]
    | smul c x hx hxt => simpa only [map_smul, smul_mul_assoc] using congrArg (c • ·) hxt
  let e : A ≃ₗ[ℂ] A := LinearEquiv.ofBijective T hbij
  let D : A := e.symm 1
  have hTD : T D = 1 := e.apply_symm_apply 1
  have hDC : D*C = 1 := (hTm D).symm.trans hTD
  have hinv (x : A) : T (x*D) = x := by rw [hTm, mul_assoc, hDC, mul_one]
  have heinv (x : A) : e.symm x = x*D := by
    apply hbij.injective
    exact (e.apply_symm_apply x).trans (hinv x).symm
  have hip : e.symm.toLinearMap.IsPositive := hpos.toLinearMap_symm
  have hDpos (x : A) : 0 ≤ τ (star x*x*D) := by
    have hh := hip.inner_nonneg_right x
    simpa only [LinearEquiv.coe_coe, heinv, hinner, mul_assoc] using hh
  let f : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ :=
    { toFun S := LinearMap.trace ℂ A (S ∘ₗ LinearMap.mulRight ℂ D)
      map_add' S V := by simp only [LinearMap.add_comp, map_add]
      map_smul' c S := by simp only [LinearMap.smul_comp, map_smul, RingHom.id_apply] }
  have hf (g : G) : f (InnerProductSpace.rankOne ℂ (π g 1) (π g 1)).toLinearMap = τ D := by
    change LinearMap.trace ℂ A (_ ∘ₗ _) = _
    rw [LinearMap.trace_comp_comm']
    have he : LinearMap.mulRight ℂ D ∘ₗ
        (InnerProductSpace.rankOne ℂ (π g 1) (π g 1)).toLinearMap =
        (InnerProductSpace.rankOne ℂ ((π g 1)*D) (π g 1)).toLinearMap := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, smul_mul_assoc]
    rw [he]
    change (InnerProductSpace.rankOne ℂ ((π g 1)*D) (π g 1)).trace ℂ A = _
    rw [InnerProductSpace.trace_rankOne, hinner, hπ, mul_one,
      ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  let : NormedAddCommGroup (A →ₗ[ℂ] A) := HilbertSchmidt.endCore.toNormedAddCommGroup
  let : InnerProductSpace ℂ (A →ₗ[ℂ] A) :=
    InnerProductSpace.ofCore { __ := HilbertSchmidt.endCore (E := A) }
  let : InnerProductSpace ℝ (A →ₗ[ℂ] A) := InnerProductSpace.complexToReal
  have hfc : ∀ S ∈ frameHull π 1, f S = τ D := by
    change closure (convexHull ℝ _) ⊆ {S | f S = τ D}
    apply closure_minimal
    · apply convexHull_min
      · rintro _ ⟨g,rfl⟩; exact hf g
      · intro S hS V hV a b ha hb hab
        change f (a • S + b • V) = τ D
        rw [map_add, ← Complex.coe_smul a S, ← Complex.coe_smul b V, map_smul, map_smul, hS, hV]
        rw [← add_smul, ← Complex.ofReal_add, hab, Complex.ofReal_one, one_smul]
    · exact isClosed_eq f.toContinuousLinearMap.continuous continuous_const
  have hτD : τ D = (Module.finrank ℂ A : ℂ) := by
    rw [← hfc T hT]
    have hcomp : T ∘ₗ LinearMap.mulRight ℂ D = LinearMap.id := by ext x; exact hinv x
    change LinearMap.trace ℂ A (_ ∘ₗ _) = _
    rw [hcomp, LinearMap.trace_id]
  refine ⟨D,hτD,hDpos,?_⟩
  intro B ℓ R hR
  let l : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ :=
    { toFun S := ℓ (S (B*D))
      map_add' S V := by simp only [LinearMap.add_apply, map_add]
      map_smul' c S := by simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply] }
  have hl : ∀ S ∈ frameHull π 1, ‖l S‖ ≤ R := by
    change closure (convexHull ℝ _) ⊆ {S | ‖l S‖ ≤ R}
    apply closure_minimal
    · apply convexHull_min
      · rintro _ ⟨g,rfl⟩
        change ‖ℓ ((InnerProductSpace.rankOne ℂ (π g 1) (π g 1)) (B*D))‖ ≤ R
        simpa only [l, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_coe,
          InnerProductSpace.rankOne_apply, map_smul, hinner, hπ, mul_one, smul_eq_mul] using hR g
      · intro S hS V hV a b ha hb hab
        change ‖l (a • S + b • V)‖ ≤ R
        rw [map_add, ← Complex.coe_smul a S, ← Complex.coe_smul b V, map_smul, map_smul]
        calc
          _ ≤ ‖(a : ℂ) • l S‖ + ‖(b : ℂ) • l V‖ := norm_add_le _ _
          _ = a * ‖l S‖ + b * ‖l V‖ := by simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
          _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hS ha) (mul_le_mul_of_nonneg_left hV hb)
          _ = R := by rw [← add_mul, hab, one_mul]
    · exact isClosed_le l.toContinuousLinearMap.continuous.norm continuous_const
  simpa only [l, LinearMap.coe_mk, AddHom.coe_mk, hinv] using hl T hT

end RowColumn.UnitaryFrame

end
end

end OAI
