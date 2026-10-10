import Mathlib
import OAI.Geometry.NilpotentCharts.Adjoint

namespace OAI

/-! Invariant vector fields, one-parameter flows and ordered axes. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)

lemma invariant_derivative (v : GroupLieAlgebra 𝓘ₙ G) (g h : G) :
    mfderiv 𝓘ₙ 𝓘ₙ (fun x => g * x) h (mulInvariantVectorField v h) =
      mulInvariantVectorField v (g * h) := by
  have hg : MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun x : G => g * x) h :=
    (contMDiff_mul_left (I := 𝓘ₙ) (n := 1)).contMDiffAt.mdifferentiableAt one_ne_zero
  have hh : MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun x : G => h * x) 1 :=
    (contMDiff_mul_left (I := 𝓘ₙ) (n := 1)).contMDiffAt.mdifferentiableAt one_ne_zero
  have hc := mfderiv_comp (I' := 𝓘ₙ) 1
    (show MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun x : G => g * x) (h * 1) by simpa using hg) hh
  have he := congrArg
    (fun f : E₀ →L[ℝ] E₀ => f v) hc
  have hp := mfderiv_congr_point (I := 𝓘ₙ) (I' := 𝓘ₙ)
    (f := fun x : G => g * x) (mul_one h)
  have hf := mfderiv_congr (I := 𝓘ₙ) (I' := 𝓘ₙ) (x := (1 : G))
    (show (fun x : G => g * (h * x)) = (fun x : G => (g * h) * x) from
      funext (fun x => (mul_assoc g h x).symm))
  change (mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => g * x) h)
      ((mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => h * x) 1) v) =
    (mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => (g * h) * x) 1) v
  exact (congrArg (fun f : E₀ →L[ℝ] E₀ =>
    f ((mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => h * x) 1) v)) hp.symm).trans
    (he.symm.trans (congrArg (fun f : E₀ →L[ℝ] E₀ => f v) hf))

lemma integralCurveOn_leftMul (v : GroupLieAlgebra 𝓘ₙ G) {γ : ℝ → G} {S : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) S) (g : G) :
    IsMIntegralCurveOn (fun t => g * γ t) (mulInvariantVectorField v) S := by
  intro t ht
  have hg : MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun x : G => g * x) (γ t) :=
    (contMDiff_mul_left (I := 𝓘ₙ) (n := 1)).contMDiffAt.mdifferentiableAt one_ne_zero
  have hcomp := hg.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)
  have hmap :
      (mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => g * x) (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, map_smul, invariant_derivative]
  exact hcomp.congr_mfderiv hmap

lemma integralCurve_leftMul (v : GroupLieAlgebra 𝓘ₙ G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (g : G) :
    IsMIntegralCurve (fun t => g * γ t) (mulInvariantVectorField v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn]
  exact integralCurveOn_leftMul v (hγ.isMIntegralCurveOn univ) g

lemma invariantField_contMDiff_one (v : GroupLieAlgebra 𝓘ₙ G) :
    ContMDiff 𝓘ₙ (𝓘ₙ).tangent 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle 𝓘ₙ G)) := by
  let : LieGroup 𝓘ₙ (minSmoothness ℝ 3) G := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : LieGroup 𝓘ₙ 3 G)
  exact (contMDiff_mulInvariantVectorField v).of_le (one_le_two.trans le_minSmoothness)

variable [FiniteDimensional ℝ E₀] [T2Space G]

lemma exists_global_integralCurve (v : GroupLieAlgebra 𝓘ₙ G) (x : G) :
    ∃ γ : ℝ → G, γ 0 = x ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  have hv := invariantField_contMDiff_one v
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := 𝓘ₙ) (x₀ := (1 : G)) 0 hv.contMDiffAt
  obtain ⟨ε, hε, hεγ⟩ := isMIntegralCurveAt_iff'.mp hγ
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε _ x
  intro y
  refine ⟨fun t => y * γ t, by simp [hγ0], ?_⟩
  simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using integralCurveOn_leftMul v hεγ y

 

theorem exists_oneParameterSubgroup (v : GroupLieAlgebra 𝓘ₙ G) :
    ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧
      (∀ s t : ℝ, γ (s + t) = γ s * γ t) ∧
      IsMIntegralCurve γ (mulInvariantVectorField v) := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_integralCurve v (1 : G)
  refine ⟨γ, hγ.continuous, hγ0, ?_, hγ⟩
  intro s t
  have hs : IsMIntegralCurve (fun u => γ (s + u)) (mulInvariantVectorField v) := by
    simpa only [Function.comp_def, add_comm] using hγ.comp_add s
  have hg := integralCurve_leftMul v hγ (γ s)
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (t₀ := 0) (invariantField_contMDiff_one v) hs hg (by simp [hγ0])
  exact congrFun heq t

 
def curve (v : GroupLieAlgebra 𝓘ₙ G) : ℝ → G :=
  (exists_oneParameterSubgroup v).choose

lemma curve_continuous (v : GroupLieAlgebra 𝓘ₙ G) : Continuous (curve v) :=
  (exists_oneParameterSubgroup v).choose_spec.1

@[simp] lemma curve_zero (v : GroupLieAlgebra 𝓘ₙ G) : curve v 0 = 1 :=
  (exists_oneParameterSubgroup v).choose_spec.2.1

lemma curve_add (v : GroupLieAlgebra 𝓘ₙ G) (s t : ℝ) :
    curve v (s + t) = curve v s * curve v t :=
  (exists_oneParameterSubgroup v).choose_spec.2.2.1 s t

lemma curve_integral (v : GroupLieAlgebra 𝓘ₙ G) :
    IsMIntegralCurve (curve v) (mulInvariantVectorField v) :=
  (exists_oneParameterSubgroup v).choose_spec.2.2.2

lemma curve_unique (v : GroupLieAlgebra 𝓘ₙ G) {γ : ℝ → G}
    (h0 : γ 0 = 1) (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) :
    γ = curve v :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (t₀ := 0) (invariantField_contMDiff_one v) hγ (curve_integral v)
    (h0.trans (curve_zero v).symm)

lemma curve_smul (v : GroupLieAlgebra 𝓘ₙ G) (a t : ℝ) :
    curve (a • v) t = curve v (t * a) := by
  have hγ : IsMIntegralCurve (fun t => curve v (t * a))
      (mulInvariantVectorField (a • v)) := by
    simpa only [Function.comp_def, mulInvariantVectorField_smul] using
      (curve_integral v).comp_mul a
  have h := curve_unique (a • v) (by simp) hγ
  exact (congrFun h t).symm

 

def exp (v : GroupLieAlgebra 𝓘ₙ G) : G := curve v 1

lemma exp_smul (v : GroupLieAlgebra 𝓘ₙ G) (a : ℝ) : exp (a • v) = curve v a := by
  simpa only [exp, one_mul] using curve_smul v a 1

@[simp] lemma exp_zero : exp (0 : GroupLieAlgebra 𝓘ₙ G) = 1 := by
  simpa only [zero_smul, curve_zero] using exp_smul (0 : GroupLieAlgebra 𝓘ₙ G) 0

lemma exp_same_line_add (v : GroupLieAlgebra 𝓘ₙ G) (a b : ℝ) :
    exp ((a + b) • v) = exp (a • v) * exp (b • v) := by
  simp only [exp_smul, curve_add]

lemma curve_neg (v : GroupLieAlgebra 𝓘ₙ G) (a : ℝ) : curve v (-a) = (curve v a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← curve_add, neg_add_cancel, curve_zero]

@[simp] lemma exp_neg (v : GroupLieAlgebra 𝓘ₙ G) : exp (-v) = (exp v)⁻¹ := by
  rw [show -v = (-1 : ℝ) • v by simp, exp_smul, curve_neg]
  rfl

 

def oneParameter (v : GroupLieAlgebra 𝓘ₙ G) : Multiplicative ℝ →* G where
  toFun t := curve v t.toAdd
  map_one' := curve_zero v
  map_mul' s t := curve_add v s.toAdd t.toAdd

lemma oneParameter_continuous (v : GroupLieAlgebra 𝓘ₙ G) : Continuous (oneParameter v) :=
  curve_continuous v

omit [FiniteDimensional ℝ E₀] [LieGroup 𝓘(ℝ, E₀) ∞ G] [T2Space G] in
lemma invariantField_one (v : GroupLieAlgebra 𝓘ₙ G) :
    (mulInvariantVectorField v 1 : E₀) = v := by
  have hf := mfderiv_congr (I := 𝓘ₙ) (I' := 𝓘ₙ) (x := (1 : G))
    (show (fun x : G => (1 : G) * x) = id from funext one_mul)
  have hh := congrArg
    (fun f : E₀ →L[ℝ] E₀ => f v) hf
  change ((mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => (1 : G) * x) 1) v) = v
  calc
    _ = ((mfderiv 𝓘ₙ 𝓘ₙ id 1) v) := hh
    _ = v := by rw [mfderiv_id]; rfl

lemma curve_derivative_zero (v : GroupLieAlgebra 𝓘ₙ G) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘ₙ (curve v) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  have hv : (mulInvariantVectorField v (curve v 0) : E₀) = v :=
    (congrArg (fun g : G => (mulInvariantVectorField v g : E₀))
      (curve_zero v)).trans (invariantField_one v)
  exact (curve_integral v 0).congr_mfderiv
    (congrArg (fun w : E₀ => (1 : ℝ →L[ℝ] ℝ).smulRight w) hv)

lemma curve_injective : Function.Injective (curve (G := G) (E₀ := E₀)) := by
  intro v w h
  have hmf := mfderiv_congr (I := 𝓘(ℝ, ℝ)) (I' := 𝓘ₙ) (x := (0 : ℝ)) h
  have hd : ((1 : ℝ →L[ℝ] ℝ).smulRight v : ℝ →L[ℝ] E₀) =
      (1 : ℝ →L[ℝ] ℝ).smulRight w :=
    (curve_derivative_zero v).mfderiv.symm.trans (hmf.trans (curve_derivative_zero w).mfderiv)
  have hd1 : (1 : ℝ) • v = (1 : ℝ) • w :=
    congrArg (fun f : ℝ →L[ℝ] E₀ => f 1) hd
  simpa only [one_smul] using hd1

local notation "E" => E₀

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma invariantField_contMDiff (v : GroupLieAlgebra 𝓘ₙ G) :
    ContMDiff 𝓘ₙ (𝓘ₙ).tangent ∞
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle 𝓘ₙ G)) := by
  let fg : G → TangentBundle 𝓘ₙ G := fun g => Bundle.TotalSpace.mk' E g 0
  have sfg : ContMDiff 𝓘ₙ (𝓘ₙ).tangent ∞ fg := Bundle.contMDiff_zeroSection _ _
  let fv : G → TangentBundle 𝓘ₙ G := fun _ => Bundle.TotalSpace.mk' E 1 v
  have sfv : ContMDiff 𝓘ₙ (𝓘ₙ).tangent ∞ fv := contMDiff_const
  let F₁ : G → TangentBundle 𝓘ₙ G × TangentBundle 𝓘ₙ G := fun g => (fg g, fv g)
  have S₁ : ContMDiff 𝓘ₙ ((𝓘ₙ).tangent.prod (𝓘ₙ).tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : TangentBundle 𝓘ₙ G × TangentBundle 𝓘ₙ G →
      TangentBundle ((𝓘ₙ).prod 𝓘ₙ) (G × G) := (equivTangentBundleProd 𝓘ₙ G 𝓘ₙ G).symm
  have S₂ : ContMDiff ((𝓘ₙ).tangent.prod (𝓘ₙ).tangent) ((𝓘ₙ).prod 𝓘ₙ).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle ((𝓘ₙ).prod 𝓘ₙ) (G × G) → TangentBundle 𝓘ₙ G :=
    tangentMap ((𝓘ₙ).prod 𝓘ₙ) 𝓘ₙ (fun p : G × G => p.1*p.2)
  have S₃ : ContMDiff ((𝓘ₙ).prod 𝓘ₙ).tangent (𝓘ₙ).tangent ∞ F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ∞) le_rfl
    simpa using contMDiff_mul 𝓘ₙ (∞ : ℕ∞ω) (G := G)
  let S := (S₃.comp S₂).comp S₁
  convert! S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul 𝓘ₙ (∞ : ℕ∞ω)).mdifferentiableAt (by simp))]
    change (mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => g * x) 1) v =
      (mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => x * 1) g) 0 +
        (mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => g * x) 1) v
    simp only [map_zero, zero_add]

lemma curve_contMDiff_nat (v : GroupLieAlgebra 𝓘ₙ G) (n : ℕ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘ₙ n (curve v) := by
  induction n with
  | zero => exact contMDiff_zero_iff.mpr (curve_continuous v)
  | succ n ih =>
    intro t₀
    apply contMDiffAt_iff_target.mpr
    refine ⟨(curve_continuous v).continuousAt, ?_⟩
    apply ContDiffAt.contMDiffAt
    let V : ℝ → TangentBundle 𝓘ₙ G :=
      fun t => ⟨curve v t, mulInvariantVectorField v (curve v t)⟩
    let e := trivializationAt E (TangentSpace 𝓘ₙ) (curve v t₀)
    let D : ℝ → E := fun t => (e (V t)).2
    have hV : ContMDiff 𝓘(ℝ, ℝ) (𝓘ₙ).tangent n V :=
      ((invariantField_contMDiff v).of_le (m := (n : ℕ∞ω)) ENat.LEInfty.out).comp ih
    have hD : ContDiffAt ℝ n D t₀ :=
      (Bundle.contMDiffAt_totalSpace.mp (hV t₀)).2.contDiffAt
    have hderiv : ∀ᶠ t in 𝓝 t₀,
        HasDerivAt ((extChartAt 𝓘ₙ (curve v t₀)) ∘ curve v) (D t) t := by
      simpa only [D, e, V, TangentBundle.trivializationAt_apply, tangentCoordChange_def, extChartAt]
        using (curve_integral v).isMIntegralCurveAt t₀ |>.eventually_hasDerivAt
    obtain ⟨U, hU, hDU⟩ := hderiv.exists_mem
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (D t), ⟨U, hU, fun t ht =>
      (hDU t ht).hasFDerivAt⟩, ?_⟩
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ E 1).contDiff.contDiffAt).comp t₀ hD

lemma curve_contMDiff (v : GroupLieAlgebra 𝓘ₙ G) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘ₙ ∞ (curve v) :=
  contMDiff_infty.mpr (curve_contMDiff_nat v)

lemma curve_contMDiff_one (v : GroupLieAlgebra 𝓘ₙ G) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘ₙ 1 (curve v) := (curve_contMDiff v).of_le ENat.LEInfty.out

 

def orderedAxes {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G) (a : Fin n → ℝ) : G :=
  (List.ofFn (fun i => curve (v i) (a i))).prod

@[simp] lemma orderedAxes_zero {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G) :
    orderedAxes v 0 = 1 := by
  simp [orderedAxes]

lemma orderedAxes_single {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G)
    (i : Fin n) (t : ℝ) : orderedAxes v (Pi.single i t) = curve (v i) t := by
  classical
  rw [orderedAxes, List.ofFn_eq_map, List.prod_map_eq_pow_single i]
  · simp
  · intro j hji _
    simp [Pi.single_eq_of_ne hji]

lemma orderedAxes_contMDiff_one {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ 1 (orderedAxes v) := by
  have hlist : ∀ l : List (Fin n), ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ 1
      (fun a : Fin n → ℝ => (l.map (fun i => curve (v i) (a i))).prod) := by
    intro l
    induction l with
    | nil => simpa using (contMDiff_const (c := (1 : G)))
    | cons i l ih =>
      have hi : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ 1 (fun a : Fin n → ℝ => curve (v i) (a i)) :=
        (curve_contMDiff_one (v i)).comp
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contMDiff
      convert hi.mul ih using 1
      ext a
      simp only [List.map_cons, List.prod_cons]
      rfl
  change ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ 1
    (fun a : Fin n → ℝ => (List.ofFn (fun i => curve (v i) (a i))).prod)
  simpa only [List.ofFn_eq_map] using hlist (List.finRange n)

lemma orderedAxes_derivative_single {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G)
    (i : Fin n) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes v) 0 (Pi.single i 1) = v i := by
  let L : ℝ →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i
  have hL : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) L 0 := L.contMDiffAt.mdifferentiableAt one_ne_zero
  have hP : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes v) (L 0) :=
    (orderedAxes_contMDiff_one v).mdifferentiableAt one_ne_zero
  have hc := mfderiv_comp (I' := 𝓘(ℝ, Fin n → ℝ)) 0 hP hL
  have hf : orderedAxes v ∘ L = curve (v i) := funext (orderedAxes_single v i)
  have he := mfderiv_congr (I := 𝓘(ℝ, ℝ)) (I' := 𝓘ₙ) (x := (0 : ℝ)) hf
  have hl : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) L 0 = L := by
    exact L.hasFDerivAt.hasMFDerivAt.mfderiv
  have hd := congrArg
    (fun f : ℝ →L[ℝ] E₀ => f 1)
    (he.symm.trans hc)
  rw [(curve_derivative_zero (v i)).mfderiv, hl] at hd
  change (1 : ℝ) • v i =
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes v) (L 0)) (L 1) at hd
  have hp := mfderiv_congr_point (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘ₙ)
    (f := orderedAxes v) (show L 0 = 0 from map_zero L)
  have hp1 := congrArg
    (fun f : (Fin n → ℝ) →L[ℝ] E₀ => f (L 1)) hp
  have hd1 := hp1.symm.trans hd.symm
  exact hd1.trans (one_smul ℝ (v i))

lemma orderedAxes_derivative_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra 𝓘ₙ G)) :
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes b) 0 :
      (Fin n → ℝ) →L[ℝ] E₀) =
    b.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  have hlin :
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes b) 0 :
        (Fin n → ℝ) →L[ℝ] E₀).toLinearMap =
      b.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap := by
    apply (Pi.basisFun ℝ (Fin n)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes b) 0) (Pi.single i 1) =
      b.equivFun.symm (Pi.single i 1)
    rw [orderedAxes_derivative_single]
    simp [Module.Basis.equivFun_symm_apply]
    rfl
  exact ContinuousLinearMap.ext (fun a => LinearMap.congr_fun hlin a)

lemma orderedAxes_chart_hasFDerivAt {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra 𝓘ₙ G)) :
    HasFDerivAt ((chartAt (E₀) (1 : G)) ∘ orderedAxes b)
      b.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap 0 := by
  have hP : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes b) 0 :=
    (orderedAxes_contMDiff_one b).mdifferentiableAt one_ne_zero
  have hs : (1 : G) ∈ (chartAt (E₀) (1 : G)).source :=
    mem_chart_source _ _
  have hc : MDifferentiableAt 𝓘ₙ 𝓘ₙ
      (chartAt (E₀) (1 : G)) 1 :=
    ((contMDiffOn_chart (I := 𝓘ₙ) (n := 1)).contMDiffAt
      ((chartAt (E₀) (1 : G)).open_source.mem_nhds hs)).mdifferentiableAt
      one_ne_zero
  have hmc : (mfderiv 𝓘ₙ 𝓘ₙ (chartAt (E₀) (1 : G)) 1 :
      E₀ →L[ℝ] E₀) =
      ContinuousLinearMap.id ℝ _ := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hs]
    apply ContinuousLinearMap.ext
    intro a
    exact tangentCoordChange_self (mem_extChartAt_source (I := 𝓘ₙ) (1 : G))
  have hmcP : (mfderiv 𝓘ₙ 𝓘ₙ (chartAt (E₀) (1 : G))
      (orderedAxes b 0) : E₀ →L[ℝ] E₀) =
      ContinuousLinearMap.id ℝ _ :=
    (mfderiv_congr_point (I := 𝓘ₙ) (I' := 𝓘ₙ)
      (f := chartAt (E₀) (1 : G)) (orderedAxes_zero b)).trans hmc
  have hcomp := mfderiv_comp_of_eq (I' := 𝓘ₙ) hc hP (orderedAxes_zero b)
  have hmd := hc.comp_of_eq 0 hP (orderedAxes_zero b)
  have hh : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ
      ((chartAt (E₀) (1 : G)) ∘ orderedAxes b) 0 =
      b.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [hcomp, hmcP, orderedAxes_derivative_basis]
    exact ContinuousLinearMap.id_comp _
  exact (hmd.hasMFDerivAt.congr_mfderiv hh).hasFDerivAt

lemma orderedAxes_chart_contDiffAt {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra 𝓘ₙ G)) :
    ContDiffAt ℝ 1 ((chartAt (E₀) (1 : G)) ∘ orderedAxes b) 0 := by
  have hc : ContMDiffAt 𝓘ₙ 𝓘ₙ 1
      (chartAt (E₀) (1 : G)) (orderedAxes b 0) := by
    rw [orderedAxes_zero]
    exact (contMDiffOn_chart (I := 𝓘ₙ) (n := 1)).contMDiffAt
      ((chartAt (E₀) (1 : G)).open_source.mem_nhds
        (mem_chart_source _ _))
  exact (hc.comp 0 (orderedAxes_contMDiff_one b 0)).contDiffAt

 

theorem exists_orderedAxes_localChart {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra 𝓘ₙ G)) :
    ∃ e : OpenPartialHomeomorph (Fin n → ℝ) G,
      0 ∈ e.source ∧ EqOn e (orderedAxes b) e.source := by
  let c : OpenPartialHomeomorph G (E₀) :=
    chartAt (E₀) (1 : G)
  let P : (Fin n → ℝ) → G := orderedAxes b
  have hf : HasStrictFDerivAt (c ∘ P)
      b.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap 0 :=
    (orderedAxes_chart_contDiffAt b).hasStrictFDerivAt'
      (orderedAxes_chart_hasFDerivAt b) one_ne_zero
  let e₀ := hf.toOpenPartialHomeomorph (c ∘ P)
  let U : Set (Fin n → ℝ) := P ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage (orderedAxes_contMDiff_one b).continuous
  have h0 : P 0 ∈ c.source := by
    dsimp [P, c]
    rw [orderedAxes_zero]
    exact mem_chart_source _ _
  refine ⟨(e₀.trans c.symm).restr U, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restr_source' _ _ hU]
    refine ⟨?_, h0⟩
    change 0 ∈ e₀.source ∧ e₀ 0 ∈ c.target
    exact ⟨hf.mem_toOpenPartialHomeomorph_source, c.map_source h0⟩
  · intro a ha
    rw [OpenPartialHomeomorph.restr_source' _ _ hU] at ha
    change c.symm (c (P a)) = P a
    exact c.left_inv ha.2

 
def axesLinear {n : ℕ} (v : Fin n → E) : (Fin n → ℝ) →L[ℝ] E :=
  ((Pi.basisFun ℝ (Fin n)).constr ℝ v).toContinuousLinearMap

lemma orderedAxes_derivative {n : ℕ} (v : Fin n → E) :
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes (G := G) v) 0 : (Fin n → ℝ) →L[ℝ] E) = axesLinear v := by
  have he :
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes (G := G) v) 0 : (Fin n → ℝ) →L[ℝ] E).toLinearMap =
      (axesLinear v).toLinearMap := by
    apply (Pi.basisFun ℝ (Fin n)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ (orderedAxes (G := G) v) 0) (Pi.single i 1) = _
    have hi : axesLinear v (Pi.single i 1) = v i := by
      simpa only [axesLinear, Pi.basisFun_apply, LinearMap.coe_toContinuousLinearMap'] using
        (Module.Basis.constr_basis (Pi.basisFun ℝ (Fin n)) ℝ v i)
    exact (orderedAxes_derivative_single (G := G) v i).trans hi.symm
  exact ContinuousLinearMap.ext (fun x => LinearMap.congr_fun he x)

 

def subspaceAxes (K : Submodule ℝ E) : K → G :=
  orderedAxes (fun i => ((Module.finBasis ℝ K) i : E)) ∘ (Module.finBasis ℝ K).equivFun

@[simp] lemma subspaceAxes_zero (K : Submodule ℝ E) : subspaceAxes (G := G) K 0 = 1 := by
  simp only [subspaceAxes, Function.comp_apply, map_zero]
  exact orderedAxes_zero _

lemma subspaceAxes_contMDiff_one (K : Submodule ℝ E) :
    ContMDiff 𝓘(ℝ, K) 𝓘ₙ 1 (subspaceAxes (G := G) K) :=
  (orderedAxes_contMDiff_one _).comp (Module.finBasis ℝ K).equivFun.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff

lemma subspaceAxes_derivative (K : Submodule ℝ E) :
    (mfderiv 𝓘(ℝ, K) 𝓘ₙ (subspaceAxes (G := G) K) 0 : K →L[ℝ] E) = K.subtypeL := by
  let b := Module.finBasis ℝ K
  let L := b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap
  let vs : Fin (Module.finrank ℝ K) → GroupLieAlgebra 𝓘ₙ G := fun i => (b i : E)
  have hP : MDifferentiableAt 𝓘(ℝ, Fin (Module.finrank ℝ K) → ℝ) 𝓘ₙ
      (orderedAxes vs) (L 0) := (orderedAxes_contMDiff_one vs).mdifferentiableAt one_ne_zero
  have hc := mfderiv_comp (I' := 𝓘(ℝ, Fin (Module.finrank ℝ K) → ℝ))
    (f := L) (g := orderedAxes vs) (0 : K) hP L.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hpoint := mfderiv_congr_point (I := 𝓘(ℝ, Fin (Module.finrank ℝ K) → ℝ)) (I' := 𝓘ₙ)
    (f := orderedAxes vs) (map_zero L)
  have hL : mfderiv 𝓘(ℝ, K) 𝓘(ℝ, Fin (Module.finrank ℝ K) → ℝ) L 0 = L :=
    L.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hpoint, orderedAxes_derivative, hL] at hc
  change (mfderiv 𝓘(ℝ, K) 𝓘ₙ (subspaceAxes (G := G) K) 0 : K →L[ℝ] E) = _ at hc
  refine hc.trans ?_
  have he : ((axesLinear (E₀ := E₀) vs).comp L).toLinearMap = K.subtype := by
    apply b.ext
    intro i
    change (axesLinear (E₀ := E₀) vs) (b.equivFun (b i)) = (b i : E)
    have hb : b.equivFun (b i) = (Pi.basisFun ℝ (Fin (Module.finrank ℝ K))) i := by
      ext j
      simp only [Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [hb]
    change ((Pi.basisFun ℝ (Fin (Module.finrank ℝ K))).constr ℝ vs)
      ((Pi.basisFun ℝ (Fin (Module.finrank ℝ K))) i) = vs i
    exact Module.Basis.constr_basis _ _ _ _
  exact ContinuousLinearMap.ext (fun x => LinearMap.congr_fun he x)

section GeneralLocalChart
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
omit [FiniteDimensional ℝ E₀] [T2Space G] [CompleteSpace V] in
lemma chart_comp_hasFDerivAt_one (f : V → G) (hf0 : f 0 = 1)
    (hf : MDifferentiableAt 𝓘(ℝ,V) 𝓘ₙ f 0) (L : V →L[ℝ] E)
    (hD : (mfderiv 𝓘(ℝ,V) 𝓘ₙ f 0 : V →L[ℝ] E) = L) :
    HasFDerivAt ((chartAt E (1 : G)) ∘ f) L 0 := by
  have hc : MDifferentiableAt 𝓘ₙ 𝓘ₙ (chartAt E (1 : G)) (1 : G) :=
    ((contMDiffOn_chart (I := 𝓘ₙ) (n := 1)).contMDiffAt
      ((chartAt E (1 : G)).open_source.mem_nhds (mem_chart_source _ _))).mdifferentiableAt one_ne_zero
  have hmc : (mfderiv 𝓘ₙ 𝓘ₙ (chartAt E (1 : G)) (1 : G) : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source E (1 : G))]
    apply ContinuousLinearMap.ext
    intro v
    exact tangentCoordChange_self (mem_extChartAt_source (I := 𝓘ₙ) (1 : G))
  have hmcP : (mfderiv 𝓘ₙ 𝓘ₙ (chartAt E (1 : G))
      (f 0) : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E :=
    (mfderiv_congr_point (I := 𝓘ₙ) (I' := 𝓘ₙ)
      (f := chartAt E (1 : G)) hf0).trans hmc
  have hcomp := mfderiv_comp_of_eq (I' := 𝓘ₙ) hc hf hf0
  have hmd := hc.comp_of_eq 0 hf hf0
  have hh : mfderiv 𝓘(ℝ,V) 𝓘ₙ ((chartAt E (1 : G)) ∘ f) 0 = L := by
    rw [hcomp, hmcP, hD]
    exact ContinuousLinearMap.id_comp _
  exact (hmd.hasMFDerivAt.congr_mfderiv hh).hasFDerivAt

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma exists_localChart_of_derivative (f : V → G) (hf0 : f 0 = 1)
    (hf : ContMDiff 𝓘(ℝ,V) 𝓘ₙ 1 f) (L : V ≃L[ℝ] E)
    (hD : (mfderiv 𝓘(ℝ,V) 𝓘ₙ f 0 : V →L[ℝ] E) = L.toContinuousLinearMap) :
    ∃ e : OpenPartialHomeomorph V G, 0 ∈ e.source ∧ EqOn e f e.source := by
  let c := chartAt E (1 : G)
  have hc : ContMDiffAt 𝓘ₙ 𝓘ₙ 1 c (f 0) := by
    rw [hf0]
    exact (contMDiffOn_chart (I := 𝓘ₙ) (n := 1)).contMDiffAt
      ((chartAt E (1 : G)).open_source.mem_nhds (mem_chart_source _ _))
  have hcf : ContDiffAt ℝ 1 (c ∘ f) 0 := (hc.comp 0 (hf 0)).contDiffAt
  have hd : HasFDerivAt (c ∘ f) L.toContinuousLinearMap 0 :=
    chart_comp_hasFDerivAt_one f hf0 (hf.mdifferentiableAt one_ne_zero) _ hD
  have hs := hcf.hasStrictFDerivAt' hd one_ne_zero
  let e₀ := hs.toOpenPartialHomeomorph (c ∘ f)
  let U := f ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have h0 : f 0 ∈ c.source := by rw [hf0]; exact mem_chart_source _ _
  refine ⟨(e₀.trans c.symm).restr U, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restr_source' _ _ hU]
    exact ⟨⟨hs.mem_toOpenPartialHomeomorph_source, c.map_source h0⟩, h0⟩
  · intro a ha
    rw [OpenPartialHomeomorph.restr_source' _ _ hU] at ha
    change c.symm (c (f a)) = f a
    exact c.left_inv ha.2
end GeneralLocalChart

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀

lemma orderedAxes_contMDiff {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ ∞ (orderedAxes v) := by
  have hlist : ∀ l : List (Fin n), ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ ∞
      (fun a : Fin n → ℝ => (l.map (fun i => curve (v i) (a i))).prod) := by
    intro l
    induction l with
    | nil => simpa using (contMDiff_const (c := (1 : G)))
    | cons i l ih =>
      have hi : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ ∞ (fun a : Fin n → ℝ => curve (v i) (a i)) :=
        (curve_contMDiff (v i)).comp
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contMDiff
      convert hi.mul ih using 1
      ext a
      simp only [List.map_cons, List.prod_cons]
      rfl
  change ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘ₙ ∞
    (fun a : Fin n → ℝ => (List.ofFn (fun i => curve (v i) (a i))).prod)
  simpa only [List.ofFn_eq_map] using hlist (List.finRange n)

lemma subspaceAxes_contMDiff (K : Submodule ℝ E) :
    ContMDiff 𝓘(ℝ, K) 𝓘ₙ ∞ (subspaceAxes (G := G) K) :=
  (orderedAxes_contMDiff _).comp
    (Module.finBasis ℝ K).equivFun.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff

def vectorDerivative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → G) (x : V) : V →L[ℝ] E := mfderiv 𝓘(ℝ,V) 𝓘ₙ f x

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma product_derivative_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : V → G} (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hf : MDifferentiableAt 𝓘(ℝ,V) 𝓘ₙ f 0) (hg : MDifferentiableAt 𝓘(ℝ,V) 𝓘ₙ g 0) :
    vectorDerivative (E₀ := E₀) (fun x => f x * g x) 0 =
      vectorDerivative (E₀ := E₀) f 0 + vectorDerivative (E₀ := E₀) g 0 := by
  have hm : MDifferentiableAt ((𝓘ₙ).prod 𝓘ₙ) 𝓘ₙ
      (fun p : G × G => p.1*p.2) (f 0,g 0) :=
    (contMDiff_mul 𝓘ₙ 1).mdifferentiableAt one_ne_zero
  have h := mfderiv_comp (I' := (𝓘ₙ).prod 𝓘ₙ) (f := fun x => (f x,g x))
    (g := fun p : G × G => p.1*p.2) (0 : V) hm (hf.prodMk hg)
  have hp := mfderiv_congr_point (I := (𝓘ₙ).prod 𝓘ₙ) (I' := 𝓘ₙ)
    (f := fun p : G × G => p.1*p.2) (show (f 0,g 0) = (1,1) by rw [hf0,hg0])
  apply ContinuousLinearMap.ext
  intro u
  have he := congrArg (fun D : V →L[ℝ] E => D u) h
  rw [mfderiv_prodMk hf hg, hp] at he
  change (mfderiv 𝓘(ℝ,V) 𝓘ₙ (fun x => f x*g x) 0) u = _ at he
  exact he.trans (RawLieAdjoint.mul_derivative_one _ _)

def productSlice (W K : Submodule ℝ E) (p : W × K) : G :=
  subspaceAxes W p.1 * subspaceAxes K p.2

@[simp] lemma productSlice_zero (W K : Submodule ℝ E) :
    productSlice (G := G) W K 0 = 1 := by simp [productSlice]

lemma productSlice_contMDiff (W K : Submodule ℝ E) :
    ContMDiff 𝓘(ℝ, W × K) 𝓘ₙ ∞ (productSlice (G := G) W K) :=
  ((subspaceAxes_contMDiff W).comp (ContinuousLinearMap.fst ℝ W K).contMDiff).mul
    ((subspaceAxes_contMDiff K).comp (ContinuousLinearMap.snd ℝ W K).contMDiff)

lemma productSlice_derivative (W K : Submodule ℝ E) :
    (mfderiv 𝓘(ℝ, W × K) 𝓘ₙ (productSlice (G := G) W K) 0 : (W × K) →L[ℝ] E) =
      W.subtypeL.coprod K.subtypeL := by
  have hW : MDifferentiableAt 𝓘(ℝ,W) 𝓘ₙ (subspaceAxes (G := G) W) 0 :=
    (subspaceAxes_contMDiff_one W).mdifferentiableAt one_ne_zero
  have hK : MDifferentiableAt 𝓘(ℝ,K) 𝓘ₙ (subspaceAxes (G := G) K) 0 :=
    (subspaceAxes_contMDiff_one K).mdifferentiableAt one_ne_zero
  let fstL := ContinuousLinearMap.fst ℝ W K
  let sndL := ContinuousLinearMap.snd ℝ W K
  have hf := mfderiv_comp_of_eq (I' := 𝓘(ℝ,W)) hW
    fstL.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (map_zero fstL)
  have hs := mfderiv_comp_of_eq (I' := 𝓘(ℝ,K)) hK
    sndL.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (map_zero sndL)
  have hfp : mfderiv 𝓘(ℝ,W × K) 𝓘(ℝ,W) fstL 0 = fstL :=
    fstL.hasFDerivAt.hasMFDerivAt.mfderiv
  have hsp : mfderiv 𝓘(ℝ,W × K) 𝓘(ℝ,K) sndL 0 = sndL :=
    sndL.hasFDerivAt.hasMFDerivAt.mfderiv
  have hW0 := mfderiv_congr_point (I := 𝓘(ℝ,W)) (I' := 𝓘ₙ)
    (f := subspaceAxes (G := G) W) (map_zero fstL)
  have hK0 := mfderiv_congr_point (I := 𝓘(ℝ,K)) (I' := 𝓘ₙ)
    (f := subspaceAxes (G := G) K) (map_zero sndL)
  rw [hW0, subspaceAxes_derivative, hfp] at hf
  rw [hK0, subspaceAxes_derivative, hsp] at hs
  have hh := product_derivative_zero
    (f := (subspaceAxes (G := G) W) ∘ fstL)
    (g := (subspaceAxes (G := G) K) ∘ sndL)
    (by simp) (by simp)
    (hW.comp_of_eq 0 fstL.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (map_zero fstL))
    (hK.comp_of_eq 0 sndL.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (map_zero sndL))
  change (mfderiv 𝓘(ℝ,W × K) 𝓘ₙ (productSlice (G := G) W K) 0 : (W × K) →L[ℝ] E) = _ at hh
  dsimp only [vectorDerivative] at hh
  rw [hf,hs] at hh
  exact hh

 
theorem exists_productSlice_localChart (W K : Submodule ℝ E) (hWK : IsCompl W K) :
    ∃ e : OpenPartialHomeomorph (W × K) G,
      0 ∈ e.source ∧ EqOn e (productSlice (G := G) W K) e.source := by
  apply exists_localChart_of_derivative (productSlice (G := G) W K) (productSlice_zero W K)
    ((productSlice_contMDiff W K).of_le ENat.LEInfty.out)
    (W.prodEquivOfIsCompl K hWK).toContinuousLinearEquiv
  exact productSlice_derivative W K

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ F : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G H : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H] [LieGroup 𝓘(ℝ,F) ∞ H] [T2Space H]
local notation "I₀" => 𝓘(ℝ,E₀)
local notation "J" => 𝓘(ℝ,F)

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ F] [T2Space G] [T2Space H] in
lemma invariantField_map (φ : G →* H) (hφ : MDifferentiable I₀ J φ)
    (v : GroupLieAlgebra I₀ G) (h : G) :
    mfderiv I₀ J φ h (mulInvariantVectorField v h) =
      mulInvariantVectorField («I» := J) (mfderiv I₀ J φ 1 v : GroupLieAlgebra J H) (φ h) := by
  have hL : MDifferentiableAt I₀ I₀ (fun x : G => h*x) 1 :=
    (contMDiff_mul_left («I» := I₀) (n := 1)).mdifferentiableAt one_ne_zero
  have hL' : MDifferentiableAt J J (fun x : H => φ h*x) (φ 1) :=
    (contMDiff_mul_left («I» := J) (n := 1)).mdifferentiableAt one_ne_zero
  have hc := mfderiv_comp (I' := I₀) (f := fun x : G => h*x) (g := φ) (1 : G)
    (hφ (h*1)) hL
  have hc' := mfderiv_comp (I' := J) (f := φ) (g := fun x : H => φ h*x) (1 : G)
    hL' (hφ 1)
  have hp := mfderiv_congr_point («I» := I₀) (I' := J) (f := φ) (mul_one h)
  have hp' := mfderiv_congr_point («I» := J) (I' := J)
    (f := fun x : H => φ h*x) φ.map_one
  have he := mfderiv_congr («I» := I₀) (I' := J) (x := (1 : G))
    (show (φ ∘ (fun x : G => h*x)) = (fun x : H => φ h*x) ∘ φ by
      funext x; exact φ.map_mul h x)
  change (mfderiv I₀ J φ h) ((mfderiv I₀ I₀ (fun x : G => h*x) 1) v) =
    (mfderiv J J (fun x : H => φ h*x) 1) ((mfderiv I₀ J φ 1) v)
  exact (congrArg
    (fun D : E₀ →L[ℝ] F => D ((mfderiv I₀ I₀ (fun x : G => h*x) 1) v)) hp.symm).trans
    ((congrArg (fun D : E₀ →L[ℝ] F => D v) hc).symm.trans
      ((congrArg (fun D : E₀ →L[ℝ] F => D v) he).trans
        ((congrArg (fun D : E₀ →L[ℝ] F => D v) hc').trans
          (congrArg (fun D : F →L[ℝ] F => D ((mfderiv I₀ J φ 1) v)) hp'))))

omit [FiniteDimensional ℝ F] [T2Space H] in
lemma integralCurve_map (φ : G →* H) (hφ : MDifferentiable I₀ J φ)
    (v : GroupLieAlgebra I₀ G) :
    IsMIntegralCurve («I» := J) (φ ∘ curve v)
      (mulInvariantVectorField («I» := J) (mfderiv I₀ J φ 1 v : GroupLieAlgebra J H)) := by
  intro t
  have hc := (hφ (curve v t)).hasMFDerivAt.comp t (curve_integral v t)
  have hm : (mfderiv I₀ J φ (curve v t)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (curve v t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField («I» := J) (mfderiv I₀ J φ 1 v : GroupLieAlgebra J H) (φ (curve v t))) := by
    apply ContinuousLinearMap.ext
    intro a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, map_smul, invariantField_map φ hφ]
  exact hc.congr_mfderiv hm

lemma curve_map (φ : G →* H) (hφ : MDifferentiable I₀ J φ)
    (v : GroupLieAlgebra I₀ G) (t : ℝ) :
    φ (curve v t) = curve (E₀ := F) (G := H) (mfderiv I₀ J φ 1 v) t := by
  exact congrFun (curve_unique (mfderiv I₀ J φ 1 v) (by simp) (integralCurve_map φ hφ v)) t

lemma orderedAxes_map (φ : G →* H) (hφ : MDifferentiable I₀ J φ)
    {n : ℕ} (v : Fin n → E₀) (a : Fin n → ℝ) :
    φ (orderedAxes (G := G) v a) = orderedAxes (G := H) (fun i => mfderiv I₀ J φ 1 (v i)) a := by
  simp only [orderedAxes, map_list_prod, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact curve_map φ hφ (v i) (a i)

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

lemma orderedAxes_succ {n : ℕ} (v : Fin (n+1) → GroupLieAlgebra I₀ G) (a : Fin (n+1) → ℝ) :
    orderedAxes v a = curve (v 0) (a 0) * orderedAxes (fun j => v j.succ) (fun j => a j.succ) := by
  simp only [orderedAxes,List.ofFn_succ,List.prod_cons]

def axisTail : {n : ℕ} → (Fin n → GroupLieAlgebra I₀ G) → (Fin n → ℝ) → Fin n → G
  | 0, _, _, i => i.elim0
  | _+1, v, a, i => Fin.cases
      (orderedAxes (fun j => v j.succ) (fun j => a j.succ))
      (fun j => axisTail (fun k => v k.succ) (fun k => a k.succ) j) i

lemma orderedAxes_shift {n : ℕ} (v : Fin n → GroupLieAlgebra I₀ G) (a : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    orderedAxes v (a + Pi.single i t) = orderedAxes v a *
      ((axisTail v a i)⁻¹ * curve (v i) t * axisTail v a i) := by
  classical
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [orderedAxes_succ,orderedAxes_succ]
      simp only [Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne (Fin.succ_ne_zero _),
        add_zero,axisTail,Fin.cases_zero]
      rw [curve_add]
      group
    · rw [orderedAxes_succ,orderedAxes_succ]
      have ha : (fun k : Fin n => (a + Pi.single j.succ t : Fin (n+1) → ℝ) k.succ) =
          (fun k : Fin n => a k.succ) + Pi.single j t := by
        ext k
        simp [Pi.single_apply,Fin.succ_inj]
      rw [ha,ih]
      simp only [Pi.add_apply,Pi.single_eq_of_ne ((Fin.succ_ne_zero j).symm),add_zero,
        axisTail,Fin.cases_succ,mul_assoc]

end RawLieIntegration
end

end OAI
