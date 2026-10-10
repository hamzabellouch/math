import OAI.Analysis.LiebThirring.RowSigns

namespace OAI

universe u148 u149 u150 u151 u152 u153 u154 u155 u156 u157

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
namespace SharpLiebThirring.ODEProof

/-- Bounded globally Lipschitz fields have solutions on the entire prescribed
compact interval. There is no restriction on the length of the interval. -/
lemma bounded_ode_exists {E : Type u148} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {l r : ℝ} (hlr : l ≤ r) (x₀ : E) (f : ℝ → E → E) (K L : ℝ≥0)
    (hK : ∀ t ∈ Icc l r, LipschitzWith K (f t))
    (hc : ∀ x, ContinuousOn (fun t ↦ f t x) (Icc l r))
    (hL : ∀ t ∈ Icc l r, ∀ x, ‖f t x‖ ≤ L) :
    ∃ x : ℝ → E, x l = x₀ ∧ ∀ t ∈ Icc l r, HasDerivWithinAt x (f t (x t)) (Icc l r) t := by
  let a : ℝ≥0 := L * ⟨r-l,sub_nonneg.mpr hlr⟩
  have hp : IsPicardLindelof f ⟨l,⟨le_refl _,hlr⟩⟩ x₀ a 0 L K :=
    { lipschitzOnWith := fun t ht ↦ (hK t ht).lipschitzOnWith
      continuousOn := fun x _ ↦ hc x
      norm_le := fun t ht x _ ↦ hL t ht x
      mul_max_le := by
        change (L : ℝ) * max (r-l) (l-l) ≤ (a : ℝ) - 0
        simp only [sub_self,max_eq_left (sub_nonneg.mpr hlr),sub_zero]
        rfl }
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma derivative_right_of_Icc {E : Type u149} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r t : ℝ} {f : ℝ → E} {v : E} (ht : t ∈ Ico l r)
    (h : HasDerivWithinAt f v (Icc l r) t) : HasDerivWithinAt f v (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- Uniform perturbation estimate for solutions, including both endpoint times. -/
lemma bounded_ode_perturbation {E : Type u150} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r : ℝ} {f g : ℝ → E → E} {x y : ℝ → E} {K : ℝ≥0} {η : ℝ}
    (hK : ∀ t, LipschitzWith K (g t))
    (hx : ∀ t ∈ Icc l r, HasDerivWithinAt x (f t (x t)) (Icc l r) t)
    (hy : ∀ t ∈ Icc l r, HasDerivWithinAt y (g t (y t)) (Icc l r) t)
    (hxy : x l = y l)
    (herr : ∀ t ∈ Icc l r, ∀ z, dist (f t z) (g t z) ≤ η) :
    ∀ t ∈ Icc l r, dist (x t) (y t) ≤ gronwallBound 0 K η (t-l) := by
  have hh := dist_le_of_approx_trajectories_ODE hK
    (HasDerivWithinAt.continuousOn hx)
    (fun t ht ↦ derivative_right_of_Icc ht (hx t (mem_Icc_of_Ico ht)))
    (fun t ht ↦ herr t (mem_Icc_of_Ico ht) (x t))
    (HasDerivWithinAt.continuousOn hy)
    (fun t ht ↦ derivative_right_of_Icc ht (hy t (mem_Icc_of_Ico ht)))
    (fun t _ ↦ (dist_self _).le)
    (show dist (x l) (y l) ≤ 0 by rw [hxy,dist_self])
  simpa only [add_zero] using hh

lemma bounded_ode_unique {E : Type u151} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r : ℝ} {f : ℝ → E → E} {x y : ℝ → E} {K : ℝ≥0}
    (hK : ∀ t, LipschitzWith K (f t))
    (hx : ∀ t ∈ Icc l r, HasDerivWithinAt x (f t (x t)) (Icc l r) t)
    (hy : ∀ t ∈ Icc l r, HasDerivWithinAt y (f t (y t)) (Icc l r) t)
    (hxy : x l = y l) : EqOn x y (Icc l r) := by
  intro t ht
  apply dist_le_zero.mp
  have hh := bounded_ode_perturbation hK hx hy hxy (fun _ _ _ ↦ (dist_self _).le) t ht
  simpa only [gronwallBound_ε0_δ0] using hh

end SharpLiebThirring.ODEProof
namespace SharpLiebThirring.ODEProof
open Set Metric Filter

/-- Continuous parameter dependence, uniform even when the evaluation time varies. -/
lemma continuous_solution_family {E : Type u152} {P : Type u153} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P] {l r : ℝ} {f : P → ℝ → E → E} {x : P → ℝ → E}
    (K : P → ℝ≥0) (η : P → P → ℝ)
    (hK : ∀ p t, LipschitzWith (K p) (f p t))
    (hx : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (x p) (f p t (x p t)) (Icc l r) t)
    (hinit : ∀ p q, x p l = x q l)
    (hη : ∀ p, Continuous (fun q ↦ η q p)) (hη0 : ∀ p, η p p = 0)
    (hηpos : ∀ p q, 0 ≤ η p q)
    (herr : ∀ p q t, t ∈ Icc l r → ∀ z, dist (f p t z) (f q t z) ≤ η p q) :
    Continuous (fun z : P × Icc l r ↦ x z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ w : P × Icc l r,
      dist (x w.1 w.2) (x z.1 z.2) ≤
        gronwallBound 0 (K z.1) (η w.1 z.1) (r-l) + dist (x z.1 w.2) (x z.1 z.2) := by
    intro w
    apply (dist_triangle _ (x z.1 w.2) _).trans
    apply add_le_add _ (le_refl _)
    exact (bounded_ode_perturbation (hK z.1) (hx w.1) (hx z.1) (hinit w.1 z.1)
      (herr w.1 z.1) w.2 w.2.prop).trans
      (gronwallBound_mono (by positivity) (hηpos w.1 z.1) (K z.1).prop
        (sub_le_sub_right w.2.prop.2 l))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ dist_nonneg)) (Eventually.of_forall hb)
  have hfirst : Tendsto (fun w : P × Icc l r ↦ gronwallBound 0 (K z.1) (η w.1 z.1) (r-l))
      (𝓝 z) (𝓝 0) := by
    have hh := ((gronwallBound_continuous_ε 0 (K z.1) (r-l)).comp
      ((hη z.1).comp continuous_fst)).continuousAt (x := z)
    simpa only [ContinuousAt,Function.comp_def,hη0,gronwallBound_ε0_δ0] using hh
  have hc : Continuous (fun t : Icc l r ↦ x z.1 t) :=
    (HasDerivWithinAt.continuousOn (hx z.1)).domRestrict
  have hsecond : Tendsto (fun w : P × Icc l r ↦ dist (x z.1 w.2) (x z.1 z.2))
      (𝓝 z) (𝓝 0) := by
    have hh := ((hc.comp continuous_snd).dist (continuous_const (y := x z.1 z.2))).continuousAt (x := z)
    simpa only [ContinuousAt,Function.comp_def,dist_self] using hh
  simpa only [add_zero] using hfirst.add hsecond

/-- Ready-to-use parameterized affine forcing in a bounded Lipschitz field. -/
lemma affine_forcing_exists_family {E : Type u154} {P : Type u155} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace P] {l r : ℝ} (hlr : l ≤ r) (x₀ : E)
    (M : E → E) (K B : ℝ≥0) (hK : LipschitzWith K M) (hB : ∀ x, ‖M x‖ ≤ B)
    (a : P → ℝ) (ha : Continuous a) (v : P → C(Icc l r,E)) (hv : Continuous v) :
    ∃ x : P → ℝ → E, (∀ p, x p l = x₀) ∧
      (∀ p t (ht : t ∈ Icc l r), HasDerivWithinAt (x p)
        (a p • M (x p t) + v p ⟨t,ht⟩) (Icc l r) t) ∧
      Continuous (fun z : P × Icc l r ↦ x z.1 z.2) := by
  let V : P → ℝ → E := fun p t ↦ if ht : t ∈ Icc l r then v p ⟨t,ht⟩ else 0
  have hV (p : P) : ContinuousOn (V p) (Icc l r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (v p).continuous using 1
    funext t
    simp only [Set.domRestrict,V,dite_eq_left t.prop]
  have hVnorm (p : P) (t : ℝ) (ht : t ∈ Icc l r) : ‖V p t‖ ≤ ‖v p‖ := by
    simpa only [V,dite_eq_left ht] using (v p).norm_coe_le_norm ⟨t,ht⟩
  let f := fun p t y ↦ a p • M y + V p t
  have hLip (p : P) (t : ℝ) : LipschitzWith (‖a p‖₊ * K) (f p t) := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro y z
    simp only [f,add_sub_add_right_eq_sub,← smul_sub,norm_smul,NNReal.coe_mul,coe_nnnorm]
    exact (mul_le_mul_of_nonneg_left (lipschitzWith_iff_norm_sub_le.mp hK y z)
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  have hex (p : P) : ∃ x : ℝ → E, x l = x₀ ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt x (f p t (x t)) (Icc l r) t := by
    apply bounded_ode_exists hlr x₀ (f p) (‖a p‖₊ * K) (‖a p‖₊ * B + ‖v p‖₊)
      (fun t _ ↦ hLip p t) (fun y ↦ continuousOn_const.add (hV p))
    intro t ht y
    calc ‖f p t y‖ ≤ ‖a p • M y‖ + ‖V p t‖ := norm_add_le _ _
      _ ≤ ‖a p‖ * B + ‖v p‖ := by rw [norm_smul]; gcongr; exact hB _; exact hVnorm p t ht
      _ = _ := by rfl
  choose x hxi hxd using hex
  refine ⟨x,hxi,?_,?_⟩
  · intro p t ht
    simpa only [f,V,dite_eq_left ht] using hxd p t ht
  · let η := fun p q ↦ ‖a p - a q‖ * B + ‖v p - v q‖
    apply continuous_solution_family (fun p ↦ ‖a p‖₊ * K) η hLip hxd
      (fun p q ↦ (hxi p).trans (hxi q).symm)
      (fun p ↦ (ha.sub continuous_const).norm.mul_const _ |>.add (hv.sub continuous_const).norm)
      (fun p ↦ by simp [η]) (fun p q ↦ by dsimp [η]; positivity)
    intro p q t ht y
    have hdiff : f p t y - f q t y = (a p-a q) • M y + (V p t - V q t) := by
      dsimp [f]; module
    rw [dist_eq_norm,hdiff]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · simpa only [V,dite_eq_left ht,ContinuousMap.sub_apply] using
        (v p-v q).norm_coe_le_norm ⟨t,ht⟩

end SharpLiebThirring.ODEProof
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
namespace SharpLiebThirring.MatrixFlow
abbrev Sym (N : ℕ) := selfAdjoint (Matrix (Fin N) (Fin N) ℝ)
def symInclude {N : ℕ} : Sym N →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ where
  toFun := Subtype.val
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl
instance {N : ℕ} : FiniteDimensional ℝ (Sym N) :=
  FiniteDimensional.of_injective symInclude Subtype.val_injective

def symDiag {N : ℕ} (k : Fin N → ℝ) : Sym N := ⟨diagonal k,isHermitian_diagonal _⟩
def symOuter {N : ℕ} (a : Fin N → ℝ) : Sym N :=
  ⟨vecMulVec a a,by ext i j; simp [vecMulVec,mul_comm]⟩
@[simp] lemma symOuter_apply {N : ℕ} (a : Fin N → ℝ) (i j : Fin N) :
    (symOuter a).val i j = a i * a j := rfl

def symEntry {N : ℕ} (i j : Fin N) : Sym N →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A.val i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
@[simp] lemma symEntry_apply {N : ℕ} (i j : Fin N) (A : Sym N) : symEntry i j A = A.val i j := rfl
lemma continuous_symOuter {N : ℕ} : Continuous (symOuter : (Fin N → ℝ) → Sym N) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Fin N → ℝ ↦ vecMulVec a a)
  fun_prop

def symConj {N : ℕ} (s : Fin N → ℝ) : Sym N →L[ℝ] Sym N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ ⟨fun i j ↦ s i * A.val i j * s j,by
        ext i j
        change s j * A.val j i * s i = s i * A.val i j * s j
        have hh : A.val j i = A.val i j := congrFun (congrFun A.prop i) j
        rw [hh]; ring⟩
      map_add' := by intro A B; apply Subtype.ext; ext i j; change s i * (_ + _) * s j = _ + _; ring
      map_smul' := by intro r A; apply Subtype.ext; ext i j; change s i * (r * _) * s j = r * _; ring }
@[simp] lemma symConj_apply {N : ℕ} (s : Fin N → ℝ) (A : Sym N) (i j : Fin N) :
    (symConj s A).val i j = s i * A.val i j * s j := rfl
lemma symConj_val {N : ℕ} (s : Fin N → ℝ) (A : Sym N) :
    (symConj s A).val = diagonal s * A.val * diagonal s := by
  ext i j; simp [diagonal_mul,mul_diagonal]
lemma sign_sq {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i : Fin N) :
    s i * s i = 1 := by rcases hs i with h|h <;> rw [h] <;> norm_num
lemma sign_diagonal_unitary {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    diagonal s ∈ unitary (Matrix (Fin N) (Fin N) ℝ) := by
  rw [Unitary.mem_iff]
  have h : star (diagonal s) = diagonal s := isHermitian_diagonal s
  rw [h,diagonal_mul_diagonal]
  have hh : diagonal (fun i ↦ s i*s i) = (1 : Matrix (Fin N) (Fin N) ℝ) := by
    simp only [sign_sq s hs,diagonal_one]
  exact ⟨hh,hh⟩
lemma norm_symConj {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
    ‖symConj s A‖ = ‖A‖ := by
  change ‖(symConj s A).val‖ = ‖A.val‖
  rw [symConj_val,CStarRing.norm_mul_mem_unitary _ (sign_diagonal_unitary s hs),
    CStarRing.norm_mem_unitary_mul _ (sign_diagonal_unitary s hs)]
lemma symConj_diag {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (k : Fin N → ℝ) : symConj s (symDiag k) = symDiag k := by
  apply Subtype.ext
  ext i j
  by_cases hij : i=j
  · subst j
    change s i * diagonal k i i * s i = diagonal k i i
    rw [diagonal_apply_eq]
    rcases hs i with h|h <;> rw [h] <;> ring
  · change s i * diagonal k i j * s j = diagonal k i j
    simp only [diagonal_apply_ne _ hij,mul_zero,zero_mul]
lemma symConj_outer {N : ℕ} (s a : Fin N → ℝ) :
    symConj s (symOuter a) = symOuter (fun i ↦ s i * a i) := by
  apply Subtype.ext; ext i j; dsimp [symOuter,symConj,vecMulVec]; ring

lemma zero_row_sign {N : ℕ} (i : Fin N) :
    ∀ j : Fin N, (if j=i then (-1 : ℝ) else 1) = 1 ∨ (if j=i then (-1 : ℝ) else 1) = -1 := by
  intro j; split_ifs <;> simp
lemma fixed_reflection_offdiag {N : ℕ} (i : Fin N) (A : Sym N)
    (h : symConj (fun j ↦ if j=i then -1 else 1) A = A) (j : Fin N) (hij : i ≠ j) :
    A.val i j = 0 := by
  have hh := congrArg (fun B : Sym N ↦ B.val i j) h
  simp only [symConj_apply,ite_true,ite_eq_right (Ne.symm hij),neg_mul,one_mul,mul_one] at hh
  linarith

lemma matrix_norm_entry {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    |B i j| ≤ ‖B‖ := by
  let T : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) B
  have h := T.le_opNorm (toLp 2 (Pi.single j (1 : ℝ)))
  have hh := PiLp.norm_apply_le (T (toLp 2 (Pi.single j (1 : ℝ)))) i
  simpa [T, Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM] using hh.trans h

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open ODEProof Set Matrix
open scoped Topology
variable {N : ℕ}

/-- The outer-product forcing, viewed in the supremum-norm space on the time interval. -/
def matrixForcing (ε : ℝ) {l r : ℝ} (u : ℝ → Fin N → ℝ)
    (hu : ContinuousOn u (Icc l r)) (C : Matrix (Fin N) (Fin N) ℝ) : C(Icc l r, Sym N) :=
  ⟨fun t ↦ -ε⁻¹ • symOuter (C *ᵥ u t), by
    exact (continuous_symOuter.comp (continuous_const.matrix_mulVec hu.domRestrict)).const_smul (-ε⁻¹)⟩

lemma continuous_matrixForcing (ε : ℝ) {l r : ℝ} (u : ℝ → Fin N → ℝ)
    (hu : ContinuousOn u (Icc l r)) : Continuous (matrixForcing ε u hu) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × Icc l r ↦
    -ε⁻¹ • symOuter (z.1 *ᵥ u z.2))
  have hu' := hu.domRestrict.comp (continuous_snd (X := Matrix (Fin N) (Fin N) ℝ))
  exact (continuous_symOuter.comp (continuous_fst.matrix_mulVec hu')).const_smul (-ε⁻¹)

def flowRhs (ε : ℝ) (M : Sym N → Sym N) (u : ℝ → Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × ℝ) (t : ℝ) (B : Sym N) : Sym N :=
  (ε⁻¹ * p.2) • M B - ε⁻¹ • symOuter (p.1 *ᵥ u t)

lemma flowRhs_lipschitz (ε : ℝ) (M : Sym N → Sym N) {L : ℝ≥0}
    (hL : LipschitzWith L M) (u : ℝ → Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × ℝ) (t : ℝ) :
    LipschitzWith (‖ε⁻¹*p.2‖₊ * L) (flowRhs ε M u p t) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro A B
  simp only [flowRhs,sub_sub_sub_cancel_right,← smul_sub,norm_smul,
    NNReal.coe_mul,coe_nnnorm]
  exact (mul_le_mul_of_nonneg_left (lipschitzWith_iff_norm_sub_le.mp hL A B)
    (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

lemma matrix_flow_exists {l r : ℝ} (hlr : l ≤ r) (ε : ℝ) (k : Fin N → ℝ)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (M : Sym N → Sym N) (L B : ℝ≥0) (hL : LipschitzWith L M) (hB : ∀ A, ‖M A‖ ≤ B) :
    ∃ X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N,
      (∀ p, X p l = symDiag k) ∧
      (∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t) ∧
      Continuous (fun z : (Matrix (Fin N) (Fin N) ℝ × ℝ) × Icc l r ↦ X z.1 z.2) := by
  obtain ⟨X,hXi,hXd,hXc⟩ := affine_forcing_exists_family hlr (symDiag k) M L B hL hB
    (fun p : Matrix (Fin N) (Fin N) ℝ × ℝ ↦ ε⁻¹*p.2) (by fun_prop)
    (fun p ↦ matrixForcing ε u hu p.1) ((continuous_matrixForcing ε u hu).comp continuous_fst)
  refine ⟨X,hXi,?_,hXc⟩
  intro p t ht
  simpa only [flowRhs,matrixForcing,ContinuousMap.coe_mk,neg_smul,sub_eq_add_neg] using hXd p t ht

lemma matrix_rowSign_mulVec (s : Fin N → ℝ) (C : Matrix (Fin N) (Fin N) ℝ)
    (u : Fin N → ℝ) : (fun i j ↦ s i * C i j) *ᵥ u = fun i ↦ s i * (C *ᵥ u) i := by
  ext i
  simp only [mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma flowRhs_equivariant (ε : ℝ) (M : Sym N → Sym N) (u : ℝ → Fin N → ℝ)
    (s : Fin N → ℝ) (hM : ∀ A, M (symConj s A) = symConj s (M A))
    (C : Matrix (Fin N) (Fin N) ℝ) (θ t : ℝ) (A : Sym N) :
    flowRhs ε M u (fun i j ↦ s i * C i j,θ) t (symConj s A) =
      symConj s (flowRhs ε M u (C,θ) t A) := by
  simp only [flowRhs,hM,map_sub,map_smul,matrix_rowSign_mulVec,symConj_outer]

lemma matrix_flow_equivariant {l r ε : ℝ} {M : Sym N → Sym N} {L : ℝ≥0}
    (hL : LipschitzWith L M) (k : Fin N → ℝ) (u : ℝ → Fin N → ℝ)
    (X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N)
    (hXi : ∀ p, X p l = symDiag k)
    (hXd : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t)
    (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hM : ∀ A, M (symConj s A) = symConj s (M A))
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) :
    EqOn (X (fun i j ↦ s i*C i j,θ)) (fun t ↦ symConj s (X (C,θ) t)) (Icc l r) := by
  apply bounded_ode_unique (fun t ↦ flowRhs_lipschitz ε M hL u (fun i j ↦ s i*C i j,θ) t)
    (hXd _) _ (by rw [hXi,hXi,symConj_diag s hs])
  intro t ht
  have hh := (symConj s).hasFDerivAt.comp_hasDerivWithinAt t (hXd (C,θ) t ht)
  simpa only [Function.comp_def,← flowRhs_equivariant ε M u s hM C θ t (X (C,θ) t)] using hh

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set ODEProof MeasureTheory
variable {N : ℕ}

def symCongr (C : Matrix (Fin N) (Fin N) ℝ) : Sym N →L[ℝ] Sym N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ ⟨C * A.val * C.transpose,
        by
          change (C * A.val * C.transpose).IsHermitian
          simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_mul_mul_conjTranspose C A.prop⟩
      map_add' := by
        intro A B; apply Subtype.ext
        change C * (A.val + B.val) * C.transpose = C * A.val * C.transpose + C * B.val * C.transpose
        rw [mul_add,add_mul]
      map_smul' := by
        intro r A; apply Subtype.ext
        change C * (r • A.val) * C.transpose = r • (C * A.val * C.transpose)
        rw [Matrix.mul_smul,Matrix.smul_mul] }
@[simp] lemma symCongr_apply (C : Matrix (Fin N) (Fin N) ℝ) (A : Sym N) :
    (symCongr C A).val = C * A.val * C.transpose := rfl

lemma symCongr_outer (C : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) :
    symCongr C (symOuter a) = symOuter (C *ᵥ a) := by
  apply Subtype.ext
  simp only [symCongr_apply,symOuter,mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

lemma integral_outer_identity {l r : ℝ} (hlr : l ≤ r)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0) :
    (∫ t in l..r, symOuter (u t)) = symDiag (fun _ ↦ 1) := by
  have hc : ContinuousOn (fun t ↦ symOuter (u t)) (Icc l r) := continuous_symOuter.comp_continuousOn hu
  apply Subtype.ext
  ext i j
  have hh := (symEntry i j).intervalIntegral_comp_comm (hc.intervalIntegrable_of_Icc (μ := volume) hlr)
  change (∫ t in l..r, u t i*u t j) = (∫ t in l..r, symOuter (u t)).val i j at hh
  rw [← hh,ho]
  exact (diagonal_apply (fun _ : Fin N ↦ (1 : ℝ)) i j).symm

lemma integral_outer_mulVec {l r : ℝ} (hlr : l ≤ r)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) :
    (∫ t in l..r, symOuter (C *ᵥ u t)).val = C * C.transpose := by
  have hc : ContinuousOn (fun t ↦ symOuter (u t)) (Icc l r) := continuous_symOuter.comp_continuousOn hu
  have hh := (symCongr C).intervalIntegral_comp_comm (hc.intervalIntegrable_of_Icc (μ := volume) hlr)
  simp only [symCongr_outer,integral_outer_identity hlr u hu ho] at hh
  rw [hh]
  simp only [symCongr_apply,symDiag,diagonal_one,mul_one]

lemma integrate_affine_ode {E : Type u156} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {l r a b : ℝ} (hlr : l ≤ r) (X V W : ℝ → E)
    (hV : ContinuousOn V (Icc l r)) (hW : ContinuousOn W (Icc l r))
    (hd : ∀ t ∈ Icc l r, HasDerivWithinAt X (a • V t - b • W t) (Icc l r) t) :
    a • (∫ t in l..r, V t) - b • (∫ t in l..r, W t) = X r - X l := by
  have hc := (hV.const_smul a).sub (hW.const_smul b)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (HasDerivWithinAt.continuousOn hd)
    (fun t ht ↦ (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (hc.intervalIntegrable_of_Icc (μ := volume) hlr)
  have hiV : IntervalIntegrable (fun t ↦ a • V t) volume l r := by
    exact (hV.intervalIntegrable_of_Icc (μ := volume) hlr).smul a
  have hiW : IntervalIntegrable (fun t ↦ b • W t) volume l r := by
    exact (hW.intervalIntegrable_of_Icc (μ := volume) hlr).smul b
  rw [intervalIntegral.integral_sub hiV hiW,intervalIntegral.integral_smul,
    intervalIntegral.integral_smul] at hh
  exact hh

lemma flow_integral_sub {l r ε θ : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (hM : Continuous M)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (C : Matrix (Fin N) (Fin N) ℝ) (X : ℝ → Sym N)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,θ) t (X t)) (Icc l r) t) :
    (ε⁻¹ * θ) • (∫ t in l..r, M (X t)) - ε⁻¹ • (∫ t in l..r, symOuter (C *ᵥ u t)) = X r - X l := by
  apply integrate_affine_ode hlr X (fun t ↦ M (X t)) (fun t ↦ symOuter (C *ᵥ u t))
    (hM.comp_continuousOn (HasDerivWithinAt.continuousOn hXd)) _ hXd
  apply continuous_symOuter.comp_continuousOn
  exact (show Continuous (fun v : Fin N → ℝ ↦ C *ᵥ v) by fun_prop).comp_continuousOn hu

lemma flow_integral_identity {l r ε : ℝ} (hlr : l ≤ r) (hε : ε ≠ 0)
    (M : Sym N → Sym N) (hM : Continuous M) (k : Fin N → ℝ)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (X : ℝ → Sym N)
    (hXi : X l = symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,θ) t (X t)) (Icc l r) t) :
    C * C.transpose = ε • (diagonal k - (X r).val) + θ • (∫ t in l..r, M (X t)).val := by
  have hh := flow_integral_sub hlr M hM u hu C X hXd
  have he := congrArg (fun Z : Sym N ↦ ε • Z) hh
  simp only [smul_sub,smul_smul,mul_inv_cancel₀ hε,one_smul] at he
  have hcoef : ε * (ε⁻¹ * θ) = θ := by field_simp
  rw [hcoef,hXi] at he
  have he' := congrArg (fun Z : Sym N ↦ Z.val) he
  change θ • (∫ t in l..r, M (X t)).val - (∫ t in l..r, symOuter (C *ᵥ u t)).val =
    ε • (X r).val - ε • diagonal k at he'
  rw [integral_outer_mulVec hlr u hu ho C,sub_eq_iff_eq_add] at he'
  rw [he',smul_sub]
  abel

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set MeasureTheory
variable {N : ℕ}

lemma gram_entry_bound (C : Matrix (Fin N) (Fin N) ℝ) {D : ℝ}
    (hD : ‖C * C.transpose‖ ≤ D) (i j : Fin N) : |C i j| ≤ max D 0 + 1 := by
  have hsq : (C i j)^2 ≤ (C*C.transpose) i i := by
    simpa only [mul_apply,transpose_apply,pow_two] using
      (Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin N))) ↦ mul_self_nonneg (C i a))
        (Finset.mem_univ j))
  have hh := hsq.trans ((le_abs_self _).trans ((matrix_norm_entry _ i i).trans hD))
  have hm := le_max_left D 0
  have hn := le_max_right D 0
  have hs := sq_abs (C i j)
  nlinarith [abs_nonneg (C i j)]

lemma bounded_integral_norm {E : Type u157} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r B : ℝ} (hlr : l ≤ r) (f : ℝ → E) (hf : ∀ t ∈ Icc l r, ‖f t‖ ≤ B) :
    ‖∫ t in l..r, f t‖ ≤ (r-l)*B := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t (ht : t ∈ Set.uIoc l r) ↦ hf t (by
      rw [uIoc_of_le hlr] at ht
      exact Ioc_subset_Icc_self ht))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hlr),mul_comm] using hh

lemma matching_gram_norm {l r ε : ℝ} (hlr : l ≤ r) (hε : ε ≠ 0)
    (M : Sym N → Sym N) (hM : Continuous M) (B : ℝ≥0) (hB : ∀ A, ‖M A‖ ≤ B)
    (k : Fin N → ℝ) (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (X : ℝ → Sym N)
    (hXi : X l = symDiag k) (hXf : X r = -symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,θ) t (X t)) (Icc l r) t) :
    ‖C * C.transpose‖ ≤ |ε| *(2*‖k‖) + (r-l)*B := by
  rw [flow_integral_identity hlr hε M hM k u hu ho C θ X hXi hXd,hXf]
  have hi := bounded_integral_norm hlr (fun t ↦ M (X t)) (fun _ _ ↦ hB _)
  have he : (-(symDiag k)).val = -diagonal k := rfl
  rw [he,sub_neg_eq_add]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hθ.1]
  apply add_le_add
  · have hh := norm_add_le (diagonal k) (diagonal k)
    rw [Matrix.l2_opNorm_diagonal] at hh
    exact mul_le_mul_of_nonneg_left (hh.trans_eq (by ring)) (abs_nonneg ε)
  · exact (mul_le_of_le_one_left (norm_nonneg _) hθ.2).trans hi

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
