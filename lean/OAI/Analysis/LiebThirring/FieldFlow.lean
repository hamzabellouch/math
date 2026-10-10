import OAI.Analysis.LiebThirring.FlowContinuation

namespace OAI

universe u158 u159 u160 u161 u162 u163 u164 u165

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology

noncomputable section
open Set Metric
open scoped NNReal
namespace SharpLiebThirring.ODEProof

/-- A radial auxiliary cutoff; its lack of smoothness is harmless because only
Lipschitz regularity is needed for the flow and barriers. -/
def radialCutoff {E : Type u158} [NormedAddCommGroup E] (R : ℝ) (x : E) : ℝ :=
  max 0 (min 1 (R+1-‖x‖))

lemma radialCutoff_nonneg {E : Type u159} [NormedAddCommGroup E] (R : ℝ) (x : E) :
    0 ≤ radialCutoff R x := le_max_left _ _
lemma radialCutoff_le_one {E : Type u160} [NormedAddCommGroup E] (R : ℝ) (x : E) :
    radialCutoff R x ≤ 1 := max_le zero_le_one (min_le_left _ _)
lemma radialCutoff_eq_one {E : Type u161} [NormedAddCommGroup E] {R : ℝ} {x : E}
    (hx : ‖x‖ ≤ R) : radialCutoff R x = 1 := by
  unfold radialCutoff
  rw [min_eq_left (by linarith),max_eq_right zero_le_one]
lemma radialCutoff_eq_zero {E : Type u162} [NormedAddCommGroup E] {R : ℝ} {x : E}
    (hx : R+1 ≤ ‖x‖) : radialCutoff R x = 0 := by
  unfold radialCutoff
  exact max_eq_left ((min_le_right _ _).trans (by linarith))
lemma radialCutoff_lipschitz {E : Type u163} [NormedAddCommGroup E] (R : ℝ) :
    LipschitzWith 1 (radialCutoff R : E → ℝ) := by
  have h : LipschitzWith 1 (fun x : E ↦ R+1-‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_left,Real.norm_eq_abs,abs_sub_comm,NNReal.coe_one,one_mul,dist_eq_norm]
      using abs_norm_sub_norm_le x y
  exact (h.const_min 1).const_max 0

lemma bounded_lipschitz_radial_cutoff {E : Type u164} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (M : E → E) (hM : LocallyLipschitz M) (R : ℝ) :
    ∃ K B : ℝ≥0, LipschitzWith K (fun x ↦ radialCutoff R x • M x) ∧
      ∀ x, ‖radialCutoff R x • M x‖ ≤ B := by
  obtain ⟨L,hL⟩ := hM.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) (R+2))
  obtain ⟨b,hb⟩ := (isCompact_closedBall (0 : E) (R+2)).bddAbove_image
    hM.continuous.norm.continuousOn
  let B : ℝ≥0 := ⟨max b 0, le_max_right _ _⟩
  have hB (x : E) (hx : ‖x‖ ≤ R+2) : ‖M x‖ ≤ B :=
    (hb (mem_image_of_mem _ (by simpa only [mem_closedBall,dist_zero_right] using hx))).trans
      (le_max_left b 0)
  let F := fun x ↦ radialCutoff R x • M x
  have hzero (x : E) (hx : R+1 ≤ ‖x‖) : F x = 0 := by
    simp only [F,radialCutoff_eq_zero hx,zero_smul]
  have hbound (x : E) : ‖F x‖ ≤ B := by
    by_cases hx : ‖x‖ ≤ R+2
    · dsimp only [F]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg R x)]
      exact (mul_le_mul_of_nonneg_right (radialCutoff_le_one R x) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hB x hx)
    · rw [hzero x (by linarith [lt_of_not_ge hx]),norm_zero]; exact B.prop
  have hlocal : LipschitzOnWith (L+B) F (closedBall (0 : E) (R+2)) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro x hx y hy
    have hyd : ‖y‖ ≤ R+2 := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hid : F x - F y = radialCutoff R x • (M x-M y) +
        (radialCutoff R x-radialCutoff R y) • M y := by dsimp [F]; module
    rw [hid]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg R x)]
    have hh := hL.dist_le_mul x hx y hy
    rw [dist_eq_norm,dist_eq_norm] at hh
    have hχ := (radialCutoff_lipschitz (E := E) R).dist_le_mul x y
    simp only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] at hχ
    calc
      _ ≤ 1 * ((L : ℝ)*‖x-y‖) + ‖x-y‖ * (B : ℝ) := by
        exact add_le_add
          (mul_le_mul (radialCutoff_le_one R x) hh (norm_nonneg _) zero_le_one)
          (mul_le_mul hχ (hB y hyd) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by push_cast; ring
  have hfar (x y : E) (hx : ‖x‖ < R+1) (hy : R+2 < ‖y‖) :
      ‖F x - F y‖ ≤ (L+B : ℝ≥0) * ‖x-y‖ := by
    rw [hzero y (by linarith),sub_zero]
    have hd : 1 ≤ ‖x-y‖ := by
      have hh := norm_le_norm_add_norm_sub x y
      linarith
    calc
      _ ≤ (B : ℝ) := hbound x
      _ ≤ (L : ℝ) + B := le_add_of_nonneg_left L.prop
      _ ≤ ((L : ℝ) + B) * ‖x-y‖ := le_mul_of_one_le_right (add_nonneg L.prop B.prop) hd
      _ = _ := rfl
  refine ⟨L+B,B,?_,hbound⟩
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  change ‖F x - F y‖ ≤ (L+B : ℝ≥0) * ‖x-y‖
  by_cases hx : ‖x‖ ≤ R+2
  · by_cases hy : ‖y‖ ≤ R+2
    · exact lipschitzOnWith_iff_norm_sub_le.mp hlocal
        (by simpa only [mem_closedBall,dist_zero_right] using hx)
        (by simpa only [mem_closedBall,dist_zero_right] using hy)
    · by_cases hx' : R+1 ≤ ‖x‖
      · rw [hzero x hx',hzero y (by linarith [lt_of_not_ge hy]),sub_self,norm_zero]
        positivity
      · exact hfar x y (lt_of_not_ge hx') (lt_of_not_ge hy)
  · by_cases hy : R+1 ≤ ‖y‖
    · rw [hzero x (by linarith [lt_of_not_ge hx]),hzero y hy,sub_self,norm_zero]; positivity
    · simpa only [norm_sub_rev] using hfar y x (lt_of_not_ge hy) (lt_of_not_ge hx)

end SharpLiebThirring.ODEProof
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SharpLiebThirring.MatrixFlow
variable {n : Type u165} [Fintype n] [DecidableEq n]

lemma cfc_isolated_row {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n)
    (hi : ∀ j, i ≠ j → A i j = 0) (f : ℝ → ℝ) (j : n) :
    cfc f A i j = f (A i i) * (1 : Matrix n n ℝ) i j := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hAU : A * U = U * diagonal hA.eigenvalues := by
    conv_lhs => rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    change U * diagonal hA.eigenvalues * star U * U = _
    rw [mul_assoc,mul_assoc,Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.prop,mul_one]
  have hspec (l : n) : U i l = 0 ∨ hA.eigenvalues l = A i i := by
    have he := congrFun (congrFun hAU i) l
    rw [mul_diagonal] at he
    have hr : (A * U) i l = A i i * U i l := by
      rw [mul_apply]
      apply Finset.sum_eq_single i
      · intro b _ hbi
        rw [hi b (Ne.symm hbi),zero_mul]
      · simp
    rw [hr] at he
    by_cases hz : U i l = 0
    · exact Or.inl hz
    · exact Or.inr (mul_right_cancel₀ hz (by nlinarith : hA.eigenvalues l * U i l = A i i * U i l))
  rw [hA.cfc_eq,IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  change (U * diagonal (f ∘ hA.eigenvalues) * star U) i j = _
  rw [← hU]
  conv_rhs => rw [Matrix.mul_apply,Finset.mul_sum]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_diagonal]
  rcases hspec l with h|h
  · simp only [h,zero_mul,mul_zero]
  · simp only [Function.comp_apply,h]
    ring

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open MatrixProof ScalarProof Matrix
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

def sourceField (σ δ : ℝ) (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) : Sym N → Sym N :=
  fun A ↦ ⟨matrixField σ δ k A.val,matrixField_isHermitian hσ hδ k A.prop⟩

lemma sourceField_locallyLipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    LocallyLipschitz (sourceField σ δ hσ hδ k) := by
  have h := (realPartCLM.lipschitzWith.locallyLipschitz).comp
    ((hermitianField_locallyLipschitz hσ hδ (realK2SelfAdjoint k).prop).comp
      realHermitianComplexifyCLM.lipschitzWith.locallyLipschitz)
  have hh : LocallyLipschitz (fun A : Sym N ↦ matrixField σ δ k A.val) := by
    convert! h using 1
    funext A
    exact matrixField_eq_realPart hσ hδ k A.prop
  intro A
  obtain ⟨L,s,hs,hL⟩ := hh A
  refine ⟨L,s,hs,?_⟩
  intro x hx y hy
  exact hL hx hy

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open MatrixProof ScalarProof Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

def complexUnitary (U : unitary (Matrix (Fin N) (Fin N) ℝ)) :
    unitary (Matrix (Fin N) (Fin N) ℂ) :=
  Unitary.map (StarMonoidHom.ofClass (complexify (n := Fin N))) U

lemma complexify_conj (U : unitary (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin N) (Fin N) ℝ) :
    complexify (Unitary.conjStarAlgAut ℝ _ U A) =
      Unitary.conjStarAlgAut ℂ _ (complexUnitary U) (complexify A) := by
  simp only [Unitary.conjStarAlgAut_apply,map_mul,map_star]
  rfl

lemma complexify_symConj (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
    complexify (symConj s A).val = Unitary.conjStarAlgAut ℂ _
      (complexUnitary ⟨diagonal s,sign_diagonal_unitary s hs⟩) (complexify A.val) := by
  rw [← complexify_conj]
  congr 1
  rw [Unitary.conjStarAlgAut_apply,symConj_val]
  congr 1
  exact (isHermitian_diagonal s).symm

lemma sourceField_equivariant {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ)
    (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
    sourceField σ δ hσ hδ k (symConj s A) = symConj s (sourceField σ δ hσ hδ k A) := by
  let U := complexUnitary ⟨diagonal s,sign_diagonal_unitary s hs⟩
  have hK := complexify_symConj s hs (symDiag (fun i ↦ k i ^ 2))
  rw [symConj_diag s hs] at hK
  have hh := hermitianField_conj hσ hδ (realK2SelfAdjoint k).prop (complexify_hermitian A.prop) U
  change complexify (diagonal (fun i ↦ k i^2)) = Unitary.conjStarAlgAut ℂ _ U (complexify (diagonal (fun i ↦ k i^2))) at hK
  change hermitianField σ δ (Unitary.conjStarAlgAut ℂ _ U (complexify (diagonal (fun i ↦ k i^2)))) _ = Unitary.conjStarAlgAut ℂ _ U (hermitianField σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A.val)) at hh
  rw [← hK,← complexify_symConj s hs A,← complexify_matrixField hσ hδ k (symConj s A).prop,
    ← complexify_matrixField hσ hδ k A.prop] at hh
  have hf := complexify_symConj s hs (sourceField σ δ hσ hδ k A)
  change complexify (symConj s (sourceField σ δ hσ hδ k A)).val = _ at hf
  change complexify (symConj s (sourceField σ δ hσ hδ k A)).val =
    Unitary.conjStarAlgAut ℂ _ U (complexify (matrixField σ δ k A.val)) at hf
  rw [← hf] at hh
  apply Subtype.ext
  simpa only [realPartCLM_complexify,sourceField] using congrArg realPartCLM hh

def matrixEntry (i j : Fin N) : Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    {toFun := fun A ↦ A i j, map_add' := by intros; rfl, map_smul' := by intros; rfl}
@[simp] lemma matrixEntry_apply (i j : Fin N) (A : Matrix (Fin N) (Fin N) ℝ) : matrixEntry i j A = A i j := rfl

lemma matrixField_tendsto {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    Tendsto (truncatedField σ δ k A) atTop (𝓝 (matrixField σ δ k A)) := by
  have ht : Tendsto (fun R ↦ complexify (truncatedField σ δ k A R)) atTop
      (𝓝 (hermitianField σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A))) := by
    have h := hermitianField_cutoff_limit hσ hδ (realK2SelfAdjoint k).prop (complexify_hermitian hA)
    change Tendsto (fun R ↦ fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A) s) atTop (𝓝 _) at h
    simpa only [complexify_truncatedField hδ k hA,realK2SelfAdjoint] using h
  have hh := realPartCLM.continuous.continuousAt.tendsto.comp ht
  rw [matrixField_eq_realPart hσ hδ k hA]
  change Tendsto (fun R ↦ realPartCLM (complexify (truncatedField σ δ k A R))) atTop (𝓝 _) at hh
  simpa only [realPartCLM_complexify] using hh

lemma matrixField_isolated_coordinate {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ)
    (A : Sym N) (i : Fin N) (hi : ∀ j, i ≠ j → A.val i j = 0) :
    (sourceField σ δ hσ hδ k A).val i i = scalarMu σ δ (k i ^ 2 - A.val i i ^ 2) := by
  have hx (s : ℝ) : (cfc (regularizedPrimitive σ δ) (matrixX k A.val s)) i i =
      regularizedPrimitive σ δ ((s-A.val i i)^2+(k i^2-A.val i i^2)) := by
    rw [cfc_isolated_row (matrixX_hermitian k A.prop s) i (fun j hij ↦ ?_) _ i]
    · simp only [one_apply_eq,mul_one]
      congr 1
      simp only [matrixX,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        diagonal_apply_eq,one_apply_eq,mul_one]
      ring
    · simp only [matrixX,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        diagonal_apply_ne _ hij,one_apply_ne hij,hi j hij,mul_zero,sub_zero,add_zero]
  have hc : Continuous (fun s : ℝ ↦ cfc (regularizedPrimitive σ δ) (matrixX k A.val s) -
      regularizedPrimitive σ δ (s^2) • (1 : Matrix (Fin N) (Fin N) ℝ)) := by
    have hx : Continuous (fun s ↦ cfc (regularizedPrimitive σ δ) (matrixX k A.val s)) :=
      Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ Filter.univ_mem
        (by unfold matrixX; fun_prop) (matrixX_hermitian k A.prop)
        (primitive_differentiable σ hδ).continuous.continuousOn
    exact hx.sub (((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2)).smul continuous_const)
  have he (R : ℝ) : truncatedField σ δ k A.val R i i = fieldNormalization σ * ∫ s in -R..R,
      regularizedPrimitive σ δ ((s-A.val i i)^2+(k i^2-A.val i i^2)) - regularizedPrimitive σ δ (s^2) := by
    have h := (matrixEntry i i).intervalIntegral_comp_comm (μ := volume) (hc.intervalIntegrable (-R) R)
    simp only [matrixEntry_apply] at h
    rw [truncatedField,Matrix.smul_apply,smul_eq_mul,← h]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,one_apply_eq,mul_one,hx]
  have hl := (matrixEntry i i).continuous.continuousAt.tendsto.comp (matrixField_tendsto hσ hδ k A.prop)
  change Tendsto (fun R ↦ truncatedField σ δ k A.val R i i) atTop (𝓝 _) at hl
  simp only [he] at hl
  exact tendsto_nhds_unique hl (primitive_shift_limit hσ hδ (k i^2-A.val i i^2) (A.val i i))

def scalarDiag : ℝ →L[ℝ] Sym N :=
  LinearMap.toContinuousLinearMap
    ({toFun := fun x : ℝ ↦ symDiag (fun _ ↦ x)
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (diagonal_add (fun _ : Fin N ↦ x) (fun _ ↦ y)).symm
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact diagonal_smul r (fun _ : Fin N ↦ x)} : ℝ →ₗ[ℝ] Sym N)

lemma coordinate_mu_locallyLipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (i : Fin N) : LocallyLipschitz (fun x : ℝ ↦ scalarMu σ δ (k i ^ 2-x^2)) := by
  have hh := (symEntry i i).lipschitzWith.locallyLipschitz.comp
    ((sourceField_locallyLipschitz hσ hδ k).comp scalarDiag.lipschitzWith.locallyLipschitz)
  convert! hh using 1
  funext x
  change _ = matrixField σ δ k (diagonal (fun _ ↦ x)) i i
  rw [matrixField_diagonal hσ hδ,diagonal_apply_eq]

end SharpLiebThirring.MatrixFlow

end
end
end
end
end
end
end

end OAI
