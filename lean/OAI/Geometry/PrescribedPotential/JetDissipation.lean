import Mathlib
import OAI.Geometry.PrescribedPotential.DirectionalJetEnergy

namespace OAI

/-! Jet Dissipation. -/

section

 
noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma jetFamily_cons (e : ι → E) (m : ℕ) (u : E → F) (i : ι) (σ : Fin m → ι) :
    jetFamily e (m+1) u (Fin.cons i σ) = dir (e i) (jetFamily e m u σ) := by
  simp only [jetFamily,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,word]

lemma jetEnergy_succ (e : ι → E) (m : ℕ) (u : E → F) (x : E) :
    jetEnergy e (m+1) u x = familyDissipation e (jetFamily e m u) x := by
  unfold jetEnergy familyEnergy familyDissipation frameGradientSq
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m+1) => ι))
    (fun σ => ‖jetFamily e (m+1) u σ x‖^2)]
  simp only [Fintype.sum_prod_type]
  change (∑ i : ι, ∑ σ : Fin m → ι, ‖jetFamily e (m+1) u (Fin.cons i σ) x‖^2) = _
  simp only [jetFamily_cons]
  exact Finset.sum_comm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
def linearArray (e : ι → E) : (E →L[ℝ] F) →ₗ[ℝ] PiLp 2 (fun _ : ι => F) where
  toFun T := WithLp.toLp 2 (fun i => T (e i))
  map_add' T R := by ext i; rfl
  map_smul' c T := by ext i; rfl

omit [Fintype ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma linearArray_injective (e : Basis ι ℝ E) :
    Function.Injective (linearArray (F := F) e) := by
  intro T R h
  apply ContinuousLinearMap.coe_injective
  exact e.ext (fun i => congrArg (fun a : PiLp 2 (fun _ : ι => F) => a i) h)

lemma linearArray_norm_control (e : Basis ι ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : E →L[ℝ] F, ‖T‖ ≤ C*‖linearArray e T‖ := by
  obtain ⟨C,hC,hb⟩ := (linearArray (F := F) e).injective_iff_antilipschitz.mp (linearArray_injective e)
  refine ⟨C,by exact_mod_cast hC,fun T => ?_⟩
  simpa only [map_zero,dist_zero_right] using hb.le_mul_dist T 0

lemma linear_frame_coercivity (e : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : E →L[ℝ] F) (τ : E ≃L[ℝ] E) (B : ℝ),
      0 ≤ B → ‖τ.symm.toContinuousLinearMap‖ ≤ B →
      ∑ i, ‖T (e i)‖^2 ≤ C*B^2*(∑ i, ‖T (τ (e i))‖^2) := by
  obtain ⟨A,hA,hb⟩ := linearArray_norm_control (F := F) e.toBasis
  refine ⟨(Fintype.card ι+1)*A^2,by positivity,fun T τ B hB hτ => ?_⟩
  have he : (T.comp τ.toContinuousLinearMap).comp τ.symm.toContinuousLinearMap = T := by ext x; simp
  have ht : ‖T‖ ≤ A*‖linearArray e (T.comp τ.toContinuousLinearMap)‖*B := by
    calc
      _ = ‖(T.comp τ.toContinuousLinearMap).comp τ.symm.toContinuousLinearMap‖ := congrArg norm he.symm
      _ ≤ ‖T.comp τ.toContinuousLinearMap‖*‖τ.symm.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (A*‖linearArray e (T.comp τ.toContinuousLinearMap)‖)*B :=
        mul_le_mul (hb _) hτ (norm_nonneg _) (by positivity)
  have hs : ‖T‖^2 ≤ A^2*B^2*(∑ i, ‖T (τ (e i))‖^2) := by
    have h := pow_le_pow_left₀ (norm_nonneg T) ht 2
    rw [mul_pow,mul_pow,PiLp.norm_sq_eq_of_L2] at h
    simpa only [linearArray,LinearMap.coe_mk,AddHom.coe_mk,PiLp.toLp_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,mul_assoc,mul_left_comm,mul_comm] using h
  calc
    _ ≤ ∑ _i : ι, ‖T‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [e.norm_eq_one,mul_one] using T.le_opNorm (e i)) 2
    _ = (Fintype.card ι : ℝ)*‖T‖^2 := by simp
    _ ≤ (Fintype.card ι+1)*(A^2*B^2*(∑ i, ‖T (τ (e i))‖^2)) := by
      have h1 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (Fintype.card ι : ℝ))
      have h2 : 0 ≤ A^2*B^2*(∑ i, ‖T (τ (e i))‖^2) := by positivity
      nlinarith only [h1,h2]
    _ = _ := by ring

lemma jetEnergy_frame_coercivity (e : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (u : E → F) (x : E) (τ : E ≃L[ℝ] E) (B : ℝ),
      0 ≤ B → ‖τ.symm.toContinuousLinearMap‖ ≤ B →
      jetEnergy e (m+1) u x ≤ C*B^2*familyDissipation (fun i => τ (e i)) (jetFamily e m u) x := by
  obtain ⟨C,hC,hb⟩ := linear_frame_coercivity (F := F) e
  refine ⟨C,hC,fun m u x τ B hB hτ => ?_⟩
  rw [jetEnergy_succ]
  unfold familyDissipation frameGradientSq dir
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun σ _ => hb (fderiv ℝ (jetFamily e m u σ) x) τ B hB hτ)
end HigherJet

end
end

end OAI
