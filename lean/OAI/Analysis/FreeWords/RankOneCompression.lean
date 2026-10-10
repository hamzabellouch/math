import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageBasic
import OAI.Analysis.FreeWords.SecondMoment
import OAI.Analysis.FreeWords.TraceTransferDefinitions

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKWeingarten MeasureTheory

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

variable {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)

def rankOne (z : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ) : ConcreteAlgebra M :=
  ρ (U : Matrix (Fin d) (Fin d) ℂ)*matrixUnit ρ z z*star (ρ (U : Matrix (Fin d) (Fin d) ℂ))

theorem rankOne_projection (z : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsStarProjection (rankOne ρ z U) := by
  have hu : star (ρ (U : Matrix (Fin d) (Fin d) ℂ))*ρ (U : Matrix (Fin d) (Fin d) ℂ)=1 := by
    rw [← map_star,← map_mul,U.property.1,map_one]
  constructor
  · change (ρ _*matrixUnit ρ z z*star (ρ _))*(ρ _*matrixUnit ρ z z*star (ρ _))=_
    calc
      _ = ρ U.val*matrixUnit ρ z z*(star (ρ U.val)*ρ U.val)*matrixUnit ρ z z*star (ρ U.val) := by noncomm_ring
      _ = _ := by rw [hu,mul_one,mul_assoc (ρ _),matrixUnit_mul_same]; rfl
  · change star (ρ _*matrixUnit ρ z z*star (ρ _))=_
    simp only [star_mul,star_star,matrixUnit_star,mul_assoc,rankOne]

theorem matrixUnit_trace (z : Fin d) : τ.map (matrixUnit ρ z z)=(d : ℂ)⁻¹ := by
  have he (i : Fin d) : τ.map (matrixUnit ρ i i)=τ.map (matrixUnit ρ z z) := by
    rw [← matrixUnit_mul_same ρ i z i,τ.tracial,matrixUnit_mul_same]
  have hh := congrArg τ.map (matrixUnit_sum_diag ρ)
  rw [map_sum,τ.normalized] at hh
  simp_rw [he] at hh
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  have hd0 : (d : ℂ)≠0 := by exact_mod_cast (show d≠0 from Nat.ne_of_gt (Nat.zero_lt_of_lt z.isLt))
  rw [← one_div]
  apply (eq_div_iff hd0).mpr
  simpa only [mul_comm] using hh

theorem rankOne_trace (z : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    τ.map (rankOne ρ z U)=(d : ℂ)⁻¹ := by
  rw [rankOne,τ.tracial (ρ _*_),← mul_assoc,← map_star,← map_mul,U.property.1,map_one,one_mul]
  exact matrixUnit_trace τ ρ z

theorem rankOne_expansion (z : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    rankOne ρ z U=∑ i,∑ j,
      ((U : Matrix (Fin d) (Fin d) ℂ) i z*star ((U : Matrix (Fin d) (Fin d) ℂ) j z)) • matrixUnit ρ i j := by
  rw [rankOne,matrixUnit,← map_star,← map_mul,← map_mul,matrix_representation]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Matrix.mul_apply,Matrix.single_apply,Matrix.star_apply,ite_and]

def columnQuartic (z i j k l : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ) : ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) i z * star ((U : Matrix (Fin d) (Fin d) ℂ) j z) *
  (U : Matrix (Fin d) (Fin d) ℂ) k z * star ((U : Matrix (Fin d) (Fin d) ℂ) l z)

theorem continuous_columnQuartic (z i j k l : Fin d) : Continuous (columnQuartic z i j k l) := by
  have he (a b : Fin d) : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      (U : Matrix (Fin d) (Fin d) ℂ) a b) :=
    (matrixApplyCLM a b).continuous.comp continuous_subtype_val
  exact (((he i z).mul (he j z).star).mul (he k z)).mul (he l z).star

theorem rankOne_pair_expansion (z : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (x y : ConcreteAlgebra M) :
    τ.map (rankOne ρ z U*x*rankOne ρ z U*y)=
      ∑ i,∑ j,∑ k,∑ l, columnQuartic z i j k l U * τ.map (matrixUnit ρ i j*x*matrixUnit ρ k l*y) := by
  have hleft (A : ConcreteAlgebra M) :
      τ.map (rankOne ρ z U*x*A*y)=∑ i,∑ j,
        ((U : Matrix (Fin d) (Fin d) ℂ) i z*star ((U : Matrix (Fin d) (Fin d) ℂ) j z)) *
          τ.map (matrixUnit ρ i j*x*A*y) := by
    rw [rankOne_expansion]
    simp only [Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul]
  rw [hleft]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [rankOne_expansion]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    map_sum,map_smul,smul_eq_mul,columnQuartic]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem continuous_rankOne_pair (z : Fin d) (x y : ConcreteAlgebra M) :
    Continuous (fun U => τ.map (rankOne ρ z U*x*rankOne ρ z U*y)) := by
  simp_rw [rankOne_pair_expansion]
  apply continuous_finsetSum _
  intro i hi
  apply continuous_finsetSum _
  intro j hj
  apply continuous_finsetSum _
  intro k hk
  apply continuous_finsetSum _
  intro l hl
  exact (continuous_columnQuartic z i j k l).mul continuous_const

theorem integral_rankOne_pair (hd : 2 ≤ d) (z : Fin d) (x y : ConcreteAlgebra M) :
    (∫ U : Matrix.unitaryGroup (Fin d) ℂ, τ.map (rankOne ρ z U*x*rankOne ρ z U*y) ∂matrixHaar d) =
    ((d : ℂ)*((d : ℂ)+1))⁻¹ * (τ.map (x*y)+(d : ℂ)*τ.map (matrixAverage ρ x*y)) := by
  have : NeZero d := ⟨by omega⟩
  have hint (i j k l : Fin d) :
      Integrable (fun U => columnQuartic z i j k l U*τ.map (matrixUnit ρ i j*x*matrixUnit ρ k l*y)) (matrixHaar d) :=
    ((continuous_columnQuartic z i j k l).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfour (f : Fin d → Fin d → Fin d → Fin d → Matrix.unitaryGroup (Fin d) ℂ → ℂ)
      (hf : ∀ i j k l, Integrable (f i j k l) (matrixHaar d)) :
      (∫ U, ∑ i,∑ j,∑ k,∑ l,f i j k l U ∂matrixHaar d)=
        ∑ i,∑ j,∑ k,∑ l,∫ U,f i j k l U ∂matrixHaar d := by
    rw [integral_finsetSum _ (fun _ _ => integrable_finsetSum _ (fun _ _ => integrable_finsetSum _
      (fun _ _ => integrable_finsetSum _ (fun _ _ => hf _ _ _ _))))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun _ _ => integrable_finsetSum _
      (fun _ _ => integrable_finsetSum _ (fun _ _ => hf _ _ _ _)))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum _ (fun _ _ => integrable_finsetSum _ (fun _ _ => hf _ _ _ _))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum _ (fun _ _ => hf _ _ _ _)]
  have hm (i j k l : Fin d) : (∫ U,columnQuartic z i j k l U ∂matrixHaar d)=
      ((d : ℂ)*((d : ℂ)+1))⁻¹ *
      ((if i=j ∧ k=l then 1 else 0)+(if i=l ∧ k=j then 1 else 0)) := haar_column_fourth d hd z i j k l
  simp_rw [rankOne_pair_expansion]
  rw [hfour _ hint]
  simp_rw [integral_mul_const,hm]
  simp only [mul_assoc,← Finset.mul_sum]
  congr 1
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,one_mul,zero_mul,ite_and]
  simp only [Finset.sum_const_zero,Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hd0 : (d : ℂ)≠0 := by exact_mod_cast (by omega : d≠0)
  have hfirst : (∑ i,∑ k, τ.map (matrixUnit ρ i i*x*matrixUnit ρ k k*y))=τ.map (x*y) := by
    simp only [← map_sum,← Finset.mul_sum,← Finset.sum_mul,matrixUnit_sum_diag,mul_one,one_mul]
  simp only [← mul_assoc] at ⊢
  rw [hfirst]
  congr 1
  simp only [matrixAverage,matrixUnit,Fintype.card_fin,smul_mul_assoc,Finset.sum_mul,map_smul,map_sum,smul_eq_mul,
    mul_inv_cancel_left₀ hd0]

end

end KKMatrixQuantization
end

end OAI
