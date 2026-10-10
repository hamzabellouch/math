import Mathlib
import OAI.Probability.SKGap.Localization.UniformSquareInduction
import OAI.Probability.SKGap.Localization.PrimaryFiniteControl
import OAI.Probability.SKGap.Matrix.FixedNormRecipeEvent

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff
variable {n : ℕ}

def fieldEnergy (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℝ :=
  energy J x+∑i,h i*spin x i

def fieldPartition (J : Interaction n) (h : Fin n→ℝ) : ℝ := ∑x,Real.exp (fieldEnergy J h x)
def fieldGibbs (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℝ :=
  Real.exp (fieldEnergy J h x)/fieldPartition J h

lemma fieldPartition_pos (J : Interaction n) (h : Fin n→ℝ) : 0<fieldPartition J h :=
  Finset.sum_pos (fun _ _=>Real.exp_pos _) Finset.univ_nonempty
lemma fieldGibbs_pos (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : 0<fieldGibbs J h x :=
  div_pos (Real.exp_pos _) (fieldPartition_pos J h)
lemma sum_fieldGibbs (J : Interaction n) (h : Fin n→ℝ) : ∑x,fieldGibbs J h x=1 := by
  simp only [fieldGibbs,←Finset.sum_div]
  change fieldPartition J h/fieldPartition J h=1
  exact div_self (ne_of_gt (fieldPartition_pos J h))
lemma fieldGibbs_zero (J : Interaction n) : fieldGibbs J 0=gibbs J := by
  funext x
  simp [fieldGibbs,fieldPartition,fieldEnergy,gibbs,partition]
lemma fieldGibbs_edge (g : SKGap.Disorder n) (h : Fin n→ℝ) :
    fieldGibbs (GapBridge.edgeInteraction g) h=SKGap.mass g h := by
  have he (x : Spin n) : fieldEnergy (GapBridge.edgeInteraction g) h x=SKGap.hamiltonian g h x := by
    simp [fieldEnergy,energy,SKGap.hamiltonian,GapBridge.edgeInteraction,spin,SKGap.spinValue,Matrix.of_apply]
    ring
  funext x
  simp only [fieldGibbs,fieldPartition,he,SKGap.mass,SKGap.partition,SKGap.weight]

lemma fieldEnergy_flip (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    fieldEnergy J h (flip x i)=fieldEnergy J h x-2*spin x i*(h i+field J x i) := by
  simp only [fieldEnergy,energy_flip J hJ hd,spin_flip,mul_sub,Finset.sum_sub_distrib]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  ring

lemma fieldGibbs_detailed_balance (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    fieldGibbs J h (flip x i)*(1+spin x i*Real.tanh (h i+field J x i))=
      fieldGibbs J h x*(1-spin x i*Real.tanh (h i+field J x i)) := by
  simp only [fieldGibbs,fieldEnergy_flip J hJ hd,Real.exp_sub]
  cases hi:x i
  · simp only [spin,hi,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul,mul_neg,Real.exp_neg]
    have ht:=exp_two_mul_one_sub_tanh (h i+field J x i)
    field_simp [ne_of_gt (fieldPartition_pos J h)]
    nlinarith only [ht]
  · simp only [spin,hi,↓reduceIte,one_mul,mul_one]
    have ht:=exp_two_mul_one_sub_tanh (h i+field J x i)
    field_simp [ne_of_gt (fieldPartition_pos J h)]
    nlinarith only [ht]

namespace Static
lemma conditionalMean_fieldGibbs (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalMean (fieldGibbs J h) x i=Real.tanh (h i+field J x i) := by
  have hb:=fieldGibbs_detailed_balance J hJ hd h x i
  have hp:=ne_of_gt (add_pos (fieldGibbs_pos J h x) (fieldGibbs_pos J h (flip x i)))
  rw [conditionalMean,←mul_div_assoc]
  apply (div_eq_iff hp).2
  cases hi:x i <;> simp only [spin,hi,Bool.false_eq_true,↓reduceIte,one_mul,neg_mul] at hb ⊢ <;>
    linarith only [hb]

lemma conditionalMean_primary (j : ℝ) (J : Interaction n) (hJ : J.IsSymm)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalMean (fieldGibbs J h) x i=Primary.mag j J h 1 x i := by
  rw [conditionalMean_fieldGibbs J (fun i k=>hJ.apply k i) hd]
  rfl
end Static
end SKGapCutoff

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {j R B W C K : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

theorem gibbs_ordinary_residuals (p N : ℕ) (hK : 2≤K) (hM : p<M)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j K p 0) B W C M (N+2*p) (J a))
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformWeak (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) ∧
    UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hA : 1≤residualCoefficientBudget j K p 0 :=
    (by linarith : 1≤K).trans (residualCoefficientBudget_ge j (by linarith) p 0)
  have hc:=primary_finite_control j R B hR hB J h M (N+2*p) hn
    (fun a=>(hevent a).1) (fun a x l hl=>(hevent a).2.1 (h a) x l hl)
    _ W C hA hW hC (fun a=>(hevent a).2.2.1) (fun a=>(hevent a).2.2.2)
  have hp : ∀a x,0≤fieldGibbs (J a) (h a) x:=fun a x=>(fieldGibbs_pos _ _ _).le
  have hm:=fun a=>conditionalMean_primary j (J a) (hJ a) (hdiag a) (h a)
  exact ⟨uniform_ordinary_weak_residual p N hK hM hc hp (fun a=>sum_fieldGibbs _ _) hm hn hJ D H,
    uniform_ordinary_square_residual p N hK hM hc hp (fun a=>sum_fieldGibbs _ _) hm hn hJ D H⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

def vectorPair (U V : VectorFields n) (x : Spin n) : ℝ := ∑i,U x i*V x i

def normalizedPair (U V : VectorFields n) (x : Spin n) : ℝ :=
  vectorPair U V x/Real.sqrt (n:ℝ)

lemma vectorPair_derivative (U V : VectorFields n) (x : Spin n) :
    derivativeVector (vectorPair U V) x =
      (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (derivativeMatrix U x)ᵀ) (WithLp.toLp 2 (V x))+
      (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (derivativeMatrix V x)ᵀ) (WithLp.toLp 2 (U x))-
      WithLp.toLp 2 (fun k=>2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k) := by
  ext k
  change halfDiff k (vectorPair U V) x =
    (∑i,halfDiff k (fun y=>U y i) x*V x i)+
    (∑i,halfDiff k (fun y=>V y i) x*U x i)-
    2*spin x k*∑i,halfDiff k (fun y=>U y i) x*halfDiff k (fun y=>V y i) x
  have hh : halfDiff k (vectorPair U V) x=∑i,halfDiff k (fun y=>U y i*V y i) x := by
    simp only [halfDiff,vectorPair]
    rw [← Finset.sum_sub_distrib,Finset.sum_div]
  rw [hh,← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [halfDiff_mul]
  ring

lemma vectorPair_abs (U V : VectorFields n) (x : Spin n) :
    |vectorPair U V x| ≤ vectorNorm (U x)*vectorNorm (V x) := by
  simpa [vectorPair,vectorNorm,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 (U x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (V x))

lemma vectorPair_cross_bound (U V : VectorFields n) (x : Spin n)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B) :
    vectorNorm (fun k=>2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k) ≤
      2*A*B*Real.sqrt (n:ℝ) := by
  have hcol (M : Interaction n) {C : ℝ} (hC : 0≤C) (hM : SKGap.opNorm M≤C) (k : Fin n) :
      vectorNorm (fun i=>M i k)≤C := by
    apply nonneg_le_nonneg_of_sq_le_sq hC
    simp only [← sq,vectorNorm_sq]
    exact (RandomMatrix.matrix_column_sq_le M k).trans (pow_le_pow_left₀ (norm_nonneg _) hM 2)
  have hdot (k : Fin n) : |∑i,derivativeMatrix U x i k*derivativeMatrix V x i k|≤A*B := by
    exact (vectorPair_abs (fun _ i=>derivativeMatrix U x i k)
      (fun _ i=>derivativeMatrix V x i k) x).trans
      (mul_le_mul (hcol _ hA hu k) (hcol _ hB hv k) (vectorNorm_nonneg _) hA)
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [← sq,vectorNorm_sq]
  calc
    _ ≤ ∑ _k : Fin n,(2*A*B)^2 := by
      apply Finset.sum_le_sum
      intro k _
      have hb : |2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k|≤2*A*B := by
        simpa only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_spin_eq_one,mul_one,one_mul,mul_assoc] using
          mul_le_mul_of_nonneg_left (hdot k) (by norm_num : (0:ℝ)≤2)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by simp [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]; ring

lemma vectorPair_derivative_bound (U V : VectorFields n) (x : Spin n)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B) :
    ‖derivativeVector (vectorPair U V) x‖ ≤
      A*vectorNorm (V x)+B*vectorNorm (U x)+2*A*B*Real.sqrt (n:ℝ) := by
  have hop (M : Interaction n) (u : Fin n→ℝ) {C : ℝ} (hM : SKGap.opNorm M≤C) :
      ‖(Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) Mᵀ) (WithLp.toLp 2 u)‖≤C*vectorNorm u := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    change SKGap.opNorm Mᵀ*vectorNorm u≤_
    rw [SKGap.opNorm_transpose]
    exact mul_le_mul_of_nonneg_right hM (vectorNorm_nonneg u)
  rw [vectorPair_derivative]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (hop _ _ hu) (hop _ _ hv)))
    (vectorPair_cross_bound U V x hA hB hu hv))

lemma normalizedPair_derivative (U V : VectorFields n) (x : Spin n) :
    derivativeVector (normalizedPair U V) x =
      (Real.sqrt (n:ℝ))⁻¹ • derivativeVector (vectorPair U V) x := by
  ext k
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,normalizedPair,halfDiff]
  ring

lemma normalizedPair_derivative_bound (hn : 0<n) (U V : VectorFields n) (x : Spin n)
    {A B Cu Cv : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B)
    (hU : vectorNorm (U x)≤Cu*Real.sqrt (n:ℝ))
    (hV : vectorNorm (V x)≤Cv*Real.sqrt (n:ℝ)) :
    ‖derivativeVector (normalizedPair U V) x‖≤A*Cv+B*Cu+2*A*B := by
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [normalizedPair_derivative,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ (Real.sqrt (n:ℝ))⁻¹*(A*vectorNorm (V x)+B*vectorNorm (U x)+2*A*B*Real.sqrt (n:ℝ)) :=
      mul_le_mul_of_nonneg_left (vectorPair_derivative_bound U V x hA hB hu hv) (inv_nonneg.mpr hs.le)
    _ ≤ (Real.sqrt (n:ℝ))⁻¹*(A*(Cv*Real.sqrt (n:ℝ))+B*(Cu*Real.sqrt (n:ℝ))+2*A*B*Real.sqrt (n:ℝ)) := by
      gcongr
    _ = _ := by field_simp

end SKGapCutoff.Recipe

end
end

end OAI
