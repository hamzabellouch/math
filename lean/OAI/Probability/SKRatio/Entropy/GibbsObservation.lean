import Mathlib
import OAI.Probability.SKRatio.Entropy.GaussianHistory
import OAI.Probability.SKRatio.Entropy.ProductEntropy

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix MatrixOrder Topology
open MeasureTheory Real Matrix
namespace SKRatio.Observation
open Calculus Fields
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma abs_quadratic_le_opNorm (J : Interaction n) (z : Fin n → ℝ) :
    |z ⬝ᵥ Matrix.mulVec J z| ≤ euclideanOpNorm J*(∑ i,z i^2) := by
  let Z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
  have hi : z ⬝ᵥ Matrix.mulVec J z = inner ℝ Z (Matrix.toEuclideanCLM (𝕜 := ℝ) J Z) :=
    (Matrix.inner_toEuclideanCLM J Z Z).symm
  rw [hi]
  calc
    _ ≤ ‖Z‖*‖Matrix.toEuclideanCLM (𝕜 := ℝ) J Z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖Z‖*(euclideanOpNorm J*‖Z‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) J).le_opNorm _) (norm_nonneg _)
    _ = _ := by
      rw [show ‖Z‖*(euclideanOpNorm J*‖Z‖)=euclideanOpNorm J*‖Z‖^2 by ring,
        EuclideanSpace.real_norm_sq_eq]

def shiftedCoupling (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (coupling g) + (2:ℝ) • 1

lemma shiftedCoupling_quad (g : Disorder n) (z : Fin n → ℝ) :
    z ⬝ᵥ (shiftedCoupling g).mulVec z = z ⬝ᵥ Matrix.mulVec (coupling g) z + 2*∑ i,z i^2 := by
  simp only [shiftedCoupling,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,
    pow_two,←mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma shiftedCoupling_nonneg (g : Disorder n) (hg : euclideanOpNorm (coupling g) ≤ 2) :
    0 ≤ shiftedCoupling g := by
  apply Matrix.PosSemidef.nonneg
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.add
    · ext i j
      exact coupling_symm g j i
    · exact Matrix.isSymm_one.smul _
  · intro z
    simp only [star_trivial]
    rw [shiftedCoupling_quad]
    have hh := (abs_quadratic_le_opNorm (coupling g) z).trans
      (mul_le_mul_of_nonneg_right hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    linarith only [neg_abs_le (z ⬝ᵥ Matrix.mulVec (coupling g) z),hh]

def observationMatrix (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (shiftedCoupling g)

lemma observationMatrix_symm (g : Disorder n) : (observationMatrix g).IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1

lemma observationMatrix_square (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2) :
    observationMatrix g * observationMatrix g = shiftedCoupling g := by
  simpa only [observationMatrix,pow_two] using CFC.sq_sqrt (shiftedCoupling g) (shiftedCoupling_nonneg g hg)

lemma symmetric_mulVec_dot (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (z y : Fin n → ℝ) : A.mulVec z ⬝ᵥ y = z ⬝ᵥ A.mulVec y := by
  rw [Matrix.dotProduct_mulVec]
  have he : Matrix.vecMul z A = A.mulVec z := by
    ext i
    simp only [Matrix.vecMul,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [show A j i = A i j from congrFun (congrFun hA i) j]
    ring
  rw [he]

lemma observationMatrix_normSq (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (z : Fin n → ℝ) :
    (∑ i, ((observationMatrix g).mulVec z i)^2) =
      z ⬝ᵥ Matrix.mulVec (coupling g) z+2*∑ i,z i^2 := by
  have he : (∑ i, ((observationMatrix g).mulVec z i)^2) =
      (observationMatrix g).mulVec z ⬝ᵥ (observationMatrix g).mulVec z := by
    simp only [dotProduct,pow_two]
  rw [he,symmetric_mulVec_dot _ (observationMatrix_symm g),Matrix.mulVec_mulVec,
    observationMatrix_square g hg,shiftedCoupling_quad]

lemma observationMatrix_normSq_le (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (z : Fin n → ℝ) : (∑ i, ((observationMatrix g).mulVec z i)^2) ≤ 4*∑ i,z i^2 := by
  rw [observationMatrix_normSq g hg]
  have hh := (le_abs_self (z ⬝ᵥ Matrix.mulVec (coupling g) z)).trans
    ((abs_quadratic_le_opNorm (coupling g) z).trans
      (mul_le_mul_of_nonneg_right hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  linarith only [hh]

def gibbsFeature (g : Disorder n) (x : Spin n) : Fin n → ℝ :=
  (observationMatrix g).mulVec (fun i => spinValue (x i))

lemma gibbsFeature_normSq (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2) (x : Spin n) :
    Channel.normSq (gibbsFeature g) x = 2*hamiltonian g 0 x+2*n := by
  unfold Channel.normSq gibbsFeature
  rw [observationMatrix_normSq g hg]
  have hs (i : Fin n) : spinValue (x i)^2 = 1 := by cases x i <;> norm_num [spinValue]
  simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    hamiltonian,Pi.zero_apply,zero_mul,dotProduct,
    Matrix.mulVec,Finset.mul_sum]
  have he : (∑ i,∑ j,spinValue (x i)*(coupling g i j*spinValue (x j))) =
      (∑ i,∑ j,spinValue (x i)*coupling g i j*spinValue (x j)) := by
    simp only [mul_assoc]
  rw [he]
  simp only [←Finset.mul_sum]
  ring

lemma gibbsFeature_linear (g : Disorder n) (a : Fin n → ℝ) :
    linear (gibbsFeature g) a = Fields.linearObservable ((observationMatrix g).mulVec a) := by
  funext x
  change a ⬝ᵥ (observationMatrix g).mulVec (fun i => spinValue (x i)) =
    (observationMatrix g).mulVec a ⬝ᵥ (fun i => spinValue (x i))
  exact (symmetric_mulVec_dot _ (observationMatrix_symm g) _ _).symm

lemma hamiltonian_scale (g : Disorder n) (h : Fin n → ℝ) (s : ℝ) (x : Spin n) :
    hamiltonian (s • g) h x = s*hamiltonian g 0 x+Fields.linearObservable h x := by
  simp only [hamiltonian,Fields.coupling_smul,Pi.zero_apply,zero_mul,Finset.sum_const_zero,
    add_zero,Fields.linearObservable,mul_left_comm (spinValue (x _)) s,mul_assoc,
    ←Finset.mul_sum]
  ring

lemma channel_weight_identity (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (s t : ℝ) (h z : Fin n → ℝ) (x : Spin n) :
    weight (s • g) h x*Channel.likelihood (gibbsFeature g) t x z =
      exp (-t*n)*weight ((s-t) • g) (h+sqrt t • (observationMatrix g).mulVec z) x := by
  simp only [weight,Channel.likelihood,←exp_add,gibbsFeature_normSq g hg,hamiltonian_scale]
  congr 1
  have he : (∑ i,gibbsFeature g x i*z i)=
      Fields.linearObservable ((observationMatrix g).mulVec z) x := by
    simpa only [linear,mul_comm] using congrFun (gibbsFeature_linear g z) x
  rw [he]
  simp only [Fields.linearObservable,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,
    Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum]
  ring

lemma channel_posterior_gibbs (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (s t : ℝ) (h z : Fin n → ℝ) :
    Channel.posterior (gibbsFeature g) (gibbsPrior (s • g) h) t z =
      gibbsPrior ((s-t) • g) (h+sqrt t • (observationMatrix g).mulVec z) := by
  let h' := h+sqrt t • (observationMatrix g).mulVec z
  have hn (x : Spin n) : gibbsPrior (s • g) h x*Channel.likelihood (gibbsFeature g) t x z =
      (exp (-t*n)/partition (s • g) h)*weight ((s-t) • g) h' x := by
    change weight (s • g) h x/partition (s • g) h*Channel.likelihood (gibbsFeature g) t x z = _
    rw [div_mul_eq_mul_div,channel_weight_identity g hg]
    ring
  have hd : Channel.density (gibbsFeature g) (gibbsPrior (s • g) h) t z =
      (exp (-t*n)/partition (s • g) h)*partition ((s-t) • g) h' := by
    simp only [Channel.density,hn,←Finset.mul_sum,partition]
  apply Prior.ext
  funext x
  change (gibbsPrior (s • g) h x*Channel.likelihood (gibbsFeature g) t x z)/
    Channel.density (gibbsFeature g) (gibbsPrior (s • g) h) t z =
      weight ((s-t) • g) h' x/partition ((s-t) • g) h'
  rw [hn,hd]
  field_simp [(exp_pos (-t*n)).ne',(partition_pos (s • g) h).ne',
    (partition_pos ((s-t) • g) h').ne']

def observedField (g : Disorder n) (t : ℝ) (h₀ : Fin n → ℝ) :
    {k : ℕ} → History n k → Fin n → ℝ
  | 0,_ => h₀
  | _+1,h => observedField g t h₀ h.1+sqrt t • (observationMatrix g).mulVec h.2

lemma history_posterior_gibbs (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (t : ℝ) (h₀ : Fin n → ℝ) : ∀ {k : ℕ} (h : History n k),
    History.posterior (gibbsFeature g) (gibbsPrior g h₀) t h =
      gibbsPrior ((1-(k:ℝ)*t) • g) (observedField g t h₀ h)
  | 0,h => by simp only [History.posterior_zero,Nat.cast_zero,zero_mul,sub_zero,one_smul,
                         observedField]
  | k+1,h => by
    rw [History.posterior_succ,history_posterior_gibbs g hg t h₀ h.1,
      channel_posterior_gibbs g hg]
    simp only [observedField,Nat.cast_add,Nat.cast_one]
    congr 2
    ring

def fieldPrior (h : ℝ) : Prior Bool where
  mass b := exp (h*spinValue b)/(exp h+exp (-h))
  nonneg b := div_nonneg (exp_pos _).le (add_pos (exp_pos _) (exp_pos _)).le
  sum_one := by
    simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one,←add_div]
    exact div_self (add_pos (exp_pos _) (exp_pos _)).ne'

lemma fieldPrior_pos (h : ℝ) (b : Bool) : 0<fieldPrior h b :=
  div_pos (exp_pos _) (add_pos (exp_pos _) (exp_pos _))

lemma zero_scale_product (g : Disorder n) (h : Fin n → ℝ) :
    gibbsPrior ((0:ℝ) • g) h = productPrior (fun i => fieldPrior (h i)) := by
  have hw (x : Spin n) : weight ((0:ℝ) • g) h x = ∏ i,exp (h i*spinValue (x i)) := by
    simp only [weight,hamiltonian_scale,zero_mul,zero_add,Fields.linearObservable,exp_sum]
  have hz : partition ((0:ℝ) • g) h = ∏ i,(exp (h i)+exp (-h i)) := by
    simp only [partition,hw]
    change (∑ x : Fin n → Bool, ∏ i,exp (h i*spinValue (x i))) = _
    rw [←Fintype.prod_sum (fun (i : Fin n) (b : Bool) => exp (h i*spinValue b))]
    simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one]
  apply Prior.ext
  funext x
  simp only [gibbsPrior,mass,hw,hz,productPrior,fieldPrior,Finset.prod_div_distrib]

lemma history_endpoint_product (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (h₀ : Fin n → ℝ) {N : ℕ} (hN : 0<N) (h : History n N) :
    History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h =
      productPrior (fun i => fieldPrior (observedField g (N:ℝ)⁻¹ h₀ h i)) := by
  rw [history_posterior_gibbs g hg, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'),
    sub_self,zero_scale_product]

lemma history_endpoint_entropy (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    (h₀ : Fin n → ℝ) (f : Spin n → ℝ) (hf : ∀ x,0<f x) {N : ℕ} (hN : 0<N) :
    History.remainingEntropy (gibbsFeature g) (gibbsPrior g h₀) f (N:ℝ)⁻¹ N ≤
      expectation g h₀ (fun x => f x*heatBathGenerator g h₀ (fun y => log (f y)) x) := by
  let R := fun x => ∑ i,logRemainder (f x) (conditionalExpectation g h₀ i f x)
  have hpoint (h : History n N) :
      ent (History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h) f ≤
        avg (History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h) R := by
    rw [history_endpoint_product g hg h₀ hN]
    exact product_entropy_le_remainders _ f hf (fun i => conditionalExpectation g h₀ i f)
      (fun i x => conditionalExpectation_pos g h₀ i f hf x)
      (fun i x => conditionalExpectation_flip g h₀ i f x)
  have hi := integral_mono
    (History.integrable_posterior_entropy_weight (gibbsFeature g) (gibbsPrior g h₀) f hf (N:ℝ)⁻¹ N)
    (History.integrable_posterior_avg_weight (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ R N)
    (fun h => mul_le_mul_of_nonneg_left (hpoint h) (History.density_pos _ _ _ h).le)
  rw [History.integral_posterior_avg_weight _ _ (inv_nonneg.mpr (Nat.cast_nonneg N))] at hi
  exact hi.trans (remainders_le_energy g h₀ f hf)

theorem entropy_of_scaled_covariance (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    {ρ : ℝ} (hρ : 0<ρ)
    (hcov : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ h a : Fin n → ℝ,
      Fields.variance (s • g) h (Fields.linearObservable a) ≤ ρ⁻¹*(∑ i,a i^2))
    (h₀ : Fin n → ℝ) (f : Spin n → ℝ) (hf : ∀ x,0<f x) :
    exp (-16/ρ)*ent (gibbsPrior g h₀) f ≤
      expectation g h₀ (fun x => f x*heatBathGenerator g h₀ (fun y => log (f y)) x) := by
  have he := History.entropy_of_observation_estimates
    (E := expectation g h₀ (fun x => f x*heatBathGenerator g h₀ (fun y => log (f y)) x))
    (gibbsFeature g) (gibbsPrior g h₀)
    (mass_pos g h₀) f hf (div_pos (by norm_num : (0:ℝ)<4) hρ)
  have hvar (N : ℕ) (hN : 0<N) (k : ℕ) (hk : k<N) (h : History n k)
      (a : Fin n → ℝ) (r : ℝ) :
      var (tilt (History.posterior (gibbsFeature g) (gibbsPrior g h₀) (N:ℝ)⁻¹ h)
        (linear (gibbsFeature g) a) r) (linear (gibbsFeature g) a) ≤ (4/ρ)*(∑ i,a i^2) := by
    rw [history_posterior_gibbs g hg,gibbsFeature_linear,tilt_gibbs_linear]
    have hs : 1-(k:ℝ)*(N:ℝ)⁻¹ ∈ Set.Icc (0:ℝ) 1 := by
      have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
      have hkn : (k:ℝ)≤N := Nat.cast_le.mpr hk.le
      have hkn' : (k:ℝ)*(N:ℝ)⁻¹≤1 := by
        rw [←div_eq_mul_inv,div_le_iff₀ hn,one_mul];exact hkn
      constructor
      · linarith only [hkn']
      · exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hn.le))
    apply (hcov _ hs _ ((observationMatrix g).mulVec a)).trans
    have hh := mul_le_mul_of_nonneg_left (observationMatrix_normSq_le g hg a) (inv_nonneg.mpr hρ.le)
    convert! hh using 1
    ring
  have hh := he hvar (fun N hN => history_endpoint_entropy g hg h₀ f hf hN)
  convert! hh using 1
  ring_nf

theorem zero_field_mlsi (g : Disorder n) (hg : euclideanOpNorm (coupling g)≤2)
    {ρ : ℝ} (hρ : 0<ρ)
    (hcov : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ h a : Fin n → ℝ,
      Fields.variance (s • g) h (Fields.linearObservable a) ≤ ρ⁻¹*(∑ i,a i^2))
    (f : Observables n) (hf : ∀ x,0<f x) :
    exp (-16/ρ)*FiniteLaw.entropy (mass g 0) f ≤
      -stationaryInner g (generator (coupling g) f) (fun y => log (f y)) := by
  have hh := entropy_of_scaled_covariance g hg hρ hcov 0 f hf
  rw [←heatBathGenerator_adjoint] at hh
  simpa only [heatBathGenerator_zero_field,expectation,neg_mul,Finset.sum_neg_distrib,
    ent,gibbsPrior,stationaryInner,FiniteLaw.mean,mul_neg,Finset.sum_neg_distrib] using hh

end SKRatio.Observation

end
end

end OAI
