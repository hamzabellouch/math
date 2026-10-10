import OAI.Geometry.HarmonicGrowth.Flow

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

/-- An actual orthonormal coordinate map for continuous real endomorphisms. -/
def orthogonalMatrixLinear (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] E) →ₗ[ℝ] Matrix ι ι ℝ where
  toFun T := LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap
  map_add' T U := by rw [ContinuousLinearMap.toLinearMap_add,map_add]
  map_smul' c T := by rw [ContinuousLinearMap.toLinearMap_smul,map_smul]; rfl

def orthogonalMatrix (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ :=
  (orthogonalMatrixLinear b).toContinuousLinearMap

lemma orthogonalMatrix_apply (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (i j : ι) :
    orthogonalMatrix b T i j=(b.repr (T (b j))) i := by
  simp only [orthogonalMatrix,LinearMap.coe_toContinuousLinearMap',orthogonalMatrixLinear,
    LinearMap.coe_mk,AddHom.coe_mk,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,
    ContinuousLinearMap.coe_coe,OrthonormalBasis.coe_toBasis_repr_apply]

lemma orthogonalMatrix_mul (b : OrthonormalBasis ι ℝ E) (T U : E →L[ℝ] E) :
    orthogonalMatrix b (T*U)=orthogonalMatrix b T*orthogonalMatrix b U := by
  change LinearMap.toMatrix b.toBasis b.toBasis (T*U).toLinearMap = _
  rw [ContinuousLinearMap.toLinearMap_mul,LinearMap.toMatrix_mul]
  rfl

lemma orthogonalMatrix_one (b : OrthonormalBasis ι ℝ E) :
    orthogonalMatrix b (1:E →L[ℝ] E)=1 := by
  change LinearMap.toMatrix b.toBasis b.toBasis (1:Module.End ℝ E)=1
  exact LinearMap.toMatrix_one b.toBasis

lemma orthogonalMatrix_mulVec (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (x : E) :
    (orthogonalMatrix b T).mulVec (fun i => b.repr x i)=fun i => b.repr (T x) i := by
  have h := LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis T.toLinearMap x
  change (LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap).mulVec
    (fun i => b.toBasis.repr x i)=(fun i => b.toBasis.repr (T x) i)
  exact h

/-- Quadratic positivity is transported exactly; no equivalence-of-norms
constant contaminates the damping rate. -/
lemma orthogonalMatrix_coercive (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E)
    {c : ℝ} (hT : ∀ x,c*‖x‖^2 ≤ inner ℝ x (T x)) (v : ι → ℝ) :
    c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*orthogonalMatrix b T i j*v j := by
  let x := b.repr.symm (WithLp.toLp 2 v)
  have hx : b.repr x=WithLp.toLp 2 v := b.repr.apply_symm_apply _
  have hn : ‖x‖^2=∑ i,(v i)^2 := by
    rw [← b.repr.norm_map x,hx]
    exact EuclideanSpace.real_norm_sq_eq _
  have hinner : inner ℝ x (T x)=∑ i,∑ j,v i*orthogonalMatrix b T i j*v j := by
    have hm := orthogonalMatrix_mulVec b T x
    have hm' : b.repr (T x)=WithLp.toLp 2 ((orthogonalMatrix b T).mulVec v) := by
      apply PiLp.ext
      intro i
      simpa only [hx] using (congrFun hm i).symm
    rw [← b.repr.inner_map_map x (T x),hx,hm']
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Matrix.mulVec,
      dotProduct,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [hn,hinner] using hT x

/-- Differentiation of coordinate matrices is the genuine continuous-linear
chain rule, for both time and parameter derivatives. -/
lemma orthogonalMatrix_hasDerivAt (b : OrthonormalBasis ι ℝ E)
    {f : ℝ → E →L[ℝ] E} {f' : E →L[ℝ] E} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => orthogonalMatrix b (f s)) (orthogonalMatrix b f') t :=
  (orthogonalMatrix b).hasFDerivAt.comp_hasDerivAt t hf

lemma orthogonalMatrix_riccati_deriv (b : OrthonormalBasis ι ℝ E)
    {P A : ℝ → E →L[ℝ] E} {p : ℝ → ℝ} {t : ℝ}
    (hP : HasDerivAt P (A t-p t • P t-P t*P t) t) :
    HasDerivAt (fun s => orthogonalMatrix b (P s))
      (orthogonalMatrix b (A t)-p t • orthogonalMatrix b (P t)-
        orthogonalMatrix b (P t)*orthogonalMatrix b (P t)) t := by
  simpa only [map_sub,map_smul,orthogonalMatrix_mul] using orthogonalMatrix_hasDerivAt b hP

lemma orthogonalMatrix_jet_deriv (b : OrthonormalBasis ι ℝ E)
    {P₁ : ℝ → E →L[ℝ] E} {A₁ P : E →L[ℝ] E} {p t : ℝ}
    (hP : HasDerivAt P₁ (A₁-p • P₁ t-P*P₁ t-P₁ t*P) t) :
    HasDerivAt (fun s => orthogonalMatrix b (P₁ s))
      (orthogonalMatrix b A₁-p • orthogonalMatrix b (P₁ t)-
        orthogonalMatrix b P*orthogonalMatrix b (P₁ t)-
        orthogonalMatrix b (P₁ t)*orthogonalMatrix b P) t := by
  simpa only [map_sub,map_smul,orthogonalMatrix_mul] using orthogonalMatrix_hasDerivAt b hP

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_deriv_of_ne_zero {f : ℝ → E} {f' : E} {t : ℝ}
    (hf : HasDerivAt f f' t) (h0 : f t ≠ 0) :
    HasDerivAt (fun s => ‖f s‖) (⟪f t,f'⟫_ℝ/‖f t‖) t := by
  have h := hf.norm_sq.sqrt (sq_pos_of_pos (norm_pos_iff.2 h0)).ne'
  simpa only [Real.sqrt_sq (norm_nonneg _),mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)] using h

/-- The norm has the sharp right upper slope, including at its zeros. -/
lemma dissipative_norm_slope {f f' : ℝ → E} {r : ℝ → ℝ} {c t : ℝ}
    (hf : HasDerivAt f (f' t) t)
    (he : ⟪f t,f' t⟫_ℝ ≤ -c*‖f t‖^2+r t*‖f t‖)
    (hz : f t = 0 → ‖f' t‖ ≤ r t) :
    ∀ z, -c*‖f t‖+r t < z → ∃ᶠ s in 𝓝[>] t,
      (s-t)⁻¹*(‖f s‖-‖f t‖) < z := by
  intro z hz'
  by_cases h0 : f t = 0
  · have hh : ‖f' t‖ < z := by
      have := hz h0
      simpa only [h0,norm_zero,mul_zero,zero_add] using lt_of_le_of_lt this (by simpa [h0] using hz')
    exact hf.hasDerivWithinAt.liminf_right_slope_norm_le hh
  · have hh : ⟪f t,f' t⟫_ℝ/‖f t‖ ≤ -c*‖f t‖+r t := by
      apply (div_le_iff₀ (norm_pos_iff.2 h0)).2
      nlinarith
    simpa only [_root_.slope,smul_eq_mul,vsub_eq_sub] using
      (norm_deriv_of_ne_zero hf h0).hasDerivWithinAt.liminf_right_slope_le (hh.trans_lt hz')

/-- Exact integrated forced damping, with neither a missing zero case nor an
assumed scalar differential inequality for the nondifferentiable norm. -/
theorem dissipative_integral {f f' : ℝ → E} {r : ℝ → ℝ} {c a b : ℝ}
    (hab : a ≤ b) (hf : ∀ t, HasDerivAt f (f' t) t) (hr : Continuous r)
    (he : ∀ t ∈ Icc a b, ⟪f t,f' t⟫_ℝ ≤ -c*‖f t‖^2+r t*‖f t‖)
    (hz : ∀ t ∈ Icc a b,f t = 0 → ‖f' t‖ ≤ r t) :
    c*(∫ t in a..b, ‖f t‖) ≤ ‖f a‖-‖f b‖+∫ t in a..b,r t := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  let B := fun t => ‖f a‖+∫ s in a..t,r s-c*‖f s‖
  have hi : Continuous (fun t => r t-c*‖f t‖) := hr.sub (continuous_const.mul hfc.norm)
  have hB (t : ℝ) : HasDerivAt B (r t-c*‖f t‖) t := by
    exact (intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable _ _)
      hi.stronglyMeasurable.stronglyMeasurableAtFilter hi.continuousAt).const_add _
  have hh : ‖f b‖ ≤ B b := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hfc.norm.continuousOn
      (show ‖f a‖ ≤ B a by simp [B])
      (continuous_iff_continuousAt.2 (fun t => (hB t).continuousAt)).continuousOn
      (fun t _ => (hB t).hasDerivWithinAt) _ ⟨hab,le_rfl⟩
    intro t ht z htz
    have hct : t ∈ Icc a b := ⟨ht.1,ht.2.le⟩
    simpa only [_root_.slope,smul_eq_mul,vsub_eq_sub] using dissipative_norm_slope (hf t)
      (he t hct) (hz t hct) z (by linarith)
  dsimp only [B] at hh
  have hci : Continuous (fun t => c*‖f t‖) := continuous_const.mul hfc.norm
  rw [intervalIntegral.integral_sub (hr.intervalIntegrable a b)
    (hci.intervalIntegrable a b),
    intervalIntegral.integral_const_mul] at hh
  linarith

/-- Uniformly forced exponential reset in a Hilbert space. The damping
constant may have either sign in the general comparison theorem. -/
theorem dissipative_gronwall {f f' : ℝ → E} {c M a b : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (he : ∀ t ∈ Icc a b, ⟪f t,f' t⟫_ℝ ≤ -c*‖f t‖^2+M*‖f t‖)
    (hz : ∀ t ∈ Icc a b,f t = 0 → ‖f' t‖ ≤ M) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ gronwallBound ‖f a‖ (-c) M (t-a) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  apply le_gronwallBound_of_liminf_deriv_right_le hfc.norm.continuousOn _ le_rfl
    (fun _ _ => le_rfl)
  intro t ht
  exact dissipative_norm_slope (r := fun _ => M) (hf t) (he t ⟨ht.1,ht.2.le⟩)
    (hz t ⟨ht.1,ht.2.le⟩)

/-- A coercive linear damping operator supplies every hypothesis above. -/
lemma dissipative_rhs {F x : E} {L : E →L[ℝ] E} {c : ℝ}
    (hL : c*‖x‖^2 ≤ ⟪x,L x⟫_ℝ) :
    ⟪x,F-L x⟫_ℝ ≤ -c*‖x‖^2+‖F‖*‖x‖ := by
  rw [inner_sub_right]
  have h := real_inner_le_norm x F
  nlinarith

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix
variable {ι : Type*} [Fintype ι]

/-- Actual Hilbert--Schmidt coordinates, not the operator norm silently
endowed with a Hilbert inner product. -/
def frobenius (M : Matrix ι ι ℝ) : EuclideanSpace ℝ (ι×ι) :=
  WithLp.toLp 2 (fun p => M p.1 p.2)

lemma frobenius_inner (M N : Matrix ι ι ℝ) :
    ⟪frobenius M,frobenius N⟫_ℝ = ∑ i,∑ j,M i j*N i j := by
  simp only [PiLp.inner_apply,frobenius,RCLike.inner_apply,
    conj_trivial,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma frobenius_norm_sq (M : Matrix ι ι ℝ) :
    ‖frobenius M‖^2 = ∑ i,∑ j,(M i j)^2 := by
  simpa only [frobenius,Fintype.sum_prod_type]
    using EuclideanSpace.real_norm_sq_eq (frobenius M)

/-- Coercivity of both sides of the actual Sylvester damping operator.
This is the uniform positive constant used in the Riccati error equation. -/
lemma sylvester_coercive {A B : Matrix ι ι ℝ} {a b : ℝ}
    (hA : ∀ v : ι → ℝ, a*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*A i j*v j)
    (hB : ∀ v : ι → ℝ, b*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*B i j*v j)
    (X : Matrix ι ι ℝ) :
    (a+b)*‖frobenius X‖^2 ≤ ⟪frobenius X,frobenius (A*X+X*B)⟫_ℝ := by
  have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hA (fun i => X i j))
  have h₂ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hB (fun j => X i j))
  have e₁ : (∑ j,a*∑ i,(X i j)^2) = a*(∑ i,∑ j,(X i j)^2) := by
    rw [← Finset.mul_sum,Finset.sum_comm]
  have e₂ : (∑ i,b*∑ j,(X i j)^2) = b*(∑ i,∑ j,(X i j)^2) := by
    rw [← Finset.mul_sum]
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [frobenius_inner,frobenius_norm_sq]
  have e : (∑ i,∑ j,X i j*((A*X+X*B) i j)) =
      (∑ j,∑ i,∑ k,X i j*A i k*X k j)+
      (∑ i,∑ k,∑ j,X i k*B k j*X i j) := by
    simp only [Matrix.add_apply,Matrix.mul_apply,mul_add,Finset.mul_sum,
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [e]
  nlinarith

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frobeniusLinear : Matrix ι ι ℝ →ₗ[ℝ] EuclideanSpace ℝ (ι×ι) where
  toFun := frobenius
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def frobeniusCLM : Matrix ι ι ℝ →L[ℝ] EuclideanSpace ℝ (ι×ι) :=
  frobeniusLinear.toContinuousLinearMap

omit [DecidableEq ι] in
lemma frobeniusCLM_apply (X : Matrix ι ι ℝ) : frobeniusCLM X=frobenius X := rfl

lemma frobenius_norm (X : Matrix ι ι ℝ) : ‖frobenius X‖=‖X‖ := by
  rw [Matrix.frobenius_norm_def,PiLp.norm_eq_of_L2]
  simp only [frobenius,PiLp.toLp_apply,Fintype.sum_prod_type,Real.rpow_two,Real.sqrt_eq_rpow]

omit [Fintype ι] [DecidableEq ι] in
lemma frobenius_injective : Function.Injective (frobenius (ι:=ι)) := by
  intro X Y h
  ext i j
  exact congrArg (fun v : EuclideanSpace ℝ (ι×ι) => v (i,j)) h

/-- Sharp integrated Sylvester damping in the actual Frobenius matrix norm. -/
theorem sylvester_integrated {X F L R : ℝ → Matrix ι ι ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hF : Continuous F)
    (hX : ∀ t,HasDerivAt X (F t-(L t*X t+X t*R t)) t)
    (hL : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j) :
    (c+d)*(∫ t in a..b,‖X t‖) ≤ ‖X a‖-‖X b‖+∫ t in a..b,‖F t‖ := by
  have hd (t : ℝ) := frobeniusCLM.hasFDerivAt.comp_hasDerivAt t (hX t)
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ⟪frobenius (X t),frobenius (F t-(L t*X t+X t*R t))⟫_ℝ ≤
        -(c+d)*‖frobenius (X t)‖^2+‖F t‖*‖frobenius (X t)‖ := by
    change ⟪frobenius (X t),frobeniusCLM (F t-(L t*X t+X t*R t))⟫_ℝ ≤ _
    rw [map_sub,inner_sub_right]
    have hco := sylvester_coercive (hL t ht) (hR t ht) (X t)
    have hcs := real_inner_le_norm (frobenius (X t)) (frobenius (F t))
    rw [frobenius_norm (F t)] at hcs
    change ⟪frobenius (X t),frobenius (F t)⟫_ℝ-
      ⟪frobenius (X t),frobenius (L t*X t+X t*R t)⟫_ℝ ≤ _
    nlinarith
  have hz (t : ℝ) (_ht : t ∈ Set.Icc a b) (hx : frobenius (X t)=0) :
      ‖frobenius (F t-(L t*X t+X t*R t))‖ ≤ ‖F t‖ := by
    have hzero : X t=0 := frobenius_injective (hx.trans (frobeniusLinear.map_zero).symm)
    simp only [hzero,mul_zero,zero_mul,add_zero,sub_zero,frobenius_norm,le_refl]
  simpa only [Function.comp_def,frobeniusCLM_apply,frobenius_norm] using
    dissipative_integral hab hd hF.norm he hz

/-- Uniform forced damping, with the exact exponentially decaying initial term. -/
theorem sylvester_gronwall {X F L R : ℝ → Matrix ι ι ℝ} {a b c d M : ℝ}
    (hX : ∀ t,HasDerivAt X (F t-(L t*X t+X t*R t)) t)
    (hF : ∀ t ∈ Set.Icc a b,‖F t‖ ≤ M)
    (hL : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j) :
    ∀ t ∈ Set.Icc a b,‖X t‖ ≤ gronwallBound ‖X a‖ (-(c+d)) M (t-a) := by
  have hd (t : ℝ) := frobeniusCLM.hasFDerivAt.comp_hasDerivAt t (hX t)
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ⟪frobenius (X t),frobenius (F t-(L t*X t+X t*R t))⟫_ℝ ≤
        -(c+d)*‖frobenius (X t)‖^2+M*‖frobenius (X t)‖ := by
    change ⟪frobenius (X t),frobeniusCLM (F t-(L t*X t+X t*R t))⟫_ℝ ≤ _
    rw [map_sub,inner_sub_right]
    have hco := sylvester_coercive (hL t ht) (hR t ht) (X t)
    have hcs := real_inner_le_norm (frobenius (X t)) (frobenius (F t))
    rw [frobenius_norm (F t)] at hcs
    have hmul := mul_le_mul_of_nonneg_right (hF t ht) (norm_nonneg (frobenius (X t)))
    change ⟪frobenius (X t),frobenius (F t)⟫_ℝ-
      ⟪frobenius (X t),frobenius (L t*X t+X t*R t)⟫_ℝ ≤ _
    nlinarith
  have hz (t : ℝ) (ht : t ∈ Set.Icc a b) (hx : frobenius (X t)=0) :
      ‖frobenius (F t-(L t*X t+X t*R t))‖ ≤ M := by
    have hzero : X t=0 := frobenius_injective (hx.trans (frobeniusLinear.map_zero).symm)
    simpa only [hzero,mul_zero,zero_mul,add_zero,sub_zero,frobenius_norm] using hF t ht
  simpa only [Function.comp_def,frobeniusCLM_apply,frobenius_norm] using
    dissipative_gronwall hd he hz

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The parameter forcing has one small coefficient multiplying the VALUE
error. This estimate never introduces the unknown size of the slope derivative. -/
lemma jet_forcing_norm (ρ Q X : Matrix ι ι ℝ) {q : ℝ} (hQ : ‖Q‖ ≤ q) :
    ‖ρ-Q*X-X*Q‖ ≤ ‖ρ‖+2*q*‖X‖ := by
  calc
    _ ≤ ‖ρ-Q*X‖+‖X*Q‖ := norm_sub_le _ _
    _ ≤ ‖ρ‖+‖Q*X‖+‖X*Q‖ := add_le_add_left (norm_sub_le _ _) _
    _ ≤ ‖ρ‖+‖Q‖*‖X‖+‖X‖*‖Q‖ := by
      gcongr <;> exact norm_mul_le _ _
    _ ≤ ‖ρ‖+2*q*‖X‖ := by
      have h := mul_le_mul_of_nonneg_right hQ (norm_nonneg X)
      nlinarith

/-- Integrated first-parameter error, driven by integrated VALUE error rather
than pulse duration times its initial size. This is the source's C1 mechanism. -/
theorem sylvester_jet_integrated {Z X ρ Q L R : ℝ → Matrix ι ι ℝ} {a b c d q : ℝ}
    (hab : a ≤ b) (hρ : Continuous ρ) (hQ : Continuous Q) (hX : Continuous X)
    (hZ : ∀ t,HasDerivAt Z ((ρ t-Q t*X t-X t*Q t)-(L t*Z t+Z t*R t)) t)
    (hQn : ∀ t ∈ Set.Icc a b,‖Q t‖ ≤ q)
    (hL : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j) :
    (c+d)*(∫ t in a..b,‖Z t‖) ≤
      ‖Z a‖+(∫ t in a..b,‖ρ t‖)+2*q*(∫ t in a..b,‖X t‖) := by
  have hF : Continuous (fun t => ρ t-Q t*X t-X t*Q t) :=
    (hρ.sub (hQ.mul hX)).sub (hX.mul hQ)
  have h := sylvester_integrated hab hF hZ hL hR
  have hbnd : (∫ t in a..b,‖ρ t-Q t*X t-X t*Q t‖) ≤
      (∫ t in a..b,‖ρ t‖)+2*q*(∫ t in a..b,‖X t‖) := by
    have hci : Continuous (fun t => ‖ρ t‖+2*q*‖X t‖) :=
      hρ.norm.add (continuous_const.mul hX.norm)
    have hi := intervalIntegral.integral_mono_on (μ := volume) hab (hF.norm.intervalIntegrable a b)
      (hci.intervalIntegrable a b) (fun t ht => jet_forcing_norm (ρ t) (Q t) (X t) (hQn t ht))
    have he : (∫ t in a..b,‖ρ t‖+2*q*‖X t‖) =
        (∫ t in a..b,‖ρ t‖)+(∫ t in a..b,2*q*‖X t‖) := by
      exact intervalIntegral.integral_add (f := fun t => ‖ρ t‖)
        (g := fun t => 2*q*‖X t‖) (hρ.norm.intervalIntegrable a b)
        ((continuous_const.mul hX.norm).intervalIntegrable a b)
    rw [he,intervalIntegral.integral_const_mul] at hi
    exact hi
  linarith [norm_nonneg (Z b)]

/-- An explicit, dimension-independent-in-time C1 integrated error constant.
All norms are honest Frobenius norms; no time interval is hidden in the constant. -/
theorem integrated_error_pair {IX IZ Iρ Iρ₁ X₀ Z₀ γ q : ℝ}
    (hγ : 0 < γ) (hq : 0 ≤ q)
    (hX : γ*IX ≤ X₀+Iρ) (hZ : γ*IZ ≤ Z₀+Iρ₁+2*q*IX) :
    IX ≤ (X₀+Iρ)/γ ∧
      IZ ≤ (Z₀+Iρ₁)/γ+2*q*(X₀+Iρ)/γ^2 := by
  have hx : IX ≤ (X₀+Iρ)/γ := (le_div_iff₀ hγ).2 (by simpa only [mul_comm] using hX)
  refine ⟨hx,?_⟩
  calc
    IZ ≤ (Z₀+Iρ₁+2*q*IX)/γ := (le_div_iff₀ hγ).2 (by nlinarith [hZ])
    _ ≤ (Z₀+Iρ₁+2*q*((X₀+Iρ)/γ))/γ := by
      apply div_le_div_of_nonneg_right _ hγ.le
      have hh : 2*q*IX ≤ 2*q*((X₀+Iρ)/γ) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      linarith
    _ = _ := by field_simp


end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The difference of the ACTUAL Riccati solution and any differentiable
comparison function satisfies the two-sided damped equation. -/
lemma riccati_error_deriv {P Q : ℝ → R} {A Q' : R} {p t : ℝ}
    (hP : HasDerivAt P (A-p • P t-P t*P t) t)
    (hQ : HasDerivAt Q Q' t) :
    HasDerivAt (fun s => P s-Q s)
      ((A-p • Q t-Q t*Q t-Q')-
        (((p • (1:R))+P t)*(P t-Q t)+(P t-Q t)*Q t)) t := by
  apply (hP.fun_sub hQ).congr_deriv
  simp only [add_mul,sub_mul,mul_sub,smul_mul_assoc,one_mul]
  abel

/-- The first parameter difference damps with P on BOTH sides. This is why
one does not need a prior bound on the actual slope derivative. -/
lemma riccati_error_jet_deriv {P₁ Q₁ : ℝ → R} {A₁ P Q Q₁' : R} {p t : ℝ}
    (hP : HasDerivAt P₁ (A₁-p • P₁ t-P*P₁ t-P₁ t*P) t)
    (hQ : HasDerivAt Q₁ Q₁' t) :
    HasDerivAt (fun s => P₁ s-Q₁ s)
      (((A₁-p • Q₁ t-Q₁ t*Q-Q*Q₁ t-Q₁')-Q₁ t*(P-Q)-(P-Q)*Q₁ t)-
        ((p • (1:R)+P)*(P₁ t-Q₁ t)+(P₁ t-Q₁ t)*P)) t := by
  apply (hP.fun_sub hQ).congr_deriv
  simp only [add_mul,sub_mul,mul_sub,smul_mul_assoc,one_mul]
  abel

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix Set
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma damped_gronwall_bound {x M γ t : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M)
    (hγ : 0 < γ) (ht : 0 ≤ t) :
    gronwallBound x (-γ) M t ≤ x+M/γ := by
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hγ.ne')]
  dsimp only
  have hExp : Real.exp (-γ*t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hExp₀ := Real.exp_pos (-γ*t)
  have h1 : x*Real.exp (-γ*t) ≤ x := by nlinarith
  have he : M/(-γ)*(Real.exp (-γ*t)-1)=M/γ*(1-Real.exp (-γ*t)) := by ring
  rw [he]
  have h2 : M/γ*(1-Real.exp (-γ*t)) ≤ M/γ := by
    have hnon : 0 ≤ M/γ := div_nonneg hM hγ.le
    nlinarith
  linarith

/-- Quantitative source slow-pulse estimate, retaining both integrated errors
and the smaller pointwise parameter error. Its hypotheses are the two proved
error equations and coefficient residual bounds, NOT a bound on the unknown jet.
C is a single uniform constant and T is the genuine pulse duration. -/
theorem slow_pulse_error_estimate
    {X Z ρ ρ₁ Q₁ L R L₁ R₁ : ℝ → Matrix ι ι ℝ}
    {a T γ c d c₁ d₁ C η : ℝ}
    (hT : 1 ≤ T) (hγ : 0 < γ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hcd : c+d=γ) (hcd₁ : c₁+d₁=γ)
    (hρ : Continuous ρ) (hρ₁ : Continuous ρ₁) (hQ₁ : Continuous Q₁)
    (hX : ∀ t,HasDerivAt X (ρ t-(L t*X t+X t*R t)) t)
    (hZ : ∀ t,HasDerivAt Z ((ρ₁ t-Q₁ t*X t-X t*Q₁ t)-(L₁ t*Z t+Z t*R₁ t)) t)
    (hbρ : ∀ t ∈ Icc a (a+T),‖ρ t‖ ≤ C*η/T)
    (hbρ₁ : ∀ t ∈ Icc a (a+T),‖ρ₁ t‖ ≤ C*η/T)
    (hbQ₁ : ∀ t ∈ Icc a (a+T),‖Q₁ t‖ ≤ C/T)
    (hL : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j)
    (hL₁ : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      c₁*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L₁ t i j*v j)
    (hR₁ : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      d₁*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R₁ t i j*v j)
    (hinit : ‖X a‖ ≤ C*η) (hzinit : Z a=0) :
    (∀ t ∈ Icc a (a+T),‖X t‖ ≤ (C+C/γ)*η) ∧
    (∫ t in a..(a+T),‖X t‖) ≤ 2*C*η/γ ∧
    (∀ t ∈ Icc a (a+T),‖Z t‖ ≤ (C+2*C*(C+C/γ))*η/(γ*T)) ∧
    (∫ t in a..(a+T),‖Z t‖) ≤ C*η/γ+4*C^2*η/γ^2 := by
  have hTpos : 0 < T := by linarith
  have hab : a ≤ a+T := by linarith
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun t => (hX t).continuousAt
  have hXpoint : ∀ t ∈ Icc a (a+T),‖X t‖ ≤ (C+C/γ)*η := by
    intro t ht
    have hg := sylvester_gronwall hX hbρ hL hR t ht
    rw [hcd] at hg
    have hg' := damped_gronwall_bound (norm_nonneg (X a))
      (by positivity : 0 ≤ C*η/T) hγ (by linarith [ht.1] : 0 ≤ t-a)
    have htdiv : C*η/T ≤ C*η := div_le_self (by positivity) hT
    have htdiv' : (C*η/T)/γ ≤ C*η/γ := div_le_div_of_nonneg_right htdiv hγ.le
    calc
      ‖X t‖ ≤ ‖X a‖+(C*η/T)/γ := hg.trans hg'
      _ ≤ C*η+C*η/γ := add_le_add hinit htdiv'
      _ = _ := by ring
  have hI (f : ℝ → Matrix ι ι ℝ) (hf : Continuous f)
      (hb : ∀ t ∈ Icc a (a+T),‖f t‖ ≤ C*η/T) :
      (∫ t in a..(a+T),‖f t‖) ≤ C*η := by
    have hh := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
      (hf.norm.intervalIntegrable a (a+T)) (continuous_const.intervalIntegrable a (a+T)) hb
    simpa only [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul,
      mul_div_cancel₀ _ hTpos.ne'] using hh
  have hIX : (∫ t in a..(a+T),‖X t‖) ≤ 2*C*η/γ := by
    have hh := sylvester_integrated hab hρ hX hL hR
    rw [hcd] at hh
    apply (le_div_iff₀ hγ).2
    nlinarith [hI ρ hρ hbρ,norm_nonneg (X (a+T))]
  have hF : ∀ t ∈ Icc a (a+T),‖ρ₁ t-Q₁ t*X t-X t*Q₁ t‖ ≤
      (C+2*C*(C+C/γ))*η/T := by
    intro t ht
    calc
      _ ≤ ‖ρ₁ t‖+2*(C/T)*‖X t‖ := jet_forcing_norm _ _ _ (hbQ₁ t ht)
      _ ≤ C*η/T+2*(C/T)*((C+C/γ)*η) := by gcongr; exact hbρ₁ t ht; exact hXpoint t ht
      _ = _ := by ring
  have hZpoint : ∀ t ∈ Icc a (a+T),‖Z t‖ ≤ (C+2*C*(C+C/γ))*η/(γ*T) := by
    intro t ht
    have hh := sylvester_gronwall hZ hF hL₁ hR₁ t ht
    rw [hcd₁,hzinit,norm_zero] at hh
    have hb := damped_gronwall_bound (le_refl (0:ℝ))
      (by positivity : 0 ≤ (C+2*C*(C+C/γ))*η/T) hγ (by linarith [ht.1] : 0 ≤ t-a)
    calc
      _ ≤ 0+((C+2*C*(C+C/γ))*η/T)/γ := hh.trans hb
      _ = _ := by ring
  refine ⟨hXpoint,hIX,hZpoint,?_⟩
  have hh := sylvester_jet_integrated hab hρ₁ hQ₁ hXc hZ hbQ₁ hL₁ hR₁
  rw [hcd₁,hzinit,norm_zero,zero_add] at hh
  have hq : 0 ≤ C/T := by positivity
  have hstep : γ*(∫ t in a..(a+T),‖Z t‖) ≤ C*η+2*(C/T)*(2*C*η/γ) := by
    exact hh.trans (add_le_add (hI ρ₁ hρ₁ hbρ₁) (mul_le_mul_of_nonneg_left hIX (by positivity)))
  have hCT : C/T ≤ C := div_le_self hC hT
  have hmul := mul_le_mul_of_nonneg_right hCT (show 0 ≤ 4*C*η/γ by positivity)
  have hstep' : (∫ t in a..(a+T),‖Z t‖) ≤ (C*η+2*(C/T)*(2*C*η/γ))/γ :=
    (le_div_iff₀ hγ).2 (by simpa only [mul_comm] using hstep)
  calc
    _ ≤ (C*η+2*(C/T)*(2*C*η/γ))/γ  := hstep'
    _ ≤ (C*η+4*C^2*η/γ)/γ := by
      apply div_le_div_of_nonneg_right _ hγ.le
      have he₁ : 2*(C/T)*(2*C*η/γ)=(C/T)*(4*C*η/γ) := by ring
      have he₂ : 4*C^2*η/γ=C*(4*C*η/γ) := by ring
      rw [he₁,he₂]
      exact add_le_add_right hmul _
    _ = _ := by field_simp

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix Set
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_scalar_one (v : ι → ℝ) (c : ℝ) :
    (∑ i,∑ j,v i*(c • (1 : Matrix ι ι ℝ)) i j*v j)=c*∑ i,(v i)^2 := by
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] in
lemma quadratic_add (v : ι → ℝ) (A B : Matrix ι ι ℝ) :
    (∑ i,∑ j,v i*(A+B) i j*v j)=
      (∑ i,∑ j,v i*A i j*v j)+(∑ i,∑ j,v i*B i j*v j) := by
  simp only [Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

/-- Genuine uniform reset including its exponentially decaying history term.
Only coefficient-size and Riccati positivity bounds are required; there is no
assumed closeness of the incoming slope to the round root. -/
theorem round_reset_estimate {A P : ℝ → Matrix ι ι ℝ} {p : ℝ → ℝ}
    {a b pmin α θ M C : ℝ}
    (hγ : 0 < pmin+α+θ) (hM : 0 ≤ M)
    (hP : ∀ t,HasDerivAt P (A t-p t • P t-P t*P t) t)
    (hp : ∀ t ∈ Icc a b,pmin ≤ p t)
    (hpos : ∀ t ∈ Icc a b,∀ v : ι → ℝ,
      α*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*P t i j*v j)
    (hforce : ∀ t ∈ Icc a b,
      ‖A t-(p t*θ+θ^2) • (1 : Matrix ι ι ℝ)‖ ≤ M)
    (hinit : ‖P a-θ • (1 : Matrix ι ι ℝ)‖ ≤ C) :
    ∀ t ∈ Icc a b,
      ‖P t-θ • (1 : Matrix ι ι ℝ)‖ ≤
        C*Real.exp (-(pmin+α+θ)*(t-a))+M/(pmin+α+θ) := by
  let X := fun t => P t-θ • (1 : Matrix ι ι ℝ)
  let F := fun t => A t-(p t*θ+θ^2) • (1 : Matrix ι ι ℝ)
  have hX (t : ℝ) : HasDerivAt X
      (F t-((p t • (1 : Matrix ι ι ℝ)+P t)*X t+X t*(θ • (1 : Matrix ι ι ℝ)))) t := by
    have hd := riccati_error_deriv (hP t) (hasDerivAt_const t (θ • (1 : Matrix ι ι ℝ)))
    apply hd.congr_deriv
    dsimp only [F,X]
    simp only [smul_smul,mul_smul_comm,mul_one,sub_zero,pow_two]
    module
  have hL (t : ℝ) (ht : t ∈ Icc a b) (v : ι → ℝ) :
      (pmin+α)*(∑ i,(v i)^2) ≤
        ∑ i,∑ j,v i*(p t • (1 : Matrix ι ι ℝ)+P t) i j*v j := by
    rw [quadratic_add,quadratic_scalar_one]
    have hm := mul_le_mul_of_nonneg_right (hp t ht) (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (v i))
    linarith [hpos t ht v]
  have hR (t : ℝ) (_ : t ∈ Icc a b) (v : ι → ℝ) :
      θ*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*(θ • (1 : Matrix ι ι ℝ)) i j*v j := by
    rw [quadratic_scalar_one]
  intro t ht
  have hg := sylvester_gronwall hX hforce hL hR t ht
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hγ.ne')] at hg
  have he : M/(-(pmin+α+θ))*(Real.exp (-(pmin+α+θ)*(t-a))-1)=
      M/(pmin+α+θ)*(1-Real.exp (-(pmin+α+θ)*(t-a))) := by rw [div_neg]; ring
  dsimp only at hg
  rw [he] at hg
  have hi := mul_le_mul_of_nonneg_right hinit (Real.exp_pos (-(pmin+α+θ)*(t-a))).le
  have hnon : 0 ≤ M/(pmin+α+θ) := div_nonneg hM hγ.le
  have hexp := Real.exp_pos (-(pmin+α+θ)*(t-a))
  dsimp only [X] at hg
  nlinarith

end HarmonicCounterexample.LinearODE

end

end OAI
