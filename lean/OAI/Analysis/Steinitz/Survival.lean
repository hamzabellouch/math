import OAI.Analysis.Steinitz.Correlation

namespace OAI

/-! Gaussian path survival with slab and state constraints. -/

section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace GaussianEvents
variable {E F I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def constraints (A : I → E →L[ℝ] F) (R : I → ℝ) : Set E :=
  {x | ∀ i,‖A i x‖ ≤ R i}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma constraints_closed (A : I → E →L[ℝ] F) (R : I → ℝ) : IsClosed (constraints A R) := by
  simp only [constraints,Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (A i).continuous.norm continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma constraints_convex (A : I → E →L[ℝ] F) (R : I → ℝ) : Convex ℝ (constraints A R) := by
  have he : constraints A R = ⋂ i,(A i) ⁻¹' Metric.closedBall 0 (R i) := by
    ext x; simp [constraints,Metric.mem_closedBall,dist_zero_right]
  rw [he]
  exact convex_iInter fun i => (convex_closedBall (0:F) (R i)).linear_preimage (A i).toLinearMap

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma constraints_symmetric (A : I → E →L[ℝ] F) (R : I → ℝ) :
    ∀ x ∈ constraints A R,-x ∈ constraints A R := by
  intro x hx i
  simpa only [map_neg,norm_neg] using hx i

lemma finite_half {J : Type*} [Fintype J] (K : J → Set E)
    (hc : ∀ i,IsClosed (K i)) (hv : ∀ i,Convex ℝ (K i))
    (hs : ∀ i,∀ x∈K i,-x∈K i)
    (hp : ∀ i,(1/2:ℝ≥0∞) ≤ stdGaussian E (K i)) :
    (1/2:ℝ)^(Fintype.card J) ≤ (stdGaussian E).real (⋂ i,K i) := by
  classical
  have h := EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation
    (ContinuousLinearMap.id ℝ E) Finset.univ K (fun i _ => hc i) (fun i _ => hv i) (fun i _ => hs i)
  have he : (stdGaussian E).map (ContinuousLinearMap.id ℝ E) = stdGaussian E := Measure.map_id
  rw [he] at h
  have hh : (∏ i,(stdGaussian E).real (K i)) ≤ (stdGaussian E).real (⋂ i,K i) := by
    simpa using h
  apply le_trans _ hh
  change (1/2:ℝ)^(Finset.univ : Finset J).card ≤ _
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (hp i)
    norm_num [Measure.real] at hh ⊢
    exact hh)

end GaussianEvents

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace BigOperators
namespace GaussianAR
open GaussianTail
variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I]

lemma epoch_survival (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (F : I → Matrix κ ι ℝ) (h k : I → ℝ)
    {H C θ : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : 0≤θ)
    (hh : ∀ i,h i ∈ Set.Icc (0:ℝ) H) (hk : ∀ i,1/4≤k i)
    (hs : ∀ i,squareMass (F i) ≤ C*k i)
    (hi : ∀ i j,⌊h i⌋₊=⌊h j⌋₊ → squareMass (F i-F j) ≤
      C*(1+k i+k j)*|h i-h j|^(2/3:ℝ))
    (ht : ∀ i,(F i*diagonal (fun j => 1-r j)*(F i).transpose).trace ≤ C*k i*θ)
    (hop : ∀ i x,‖matrixMap (F i) x‖^2 ≤ ‖x‖^2) :
    Real.exp (-(H+1)*(θ*n+1)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
      {x | ∀ i (t : Fin (n+1)), ‖matrixMap (F i*evaluation r n t) x‖ ≤
        800*(640*C+2)*Real.sqrt (k i)} := by
  classical
  let J := Fin (⌊H⌋₊+1) × Fin (⌊θ*n⌋₊+1)
  let label (p : I × Fin (n+1)) : J :=
    (⟨⌊h p.1⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (hh p.1).2)⟩,
      ⟨⌊θ*(p.2.val:ℝ)⌋₊,Nat.lt_succ_of_le (Nat.floor_mono
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt_succ p.2.isLt) hθ))⟩)
  let B (j : J) := {p : I × Fin (n+1) // label p=j}
  let A (j : J) (p : B j) := matrixMap (F p.val.1*evaluation r n p.val.2)
  let R (j : J) (p : B j) := 800*(640*C+2)*Real.sqrt (k p.val.1)
  let K (j : J) := GaussianEvents.constraints (A j) (R j)
  have hp (j : J) : (1/2:ℝ≥0∞) ≤ stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι)) (K j) := by
    let a (p : B j) := h p.val.1-(j.1.val:ℝ)
    let b (p : B j) := θ*(p.val.2.val:ℝ)-(j.2.val:ℝ)
    have hla (p : B j) : ⌊h p.val.1⌋₊=j.1.val := congrArg (fun z : J => z.1.val) p.property
    have hlb (p : B j) : ⌊θ*(p.val.2.val:ℝ)⌋₊=j.2.val := congrArg (fun z : J => z.2.val) p.property
    have ha (p : B j) : a p ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [a]; rw [← hla p]
      exact ⟨sub_nonneg.mpr (Nat.floor_le (hh p.val.1).1),by linarith [Nat.lt_floor_add_one (h p.val.1)]⟩
    have hb (p : B j) : b p ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [b]; rw [← hlb p]
      exact ⟨sub_nonneg.mpr (Nat.floor_le (by positivity)),by linarith [Nat.lt_floor_add_one (θ*(p.val.2.val:ℝ))]⟩
    have hinc (p q : B j) : squareMass (F p.val.1-F q.val.1) ≤
        C*(1+k p.val.1+k q.val.1)*|a p-a q|^(2/3:ℝ) := by
      simpa only [a,sub_sub_sub_cancel_right] using hi p.val.1 q.val.1 ((hla p).trans (hla q).symm)
    have htime (p q : B j) : θ*|((p.val.2).val:ℝ)-(q.val.2).val| ≤ |b p-b q| := by
      dsimp [b]
      rw [sub_sub_sub_cancel_right,← mul_sub,abs_mul,abs_of_nonneg hθ]
    exact block_survival r hr hr1 n (fun p : B j => F p.val.1) (fun p => p.val.2)
      a b (fun p => k p.val.1) ha hb (fun p => hk p.val.1) hC
      (fun p => hs p.val.1) hinc (fun p => ht p.val.1) htime (fun p => hop p.val.1)
  have hprob := GaussianEvents.finite_half K
    (fun j => GaussianEvents.constraints_closed (A j) (R j))
    (fun j => GaussianEvents.constraints_convex (A j) (R j))
    (fun j => GaussianEvents.constraints_symmetric (A j) (R j)) hp
  have he : (⋂ j,K j)={x | ∀ i (t : Fin (n+1)), ‖matrixMap (F i*evaluation r n t) x‖ ≤
        800*(640*C+2)*Real.sqrt (k i)} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,K,GaussianEvents.constraints]
    constructor
    · intro hx i t; exact hx (label (i,t)) ⟨(i,t),rfl⟩
    · intro hx j p; exact hx p.val.1 p.val.2
  rw [he] at hprob
  apply le_trans _ hprob
  have hcard : (Fintype.card J:ℝ) ≤ (H+1)*(θ*n+1) := by
    simp only [J,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    exact mul_le_mul (by linarith [Nat.floor_le hH]) (by linarith [Nat.floor_le (show 0≤θ*n by positivity)])
      (by positivity) (by linarith)
  calc
    _ ≤ Real.exp (-(Fintype.card J:ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = (Real.exp (-1))^(Fintype.card J) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by
      have hg := Real.add_one_le_exp (1:ℝ)
      rw [Real.exp_neg]
      exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; linarith)) _

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient Gain Energy GaussianTail GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

noncomputable def epochFactor : ℝ := 1+16*gainConstant
noncomputable def momentConstant : ℝ := incrementConstant+20
noncomputable def survivalRadius : ℝ := 800*(640*momentConstant+2)

lemma epochFactor_ge_one : 1≤epochFactor := by
  unfold epochFactor
  linarith [gainConstant_pos]
lemma momentConstant_ge : 16≤ momentConstant := by
  unfold momentConstant
  linarith [incrementConstant_pos]
lemma survivalRadius_pos : 0<survivalRadius := by
  unfold survivalRadius
  linarith [momentConstant_ge]

omit [DecidableEq ι] [DecidableEq κ] in
lemma squareMass_sub_comm (A B : Matrix ι κ ℝ) : squareMass (A-B)=squareMass (B-A) := by
  unfold squareMass
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply]
  ring

lemma filtered_epoch_survival {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    {q : κ → ℝ} (hq : ∀ j,0<q j) {θ : ℝ} (hθ : 0<θ)
    (r : κ → ℝ) (hr : ∀ j,0≤r j) (hr1 : ∀ j,r j≤1) (hrq : ∀ j,1-r j≤q j) (n : ℕ) :
    let qθ := fun j => q j/θ
    let F := fun t => lift (run R (ps t)) (cfc cutoff (state qθ (run R (ps t))))
    let k := fun t => (cfc sizeWeight (state qθ (run R (ps t)))).trace
    Real.exp (-(epochFactor*cost (state qθ R) (L.map (fun p => p.move qθ))+1)*(θ*n+1)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×κ))).real
      {x | ∀ t (u : Fin (n+1)), ‖matrixMap (F t*evaluation r n u) x‖ ≤ survivalRadius*Real.sqrt (k t)} := by
  classical
  dsimp only
  let qθ := fun j => q j/θ
  let F := fun t => lift (run R (ps t)) (cfc cutoff (state qθ (run R (ps t))))
  let k := fun t => (cfc sizeWeight (state qθ (run R (ps t)))).trace
  let e := fun t => cost (state qθ R) ((ps t).map (fun p => p.move qθ))
  let H := epochFactor*cost (state qθ R) (L.map (fun p => p.move qθ))
  let h := fun t => epochFactor*e t
  have hqθ : ∀ j,0<qθ j := fun j => div_pos (hq j) hθ
  have hR' (t : T) : run R (ps t)*(run R (ps t)).transpose=1 :=
    run_coisometry hR (good_prefix hp (hps t)) (fresh_prefix hf (hps t)) (nodup_prefix hd (hps t))
  have hX (t : T) : (state qθ (run R (ps t))).PosDef := state_posDef (hR' t) hqθ
  have hk0 (t : T) : 0≤k t := by
    change 0 ≤ (cfc sizeWeight (state qθ (run R (ps t)))).trace
    rw [trace_cfc (hX t).1]
    exact Finset.sum_nonneg fun i _ => Scale.size_nonneg ((hX t).eigenvalues_pos i).le
  have he0 (t : T) : 0≤e t := cost_nonneg (state_posDef hR hqθ).posSemidef
    (moves_good (good_prefix hp (hps t)) (fun j => (hqθ j).le))
  have hfac : 0<epochFactor := lt_of_lt_of_le (by norm_num) epochFactor_ge_one
  have hH : 0≤H := mul_nonneg hfac.le
    (cost_nonneg (state_posDef hR hqθ).posSemidef (moves_good hp (fun j => (hqθ j).le)))
  have hh (t : T) : h t ∈ Set.Icc (0:ℝ) H := by
    refine ⟨mul_nonneg hfac.le (he0 t),mul_le_mul_of_nonneg_left ?_ hfac.le⟩
    exact cost_prefix (state_posDef hR hqθ).posSemidef (moves_good hp (fun j => (hqθ j).le))
      ((hps t).map _)
  have he_mono {s t : T} (hst : ps s <+: ps t) : e s≤e t :=
    cost_prefix (state_posDef hR hqθ).posSemidef
      (moves_good (good_prefix hp (hps t)) (fun j => (hqθ j).le)) (hst.map _)
  have hlocal {s t : T} (hst : ps s <+: ps t) (hab : ⌊h s⌋₊=⌊h t⌋₊) :
      squareMass (F t-F s) ≤ momentConstant*(1+k s+k t)*|h s-h t|^(2/3:ℝ) := by
    have hen : 0≤e t-e s := sub_nonneg.mpr (he_mono hst)
    have hex : |h s-h t|=epochFactor*(e t-e s) := by
      rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr
        (mul_le_mul_of_nonneg_left (he_mono hst) hfac.le))]
      ring
    have hsmall : e t-e s ≤ 1/(16*gainConstant) := by
      have ht := Nat.lt_floor_add_one (h t)
      rw [← hab] at ht
      have hss := Nat.floor_le (hh s).1
      have hdiff : epochFactor*(e t-e s) ≤ 1 := by dsimp [h] at ht hss; linarith
      apply (le_div_iff₀ (mul_pos (by norm_num) gainConstant_pos)).mpr
      have hscale : 16*gainConstant≤epochFactor := by unfold epochFactor; linarith
      nlinarith [mul_le_mul_of_nonneg_right hscale hen]
    have hi := local_prefix_increment hR hp hf hd hst (hps t) hqθ hsmall
    have hip : (e t-e s)^(1/exponent) ≤ |h s-h t|^(2/3:ℝ) := by
      rw [show 1/exponent=(2/3:ℝ) by norm_num [exponent]]
      apply Real.rpow_le_rpow hen
      · rw [hex]; nlinarith [epochFactor_ge_one]
      · norm_num
    have hinc : incrementConstant*(1+k t) ≤ momentConstant*(1+k s+k t) := by
      have hc : incrementConstant≤ momentConstant := by unfold momentConstant; linarith
      exact mul_le_mul hc (by linarith [hk0 s]) (by linarith [hk0 t]) (by linarith [momentConstant_ge])
    exact (squareMass_le_weighted (F t-F s) (fun j => (hqθ j).le)).trans
      (hi.trans (mul_le_mul hinc hip (Real.rpow_nonneg hen _) (mul_nonneg (by linarith [momentConstant_ge]) (by linarith [hk0 s,hk0 t]))))
  let I := {t : T // F t≠0}
  have hbound := epoch_survival r hr hr1 n (fun t : I => F t.val) (fun t => h t.val)
    (fun t => k t.val) hH (show 0≤ momentConstant by linarith [momentConstant_ge]) hθ.le
    (fun t => hh t.val) (fun t => lift_cutoff_size (hX t.val).posSemidef t.property)
    (fun t => (lift_cutoff_mass (hR' t.val) (hX t.val).posSemidef).trans
      (mul_le_mul_of_nonneg_right (by linarith [momentConstant_ge]) (hk0 t.val)))
    (by
      intro s t hab
      rcases List.prefix_or_prefix_of_prefix (hps s.val) (hps t.val) with hst|hts
      · rw [squareMass_sub_comm]
        exact hlocal hst hab
      · have hu := hlocal hts hab.symm
        simpa only [abs_sub_comm,add_comm,add_left_comm,add_assoc] using hu)
    (by
      intro t
      change weightedSq (F t.val) (diagonal (fun j => 1-r j))≤_
      exact (weightedSq_diagonal_mono _ hrq).trans ((lift_cutoff_time (hR' t.val) hq hθ).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by linarith [momentConstant_ge]) (hk0 t.val)) hθ.le)))
    (fun t => lift_cutoff_contract (hR' t.val) (hX t.val).1)
  apply hbound.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx t u
  change ‖matrixMap (F t*evaluation r n u) x‖ ≤ survivalRadius*Real.sqrt (k t)
  by_cases ht : F t=0
  · simp only [ht,Matrix.zero_mul,matrixMap,map_zero,_root_.zero_apply,norm_zero]
    exact mul_nonneg survivalRadius_pos.le (Real.sqrt_nonneg _)
  · exact hx ⟨t,ht⟩ u

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleMatrix ScaleEnergy
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
lemma state_scale (q : κ → ℝ) (R : Matrix ι κ ℝ) (θ : ℝ) :
    state (fun j => q j/θ) R = θ⁻¹ • state q R := by
  unfold state
  have he : diagonal (fun j => q j/θ) = θ⁻¹ • diagonal q := by
    rw [← Matrix.diagonal_smul]
    congr 1
    ext j
    simp [div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mul_smul,Matrix.smul_mul]

lemma sum_scale_size {A : Matrix ι ι ℝ} (hA : A.PosDef) (S : Finset ℤ) :
    (∑ k ∈ S,(cfc sizeWeight (((2:ℝ)^k)⁻¹ • A)).trace) ≤ 14*Fintype.card ι := by
  simp only [cfc_scaled hA.1,trace_cfc hA.1]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : ι,(14:ℝ) := Finset.sum_le_sum fun i _ => by
      simpa only [div_eq_mul_inv,mul_comm] using Scale.sum_size_dyadic S (hA.eigenvalues_pos i)
    _ = _ := by simp [mul_comm]

lemma form_mono {A B : Matrix ι ι ℝ} (hAB : A≤B) (x : EuclideanSpace ℝ ι) :
    ⟪x,toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ ⟪x,toEuclideanCLM (𝕜 := ℝ) B x⟫ := by
  have h := (Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg (WithLp.ofLp x)
  simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,inner_toEuclideanCLM,sub_nonneg] using h

lemma cutoff_cover {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (S : Finset ℤ)
    (hS : ∀ i,∃ k∈S,1≤hA.eigenvalues i/(2:ℝ)^k ∧ hA.eigenvalues i/(2:ℝ)^k≤2) :
    (1 : Matrix ι ι ℝ) ≤ ∑ k∈S,cfc cutoff (((2:ℝ)^k)⁻¹ • A)*cfc cutoff (((2:ℝ)^k)⁻¹ • A) := by
  have he (k : ℤ) : cfc cutoff (((2:ℝ)^k)⁻¹ • A)*cfc cutoff (((2:ℝ)^k)⁻¹ • A) =
      cfc (fun x => cutoff (x/(2:ℝ)^k)^2) A := by
    rw [cfc_scaled hA,cfc_mul_same hA]
    congr 1
    ext x
    simp [div_eq_mul_inv,mul_comm,pow_two]
  simp only [he]
  rw [← cfc_sum _ A S (fun _ _ => Gain.finite_spectrum_continuous _ _)]
  rw [← cfc_const_one ℝ A]
  apply (cfc_le_iff _ _ A continuousOn_const (Gain.finite_spectrum_continuous _ _) hA.isSelfAdjoint).mpr
  intro x hx
  obtain ⟨i,rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  obtain ⟨k,hk,hk1,hk2⟩ := hS i
  simp only [Finset.sum_apply]
  change 1≤∑ k∈S,cutoff (hA.eigenvalues i/(2:ℝ)^k)^2
  have hh := Finset.single_le_sum (fun j (_ : j∈S) => sq_nonneg (cutoff (hA.eigenvalues i/(2:ℝ)^j))) hk
  have hone : cutoff (hA.eigenvalues i/(2:ℝ)^k)=1 := by
    simp [cutoff,show (2:ℝ)⁻¹ < hA.eigenvalues i/(2:ℝ)^k by norm_num; linarith,not_lt.mpr hk1,hk2]
  rwa [hone,one_pow] at hh

omit [DecidableEq κ] in
lemma lift_gram {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {A : Matrix ι ι ℝ} (hA : A.transpose=A) :
    (lift R A).transpose*lift R A = R.transpose*(A*A)*R := by
  simp only [lift,Matrix.transpose_mul,Matrix.transpose_transpose,hA]
  calc
    _ = R.transpose*A*(R*R.transpose)*A*R := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR,Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma norm_sq_reconstruct {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (S : Finset ℤ)
    (hS : ∀ i,∃ k∈S,1≤hA.eigenvalues i/(2:ℝ)^k ∧ hA.eigenvalues i/(2:ℝ)^k≤2)
    (x : EuclideanSpace ℝ κ) :
    ‖matrixMap R x‖^2 ≤ ∑ k∈S,‖matrixMap (lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • A))) x‖^2 := by
  have hp := (Matrix.le_iff.mp (cutoff_cover hA S hS)).mul_mul_conjTranspose_same R.transpose
  simp only [conjTranspose_eq_transpose_of_trivial,transpose_transpose,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_one,Matrix.mul_sum,Matrix.sum_mul] at hp
  have hh := form_mono (Matrix.le_iff.mpr hp) x
  rw [gram_form] at hh
  have he (k : ℤ) : R.transpose*(cfc cutoff (((2:ℝ)^k)⁻¹ • A)*cfc cutoff (((2:ℝ)^k)⁻¹ • A))*R =
      (lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • A))).transpose*lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • A)) :=
    (lift_gram hR (cfc_transpose (hA.smul (IsSelfAdjoint.all _)) cutoff)).symm
  simp only [he,map_sum,_root_.sum_apply,inner_sum,gram_form] at hh
  exact hh

lemma exists_finite_scales {T : Type*} [Fintype T] (A : T → Matrix ι ι ℝ)
    (hA : ∀ t,(A t).PosDef) :
    ∃ S : Finset ℤ, (∀ t i,∃ k∈S,1≤(hA t).1.eigenvalues i/(2:ℝ)^k ∧
      (hA t).1.eigenvalues i/(2:ℝ)^k≤2) ∧
      (∀ k∈S,∃ t i,(2:ℝ)^k≤(hA t).1.eigenvalues i) := by
  classical
  choose f hf using fun t i => Scale.dyadic_normalize ((hA t).eigenvalues_pos i)
  refine ⟨Finset.univ.image (fun p : T×ι => f p.1 p.2),?_,?_⟩
  · intro t i
    exact ⟨f t i,Finset.mem_image.mpr ⟨(t,i),Finset.mem_univ _,rfl⟩,hf t i⟩
  · intro k hk
    obtain ⟨⟨t,i⟩,_,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨t,i,(le_div_iff₀ (zpow_pos (by norm_num) _)).mp (hf t i).1 |>.trans' (by simp)⟩

end EuclideanSteinitz.Filter

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianEvents
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma finite_exp {J : Type*} [Fintype J] (K : J → Set E) (c : J → ℝ)
    (hc : ∀ i,IsClosed (K i)) (hv : ∀ i,Convex ℝ (K i))
    (hs : ∀ i,∀ x∈K i,-x∈K i)
    (hp : ∀ i,Real.exp (-c i) ≤ (stdGaussian E).real (K i)) :
    Real.exp (-(∑ i,c i)) ≤ (stdGaussian E).real (⋂ i,K i) := by
  classical
  have hh := EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation
    (ContinuousLinearMap.id ℝ E) Finset.univ K (fun i _ => hc i) (fun i _ => hv i) (fun i _ => hs i)
  have he : (stdGaussian E).map (ContinuousLinearMap.id ℝ E) = stdGaussian E := Measure.map_id
  rw [he] at hh
  have hp' : (∏ i,Real.exp (-c i)) ≤ ∏ i,(stdGaussian E).real (K i) :=
    Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) (fun i _ => hp i)
  simpa only [← Real.exp_sum,Finset.sum_neg_distrib,Finset.mem_univ,Set.iInter_true] using hp'.trans hh

end GaussianEvents

namespace GaussianAR
open GaussianTail EuclideanSteinitz.Coefficient EuclideanSteinitz.Filter
variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]  [Fintype J]
noncomputable def slabRadius : ℝ := 800*(640+2)
lemma slabRadius_pos : 0<slabRadius := by norm_num [slabRadius]

lemma weighted_diagonal_eq (A : Matrix κ ι ℝ) (q : ι → ℝ) :
    weightedSq A (diagonal q) = ∑ j,∑ i,q i*(A j i)^2 := by
  change (∑ j,∑ i,(A*diagonal q) j i*A j i)=_
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma one_slab_survival (A : Matrix κ ι ℝ) (hA : squareMass A ≤ 1)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (q : ι → ℝ) (hq : ∀ i,0≤q i) (hrq : ∀ i,1-r i≤q i) (n : ℕ) :
    Real.exp (-(weightedSq A (diagonal q)*n+1)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ t : Fin (n+1),‖matrixMap (A*evaluation r n t) x‖ ≤ slabRadius} := by
  have ht : 0≤weightedSq A (diagonal q) := weightedSq_nonneg A (PosSemidef.diagonal hq)
  have hh := epoch_survival r hr hr1 n (fun _ : Unit => A) (fun _ => 0) (fun _ => 1)
    (H := 0) (C := 1) (θ := weightedSq A (diagonal q)) (by norm_num) (by norm_num) ht
    (fun _ => by simp) (fun _ => by norm_num) (fun _ => by simpa using hA)
    (by intros; simp [squareMass])
    (fun _ => by
      change weightedSq A (diagonal (fun i => 1-r i)) ≤ 1*1*weightedSq A (diagonal q)
      simpa only [one_mul] using weightedSq_diagonal_mono A hrq)
    (fun _ x => (norm_sq_le_squareMass A x).trans (by nlinarith [sq_nonneg ‖x‖]))
  simpa only [zero_add,neg_mul,one_mul,Real.sqrt_one,mul_one,forall_const,slabRadius] using hh

lemma slabs_survival (A : J → Matrix κ ι ℝ) (hA : ∀ j,squareMass (A j) ≤ 1)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (q : ι → ℝ) (hq : ∀ i,0≤q i) (hrq : ∀ i,1-r i≤q i) (n : ℕ) :
    Real.exp (-(Fintype.card J:ℝ)-(∑ j,weightedSq (A j) (diagonal q))*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ j (t : Fin (n+1)),‖matrixMap (A j*evaluation r n t) x‖ ≤ slabRadius} := by
  let K := fun j => GaussianEvents.constraints (fun t : Fin (n+1) => matrixMap (A j*evaluation r n t)) (fun _ => slabRadius)
  have hh := GaussianEvents.finite_exp K (fun j => weightedSq (A j) (diagonal q)*n+1)
    (fun j => GaussianEvents.constraints_closed _ _) (fun j => GaussianEvents.constraints_convex _ _)
    (fun j => GaussianEvents.constraints_symmetric _ _) (fun j => one_slab_survival (A j) (hA j) r hr hr1 q hq hrq n)
  have he : (⋂ j,K j)={x | ∀ j (t : Fin (n+1)),‖matrixMap (A j*evaluation r n t) x‖ ≤ slabRadius} := by
    ext x; simp only [K,GaussianEvents.constraints,Set.mem_iInter,Set.mem_ofPred_eq]
  rw [he] at hh
  convert hh using 1
  congr 1
  simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

end GaussianAR

end

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleMatrix ScaleEnergy Energy GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

noncomputable def stateRadius : ℝ := 4*survivalRadius
noncomputable def stateRate : ℝ := 84*epochFactor+2
lemma stateRadius_pos : 0 < stateRadius := mul_pos (by norm_num) survivalRadius_pos
lemma stateRate_nonneg : 0 ≤ stateRate := by unfold stateRate; linarith [epochFactor_ge_one]

omit [DecidableEq ι] in
lemma matrixMap_mul_apply {ν : Type*} [Fintype ν] [DecidableEq ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) (x : EuclideanSpace ℝ ν) :
    matrixMap (A*B) x = matrixMap A (matrixMap B x) := by
  apply WithLp.ofLp_injective
  exact Matrix.mulVec_mulVec x A B |>.symm

lemma reconstruction_bound {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {q : κ → ℝ} (hq : ∀ j,0<q j) (S : Finset ℤ)
    (hS : ∀ i,∃ k∈S,1≤(state_posDef hR hq).1.eigenvalues i/(2:ℝ)^k ∧
      (state_posDef hR hq).1.eigenvalues i/(2:ℝ)^k≤2)
    (x : EuclideanSpace ℝ κ)
    (hx : ∀ k∈S,‖matrixMap (lift R (cfc cutoff (state (fun j => q j/(2:ℝ)^k) R))) x‖ ≤
      survivalRadius*Real.sqrt ((cfc sizeWeight (state (fun j => q j/(2:ℝ)^k) R)).trace)) :
    ‖matrixMap R x‖ ≤ stateRadius*Real.sqrt (Fintype.card ι) := by
  have hA := state_posDef hR hq
  have hrec := norm_sq_reconstruct hR hA.1 S hS x
  have hk (k : ℤ) : 0≤(cfc sizeWeight (((2:ℝ)^k)⁻¹ • state q R)).trace := by
    rw [cfc_scaled hA.1,trace_cfc hA.1]
    exact Finset.sum_nonneg fun i _ => Scale.size_nonneg (mul_nonneg (inv_nonneg.mpr (zpow_pos (by norm_num) _).le) (hA.eigenvalues_pos i).le)
  have hb : (∑ k∈S,‖matrixMap (lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • state q R))) x‖^2) ≤
      survivalRadius^2*(14*Fintype.card ι) := by
    calc
      _ ≤ ∑ k∈S,survivalRadius^2*(cfc sizeWeight (((2:ℝ)^k)⁻¹ • state q R)).trace := by
        apply Finset.sum_le_sum
        intro k hkS
        have hh := pow_le_pow_left₀ (norm_nonneg _) (hx k hkS) 2
        simpa only [state_scale,mul_pow,Real.sq_sqrt (hk k)] using hh
      _ = survivalRadius^2*(∑ k∈S,(cfc sizeWeight (((2:ℝ)^k)⁻¹ • state q R)).trace) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_scale_size hA S) (sq_nonneg _)
  have hs := Real.sq_sqrt (show (0:ℝ)≤Fintype.card ι by positivity)
  have hp : 0 ≤ stateRadius*Real.sqrt (Fintype.card ι) := mul_nonneg stateRadius_pos.le (Real.sqrt_nonneg _)
  have ht : ‖matrixMap R x‖^2 ≤ (stateRadius*Real.sqrt (Fintype.card ι))^2 := by
    apply hrec.trans (hb.trans _)
    rw [mul_pow,hs,stateRadius]
    nlinarith [mul_nonneg (sq_nonneg survivalRadius) (show (0:ℝ)≤Fintype.card ι by positivity)]
  exact (sq_le_sq₀ (norm_nonneg _) hp).mp ht

lemma state_survival {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    {q : κ → ℝ} (hq : ∀ j,0<q j)
    (r : κ → ℝ) (hr : ∀ j,0≤r j) (hr1 : ∀ j,r j≤1) (hrq : ∀ j,1-r j≤q j) :
    ∃ a : ℝ,∀ n : ℕ,
      Real.exp (-a-stateRate*(∑ j,q j)*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×κ))).real
        {x | ∀ t (u : Fin (n+1)),‖matrixMap (run R (ps t)*evaluation r n u) x‖ ≤ stateRadius*Real.sqrt (Fintype.card ι)} := by
  classical
  let Rt := fun t => run R (ps t)
  have hRt (t : T) : Rt t*(Rt t).transpose=1 :=
    run_coisometry hR (good_prefix hp (hps t)) (fresh_prefix hf (hps t)) (nodup_prefix hd (hps t))
  let A := fun t => state q (Rt t)
  have hA (t : T) : (A t).PosDef := state_posDef (hRt t) hq
  obtain ⟨S,hS,hS'⟩ := exists_finite_scales A hA
  let e := fun k : ℤ => cost (state (fun j => q j/(2:ℝ)^k) R) (L.map (fun p => p.move (fun j => q j/(2:ℝ)^k)))
  let c := fun k : ℤ => epochFactor*e k+1
  have htq : 0≤∑ j,q j := Finset.sum_nonneg fun j _ => (hq j).le
  have hθ (k : ℤ) (hk : k∈S) : (2:ℝ)^k ≤ ∑ j,q j := by
    obtain ⟨t,i,hi⟩ := hS' k hk
    apply hi.trans
    have htrace : (hA t).1.eigenvalues i ≤ (A t).trace := by
      rw [trace_spectral (hA t).1]
      exact Finset.single_le_sum (fun j _ => (hA t).eigenvalues_pos j |>.le) (Finset.mem_univ i)
    exact htrace.trans (state_trace_le (hRt t) (fun j => (hq j).le))
  have hrate : (∑ k : S,c k.val*(2:ℝ)^k.val) ≤ stateRate*(∑ j,q j) := by
    have he := sum_epoch_cost hR hp hd (fun j => (hq j).le) S
    have ht := sum_dyadic_le htq hθ
    simp only [← state_scale] at he
    have hsum : (∑ k : S,c k.val*(2:ℝ)^k.val) =
        epochFactor*(∑ k∈S,(2:ℝ)^k*e k)+(∑ k∈S,(2:ℝ)^k) := by
      rw [Finset.sum_coe_sort S (fun k => c k*(2:ℝ)^k),Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [c]
      ring
    rw [hsum]
    unfold stateRate
    nlinarith [mul_le_mul_of_nonneg_left he (show 0≤epochFactor by linarith [epochFactor_ge_one])]
  refine ⟨∑ k : S,c k.val,fun n => ?_⟩
  let F := fun k : S => fun t => lift (Rt t) (cfc cutoff (state (fun j => q j/(2:ℝ)^k.val) (Rt t)))
  let w := fun k : S => fun t => survivalRadius*Real.sqrt ((cfc sizeWeight (state (fun j => q j/(2:ℝ)^k.val) (Rt t))).trace)
  let K := fun k : S => GaussianEvents.constraints
    (fun p : T×Fin (n+1) => matrixMap (F k p.1*evaluation r n p.2)) (fun p => w k p.1)
  have hprob := GaussianEvents.finite_exp K (fun k : S => c k.val*((2:ℝ)^k.val*n+1))
    (fun k => GaussianEvents.constraints_closed _ _) (fun k => GaussianEvents.constraints_convex _ _)
    (fun k => GaussianEvents.constraints_symmetric _ _) (fun k => by
      have hh := filtered_epoch_survival hR hp hf hd ps hps hq (θ := (2:ℝ)^k.val) (zpow_pos (by norm_num) k.val) r hr hr1 hrq n
      dsimp only at hh
      convert hh using 1
      · dsimp [c,e]; congr 1; ring
      · congr 1
        ext x
        simp only [K,GaussianEvents.constraints,Set.mem_ofPred_eq,Prod.forall]
        rfl)
  have hlow : Real.exp (-(∑ k : S,c k.val)-stateRate*(∑ j,q j)*n) ≤
      Real.exp (-(∑ k : S,c k.val*((2:ℝ)^k.val*n+1))) := by
    apply Real.exp_le_exp.mpr
    have heq : (∑ k : S,c k.val*((2:ℝ)^k.val*n+1)) =
        (∑ k : S,c k.val)+(∑ k : S,c k.val*(2:ℝ)^k.val)*n := by
      simp only [mul_add,mul_one,Finset.sum_add_distrib,← mul_assoc,← Finset.sum_mul]
      ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg n : (0:ℝ)≤n)]
  apply hlow.trans (hprob.trans _)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx t u
  rw [matrixMap_mul_apply]
  apply reconstruction_bound (hRt t) hq S (hS t) (matrixMap (evaluation r n u) x)
  intro k hk
  have hh := Set.mem_iInter.mp hx (⟨k,hk⟩ : S) (t,u)
  change ‖matrixMap (F ⟨k,hk⟩ t*evaluation r n u) x‖≤_ at hh
  rw [matrixMap_mul_apply] at hh
  exact hh

end EuclideanSteinitz.Filter

end

section

open Matrix
open scoped BigOperators
namespace GaussianAR
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pathMatrix (r : ι → ℝ) (n : ℕ) : Matrix (Fin (n+1)×ι) (Fin (n+1)×ι) ℝ :=
  fun i j => evaluation r n i.1 i.2 j

lemma pathMatrix_det (r : ι → ℝ) (n : ℕ) :
    (pathMatrix r n).det = (∏ i,Real.sqrt (1-(r i)^2))^n := by
  have htri : (pathMatrix r n).transpose.BlockTriangular (fun p => p.1) := by
    intro a b hab
    change (if b.2=a.2 then row (r b.2) b.1.val a.1.val else 0)=0
    split_ifs
    · exact row_support _ hab
    · rfl
  rw [← Matrix.det_transpose,htri.det_fintype]
  have hb (t : Fin (n+1)) : ((pathMatrix r n).transpose.toSquareBlock (fun p => p.1) t).det =
      ∏ i, row (r i) t.val t.val := by
    let e : ι ≃ {p : Fin (n+1)×ι // p.1=t} :=
      { toFun := fun i => ⟨(t,i),rfl⟩
        invFun := fun p => p.val.2
        left_inv := fun _ => rfl
        right_inv := fun p => by ext <;> simp [p.property] }
    rw [← Matrix.det_reindex_self e.symm]
    have he : Matrix.reindex e.symm e.symm
        ((pathMatrix r n).transpose.toSquareBlock (fun p => p.1) t) =
        diagonal (fun i => row (r i) t.val t.val) := by
      ext i j
      simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.toSquareBlock_def,
        Matrix.transpose_apply,pathMatrix,e,evaluation,Matrix.diagonal_apply]
      split_ifs with h <;> simp_all [eq_comm]
    rw [he,Matrix.det_diagonal]
  simp_rw [hb]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero,row,ite_true,Fin.val_succ,row_diag,Finset.prod_const_one,one_mul]
  simp

lemma pathMatrix_det_pos (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ) :
    0 < (pathMatrix r n).det := by
  rw [pathMatrix_det]
  apply pow_pos
  exact Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (by nlinarith [hr i,hr1 i])

lemma evaluation_apply (r : ι → ℝ) (n : ℕ) (t : Fin (n+1))
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (i : ι) :
    GaussianTail.matrixMap (evaluation r n t) x i =
      ∑ u : Fin (n+1),row (r i) t.val u.val*x (u,i) := by
  change (∑ u,evaluation r n t i u*x u)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  simp only [evaluation,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma pathMatrix_apply (r : ι → ℝ) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (t : Fin (n+1)) (i : ι) :
    GaussianTail.matrixMap (pathMatrix r n) x (t,i) =
      GaussianTail.matrixMap (evaluation r n t) x i := rfl

lemma path_initial (r : ι → ℝ) (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (i : ι) :
    GaussianTail.matrixMap (pathMatrix r n) x (0,i)=x (0,i) := by
  rw [pathMatrix_apply,evaluation_apply]
  simp only [Fin.val_zero,row,ite_mul,one_mul,zero_mul,Fin.val_eq_zero_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma path_step (r : ι → ℝ) (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1)×ι))
    (t : Fin n) (i : ι) :
    GaussianTail.matrixMap (pathMatrix r n) x (t.succ,i)=
      r i*GaussianTail.matrixMap (pathMatrix r n) x (t.castSucc,i)+
      Real.sqrt (1-(r i)^2)*x (t.succ,i) := by
  simp only [pathMatrix_apply,evaluation_apply,Fin.val_succ,Fin.val_castSucc,row,
    add_mul,ite_mul,zero_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  have he (u : Fin (n+1)) : (u.val=t.val+1) ↔ u=t.succ := by
    exact (show (u.val=t.succ.val) ↔ u=t.succ from Fin.ext_iff.symm)
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma pathMatrix_lin_det (r : ι → ℝ) (n : ℕ) :
    (Matrix.toEuclideanLin (pathMatrix r n)).det=(pathMatrix r n).det := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

noncomputable def pathEquiv (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ) :
    EuclideanSpace ℝ (Fin (n+1)×ι) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+1)×ι) :=
  (LinearMap.equivOfIsUnitDet (show IsUnit (Matrix.toEuclideanLin (pathMatrix r n)).det from by
    rw [pathMatrix_lin_det]
    exact isUnit_iff_ne_zero.mpr (pathMatrix_det_pos r hr hr1 n).ne')).toContinuousLinearEquiv

lemma pathEquiv_apply (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) :
    pathEquiv r hr hr1 n x = GaussianTail.matrixMap (pathMatrix r n) x := by
  simp only [pathEquiv,LinearEquiv.coe_toContinuousLinearEquiv',LinearMap.equivOfIsUnitDet_apply]
  rfl

lemma pathEquiv_symm_initial (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (i : ι) :
    (pathEquiv r hr hr1 n).symm x (0,i) = x (0,i) := by
  have hs := congrArg (fun x : EuclideanSpace ℝ (Fin (n+1)×ι) => x (0,i))
    ((pathEquiv r hr hr1 n).apply_symm_apply x)
  rw [pathEquiv_apply,path_initial] at hs
  exact hs

lemma pathEquiv_symm_step (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (t : Fin n) (i : ι) :
    (pathEquiv r hr hr1 n).symm x (t.succ,i) =
      (x (t.succ,i)-r i*x (t.castSucc,i))/Real.sqrt (1-(r i)^2) := by
  have hpos : 0 < Real.sqrt (1-(r i)^2) := Real.sqrt_pos.mpr (by nlinarith [hr i,hr1 i])
  have hs := path_step r n ((pathEquiv r hr hr1 n).symm x) t i
  simp only [← pathEquiv_apply r hr hr1,(pathEquiv r hr hr1 n).apply_symm_apply] at hs
  apply (eq_div_iff hpos.ne').mpr
  linarith

lemma pathEquiv_det (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ) :
    (pathEquiv r hr hr1 n).toContinuousLinearMap.det=(∏ i,Real.sqrt (1-(r i)^2))^n := by
  change (pathEquiv r hr hr1 n).toLinearEquiv.toLinearMap.det=_
  simp only [pathEquiv,LinearEquiv.toLinearEquiv_toContinuousLinearEquiv,
    LinearMap.coe_equivOfIsUnitDet,pathMatrix_lin_det,pathMatrix_det]

end GaussianAR

end

section

open ProbabilityTheory
namespace GaussianAR

lemma transition_scalar {r w : ℝ} (hr : 0<r) (hr1 : r<1) (hw : w=(1-r^2)/r)
    (hw0 : 0≤w) (x y : ℝ) :
    (Real.sqrt (1-r^2))⁻¹ * gaussianPDFReal 0 1 ((y-r*x)/Real.sqrt (1-r^2)) ≤
      (Real.sqrt r)⁻¹ * gaussianPDFReal 0 ⟨w,hw0⟩ (y-x) * Real.exp ((x^2-y^2)/4) := by
  have hs : 0 < 1-r^2 := by nlinarith
  have hsr := Real.sqrt_pos.mpr hs
  have hrr := Real.sqrt_pos.mpr hr
  have hwpos : 0<w := by rw [hw]; positivity
  have hsqr := Real.sq_sqrt hr.le
  have hsqs := Real.sq_sqrt hs.le
  have hp := Real.pi_pos
  have hconst : (Real.sqrt (1-r^2))⁻¹*(Real.sqrt (2*Real.pi))⁻¹ =
      (Real.sqrt r)⁻¹*(Real.sqrt (2*Real.pi*w))⁻¹ := by
    rw [← mul_inv,← mul_inv]
    congr 1
    rw [← Real.sqrt_mul hs.le,← Real.sqrt_mul hr.le]
    congr 1
    rw [hw]
    field_simp
  have hexp : -(((y-r*x)/Real.sqrt (1-r^2))^2)/2 ≤
      -((y-x)^2)/(2*w)+(x^2-y^2)/4 := by
    rw [div_pow,hsqs,hw]
    have he : -((y-r*x)^2/(1-r^2))/2 + ((y-x)^2)/(2*((1-r^2)/r))-(x^2-y^2)/4 =
        -((1-r)^2*(x^2+y^2))/(4*(1-r^2)) := by field_simp; ring
    have hn : 0 ≤ ((1-r)^2*(x^2+y^2))/(4*(1-r^2)) := by positivity
    simp only [neg_div] at he ⊢
    linarith
  unfold gaussianPDFReal
  simp only [sub_zero, NNReal.coe_one, mul_one]
  change (Real.sqrt (1-r^2))⁻¹*((Real.sqrt (2*Real.pi))⁻¹ *
      Real.exp (-((y-r*x)/Real.sqrt (1-r^2))^2/2)) ≤
    (Real.sqrt r)⁻¹*((Real.sqrt (2*Real.pi*w))⁻¹*Real.exp (-(y-x)^2/(2*w)))*
      Real.exp ((x^2-y^2)/4)
  calc
    _ = ((Real.sqrt (1-r^2))⁻¹*(Real.sqrt (2*Real.pi))⁻¹)*
      Real.exp (-((y-r*x)/Real.sqrt (1-r^2))^2/2) := by ring
    _ ≤ ((Real.sqrt (1-r^2))⁻¹*(Real.sqrt (2*Real.pi))⁻¹)*
      Real.exp (-(y-x)^2/(2*w)+(x^2-y^2)/4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [hconst,Real.exp_add]; ring

lemma reciprocal_rate {v : ℝ} (hv : 0<v) :
    let r := (1+v)⁻¹
    0<r ∧ r<1 ∧ v ≤ (1-r^2)/r ∧ (1-r^2)/r ≤ 2*v ∧ 1-r ≤ v ∧ -Real.log r ≤ v := by
  dsimp
  have hp : 0<1+v := by linarith
  have hr : 0<(1+v)⁻¹ := inv_pos.mpr hp
  have hr1 : (1+v)⁻¹<1 := (inv_lt_one₀ hp).mpr (by linarith)
  have he : (1-((1+v)⁻¹)^2)/(1+v)⁻¹ = v*(2+v)/(1+v) := by field_simp; ring
  refine ⟨hr,hr1,?_,?_,?_,?_⟩
  · rw [he]; apply (le_div_iff₀ hp).mpr; nlinarith
  · rw [he]; apply (div_le_iff₀ hp).mpr; nlinarith [sq_nonneg v]
  · apply (sub_le_iff_le_add).mpr
    have hh : 1 ≤ v+(1+v)⁻¹ := by
      apply (le_of_mul_le_mul_right ?_ hp)
      field_simp
      nlinarith [sq_nonneg v]
    linarith
  · rw [Real.log_inv,neg_neg]
    simpa using Real.log_le_sub_one_of_pos hp

end GaussianAR

end

end OAI
