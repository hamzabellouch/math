import OAI.Analysis.TracialSplitting.MatrixCoefficients

namespace OAI

noncomputable section

universe uD uI uJ uN uO

namespace CurrentMain

section

open Pureness

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceOneNorm_covariance_l2 (τ : TracialState D) (a b : D) :
    traceOneNorm τ (b * star b - a * star a) ≤
      (traceTwoNorm τ a + traceTwoNorm τ b) * traceTwoNorm τ (b-a) := by
  apply traceOneNorm_le_of_pairing τ ((selfAdjoint_covariance b).sub
    (selfAdjoint_covariance a))
  intro s _ hs
  have he : b * star b - a * star a =
      (b-a) * star b + a * star (b-a) := by
    rw [star_sub]
    noncomm_ring
  rw [he,mul_add,map_add,Complex.add_re]
  have hsbound (v : D) : traceTwoNorm τ (s*v) ≤ traceTwoNorm τ v := by
    exact (traceTwoNorm_mul_left τ s v).trans
      ((mul_le_mul_of_nonneg_right hs (traceTwoNorm_nonneg τ v)).trans_eq (one_mul _))
  have hfirst : (τ.functional (s*((b-a)*star b))).re ≤
      traceTwoNorm τ (b-a) * traceTwoNorm τ b := by
    apply (Complex.re_le_norm _).trans
    rw [← mul_assoc]
    exact (trace_norm_mul_le τ _ _).trans (by
      rw [traceTwoNorm_star]
      exact mul_le_mul_of_nonneg_right (hsbound _) (traceTwoNorm_nonneg τ _))
  have hsecond : (τ.functional (s*(a*star (b-a)))).re ≤
      traceTwoNorm τ a * traceTwoNorm τ (b-a) := by
    apply (Complex.re_le_norm _).trans
    rw [← mul_assoc]
    exact (trace_norm_mul_le τ _ _).trans (by
      rw [traceTwoNorm_star]
      exact mul_le_mul_of_nonneg_right (hsbound _) (traceTwoNorm_nonneg τ _))
  nlinarith

variable {I : Type uI} [Fintype I]

lemma traceOneNorm_covariance_sum_l2 (τ : TracialState D) (a b : I → D) :
    traceOneNorm τ ((∑ i, b i * star (b i)) - (∑ i, a i * star (a i))) ^ 2 ≤
      2 * ((∑ i, traceTwoNorm τ (a i)^2) + (∑ i, traceTwoNorm τ (b i)^2)) *
        (∑ i, traceTwoNorm τ (b i-a i)^2) := by
  classical
  let f (i : I) := (traceTwoNorm τ (a i) + traceTwoNorm τ (b i)) *
    traceTwoNorm τ (b i-a i)
  have hf : ∀ i, 0 ≤ f i := fun i => mul_nonneg
    (add_nonneg (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _))
    (traceTwoNorm_nonneg τ _)
  have hle : traceOneNorm τ ((∑ i, b i * star (b i)) - (∑ i, a i * star (a i))) ≤
      ∑ i, f i := by
    rw [← Finset.sum_sub_distrib]
    exact (traceOneNorm_sum_le τ _ (fun i =>
      (selfAdjoint_covariance _).sub (selfAdjoint_covariance _))).trans
      (Finset.sum_le_sum fun i _ => traceOneNorm_covariance_l2 τ (a i) (b i))
  have hCS : (∑ i, f i)^2 ≤
      (∑ i, 2 * (traceTwoNorm τ (a i)^2 + traceTwoNorm τ (b i)^2)) *
        (∑ i, traceTwoNorm τ (b i-a i)^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; positivity
    · intro i _; positivity
    · intro i _
      dsimp [f]
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [sq_nonneg (traceTwoNorm τ (a i)-traceTwoNorm τ (b i))]
  apply (sq_le_sq₀ (traceOneNorm_nonneg τ _) (Finset.sum_nonneg fun i _ => hf i)).mpr
    hle |>.trans
  simpa only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc] using hCS

lemma global_partition_covariance_l2 {J : Type uJ} [Fintype J]
    (τ : TracialState D) (q : J → D) (hq : ∀ j, IsStarProjection (q j))
    (hsum : ∑ j, q j = 1) (a b : I → D) :
    (∑ j, traceOneNorm τ ((∑ i, star (b i) * q j * b i) -
      ∑ i, star (a i) * q j * a i)) ^ 2 ≤
      2 * ((∑ i, traceTwoNorm τ (a i)^2) + (∑ i, traceTwoNorm τ (b i)^2)) *
        (∑ i, traceTwoNorm τ (b i-a i)^2) := by
  classical
  let c (j : J) (i : I) := star (a i)*q j
  let d (j : J) (i : I) := star (b i)*q j
  have hc (j : J) (i : I) : c j i * star (c j i) = star (a i)*q j*a i := by
    dsimp [c]
    rw [star_mul,star_star,(hq j).isSelfAdjoint.star_eq]
    simp only [mul_assoc,← mul_assoc (q j) (q j) (a i),(hq j).isIdempotentElem.eq]
  have hd (j : J) (i : I) : d j i * star (d j i) = star (b i)*q j*b i := by
    dsimp [d]
    rw [star_mul,star_star,(hq j).isSelfAdjoint.star_eq]
    simp only [mul_assoc,← mul_assoc (q j) (q j) (b i),(hq j).isIdempotentElem.eq]
  have he (j : J) :
      traceOneNorm τ ((∑ i, star (b i)*q j*b i) - ∑ i, star (a i)*q j*a i)^2 ≤
      (2 * ((∑ i, traceTwoNorm τ (c j i)^2) + ∑ i, traceTwoNorm τ (d j i)^2)) *
        (∑ i, traceTwoNorm τ (d j i-c j i)^2) := by
    simpa only [hc,hd,← mul_assoc] using traceOneNorm_covariance_sum_l2 τ (c j) (d j)
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun j => traceOneNorm τ ((∑ i, star (b i)*q j*b i) - ∑ i, star (a i)*q j*a i))
    (f := fun j => 2*((∑ i, traceTwoNorm τ (c j i)^2)+∑ i, traceTwoNorm τ (d j i)^2))
    (g := fun j => ∑ i, traceTwoNorm τ (d j i-c j i)^2)
    (fun j _ => by positivity) (fun j _ => by positivity) (fun j _ => he j)
  have hca : (∑ j, ∑ i, traceTwoNorm τ (c j i)^2) = ∑ i, traceTwoNorm τ (a i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [c,traceTwoNorm_star] using traceTwoNorm_sq_partition_right τ q hq hsum (star (a i))
  have hdb : (∑ j, ∑ i, traceTwoNorm τ (d j i)^2) = ∑ i, traceTwoNorm τ (b i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [d,traceTwoNorm_star] using traceTwoNorm_sq_partition_right τ q hq hsum (star (b i))
  have hdc : (∑ j, ∑ i, traceTwoNorm τ (d j i-c j i)^2) =
      ∑ i, traceTwoNorm τ (b i-a i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c,d,← sub_mul,← star_sub]
    rw [traceTwoNorm_sq_partition_right τ q hq hsum,traceTwoNorm_star]
  have hf : (∑ j, 2*((∑ i, traceTwoNorm τ (c j i)^2)+∑ i, traceTwoNorm τ (d j i)^2)) =
      2*((∑ i, traceTwoNorm τ (a i)^2)+∑ i, traceTwoNorm τ (b i)^2) := by
    rw [← Finset.mul_sum,Finset.sum_add_distrib,hca,hdb]
  simpa only [hf,hdc] using hCS

end

section

open scoped ComplexOrder

section ChoiKraus

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {N : Type uN} [Fintype N] [DecidableEq N]

lemma choi_sqrt_factorization (Q : CStarMatrix N N D) (hQ : 0 ≤ Q) :
    ∃ V : CStarMatrix N N D, IsSelfAdjoint V ∧ star V * V = Q := by
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (CStarMatrix N N D) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix N N D) :=
    CStarAlgebra.instNonnegSpectrumClass
  refine ⟨CFC.sqrt Q, (CFC.sqrt_nonneg Q).isSelfAdjoint, ?_⟩
  rw [((CFC.sqrt_nonneg Q).isSelfAdjoint : IsSelfAdjoint (CFC.sqrt Q)).star_eq]
  exact CFC.sqrt_mul_sqrt_self Q hQ

lemma choi_bistochastic_family (Q : CStarMatrix N N D) (hQ : 0 ≤ Q)
    (hmass : ∑ i, Q i i = 1) :
    ∃ a : (N × N) → D,
      (∑ i, star (a i) * a i = 1) ∧
      (∑ i, a i * star (a i) = 1) ∧
      ∀ i j, Q i j = ∑ k, star (a (k,i)) * a (k,j) := by
  classical
  obtain ⟨V,hV,hVV⟩ := choi_sqrt_factorization Q hQ
  have hentry (i j : N) : Q i j = ∑ k, star (V k i) * V k j := by
    rw [← hVV]
    simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply]
  refine ⟨fun i => V i.1 i.2, ?_, ?_, hentry⟩
  · rw [Fintype.sum_prod_type,Finset.sum_comm]
    simpa only [← hentry] using hmass
  · rw [Fintype.sum_prod_type]
    have hstar (i j : N) : star (V i j) = V j i :=
      CStarMatrix.star_apply_of_isSelfAdjoint hV
    simp_rw [hstar]
    have hsum (i : N) : (∑ j, V i j * V j i) = Q i i := by
      rw [hentry]
      simp only [hstar]
    simpa only [hsum] using hmass

open scoped CStarAlgebra

def scalarMatrixUnit (i j : N) : CStarMatrix N N ℂ :=
  CStarMatrix.ofMatrix (Matrix.single i j 1)

omit [Fintype N] in
@[simp] lemma star_scalarMatrixUnit (i j : N) :
    star (scalarMatrixUnit i j) = scalarMatrixUnit j i := by
  change Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) = Matrix.single j i 1
  simp

@[simp] lemma scalarMatrixUnit_mul (i j k : N) :
    scalarMatrixUnit i j * scalarMatrixUnit j k = scalarMatrixUnit i k := by
  apply CStarMatrix.ext
  intro a b
  rw [CStarMatrix.mul_apply]
  change (∑ l : N, Matrix.single i j (1 : ℂ) a l *
    Matrix.single j k (1 : ℂ) l b) = Matrix.single i k (1 : ℂ) a b
  by_cases hia : i = a <;> by_cases hkb : k = b <;> simp [Matrix.single_apply,hia,hkb]

lemma sum_scalarMatrixUnit_diag : (∑ i : N, scalarMatrixUnit i i) = 1 := by
  ext i j
  change (∑ k : N, Matrix.single k k (1 : ℂ)) i j = if i = j then 1 else 0
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

lemma matrixUnits_positive [Nonempty N] :
    0 ≤ (CStarMatrix.ofMatrix (fun i j : N => scalarMatrixUnit i j)) := by
  let k : N := Classical.choice inferInstance
  let R : CStarMatrix N N (CStarMatrix N N ℂ) :=
    CStarMatrix.ofMatrix (fun i j => if i = k then scalarMatrixUnit k j else 0)
  have hr : star R * R = CStarMatrix.ofMatrix (fun i j : N => scalarMatrixUnit i j) := by
    apply CStarMatrix.ext
    intro i j
    rw [CStarMatrix.mul_apply]
    change (∑ l : N, star (if l = k then scalarMatrixUnit k i else 0) *
      (if l = k then scalarMatrixUnit k j else 0)) = scalarMatrixUnit i j
    simp
  rw [← hr]
  exact star_mul_self_nonneg R

lemma cp_choi_positive [Nonempty N] (φ : CStarMatrix N N ℂ →CP D) :
    0 ≤ CStarMatrix.ofMatrix (fun i j : N => φ (scalarMatrixUnit i j)) := by
  exact φ.map_cstarMatrix_nonneg _ matrixUnits_positive

lemma ucp_choi_bistochastic [Nonempty N] (φ : CStarMatrix N N ℂ →CP D)
    (hφ : φ 1 = 1) :
    ∃ a : (N × N) → D,
      (∑ i, star (a i) * a i = 1) ∧ (∑ i, a i * star (a i) = 1) ∧
      ∀ i j, φ (scalarMatrixUnit i j) = ∑ k, star (a (k,i)) * a (k,j) := by
  apply choi_bistochastic_family _ (cp_choi_positive φ)
  change (∑ i : N, φ (scalarMatrixUnit i i)) = 1
  rw [← map_sum,sum_scalarMatrixUnit_diag,hφ]

lemma scalarMatrixUnit_expansion (T : CStarMatrix N N ℂ) :
    (∑ i, ∑ j, T i j • scalarMatrixUnit i j) = T := by
  apply CStarMatrix.ext
  intro k l
  change (∑ i, ∑ j, T i j • Matrix.single i j (1 : ℂ)) k l = T k l
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.single_apply,smul_eq_mul]
  simp [ite_and]

omit [PartialOrder D] [StarOrderedRing D] in
lemma linearMap_choi_expansion (φ : CStarMatrix N N ℂ →ₗ[ℂ] D)
    (T : CStarMatrix N N ℂ) :
    φ T = ∑ i, ∑ j, T i j • φ (scalarMatrixUnit i j) := by
  conv_lhs => rw [← scalarMatrixUnit_expansion T]
  simp only [map_sum,map_smul]

lemma scalar_contraction_dilation (T : CStarMatrix N N ℂ) (hT : ‖T‖ ≤ 1) :
    ∃ S : CStarMatrix N N ℂ, star T * T + star S * S = 1 := by
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (CStarMatrix N N ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix N N ℂ) :=
    CStarAlgebra.instNonnegSpectrumClass
  have hTT : star T*T ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star T*T) (star_mul_self_nonneg T)).mp
    calc
      ‖star T*T‖ = ‖T‖*‖T‖ := CStarRing.norm_star_mul_self (x := T)
      _ ≤ 1 := by nlinarith [norm_nonneg T]
  obtain ⟨S,_,hS⟩ := choi_sqrt_factorization (1-star T*T) (sub_nonneg.mpr hTT)
  exact ⟨S,by rw [hS]; abel⟩

end ChoiKraus

section ScalarMix

variable {D : Type uD} [CStarAlgebra D]

variable {I : Type uI} {O : Type uO} [Fintype I] [Fintype O] [DecidableEq I]

def scalarMix (R : Matrix O I ℂ) (a : I → D) (o : O) : D :=
  ∑ i, R o i • a i

omit [DecidableEq I] in
lemma scalarMix_covariance (R : Matrix O I ℂ) (a : I → D) (q : D) :
    (∑ o, star (scalarMix R a o) * q * scalarMix R a o) =
      ∑ i, ∑ j, (∑ o, star (R o i) * R o j) • (star (a i)*q*a j) := by
  classical
  have he (o : O) : star (scalarMix R a o)*q*scalarMix R a o =
      ∑ i, ∑ j, (star (R o i)*R o j) • (star (a i)*q*a j) := by
    simp only [scalarMix,star_sum,star_smul,Finset.sum_mul,Finset.mul_sum,
      smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  simp_rw [he,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

lemma scalarMix_covariance_of_isometry (R : Matrix O I ℂ) (a : I → D)
    (hR : ∀ i j, (∑ o, star (R o i)*R o j) = if i=j then 1 else 0) (q : D) :
    (∑ o, star (scalarMix R a o)*q*scalarMix R a o) = ∑ i, star (a i)*q*a i := by
  rw [scalarMix_covariance]
  simp only [hR,ite_smul,one_smul,zero_smul]
  simp

lemma scalarMix_dilation_covariance {N : Type uN} [Fintype N] [DecidableEq N]
    (T S : CStarMatrix N N ℂ) (hTS : star T*T + star S*S = 1)
    (a : N → D) (q : D) :
    (∑ i, star (scalarMix (CStarMatrix.ofMatrix.symm T) a i)*q*scalarMix (CStarMatrix.ofMatrix.symm T) a i) +
      (∑ i, star (scalarMix (CStarMatrix.ofMatrix.symm S) a i)*q*scalarMix (CStarMatrix.ofMatrix.symm S) a i) =
        ∑ i, star (a i)*q*a i := by
  classical
  have hentry (i j : N) :
      (∑ k, star (T k i)*T k j) + (∑ k, star (S k i)*S k j) =
      if i=j then 1 else 0 := by
    have h := congrArg (fun M : CStarMatrix N N ℂ => M i j) hTS
    simpa only [CStarMatrix.add_apply,CStarMatrix.mul_apply,CStarMatrix.star_apply,
      CStarMatrix.one_apply] using h
  rw [scalarMix_covariance,scalarMix_covariance,← Finset.sum_add_distrib]
  simp only [CStarMatrix.ofMatrix_symm_apply]
  simp_rw [← Finset.sum_add_distrib,← add_smul,hentry,ite_smul,one_smul,zero_smul]
  simp

end ScalarMix

variable {D : Type uD} [CStarAlgebra D]

variable {N : Type uN} [Fintype N] [DecidableEq N]

lemma choi_evaluation (φ : CStarMatrix N N ℂ →ₗ[ℂ] D) (a : (N × N) → D)
    (ha : ∀ i j, φ (scalarMatrixUnit i j) = ∑ k, star (a (k,i))*a (k,j))
    (T : CStarMatrix N N ℂ) :
    φ T = ∑ k, ∑ i, star (a (k,i))*scalarMix (CStarMatrix.ofMatrix.symm T) (fun j => a (k,j)) i := by
  rw [linearMap_choi_expansion]
  simp only [ha,Finset.smul_sum,scalarMix,Finset.mul_sum,mul_smul_comm,
    CStarMatrix.ofMatrix_symm_apply]
  trans ∑ i, ∑ k, ∑ j, T i j • (star (a (k,i))*a (k,j))
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

end

open Pureness

open scoped ComplexOrder CStarAlgebra

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {N : Type uN} [Fintype N] [DecidableEq N]

omit [PartialOrder D] [StarOrderedRing D] in
lemma choi_coupling (φ : CStarMatrix N N ℂ →ₗ[ℂ] D) (a : (N × N) → D)
    (ha : ∀ i j, φ (scalarMatrixUnit i j) = ∑ k, star (a (k,i))*a (k,j))
    (ha1 : ∑ i, star (a i)*a i = 1)
    (T : CStarMatrix N N ℂ) (hT : ‖T‖ ≤ 1) (x : unitary D) :
    ∃ b v : ((N × N) ⊕ (N × N)) → D,
      (∀ q, (∑ i, star (b i)*q*b i) = ∑ i, star (a i)*q*a i) ∧
      (∀ q, (∑ i, star (v i)*q*v i) =
        star (x : D)*(∑ i, star (a i)*q*a i)*(x : D)) ∧
      (∑ i, star (b i)*b i = 1) ∧ (∑ i, star (v i)*v i = 1) ∧
      (∑ i, star (b i-v i)*(b i-v i)) =
        2 - star (φ T)*(x : D) - star (x : D)*φ T := by
  classical
  obtain ⟨S,hTS⟩ := scalar_contraction_dilation T hT
  let b : ((N × N) ⊕ (N × N)) → D := Sum.elim
    (fun z => scalarMix (CStarMatrix.ofMatrix.symm T) (fun j => a (z.1,j)) z.2)
    (fun z => scalarMix (CStarMatrix.ofMatrix.symm S) (fun j => a (z.1,j)) z.2)
  let v : ((N × N) ⊕ (N × N)) → D := Sum.elim (fun z => a z*(x : D)) (fun _ => 0)
  have hb (q : D) : (∑ i, star (b i)*q*b i) = ∑ i, star (a i)*q*a i := by
    simp only [b,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => scalarMix_dilation_covariance T S hTS
      (fun i => a (k,i)) q)
  have hv (q : D) : (∑ i, star (v i)*q*v i) =
      star (x : D)*(∑ i, star (a i)*q*a i)*(x : D) := by
    simp only [v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,star_zero,zero_mul,
      Finset.sum_const_zero,add_zero,star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  have hb1 : (∑ i, star (b i)*b i) = 1 := by
    simpa only [mul_one] using (hb 1).trans (by simpa only [mul_one] using ha1)
  have hv1 : (∑ i, star (v i)*v i) = 1 := by
    simpa only [mul_one,ha1,Unitary.coe_star_mul_self] using hv 1
  have hcross : (∑ i, star (v i)*b i) = star (x : D)*φ T := by
    rw [choi_evaluation φ a ha T]
    simp only [v,b,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,star_zero,zero_mul,
      Finset.sum_const_zero,add_zero,star_mul,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hcross' : (∑ i, star (b i)*v i) = star (φ T)*(x : D) := by
    have h := congrArg star hcross
    simpa only [star_sum,star_mul,star_star] using h
  refine ⟨b,v,hb,hv,hb1,hv1,?_⟩
  have he (i : ((N × N) ⊕ (N × N))) :
      star (b i-v i)*(b i-v i) =
        star (b i)*b i + star (v i)*v i - star (b i)*v i - star (v i)*b i := by
    rw [star_sub]
    noncomm_ring
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,hb1,hv1,hcross,hcross']
  norm_num

lemma trace_choi_coupling_error {I : Type uI} [Fintype I]
    (τ : TracialState D) (b v : I → D) (z : D) (x : unitary D)
    (herr : (∑ i, star (b i-v i)*(b i-v i)) =
      2 - star z*(x : D) - star (x : D)*z) {ε : ℝ}
    (hε : ‖z-(x : D)‖ ≤ ε) :
    (∑ i, traceTwoNorm τ (b i-v i)^2) ≤ 2*ε := by
  let y : D := star (x : D)*((x : D)-z)
  have hy : ‖y‖ ≤ ε := by
    dsimp [y]
    change ‖((star x : unitary D) : D) * ((x : D)-z)‖ ≤ ε
    rw [CStarRing.norm_coe_unitary_mul (star x),norm_sub_rev]
    exact hε
  have he : 2 - star z*(x : D) - star (x : D)*z = y + star y := by
    dsimp [y]
    simp only [star_mul,star_sub,star_star,mul_sub,Unitary.coe_star_mul_self,star_one]
    rw [show (2 : D) = 1+1 by norm_num]
    abel
  calc
    (∑ i, traceTwoNorm τ (b i-v i)^2) =
        (τ.functional (∑ i, star (b i-v i)*(b i-v i))).re := by
      simp only [traceTwoNorm_sq,map_sum,Complex.re_sum]
    _ = (τ.functional (y+star y)).re := by rw [herr,he]
    _ ≤ ‖y+star y‖ := (Complex.re_le_norm _).trans (trace_norm_le_norm τ _)
    _ ≤ ‖y‖ + ‖star y‖ := norm_add_le _ _
    _ ≤ 2*ε := by rw [norm_star]; linarith

lemma choi_global_partition_bound {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (τ : TracialState D) (b v : I → D) (z : D) (x : unitary D)
    (hb : ∑ i, star (b i)*b i = 1) (hv : ∑ i, star (v i)*v i = 1)
    (herr : (∑ i, star (b i-v i)*(b i-v i)) =
      2 - star z*(x : D) - star (x : D)*z) {ε : ℝ}
    (hε : ‖z-(x : D)‖ ≤ ε) (q : J → D)
    (hq : ∀ j, IsStarProjection (q j)) (hsum : ∑ j, q j = 1) :
    (∑ j, traceOneNorm τ ((∑ i, star (b i)*q j*b i) -
      ∑ i, star (v i)*q j*v i))^2 ≤ 8*ε := by
  have hs (c : I → D) (hc : ∑ i, star (c i)*c i = 1) :
      (∑ i, traceTwoNorm τ (c i)^2) = 1 := by
    simp only [traceTwoNorm_sq,← Complex.re_sum,← map_sum,hc,τ.normalized,Complex.one_re]
  have he := trace_choi_coupling_error τ b v z x herr hε
  have h := global_partition_covariance_l2 τ q hq hsum v b
  rw [hs b hb,hs v hv] at h
  nlinarith

lemma ucp_global_partition_averaging [Nonempty N]
    (φ : CStarMatrix N N ℂ →CP D) (hφ : φ 1 = 1) :
    ∃ a : (N × N) → D,
      (∑ i, star (a i)*a i = 1) ∧ (∑ i, a i*star (a i) = 1) ∧
      ∀ (T : CStarMatrix N N ℂ), ‖T‖ ≤ 1 → ∀ (x : unitary D) (ε : ℝ),
      ‖φ T-(x : D)‖ ≤ ε → ∀ (J : Type) [Fintype J] (q : J → D),
      (∀ j, IsStarProjection (q j)) → (∑ j, q j = 1) →
      ∀ τ : TracialState D,
      (∑ j, traceOneNorm τ ((∑ i, star (a i)*q j*a i) -
        star (x : D)*(∑ i, star (a i)*q j*a i)*(x : D)))^2 ≤ 8*ε := by
  obtain ⟨a,ha1,ha2,ha⟩ := ucp_choi_bistochastic φ hφ
  refine ⟨a,ha1,ha2,?_⟩
  intro T hT x ε he J _ q hq hsum τ
  obtain ⟨b,v,hb,hv,hb1,hv1,herr⟩ := choi_coupling φ.toLinearMap a ha ha1 T hT x
  simpa only [hb,hv] using
    choi_global_partition_bound τ b v (φ T) x hb1 hv1 herr he q hq hsum

lemma trace_choi_coupling_pairing {I : Type uI} [Fintype I]
    (τ : TracialState D) (b v : I → D) (z : D) (x : unitary D)
    (herr : (∑ i, star (b i-v i)*(b i-v i)) =
      2 - star z*(x : D) - star (x : D)*z) :
    (∑ i, traceTwoNorm τ (b i-v i)^2) =
      2*(τ.functional (star (x : D)*((x : D)-z))).re := by
  let y : D := star (x : D)*((x : D)-z)
  have he : 2 - star z*(x : D) - star (x : D)*z = y+star y := by
    dsimp [y]
    simp only [star_mul,star_sub,star_star,mul_sub,Unitary.coe_star_mul_self,star_one]
    rw [show (2 : D) = 1+1 by norm_num]
    abel
  rw [show (∑ i, traceTwoNorm τ (b i-v i)^2) =
      (τ.functional (∑ i, star (b i-v i)*(b i-v i))).re by
        simp only [traceTwoNorm_sq,map_sum,Complex.re_sum],herr,he]
  simp only [map_add,map_star,Complex.add_re,Complex.star_def,Complex.conj_re]
  ring

lemma choi_global_partition_pairing {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (τ : TracialState D) (b v : I → D) (z : D) (x : unitary D)
    (hb : ∑ i, star (b i)*b i = 1) (hv : ∑ i, star (v i)*v i = 1)
    (herr : (∑ i, star (b i-v i)*(b i-v i)) =
      2 - star z*(x : D) - star (x : D)*z)
    (q : J → D) (hq : ∀ j, IsStarProjection (q j)) (hsum : ∑ j, q j = 1) :
    (∑ j, traceOneNorm τ ((∑ i, star (b i)*q j*b i) -
      ∑ i, star (v i)*q j*v i))^2 ≤
        8*(τ.functional (star (x : D)*((x : D)-z))).re := by
  have hs (c : I → D) (hc : ∑ i, star (c i)*c i = 1) :
      (∑ i, traceTwoNorm τ (c i)^2) = 1 := by
    simp only [traceTwoNorm_sq,← Complex.re_sum,← map_sum,hc,τ.normalized,Complex.one_re]
  have h := global_partition_covariance_l2 τ q hq hsum v b
  rw [hs b hb,hs v hv,trace_choi_coupling_pairing τ b v z x herr] at h
  nlinarith

lemma normalized_choi_global_averaging
    (φ : CStarMatrix N N ℂ →ₗ[ℂ] D)
    (hQ : 0 ≤ CStarMatrix.ofMatrix (fun i j => φ (scalarMatrixUnit i j)))
    (hφ : φ 1 = 1) :
    ∃ a : (N × N) → D,
      (∑ i, star (a i)*a i = 1) ∧ (∑ i, a i*star (a i) = 1) ∧
      ∀ (T : CStarMatrix N N ℂ), ‖T‖ ≤ 1 → ∀ (x : unitary D),
      ∀ (J : Type) [Fintype J] (q : J → D),
      (∀ j, IsStarProjection (q j)) → (∑ j, q j = 1) →
      ∀ τ : TracialState D,
      (∑ j, traceOneNorm τ ((∑ i, star (a i)*q j*a i) -
        star (x : D)*(∑ i, star (a i)*q j*a i)*(x : D)))^2 ≤
          8*(τ.functional (star (x : D)*((x : D)-φ T))).re := by
  have hmass : ∑ i : N, (CStarMatrix.ofMatrix (fun i j => φ (scalarMatrixUnit i j))) i i = 1 := by
    change (∑ i, φ (scalarMatrixUnit i i)) = 1
    rw [← map_sum,sum_scalarMatrixUnit_diag,hφ]
  obtain ⟨a,ha1,ha2,ha⟩ := choi_bistochastic_family _ hQ hmass
  refine ⟨a,ha1,ha2,?_⟩
  intro T hT x J _ q hq hsum τ
  obtain ⟨b,v,hb,hv,hb1,hv1,herr⟩ := choi_coupling φ a ha ha1 T hT x
  simpa only [hb,hv] using
    choi_global_partition_pairing τ b v (φ T) x hb1 hv1 herr q hq hsum

end CurrentMain

end

end OAI
