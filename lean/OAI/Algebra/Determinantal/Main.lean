import OAI.Algebra.Determinantal.ConductorDimension
import OAI.Algebra.Determinantal.InitialForm

namespace OAI

namespace PermanentBorder.SpectralPlane
open Polynomial MvPolynomial Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def slope (θ : ι → K) : Matrix ι ι (MvPolynomial (Fin 2) K) :=
  Matrix.diagonal (fun i => BinaryLeading.linear (θ i))
noncomputable def matrix (θ : ι → K) (A : Matrix ι ι K) : Matrix ι ι (MvPolynomial (Fin 2) K) :=
  slope θ + A.map MvPolynomial.C
noncomputable def equation (θ : ι → K) (A : Matrix ι ι K) : MvPolynomial (Fin 2) K :=
  (matrix θ A).det

lemma scale_C (c : K) : PlaneScaling.scale (MvPolynomial.C c : MvPolynomial (Fin 2) K) =
    Polynomial.C (MvPolynomial.C c) := by
  simp only [PlaneScaling.scale,MvPolynomial.aeval_C]
  rfl

lemma scale_linear (t : K) : PlaneScaling.scale (BinaryLeading.linear t) =
    Polynomial.C (BinaryLeading.linear t)*Polynomial.X := by
  simp [PlaneScaling.scale,BinaryLeading.linear]
  ring

omit [Fintype ι] in
lemma scale_matrix (θ : ι → K) (A : Matrix ι ι K) :
    (matrix θ A).map PlaneScaling.scale =
      (Polynomial.X : (MvPolynomial (Fin 2) K)[X]) • (slope θ).map Polynomial.C +
        (A.map MvPolynomial.C).map Polynomial.C := by
  apply Matrix.ext
  intro i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.map_apply,matrix,slope,Matrix.add_apply,
      Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,map_add,scale_linear,scale_C]
    change Polynomial.C (BinaryLeading.linear (θ i))*Polynomial.X +
      Polynomial.C (MvPolynomial.C (A i i)) =
      Polynomial.X*Polynomial.C (BinaryLeading.linear (θ i)) +
        Polynomial.C (MvPolynomial.C (A i i))
    rw [mul_comm (Polynomial.C _) Polynomial.X]
  · simp only [Matrix.map_apply,matrix,slope,Matrix.add_apply,
      Matrix.diagonal_apply_ne _ h,Matrix.smul_apply,smul_eq_mul,map_zero,zero_add,mul_zero]
    exact scale_C _

lemma totalDegree_equation (θ : ι → K) (A : Matrix ι ι K) :
    (equation θ A).totalDegree ≤ Fintype.card ι := by
  apply PlaneScaling.degree_le_of_scale
  have hmap := RingHom.map_det PlaneScaling.scale.toRingHom (matrix θ A)
  change PlaneScaling.scale (equation θ A) = ((matrix θ A).map PlaneScaling.scale).det at hmap
  rw [hmap,scale_matrix]
  exact Polynomial.natDegree_det_X_add_C_le _ _

lemma leading_equation (θ : ι → K) (A : Matrix ι ι K) :
    homogeneousComponent (Fintype.card ι) (equation θ A) = ∏ i, BinaryLeading.linear (θ i) := by
  have hmap := RingHom.map_det PlaneScaling.scale.toRingHom (matrix θ A)
  change PlaneScaling.scale (equation θ A) = ((matrix θ A).map PlaneScaling.scale).det at hmap
  rw [← PlaneScaling.coeff_scale,hmap,scale_matrix,Polynomial.coeff_det_X_add_C_card]
  exact Matrix.det_diagonal

lemma to_charpoly (θ : ι → K) (A : Matrix ι ι K) :
    PlaneBivariate.toBivariate K (equation θ A) =
      (-((Polynomial.X : K[X]) • (Matrix.diagonal θ).map Polynomial.C +
        A.map Polynomial.C)).charpoly := by
  have hmap := RingHom.map_det (PlaneBivariate.toBivariate K).toRingHom (matrix θ A)
  change PlaneBivariate.toBivariate K (equation θ A) =
    ((matrix θ A).map (PlaneBivariate.toBivariate K)).det at hmap
  rw [hmap,Matrix.charpoly]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases h : i=j
  · subst j
    simp [matrix,slope,BinaryLeading.linear,Matrix.charmatrix]
    ring
  · simp [matrix,slope,BinaryLeading.linear,Matrix.charmatrix,h]

omit [DecidableEq ι] in
lemma homogeneous_leading (θ : ι → K) :
    (∏ i, BinaryLeading.linear (θ i)).IsHomogeneous (Fintype.card ι) := by
  classical
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => BinaryLeading.linear (θ i))
      (fun _ : ι => 1) (fun i _ => (isHomogeneous_X K 1).add
        ((isHomogeneous_X K 0).C_mul (θ i)))

omit [DecidableEq ι] in
lemma map_leading {L : Type*} [Field L] [Algebra K L] (θ : ι → K) :
    (∏ i, BinaryLeading.linear (θ i)).map (algebraMap K L) =
      ∏ i, BinaryLeading.linear (algebraMap K L (θ i)) := by
  simp [BinaryLeading.linear]

end PermanentBorder.SpectralPlane

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers SpectralPlane FrobeniusPlane CurveFamily
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma curveField_le_of_inField (E : IntermediateField K L) (f : Plane L)
    (hf : CurveFamily.InField E f) :
    curveCoefficientField (K := K) (PlaneBivariate.toBivariate L f) ≤ E := by
  obtain ⟨f₀,hf₀⟩ := CurveFamily.inField_lift E hf
  have hb : Bivariate.InField E (PlaneBivariate.toBivariate L f) := by
    apply (Bivariate.inField_iff_lifts E _).mpr
    refine ⟨PlaneBivariate.toBivariate E f₀,?_⟩
    rw [← hf₀]
    change (PlaneBivariate.toBivariate E f₀).map (Polynomial.mapRingHom (algebraMap E L)) =
      PlaneBivariate.toBivariate L (MvPolynomial.map (algebraMap E L) f₀)
    exact (PlaneBivariate.map_to E f₀).symm
  apply IntermediateField.adjoin_le_iff.mpr
  rintro c ⟨⟨i,j⟩,rfl⟩
  exact hb i j

lemma to_pencil_det {k : ℕ} (θ : Fin (k+1) → L)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) :
    PlaneBivariate.toBivariate L (SpectralPlane.equation θ A) =
      (pencilMatrix (pencilBase θ A)).det := by
  rw [SpectralPlane.to_charpoly,Matrix.charpoly]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i=j <;> simp [Matrix.charmatrix,pencilMatrix,pencilBase,Matrix.scalar_apply,hij]
  ring

variable [CharP K 2] [CharP L 2] [PerfectRing K 2] [Infinite K] [IsAlgClosed L]

theorem spectral_effective_bound {k : ℕ} (hk : 4 ≤ k+1)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) L) (T : ℕ)
    (hT : (T : ℕ∞) ≤ normalizationDefect (fun i => algebraMap K L (θ i)) A) :
    ∃ n : ℕ, Algebra.trdeg K (curveCoefficientField (K := K)
      (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det) ≤ (n : Cardinal) ∧
      18*n+T ≤ 9*((k+1)*(k+2)) := by
  let θL : Fin (k+1) → L := fun i => algebraMap K L (θ i)
  have hθL : Function.Injective θL := (algebraMap K L).injective.comp hθ
  let f := SpectralPlane.equation θL A
  obtain ⟨a,b,c,d,he⟩ := exists_squareForm f
  have hdeg : (squareForm a b c d).totalDegree ≤ k+1 := by
    rw [← he]
    simpa only [f,Fintype.card_fin] using SpectralPlane.totalDegree_equation θL A
  have hlead : homogeneousComponent (k+1) (squareForm a b c d) =
      ∏ i, BinaryLeading.linear (θL i) := by
    rw [← he]
    simpa only [f,Fintype.card_fin] using SpectralPlane.leading_equation θL A
  have hsf := BinaryLeading.squarefree_product θL hθL
  have hnz := BinaryLeading.product_nonzero θL
  have hpz := BinaryLeading.product_partial_nonzero θL hθL
  have hcop := BinaryLeading.product_partial_coprime θL hθL
  have hs' : Squarefree (homogeneousComponent (k+1) (squareForm a b c d)) := hlead.symm ▸ hsf
  have hn' : homogeneousComponent (k+1) (squareForm a b c d) ≠ 0 := hlead.symm ▸ hnz
  have hp' : pderiv 1 (homogeneousComponent (k+1) (squareForm a b c d)) ≠ 0 := hlead.symm ▸ hpz
  have hc' : IsRelPrime (homogeneousComponent (k+1) (squareForm a b c d))
      (pderiv 1 (homogeneousComponent (k+1) (squareForm a b c d))) := hlead.symm ▸ hcop
  let := CurveFamily.singular_finite (squareForm a b c d) (by omega) hdeg hn' hp' hc'
  let := CurveFamily.finite_zeroLocus (singularIdeal (squareForm a b c d))
  let := Fintype.ofFinite (zeroLocus L (singularIdeal (squareForm a b c d)))
  let := CurveFamily.halfIdeal_finite hk hdeg hs'
  obtain ⟨E,n,hE,htr,hnum⟩ := CurveFamily.half_curve_parameter_bound hk hdeg hs' hn' hp' hc'
    (∏ i, BinaryLeading.linear (θ i)) (by simpa only [Fintype.card_fin] using SpectralPlane.homogeneous_leading θ)
    (hlead.trans (SpectralPlane.map_leading θ).symm)
  have hmon : (PlaneBivariate.toBivariate L (squareForm a b c d)).Monic := by
    rw [← he,SpectralPlane.to_charpoly]
    exact Matrix.charpoly_monic _
  have hsep : ((PlaneBivariate.toBivariate L (squareForm a b c d)).map
      (algebraMap L[X] (FractionRing L[X]))).Separable := by
    rw [← he,SpectralPlane.to_charpoly]
    exact PencilSeparability.distinct_slope_pencil_separable θL hθL A
  have hnorm := Conductor.normalization_length_le_half a b c d hmon hsep
  have hnorm' : normalizationDefect θL A ≤
      (5*Module.finrank L (Plane L ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} : ℕ) := by
    let D (p : L[X][X]) (hp : p.Monic) : ℕ∞ :=
      let R := integralClosure L[X] (AdjoinRoot (p.map (algebraMap L[X] (FractionRing L[X]))))
      Module.length L (R ⧸ LinearMap.range
        (normalizationInclusion (Q := FractionRing L[X]) p hp).toLinearMap)
    have hD (p q : L[X][X]) (hp : p.Monic) (hq : q.Monic) (heq : p=q) :
        D p hp = D q hq := by subst q; rfl
    have hp : PlaneBivariate.toBivariate L (squareForm a b c d) =
        (-pencilBase θL A).charpoly := by rw [← he,SpectralPlane.to_charpoly]; rfl
    change D _ hmon ≤ _ at hnorm
    change D _ (Matrix.charpoly_monic _) ≤ _
    rw [← hD _ _ hmon (Matrix.charpoly_monic _) hp]
    exact hnorm
  have hTN : T ≤ 5*Module.finrank L (Plane L ⧸ halfIdeal a b c d) +
      Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} := by
    exact_mod_cast hT.trans hnorm'
  simp only [Nat.add_assoc,Nat.reduceAdd] at hnum
  refine ⟨n,?_,by omega⟩
  have hfE : CurveFamily.InField E f := he.symm ▸ hE
  have hle := curveField_le_of_inField E f hfE
  rw [to_pencil_det] at hle
  exact (trdeg_le_of_injective (IntermediateField.inclusion hle) (IntermediateField.inclusion_injective hle)).trans htr

end PermanentBorder.SpectralDimension

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers
universe u

lemma effective_matrix_budget {k n T : ℕ} (h : 18*n+T ≤ 9*((k+1)*(k+2))) :
    n+(k+1).choose 2 ≤ (k+1)^2-T/18 := by
  have hc : 2*((k+1).choose 2)=(k+1)*k := by
    have heven : 2 ∣ (k+1)*k := by simpa [mul_comm] using (Nat.even_mul_succ_self k).two_dvd
    rw [Nat.choose_two_right,Nat.add_sub_cancel,Nat.mul_div_cancel' heven]
  have hdiv := Nat.div_mul_le_self T 18
  have hsum : n+(k+1).choose 2+T/18 ≤ (k+1)^2 := by nlinarith
  omega

theorem critical_dimension_effective {K : Type u} [Field K] [Infinite K]
    [CharP K 2] [PerfectRing K 2] {k q : ℕ} (hk : 4 ≤ k+1) (hq : 3*q ≤ k)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ) :
    ringKrullDim (MvPolynomial (Fin (k+1) × Fin (k+1)) K ⧸ gradientIdeal K θ q) ≤
      (((k+1)^2-(q+2).choose 2/18 : ℕ) : WithBot ℕ∞) := by
  classical
  apply AlgebraicDimension.krullDim_le_of_field_images (K := K)
  intro L _ _ f
  let Ω := AlgebraicClosure L
  let : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let ι : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  let f' := ι.comp f
  let g := f'.comp (Ideal.Quotient.mkₐ K (gradientIdeal K θ q))
  let A : Matrix (Fin (k+1)) (Fin (k+1)) Ω := fun a b => g (MvPolynomial.X (a,b))
  have hc := field_point_critical θ f'
  have hθΩ : Function.Injective (fun i => algebraMap K Ω (θ i)) :=
    (algebraMap K Ω).injective.comp hθ
  have hd : ((q+2).choose 2 : ℕ∞) ≤
      normalizationDefect (fun i => algebraMap K Ω (θ i)) A :=
    Selector.gradient_forces_normalization_defect hq _ hθΩ A hc
  obtain ⟨n,hn,hnum⟩ := spectral_effective_bound hk θ hθ A ((q+2).choose 2) hd
  obtain ⟨F,hF,hAF⟩ := matrix_field_bound_over_curve θ hθ A (by omega) n hn
  have hg : g.range ≤ F.toSubalgebra := by
    apply DeterminantFiberScheme.range_le_of_variables_mem
    rintro ⟨i,j⟩
    exact hAF i j
  let h : f.range →ₐ[K] Ω := ι.comp f.range.val
  have hmem : ∀ z, h z ∈ F.toSubalgebra := by
    rintro ⟨z,x,hx⟩
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply hg
    exact ⟨p, congrArg ι hx⟩
  let hFmap := h.codRestrict F.toSubalgebra hmem
  have hinj : Function.Injective hFmap := by
    intro x y heq
    apply Subtype.ext
    exact (FaithfulSMul.algebraMap_injective L Ω) (congrArg Subtype.val heq)
  refine ((trdeg_le_of_injective hFmap hinj).trans hF).trans ?_
  exact_mod_cast effective_matrix_budget hnum

end PermanentBorder.SpectralDimension

namespace PermanentBorder.EffectiveParameters
open PermanentBorder.Parameters

def sectionSize (k : ℕ) : ℕ := (selectorIndex k+2).choose 2 / 18

lemma sectionSize_bounds {k : ℕ} (hk : 128 ≤ k) :
    2 ≤ sectionSize k ∧ sectionSize k ≤ k^2 ∧
      (k : ℝ)^2 / 330 ≤ ((sectionSize k-1 : ℕ) : ℝ) := by
  let q := selectorIndex k
  let T := (q+2).choose 2
  let d := sectionSize k
  have hq : 3*q ≤ k-1 ∧ k ≤ 3*(q+1) := by
    dsimp [q,selectorIndex]
    omega
  have hq40 : 40 ≤ q := by omega
  have hT : 2*T=(q+2)*(q+1) := by
    dsimp [T]
    have heven : 2 ∣ (q+2)*(q+1) := by
      simpa [Nat.add_assoc,mul_comm] using (Nat.even_mul_succ_self (q+1)).two_dvd
    rw [Nat.choose_two_right,show q+2-1=q+1 by omega,Nat.mul_div_cancel' heven]
  have hTlarge : 36 ≤ T := by nlinarith
  have hd2 : 2 ≤ d := by dsimp [d,sectionSize]; change 2 ≤ T/18; omega
  have hTd : T < 18*(d+1) := by dsimp [T,d,sectionSize,q]; omega
  have hdT : d ≤ T := by dsimp [T,d,sectionSize,q]; omega
  have hTk : T ≤ k^2 := by
    have hh := Nat.mul_le_mul (show q+2≤k by omega) (show q+1≤k by omega)
    nlinarith
  have hdR : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hTkR : (k : ℝ) ≤ 3*((q : ℝ)+1) := by exact_mod_cast hq.2
  have hTdR : (T : ℝ) ≤ 18*((d : ℝ)+1) := by exact_mod_cast Nat.le_of_lt hTd
  have hTR : 2*(T : ℝ)=((q : ℝ)+2)*((q : ℝ)+1) := by exact_mod_cast hT
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hTlower : (k : ℝ)*((k : ℝ)+3) ≤ 18*T := by
    have hm := mul_le_mul hTkR (by linarith : (k : ℝ)+3 ≤ 3*((q : ℝ)+2))
      (by positivity : (0:ℝ) ≤ (k : ℝ)+3) (by positivity : (0:ℝ) ≤ 3*((q : ℝ)+1))
    nlinarith
  refine ⟨hd2,hdT.trans hTk,?_⟩
  change (k : ℝ)^2/330 ≤ ((d-1 : ℕ) : ℝ)
  rw [hdR]
  have hk2 : (16384 : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  nlinarith

lemma degree_effective_bound {k : ℕ} (hk : 128 ≤ k) :
    (33 : ℝ)*(k : ℝ)/100 ≤ ((k-2*selectorIndex k-1 : ℕ) : ℝ) := by
  have hq : 3*selectorIndex k ≤ k-1 := by dsimp [selectorIndex]; omega
  have hqk : 2*selectorIndex k+1 ≤ k := by omega
  have he : ((k-2*selectorIndex k-1 : ℕ) : ℝ) = (k : ℝ)-2*(selectorIndex k : ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    norm_cast
  have hqR : 3*(selectorIndex k : ℝ) ≤ (k : ℝ)-1 := by
    have : 3*selectorIndex k+1 ≤ k := by omega
    have hh : 3*(selectorIndex k : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast this
    linarith
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  rw [he]
  linarith

theorem explicit_constant {m : ℕ} (hm : 1408 ≤ m) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤
      (((auxiliarySize m-2*selectorIndex (auxiliarySize m)-1 : ℕ) : ℝ)*
        ((sectionSize (auxiliarySize m)-1 : ℕ) : ℝ)) / (4*Real.exp 1) := by
  let k := auxiliarySize m
  have hk : 128 ≤ k := (Parameters.size_bound hm).1
  have hr := degree_effective_bound hk
  have hd := (sectionSize_bounds hk).2.2
  have hprod : (k : ℝ)^3/1000 ≤
      ((k-2*selectorIndex k-1 : ℕ) : ℝ)*((sectionSize k-1 : ℕ) : ℝ) := by
    have hmul := mul_le_mul hr hd (by positivity : (0:ℝ) ≤ (k : ℝ)^2/330)
      (by positivity : (0:ℝ) ≤ ((k-2*selectorIndex k-1 : ℕ) : ℝ))
    nlinarith
  have hmkN : m ≤ 11*k+10 := by dsimp [k,auxiliarySize]; omega
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hmk : (m : ℝ) ≤ 111*(k : ℝ)/10 := by
    have : (m : ℝ) ≤ 11*(k : ℝ)+10 := by exact_mod_cast hmkN
    linarith
  have hcubes : (m : ℝ)^3 ≤ (111*(k : ℝ)/10)^3 :=
    pow_le_pow_left₀ (by positivity) hmk 3
  have he := Real.exp_pos (1 : ℝ)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  change (m : ℝ)^3*(4*Real.exp 1) ≤ _
  dsimp [k] at hprod hcubes ⊢
  nlinarith [show (0:ℝ) ≤ (auxiliarySize m : ℝ)^3 by positivity]

end PermanentBorder.EffectiveParameters

namespace PermanentBorder
open Parameters EffectiveParameters SpectralDimension MvPolynomial

theorem exists_effective_critical_bound {K : Type} [Field K] [Infinite K]
    [CharP K 2] [PerfectRing K 2] {d : ℕ} (hd : 128 ≤ d) :
    ∃ θ : Fin d → K,
      ringKrullDim (MvPolynomial (Variables d) K ⧸
        Ideal.span (Set.range (fun i => pderiv i
          (Selector.diagonalCoefficient
            (Matrix.of fun a b => (X (a,b) : MvPolynomial (Variables d) K))
            (fun i => C (θ i)) (selectorIndex d))))) ≤
        ((d^2-sectionSize d : ℕ) : WithBot ℕ∞) := by
  classical
  cases d with
  | zero => omega
  | succ k =>
    let θ : Fin (k+1) → K := fun i => Infinite.natEmbedding K i.val
    have hθ : Function.Injective θ := by
      intro i j hij
      exact Fin.ext ((Infinite.natEmbedding K).injective hij)
    have hq : 3*selectorIndex (k+1) ≤ k := by dsimp [selectorIndex]; omega
    exact ⟨θ,critical_dimension_effective (by omega) hq θ hθ⟩

theorem permanent_border_cubic_lower_bound (m n : ℕ) (hm : 1408 ≤ m)
    (h : HasBorderDeterminant n (permanentPolynomial m)) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ) := by
  let k := auxiliarySize m
  have hk : 128 ≤ k := (Parameters.size_bound hm).1
  obtain ⟨θ,hdim⟩ := exists_effective_critical_bound (K := AlgebraicClosure (ZMod 2)) hk
  have hs := EffectiveParameters.sectionSize_bounds hk
  have hi := Parameters.index_bounds hk
  have hB : k^2-sectionSize k+(sectionSize k-1) < k^2 := by omega
  apply (EffectiveParameters.explicit_constant hm).trans
  exact h.selector_lower_of_critical_dimension
    (by omega : 0 < k) (by have := Nat.div_le_self k 2; omega : selectorIndex k ≤ k)
    hi.2.2.2 hs.1 (by have := (Parameters.size_bound hm).2.2; omega)
    θ hdim hB

theorem permanent_exact_cubic_lower_bound (m n : ℕ) (hm : 1408 ≤ m)
    (h : HasExactDeterminant n (permanentPolynomial m)) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ) :=
  permanent_border_cubic_lower_bound m n hm h.hasBorderDeterminant

theorem permanent_cubic_lower_bounds :
    (∀ (m n : ℕ), 1408 ≤ m → HasBorderDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ)) ∧
    (∀ (m n : ℕ), 1408 ≤ m → HasExactDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ)) :=
  ⟨permanent_border_cubic_lower_bound, permanent_exact_cubic_lower_bound⟩

end PermanentBorder

end OAI
