import Mathlib
import OAI.Probability.SKGap.Localization.EmpiricalConditionalData
import OAI.Probability.SKGap.Gaussian.ConditionalUniformTail

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix
open scoped BigOperators Matrix.Norms.Frobenius

def augmentedToleranceConstant (L : ℝ) :=
  4*(1+(L+1)*(1+L)+L*(1+2*L+L^2))

lemma augmentedToleranceConstant_pos {L : ℝ} (hL : 0 ≤ L) :
    0 < augmentedToleranceConstant L := by unfold augmentedToleranceConstant; positivity

lemma augmentedGramTolerance_bound {B L ε : ℝ} (hB : 0 < B) (hL : 1 ≤ L)
    (hε : 0 ≤ ε) (hb : B ≤ L) (hi : 1/B ≤ L) :
    augmentedGramTolerance B ε ≤ augmentedToleranceConstant L*ε := by
  have hL0 : 0 ≤ L := by linarith
  have hir : (sqrt B)⁻¹ ≤ L+1 := by
    have hs : (sqrt B)⁻¹=sqrt B⁻¹ := (sqrt_inv B).symm
    rw [hs]
    have hh := sq_sqrt (inv_pos.mpr hB).le
    have hh' : B⁻¹ ≤ L := by simpa only [one_div] using hi
    nlinarith [sq_nonneg (sqrt B⁻¹-1)]
  have hB2 : B^2 ≤ L^2 := pow_le_pow_left₀ hB.le hb 2
  have ht1 : (sqrt B)⁻¹*(1+B) ≤ (L+1)*(1+L) :=
    mul_le_mul hir (by linarith) (by positivity) (by linarith)
  have ht2 : B⁻¹*(1+2*B+B^2) ≤ L*(1+2*L+L^2) :=
    mul_le_mul (by simpa only [one_div] using hi) (by linarith) (by positivity) hL0
  unfold augmentedGramTolerance augmentedToleranceConstant
  have h1 := mul_le_mul_of_nonneg_right ht1 hε
  have h2 := mul_le_mul_of_nonneg_right ht2 hε
  nlinarith

lemma conditionalMeanData_hermitian (j : ℝ) (p : ScalarPoint) (r : ℝ) :
    (conditionalMeanData j p r).IsHermitian := by
  exact conditionalCoefficient_hermitian _ _ _ _
lemma conditionalScalarData_hermitian (j : ℝ) (p : ScalarPoint) :
    (conditionalScalarData j p).IsHermitian := by
  exact conditionalCoefficient_hermitian _ _ _ _
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma diagonal_mass_margin {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) {m r A : ℝ} (ha : ∀ i,0 ≤ a i) (hA : ∀ i,a i ≤ A)
    (hr : |r| * A ≤ m) (hH : (H-(2*m) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) :
    (H-r • diagonal a-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hd : (diagonal (fun i=>m-r*a i)).PosSemidef := Matrix.PosSemidef.diagonal (fun i=>by
    change 0 ≤ m-r*a i
    have hh : r*a i ≤ |r| * A := (mul_le_mul_of_nonneg_right (le_abs_self r) (ha i)).trans
      (mul_le_mul_of_nonneg_left (hA i) (abs_nonneg r))
    linarith)
  convert hH.add_posSemidef hd using 1
  ext i k
  by_cases hik : i=k
  · subst k; simp; ring
  · simp [hik]

lemma empirical_moment_vector_bound {n : ℕ} [NeZero n] {R : ℝ}
    (hR : 0 ≤ R) (y : Fin n → ℝ) (hy : empiricalLaw y ∈ momentBall R) :
    ∑ i,y i^2 ≤ (R+1)^2*(n:ℝ) := by
  have hh := momentBall_integral_le hR hy
  rw [integral_empiricalLaw] at hh
  simp only [Fintype.card_fin] at hh
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hp := mul_le_mul_of_nonneg_left hh hn.le
  have hp' : ∑ i,y i^2 ≤ R*(n:ℝ) := by
    simpa only [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul,mul_comm (n:ℝ) R] using hp
  have hR' : R ≤ (R+1)^2 := by nlinarith [sq_nonneg R]
  exact hp'.trans (mul_le_mul_of_nonneg_right hR' hn.le)

lemma empirical_cutoff_gram_small {n : ℕ} [NeZero n] (a y : Fin n → ℝ)
    {A L ε ν R1 ρ d s : ℝ}
    (ha : ∀ i,0 ≤ a i) (haA : ∀ i,a i ≤ A) (hA : 0 ≤ A)
    (hs : 0 < s) (hL : 1 ≤ L) (hd : (1+|d|)/s ≤ L)
    (hR1 : 1 ≤ R1) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (haclose : ∑ i,(a i-(1-tanh (y i)^2))^2 ≤ ε^2*(n:ℝ))
    (hy : (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ))
    (hεgram : 8*L^2*(1+R1^2)*ε ≤ ρ/8)
    (hνgram : 16*L^2*(A+1)*ν ≤ ρ/8) :
    ‖diagonalAugmentedGram a (empiricalGramColumns y d s)-
      augmentedGram (ν := Unit) (scalarMomentGram (empiricalLaw y) d s)‖ ≤ ρ/4 := by
  have hdiff (i : Fin n) : |a i-(1-tanh (y i)^2)| ≤ A+1 := by
    have hv0 := tanh_sq_lt_one (y i)
    have hv1 := sq_nonneg (tanh (y i))
    exact abs_le.mpr ⟨by linarith [ha i],by linarith [haA i]⟩
  have hg := empirical_augmented_gram_comparison a y hs hL hd
    (by positivity : 0 ≤ A+1) hR1 hε hν hdiff haclose hy
  apply hg.trans
  nlinarith

lemma gram_close_by_quarters {α : Type*} [SeminormedAddCommGroup α] (a b c : α)
    {ρ : ℝ} (hab : ‖a-b‖ ≤ ρ/4) (hbc : ‖b-c‖ < ρ/4) : ‖a-c‖ < ρ/2 := by
  exact (norm_sub_le_norm_sub_add_norm_sub a b c).trans_lt (by linarith)

def conditionalEmpiricalCore {n : ℕ} [NeZero n] (j t σ : ℝ) (a y : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let B := j*scalarBMoment p.1
  let BA := j/(n:ℝ)*∑ i,a i
  let u := empiricalUnit y (scalarQMoment p.1)
  let V := conditionalUpdateColumns j a (empiricalGramColumns y (scalarD j p) (scalarS j p)) u g
  conditionalBase j a g-pathDiagonal a 1*V*
    (conditionalMeanData j p (BA-B)+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • conditionalScalarData j p)*
    Vᵀ*pathDiagonal a 1+(B-BA) • diagonal a

theorem conditional_empirical_fixed_tail {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
    (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
      {g | ¬(conditionalEmpiricalCore j x.2 σ a y g-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
      101*exp (-c*(n:ℝ)) := by
  have hA0 : 0 < A := by linarith
  obtain ⟨hs,hq,hb,he,hκ,_⟩ := continuous_curve_statistics (T := T) hj hj1 ht0
  obtain ⟨δ,ρ,hδ,_,hρ,htail⟩ := compact_conditional_uniform_tail hj hj1 hA0 hsub
    (fun t : Icc t0 T=>scalarBMoment (scalarCurve j t))
    (fun t : Icc t0 T=>scalarEMoment (scalarCurve j t))
    (fun t : Icc t0 T=>scalarFixedPoint j t) (fun t : Icc t0 T=>scalarQ j t)
    (fun t : Icc t0 T=>curveKappa j t) hb he hs hq hκ
    (fun t=>scalarBMoment_pos _) (fun t=>scalarBMoment_le_one _) (fun t=>scalarEMoment_nonneg _)
    (fun t=>(scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).1)
    (fun t=>(scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).2)
    (fun t=>curveKappa_sq hj hj1 (ht0.trans_le t.2.1))
  obtain ⟨L,hL,U,hU,hKU,σ0,hσ0,hnb⟩ := scalar_conditional_neighborhood (R := R) (T := T) hj hj1 hR ht0 (by positivity : 0 < ρ/4)
  let m := δ*((1-sqrt j*A)^2/4)/2
  have hm : 0 < m := by dsimp [m]; positivity
  let terr := 16*L^2*(A+1)
  have hterr : 0 < terr := by dsimp [terr]; positivity
  let ν := ρ/(8*terr)
  have hν : 0 < ν := by dsimp [ν]; positivity
  let Vbound := 2*L*(R+2)+1
  have hV : 0 ≤ Vbound := by dsimp [Vbound]; positivity
  let K := augmentedToleranceConstant L
  have hK : 0 < K := augmentedToleranceConstant_pos (by linarith)
  let εg := ρ/(4*K)
  let τ := ρ/(4*(L+1))
  have hεg : 0 < εg := by dsimp [εg]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨c,N,hc,hN,hfixed⟩ := htail Vbound hV εg τ hεg hτ
  refine ⟨m,ν,σ0,hm,hν,hσ0,U,hU,hKU,?_⟩
  intro R1 hR1
  let berr := 8*L^2*(1+R1^2)
  have hberr : 0 < berr := by dsimp [berr]; positivity
  let ε := min (σ0/(j+1)) (min (ρ/(8*berr)) (m/(j*A+1)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεσ : ε*(j+1) ≤ σ0 := (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hεgram : berr*ε ≤ ρ/8 := by
    have hh : ε ≤ ρ/(8*berr) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 8*berr)).mp hh
    nlinarith only [hh']
  have hεmass : ε*(j*A+1) ≤ m := (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε,c,N,hε,hc,hN,?_⟩
  intro n _ hn x hx y hP hy σ hσ a ha haA haclose
  let p : ScalarPoint := (empiricalLaw y,(x.2:ℝ),σ)
  let BA := j/(n:ℝ)*∑ i,a i
  let B := j*scalarBMoment (empiricalLaw y)
  let r := BA-B
  have hr : |r| ≤ j*ε := empirical_mass_close a y hj.le hε.le haclose
  have hrσ : |r| ≤ σ0 := hr.trans (by nlinarith only [hεσ,hε.le])
  have hnbe := hnb x hx σ r hσ hrσ
  rw [← hP] at hnbe
  change 0 < scalarQMoment p.1 ∧ 0 < scalarS j p ∧ 0 < B+r ∧
    conditionalScalarSize j p r < L ∧ _ ∧ _ at hnbe
  have hBr : B+r=BA := by dsimp [r]; ring
  have hBA : 0 < BA := by simpa only [hBr] using hnbe.2.2.1
  have hd := conditionalSize_bounds hnbe.1 hnbe.2.1 hnbe.2.2.1 hnbe.2.2.2.1
  have hBAle : BA < L := by
    have hh := hd.2.2.2.2.1
    change B+r<L at hh
    simpa only [hBr] using hh
  have hBAinv : 1/BA < L := by
    have hh := hd.2.2.2.1
    change 1/(B+r)<L at hh
    simpa only [hBr] using hh
  have htol : augmentedGramTolerance BA εg < ρ/2 := by
    apply (augmentedGramTolerance_bound hBA hL hεg.le hBAle.le hBAinv.le).trans_lt
    have heq : augmentedToleranceConstant L*εg=ρ/4 := by
      dsimp [εg]
      change K*(ρ/(4*K))=ρ/4
      field_simp
    rw [heq]; linarith
  have hEbound : τ*‖conditionalScalarData j p‖ < ρ/2 := by
    apply (mul_lt_mul_of_pos_left hd.2.2.2.2.2 hτ).trans
    have hL0 : 0 < L+1 := by linarith
    have hh : τ*(L+1)=ρ/4 := by dsimp [τ]; field_simp
    nlinarith only [hh,hτ,hρ]
  have hvecmom := empirical_moment_vector_bound hR y (by rw [hP]; exact x.1.2)
  let cols := empiricalGramColumns y (scalarD j p) (scalarS j p)
  let u := empiricalUnit y (scalarQMoment p.1)
  have hpbound : ∀ k,‖cols k‖ ≤ Vbound := fun k=>(empiricalGramColumns_norm (NeZero.pos n) y hnbe.2.1 hL (by linarith : 0 ≤ R+1) hd.1.le hvecmom k).trans (by dsimp [Vbound]; linarith)
  have hubound : ‖u‖ ≤ Vbound := by
    rw [empiricalUnit_norm y hnbe.1]
    dsimp [Vbound]
    have hp : 0 ≤ 2*L*(R+2) := by positivity
    linarith
  have hunit : u.ofLp⬝ᵥu.ofLp=1 := empiricalUnit_unit y hnbe.1
  have hνgram : 16*L^2*(A+1)*ν ≤ ρ/8 := by
    have ht : terr*ν=ρ/8 := by dsimp [ν]; field_simp
    exact ht.le
  have hgsmall := empirical_cutoff_gram_small a y ha haA hA0.le hnbe.2.1 hL hd.1.le
    hR1 hε.le hν.le haclose hy hεgram hνgram
  have hGram : ‖diagonalAugmentedGram a cols-augmentedGram (ν := Unit)
      (limitingGram (scalarBMoment (scalarCurve j x.2)) (scalarEMoment (scalarCurve j x.2))
        (scalarFixedPoint j x.2))‖ < ρ/2 := by
    exact gram_close_by_quarters _ _ _ hgsmall hnbe.2.2.2.2.1
  have hCoef : ‖conditionalMeanData j p r-curveCoefficient j x.2‖ < ρ/2 :=
    hnbe.2.2.2.2.2.trans (by linarith)
  have hprob := hfixed n hn a ha haA hBA htol cols u hpbound hubound hunit x.2
    (conditionalMeanData j p r) (conditionalScalarData j p)
    (conditionalMeanData_hermitian j p r) (conditionalScalarData_hermitian j p) hEbound hGram hCoef
  apply le_trans (measureReal_mono (s₂ := {g | ¬(conditionalBase j a g-
      pathDiagonal a 1*conditionalUpdateColumns j a cols u g*
      (conditionalMeanData j p r+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • conditionalScalarData j p)*
      (conditionalUpdateColumns j a cols u g)ᵀ*pathDiagonal a 1-
      (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef}) ?_ (measure_ne_top _ _)) hprob
  intro g hg
  contrapose! hg
  simp only [Set.mem_ofPred_eq,not_not] at hg ⊢
  have hrm : |r| * A ≤ m := by
    apply (mul_le_mul_of_nonneg_right hr hA0.le).trans
    nlinarith only [hεmass,hε.le]
  have hm2 : 2*m=δ*((1-sqrt j*A)^2/4) := by dsimp [m]; ring
  have hh := diagonal_mass_margin _ a ha haA hrm (by rw [hm2]; exact hg)
  convert hh using 1
  dsimp [conditionalEmpiricalCore,p,B,BA,r,cols,u]
  congr 1
  module
end SKGap
end
end

end OAI
