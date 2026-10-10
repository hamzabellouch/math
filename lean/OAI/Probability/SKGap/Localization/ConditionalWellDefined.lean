import Mathlib
import OAI.Probability.SKGap.Matrix.ConditionalEmpiricalNorm
import OAI.Probability.SKGap.Localization.SparseShrink

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

theorem empirical_conditional_wellDefined {j R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∃ σ0 ε0 : ℝ, 0 < σ0 ∧ 0 < ε0 ∧ ∀ x ∈ U,∀ σ : ℝ, |σ| ≤ σ0 →
      ∀ (n : ℕ) [NeZero n] (y a : Fin n → ℝ), empiricalLaw y=(x.1:ProbabilityMeasure ℝ) →
      (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε0^2*(n:ℝ) →
      0 < scalarQMoment (empiricalLaw y) ∧ 0 < scalarS j (empiricalLaw y,(x.2:ℝ),σ) ∧
      0 < j/(n:ℝ)*∑ i,a i := by
  obtain ⟨L,hL,U,hU,hKU,δ,hδ,hnb⟩ := scalar_conditional_neighborhood (R := R) (T := T)
    hj hj1 hR ht0 (by norm_num : (0:ℝ)<1)
  let ε := δ/(j+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : j*ε ≤ δ := by
    have hh : (j+1)*ε=δ := by dsimp [ε]; field_simp
    nlinarith only [hh,hε.le]
  refine ⟨U,hU,hKU,δ,ε,hδ,hε,?_⟩
  intro x hx σ hσ n _ y a hP hclose
  let r := j/(n:ℝ)*∑ i,a i-j*scalarBMoment (empiricalLaw y)
  have hr : |r| ≤ δ := (empirical_mass_close a y hj.le hε.le hclose).trans hεδ
  have hh := hnb x hx σ r hσ hr
  rw [← hP] at hh
  refine ⟨hh.1,hh.2.1,?_⟩
  have hB : j*scalarBMoment (empiricalLaw y)+r=j/(n:ℝ)*∑ i,a i := by dsimp [r]; ring
  simpa only [hB] using hh.2.2.1
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma four_radius_sq_le {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ/2) :
    4*ε^2 ≤ δ^2 := by
  have hh := mul_self_le_mul_self (by linarith : 0 ≤ 2*ε) (by linarith : 2*ε ≤ δ)
  nlinarith only [hh]

theorem conditional_empirical_simultaneous {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
      {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧
        (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) ∧
        ¬(diagonalHessian a (empiricalConditionalMiddle j x.2 σ y g)-
          m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} ≤
      103*exp (-c*(n:ℝ)) := by
  obtain ⟨m,ν,σf,hm,hν,hσf,Uf,hUf,hKUf,hfixed⟩ :=
    conditional_empirical_fixed_tail (T := T) hj hj1 hA hsub hR ht0
  obtain ⟨Uw,hUw,hKUw,σw,εw,hσw,hεw,hwell⟩ :=
    empirical_conditional_wellDefined (T := T) hj hj1 hR ht0
  obtain ⟨L,hL,hnorm⟩ := empiricalConditionalMiddle_uniform_norm (T := T) hj.le hR ht0 (2*sqrt j+1)
  let σ0 := min 1 (min σf σw)
  have hσ0 : 0 < σ0 := by dsimp [σ0]; positivity
  refine ⟨m/2,ν,σ0,half_pos hm,hν,hσ0,Uf ∩ Uw,hUf.inter hUw,?_,?_⟩
  · exact fun x hx=>⟨hKUf hx,hKUw hx⟩
  intro R1 hR1
  obtain ⟨εf,c,N,hεf,hc,hN,hfix⟩ := hfixed R1 hR1
  obtain ⟨εs,hεs,hsparse⟩ := conditional_sparse_uniform hj (by linarith : 0 < A)
    (by linarith : 0 < L) hm hc
  let ε := min εs (min (εf/2) (εw/2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεs' : ε ≤ εs := min_le_left _ _
  have hεf' : ε ≤ εf/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεw' : ε ≤ εw/2 := (min_le_right _ _).trans (min_le_right _ _)
  let c0 := min (1/(π^2*j)) (c/2)
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  refine ⟨ε,c0,N,hε,hc0,hN,?_⟩
  intro n _ hn x hx y hP hy σ hσ
  have hσ1 : |σ| ≤ 1 := hσ.trans (min_le_left _ _)
  have hσf' : |σ| ≤ σf := hσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσw' : |σ| ≤ σw := hσ.trans ((min_le_right _ _).trans (min_le_right _ _))
  let v : Fin n → ℝ := fun i=>1-tanh (y i)^2
  have hv (i : Fin n) : v i ∈ Icc 0 A := ⟨by dsimp [v]; linarith [tanh_sq_lt_one (y i)],
    by dsimp [v]; linarith [sq_nonneg (tanh (y i))]⟩
  have hzero : (∑ i,(v i-(1-tanh (y i)^2))^2) ≤ εw^2*(n:ℝ) := by
    simp only [v,sub_self,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero]
    positivity
  have hpos := hwell x hx.2 σ hσw' n y v hP hzero
  have hnorm' : ∀ g,opNorm (goeMatrix (j/(n:ℝ)) g) ≤ 2*sqrt j+1 →
      opNorm (empiricalConditionalMiddle j x.2 σ y g) ≤ L :=
    hnorm n y (by rw [hP]; exact x.1.2) hpos.1 x.2 x.2.2 σ hσ1
  apply hsparse ε hε hεs' n v hv (empiricalConditionalMiddle j x.2 σ y)
    (empiricalConditionalMiddle_hermitian j x.2 σ y) hnorm'
  intro b hb hbclose
  have hclosef : (∑ i,(b i-(1-tanh (y i)^2))^2) ≤ εf^2*(n:ℝ) :=
    hbclose.trans (mul_le_mul_of_nonneg_right (four_radius_sq_le hε.le hεf') (Nat.cast_nonneg n))
  have hclosew : (∑ i,(b i-(1-tanh (y i)^2))^2) ≤ εw^2*(n:ℝ) :=
    hbclose.trans (mul_le_mul_of_nonneg_right (four_radius_sq_le hε.le hεw') (Nat.cast_nonneg n))
  have hposb := hwell x hx.2 σ hσw' n y b hP hclosew
  have heq (g : MatrixCoordinates (Fin n) → ℝ) := conditionalEmpiricalCore_eq_hessian j x.2 σ b y g
    (fun i=>(hb i).1) hposb.1 hposb.2.1 hposb.2.2
  have hh := hfix n hn x hx.1 y hP hy σ hσf' b (fun i=>(hb i).1) (fun i=>(hb i).2) hclosef
  simp only [heq] at hh
  exact hh
end SKGap
end
end

end OAI
