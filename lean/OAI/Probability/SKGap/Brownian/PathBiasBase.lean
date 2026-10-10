import Mathlib
import OAI.Probability.SKGap.Localization.TruncationGoodSet

namespace OAI

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_schwartzMatrix_comp {X : Type*} [TopologicalSpace X]
    (f : 𝓢(ℝ,ℂ)) {S : X → Matrix ι ι ℂ} (hS : Continuous S)
    (hh : ∀ x, (S x)ᴴ=S x) : Continuous (fun x => schwartzMatrix f (S x)) := by
  let H := {M : Matrix ι ι ℂ // Mᴴ=M}
  let : MetricSpace (Matrix ι ι ℂ) := Matrix.frobeniusNormedAddCommGroup.toMetricSpace
  let : MetricSpace H := MetricSpace.induced Subtype.val Subtype.val_injective inferInstance
  have hl : LipschitzWith (Real.toNNReal (2*Real.pi*fourierMoment f 1))
      (fun M : H => schwartzMatrix f M.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro M N
    change dist (schwartzMatrix f M.1) (schwartzMatrix f N.1) ≤
      (Real.toNNReal (2*Real.pi*fourierMoment f 1) : ℝ) * dist M.1 N.1
    simp only [dist_eq_norm]
    exact (schwartzMatrix_lipschitz f M.1 N.1 M.2 N.2).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  exact hl.continuous.comp (hS.subtype_mk hh)

lemma continuous_truncatedK_comp {X : Type*} [TopologicalSpace X]
    (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) {B D C M : X → Matrix ι ι ℂ}
    (hB : Continuous B) (hD : Continuous D) (hC : Continuous C) (hM : Continuous M)
    (hBh : ∀ x, (B x)ᴴ=B x) (hDh : ∀ x, (D x)ᴴ=D x) :
    Continuous (fun x => truncatedK f R hR (B x) (D x) (C x) (M x)) := by
  have hP := (matrixProject_lipschitz R hR).continuous.comp hM
  have hS : Continuous (fun x => sandShift (B x) (D x) (matrixProject R hR (M x))) := by
    unfold sandShift
    exact hB.sub ((hD.mul hP).mul hD)
  have hF := continuous_schwartzMatrix_comp f hS (fun x =>
    sandShift_hermitian _ _ _ (hBh x) (hDh x) (matrixProject_bound R hR (M x)).1)
  exact continuous_const.add (((hD.mul hF).mul hD).mul (hP.sub hC))

end SKGap.ComplexMatrix

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_realTruncatedK_comp {X : Type*} [TopologicalSpace X]
    (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) {D C M : X → Matrix ι ι ℝ}
    (hD : Continuous D) (hC : Continuous C) (hM : Continuous M)
    (hDh : ∀ x, (D x)ᵀ=D x) (hCh : ∀ x, (C x)ᵀ=C x) :
    Continuous (fun x => realTruncatedK f R hR (D x) (C x) (M x)) := by
  have hlift : Continuous (RealComplex.liftMatrix (ι := ι)) := by
    change Continuous (fun M : Matrix ι ι ℝ => M.map Complex.ofReal)
    fun_prop
  have hdl := hlift.comp hD
  have hcl := hlift.comp hC
  have hml := hlift.comp hM
  have hB : Continuous (fun x => (1 : Matrix ι ι ℂ) +
      liftMatrix (D x)*liftMatrix (C x)*liftMatrix (D x)) :=
    continuous_const.add ((hdl.mul hcl).mul hdl)
  have hh (x : X) : (1+liftMatrix (D x)*liftMatrix (C x)*liftMatrix (D x))ᴴ =
      1+liftMatrix (D x)*liftMatrix (C x)*liftMatrix (D x) := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
      liftMatrix_hermitian (D x) (hDh x),liftMatrix_hermitian (C x) (hCh x),mul_assoc]
  exact realPart_lipschitz.continuous.comp (ComplexMatrix.continuous_truncatedK_comp
    f hR hB hdl hcl hml hh (fun x => liftMatrix_hermitian _ (hDh x)))

lemma continuousOn_expected_realTruncatedK (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    {D C : ℝ → Matrix ι ι ℝ} (r : ℝ) (i : ι) (s : Set ℝ) (B : ℝ)
    (hD : Continuous D) (hC : Continuous C)
    (hDh : ∀ z, (D z)ᵀ=D z) (hCh : ∀ z, (C z)ᵀ=C z)
    (hB : ∀ z ∈ s, ComplexMatrix.kBound f R (liftMatrix (D z)) (liftMatrix (C z)) ≤ B) :
    ContinuousOn (fun z => ∫ g, realTruncatedK f R hR (D z) (C z) (goeMatrix r g) i i
      ∂(Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))) s := by
  apply continuousOn_of_dominated (bound := fun _ => B)
  · intro z _
    exact (((realTruncatedK_lipschitz f hR (D z) (C z) (hDh z) (hCh z)).continuous.comp
      (goeMatrix_pi_lipschitz r).continuous).matrix_elem i i).aestronglyMeasurable
  · intro z hz
    filter_upwards [] with g
    simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ i i).trans
      ((realTruncatedK_opNorm f hR (D z) (C z) _ (hDh z) (hCh z)).trans (hB z hz))
  · exact integrable_const B
  · filter_upwards [] with g
    exact ((continuous_realTruncatedK_comp f hR hD hC continuous_const hDh hCh).matrix_elem i i).continuousOn

lemma realTruncatedK_zero_diagonal (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (C M : Matrix ι ι ℝ) : realTruncatedK f R hR 0 C M=1 := by
  simp [realTruncatedK,ComplexMatrix.truncatedK,ComplexMatrix.truncatedG,RealComplex.liftMatrix,RealComplex.realPart]

end SKGap

noncomputable section
open Real
namespace SKGap

lemma power_exponential_bound (k : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x^k*Real.exp (-c*x) ≤ (k.factorial:ℝ)/c^k := by
  have hfac : (0:ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have h := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (c*x) (mul_nonneg hc.le hx) k)
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-c*x)).le
  have he : Real.exp (c*x)*Real.exp (-c*x)=1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hr : (Real.exp (c*x)*(k.factorial:ℝ))*Real.exp (-c*x) = (k.factorial:ℝ) := by
    calc
      _ = (k.factorial:ℝ)*(Real.exp (c*x)*Real.exp (-c*x)) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hr,mul_pow] at hh
  apply (le_div_iff₀ (pow_pos hc k)).mpr
  nlinarith only [hh]

lemma exponential_tail_absorptions {c n p : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ≤ 3*Real.exp (-c*n)) :
    p ≤ (3/c)/n ∧ (n^2+n)*p ≤ (36/c^3)/n ∧
      n*sqrt p ≤ (8*sqrt 3/c^2)/n := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have he1 : n*Real.exp (-c*n) ≤ 1/c := by
    simpa only [pow_one,Nat.factorial_one,Nat.cast_one] using power_exponential_bound 1 hc hn0.le
  have he3 : n^3*Real.exp (-c*n) ≤ 6/c^3 := by
    convert power_exponential_bound 3 hc hn0.le using 1
    norm_num
  have he2 : n^2*Real.exp (-(c/2)*n) ≤ 2/(c/2)^2 := by
    convert power_exponential_bound 2 (half_pos hc) hn0.le using 1
    norm_num
  have he : 0 ≤ Real.exp (-c*n) := (Real.exp_pos _).le
  refine ⟨?_,?_,?_⟩
  · apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hp hn0.le
    have hx : (3:ℝ)/c=3*(1/c) := by ring
    rw [hx]
    nlinarith only [hh,he1]
  · apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ (n^2+n)*n by positivity)
    have hnn : (n^2+n)*n ≤ 2*n^3 := by nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn)]
    have hh' := mul_le_mul_of_nonneg_right hnn (show 0 ≤ 3*Real.exp (-c*n) by positivity)
    have hx : (36:ℝ)/c^3=6*(6/c^3) := by ring
    rw [hx]
    nlinarith only [hh,hh',he3]
  · have hs : sqrt p ≤ sqrt 3*Real.exp (-(c/2)*n) := by
      apply (sqrt_le_sqrt hp).trans_eq
      rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1
      rw [← Real.exp_half]
      congr 1
      ring
    apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg n)
    have hh' := mul_le_mul_of_nonneg_left he2 (sqrt_nonneg 3)
    have heq : sqrt 3*(2/(c/2)^2)=8*sqrt 3/c^2 := by field_simp; ring
    rw [heq] at hh'
    nlinarith only [hh,hh']

end SKGap

namespace SKGap
open Real

def loopErrorConstantOne (j A B L rate : ℝ) : ℝ :=
  2*j*L*(36/rate^3)+2*j*B*A*B*(3/rate)+
    j*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B)
def loopErrorConstantTwo (j A B rate : ℝ) : ℝ :=
  (B+1+A*(j*A)*B)*(3/rate)+A*B*sqrt (2*j)*(8*sqrt 3/rate^2)

lemma loopErrorConstants_nonneg (j A B L rate : ℝ)
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hc : 0 < rate) :
    0 ≤ loopErrorConstantOne j A B L rate ∧ 0 ≤ loopErrorConstantTwo j A B rate := by
  unfold loopErrorConstantOne loopErrorConstantTwo
  exact ⟨by positivity,by positivity⟩

lemma loop_error_one_absorption {j A B L rate n p : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hc : 0 < rate) (hn : 1 ≤ n) (hp : p ≤ 3*Real.exp (-rate*n)) :
    (2*j*L*(n^2+n)+2*j*B*A*B)*p+
      (j/n)*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) ≤
      loopErrorConstantOne j A B L rate/n := by
  obtain ⟨h₁,h₂,_⟩ := exponential_tail_absorptions hc hn hp
  calc
    _ = 2*j*L*((n^2+n)*p)+2*j*B*A*B*p+
      (j/n)*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) := by ring
    _ ≤ 2*j*L*((36/rate^3)/n)+2*j*B*A*B*((3/rate)/n)+
      (j/n)*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B) := by gcongr
    _ = _ := by unfold loopErrorConstantOne; ring

lemma loop_error_two_absorption {j A B rate n p : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < rate) (hn : 1 ≤ n) (hp : p ≤ 3*Real.exp (-rate*n)) :
    (B+1+A*(j*A)*B)*p+A*B*n*sqrt (2*j)*sqrt p ≤
      loopErrorConstantTwo j A B rate/n := by
  obtain ⟨h₁,_,h₃⟩ := exponential_tail_absorptions hc hn hp
  calc
    _ = (B+1+A*(j*A)*B)*p+A*B*sqrt (2*j)*(n*sqrt p) := by ring
    _ ≤ (B+1+A*(j*A)*B)*((3/rate)/n)+A*B*sqrt (2*j)*((8*sqrt 3/rate^2)/n) := by gcongr
    _ = _ := by unfold loopErrorConstantTwo; ring
end SKGap

noncomputable section
open Set Finset
open scoped BigOperators
namespace SKGap

lemma continuous_no_exit {h : ℝ → ℝ} {δ ε : ℝ} (hδ : 0 < δ)
    (hε : ε < δ) (hh : ContinuousOn h (Icc 0 1)) (hzero : h 0 = 0)
    (hlocal : ∀ z ∈ Icc (0:ℝ) 1, |h z| ≤ δ → |h z| ≤ ε) :
    ∀ z ∈ Icc (0:ℝ) 1, |h z| ≤ ε := by
  intro z hz
  by_cases hs : |h z| ≤ δ
  · exact hlocal z hz hs
  · have hzz : 0 ≤ z := hz.1
    have habs : ContinuousOn (fun z => |h z|) (Icc 0 z) :=
      hh.abs.mono (Icc_subset_Icc le_rfl hz.2)
    have hδrange : δ ∈ Icc (|h 0|) (|h z|) := by
      rw [hzero,abs_zero]
      exact ⟨hδ.le,le_of_lt (lt_of_not_ge hs)⟩
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hzz habs hδrange
    change |h t| = δ at heq
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans hz.2⟩
    have hb := hlocal t ht' (by rw [heq])
    rw [heq] at hb
    exact False.elim ((not_le_of_gt hε) hb)

section Loop
variable {ι : Type*} [Fintype ι]

lemma weighted_abs_sum_le {w v : ι → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, |v i| ≤ C) :
    |∑ i, w i*v i| ≤ (∑ i, w i)*C := by
  calc
    _ ≤ ∑ i, |w i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i*|v i| := by simp_rw [abs_mul,abs_of_nonneg (hw _)]
    _ ≤ ∑ i, w i*C := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (hw i)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma loop_local_control {w a k : ι → ℝ} {j A M z h ε δ γ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (hA : 0 ≤ A)
    (hj : 0 ≤ j) (hz : z ∈ Icc (0:ℝ) 1) (hM : ∀ i, |k i| ≤ M)
    (_hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hγ : 0 < γ)
    (hh : h = ∑ i, w i*a i*(k i-1)) (hsmall : |h| ≤ δ)
    (hloop : ∀ i, |k i-1-z^2*j*a i*h*k i| ≤ ε)
    (hmargin : j*A^2*(1+j*A*M*δ+ε) ≤ 1-γ) :
    |h| ≤ A*ε/γ := by
  have hz2 : 0 ≤ z^2 := sq_nonneg z
  have hz2le : z^2 ≤ 1 := by nlinarith [hz.1,hz.2]
  have hki (i : ι) : |k i-1| ≤ j*A*M*δ+ε := by
    have hM0 : 0 ≤ M := (abs_nonneg (k i)).trans (hM i)
    have hmul : |z^2*j*a i*h*k i| ≤ j*A*δ*M := by
      simp only [abs_mul,abs_of_nonneg hz2,abs_of_nonneg hj,abs_of_nonneg (ha i)]
      calc
        _ ≤ 1*j*A*δ*M := by
          gcongr <;> first | exact ha i | exact hz2le | exact haA i | exact hsmall | exact hM i
        _ = _ := by ring
    have he := abs_add_le (k i-1-z^2*j*a i*h*k i) (z^2*j*a i*h*k i)
    have hid : k i-1-z^2*j*a i*h*k i+(z^2*j*a i*h*k i) = k i-1 := by ring
    rw [hid] at he
    nlinarith [hloop i]
  let c := ∑ i, w i*(z^2*j*(a i)^2*k i)
  have hc : |c| ≤ 1-γ := by
    have hki' (i : ι) : |k i| ≤ 1+j*A*M*δ+ε := by
      have hh' := abs_add_le (k i-1) 1
      simp only [sub_add_cancel,abs_one] at hh'
      linarith [hki i]
    have hc' : |c| ≤ j*A^2*(1+j*A*M*δ+ε) := by
      calc
        _ ≤ (∑ i, w i)*(j*A^2*(1+j*A*M*δ+ε)) := by
          apply weighted_abs_sum_le hw
          intro i
          simp only [abs_mul,abs_of_nonneg hz2,abs_of_nonneg hj,abs_of_nonneg (sq_nonneg (a i))]
          calc
            _ ≤ 1*j*A^2*(1+j*A*M*δ+ε) := by
              gcongr <;> first | exact ha i | exact hz2le | exact haA i | exact hki' i
            _ = _ := by ring
        _ = _ := by rw [hws,one_mul]
    exact hc'.trans hmargin
  have herr : |h-c*h| ≤ A*ε := by
    have heq : h-c*h = ∑ i, w i*(a i*(k i-1-z^2*j*a i*h*k i)) := by
      rw [hh]
      dsimp only [c]
      rw [Finset.sum_mul,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    calc
      _ ≤ (∑ i, w i)*(A*ε) := by
        apply weighted_abs_sum_le hw
        intro i
        rw [abs_mul,abs_of_nonneg (ha i)]
        exact mul_le_mul (haA i) (hloop i) (abs_nonneg _) hA
      _ = _ := by rw [hws,one_mul]
  have hlast := abs_add_le (h-c*h) (c*h)
  have heqh : h-c*h+c*h = h := by ring
  rw [heqh,abs_mul] at hlast
  have hch := mul_le_mul_of_nonneg_right hc (abs_nonneg h)
  apply (le_div_iff₀ hγ).mpr
  nlinarith

lemma loop_global_control {w a : ι → ℝ} {k : ℝ → ι → ℝ} {j A M ε δ γ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (hA : 0 ≤ A)
    (hj : 0 ≤ j) (hk : ∀ i, ContinuousOn (fun z => k z i) (Icc 0 1))
    (hk0 : ∀ i, k 0 i = 1) (hM : ∀ z ∈ Icc (0:ℝ) 1, ∀ i, |k z i| ≤ M)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hγ : 0 < γ)
    (hloop : ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
      |k z i-1-z^2*j*a i*(∑ b, w b*a b*(k z b-1))*k z i| ≤ ε)
    (hmargin : j*A^2*(1+j*A*M*δ+ε) ≤ 1-γ) (hexit : A*ε/γ < δ) :
    ∀ z ∈ Icc (0:ℝ) 1,
      |∑ i, w i*a i*(k z i-1)| ≤ A*ε/γ ∧
      ∀ i, |k z i-1| ≤ j*A*M*(A*ε/γ)+ε := by
  let h : ℝ → ℝ := fun z => ∑ i, w i*a i*(k z i-1)
  have hh : ContinuousOn h (Icc 0 1) := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.mul ((hk i).sub continuousOn_const)
  have hh0 : h 0 = 0 := by simp [h,hk0]
  have hg : ∀ z ∈ Icc (0:ℝ) 1, |h z| ≤ A*ε/γ := by
    apply continuous_no_exit hδ hexit hh hh0
    intro z hz hs
    exact loop_local_control hw hws ha haA hA hj hz (hM z hz) hε hδ.le hγ rfl hs
      (hloop z hz) hmargin
  intro z hz
  refine ⟨hg z hz, ?_⟩
  intro i
  have hM0 : 0 ≤ M := (abs_nonneg (k z i)).trans (hM z hz i)
  have hs0 : 0 ≤ A*ε/γ := by positivity
  have hz2le : z^2 ≤ 1 := by nlinarith [hz.1,hz.2]
  have hm : |z^2*j*a i*h z*k z i| ≤ j*A*(A*ε/γ)*M := by
    simp only [abs_mul,abs_of_nonneg (sq_nonneg z),abs_of_nonneg hj,abs_of_nonneg (ha i)]
    calc
      _ ≤ 1*j*A*(A*ε/γ)*M := by
        gcongr <;> first | exact ha i | exact hz2le | exact haA i | exact hg z hz | exact hM z hz i
      _ = _ := by ring
  have hs := abs_add_le (k z i-1-z^2*j*a i*h z*k z i) (z^2*j*a i*h z*k z i)
  have he : k z i-1-z^2*j*a i*h z*k z i+(z^2*j*a i*h z*k z i) = k z i-1 := by ring
  rw [he] at hs
  have hl : |k z i-1-z^2*j*a i*h z*k z i| ≤ ε := hloop z hz i
  nlinarith

end Loop
end SKGap

noncomputable section
open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform ContDiff
namespace SKGap

lemma exists_schwartz_inverse {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹) ∧
      (∀ x, star (f x) = f x) := by
  let b : ContDiffBump hi := {
    rIn := hi-lo/2
    rOut := hi-lo/4
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  let g : ℝ → ℂ := fun x => (b x : ℂ) * (x : ℂ)⁻¹
  have hgcompact : HasCompactSupport g := by
    exact (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hb0 : (0 : ℝ) ∉ tsupport (b : ℝ → ℝ) := by
    rw [b.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,zero_sub,abs_neg,
      abs_of_pos (lt_of_lt_of_le hlo hhi)]
    change ¬ hi ≤ hi-lo/4
    linarith
  have hgsmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hb0] with y hy
      simp [g,hy]
    · have hbr : ContDiffAt ℝ ∞ (fun y : ℝ => (b y : ℂ)) x := by
        exact Complex.ofRealCLM.contDiff.contDiffAt.comp x b.contDiff.contDiffAt
      have hxr : ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt
      exact hbr.mul (hxr.inv (by exact_mod_cast hx))
  refine ⟨hgcompact.toSchwartzMap hgsmooth, ?_, ?_⟩
  · intro x hx
    have hxball : x ∈ Metric.closedBall hi b.rIn := by
      rw [Metric.mem_closedBall,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hx.2)]
      change -(x-hi) ≤ hi-lo/2
      linarith [hx.1]
    simp [g,b.one_of_mem_closedBall hxball]
  · intro x
    simp [g]

lemma schwartz_inverse_fourier_moments (f : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Integrable (fun t : ℝ => ‖t‖^k * ‖(𝓕 f) t‖) :=
  (𝓕 f).integrable_pow_mul volume k

lemma schwartz_fourier_inverse (f : 𝓢(ℝ, ℂ)) : 𝓕⁻ (𝓕 f) = f :=
  FourierTransform.fourierInv_fourier_eq f

end SKGap
end
end
end
end
end

end OAI
