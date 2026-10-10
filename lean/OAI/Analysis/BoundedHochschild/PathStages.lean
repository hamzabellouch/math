import Mathlib
import OAI.Analysis.BoundedHochschild.FiniteConstraints
import OAI.Analysis.BoundedHochschild.WalkLabels

namespace OAI

/-! Finite path stages, labelled walks and distinguished fresh letters. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

include e hL hτ htr hfaith in
 

theorem exists_projection_tails (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n))
    (hat : ∀ n, (τ (a n)).re ≤ (1/2:ℝ)^n) :
    ∃ p : ℕ → M, (∀ n, IsStarProjection (p n)) ∧ Antitone p ∧
      (∀ n m, n ≤ m → a m ≤ p n) ∧ GNSTendsto τ p atTop 0 := by
  have hsum (n k : ℕ) : (∑ i ∈ Finset.range k, (τ (a (n+i))).re) ≤ 2*(1/2:ℝ)^n := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, (1/2:ℝ)^(n+i) := Finset.sum_le_sum (fun i _ => hat (n+i))
      _ = (1/2:ℝ)^n * ∑ i ∈ Finset.range k, (1/2:ℝ)^i := by simp only [pow_add,Finset.mul_sum]
      _ ≤ (1/2:ℝ)^n * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (by positivity)
      _ = _ := mul_comm _ _
  choose p hp hpa hpl hpt using fun n =>
    exists_projection_countable_join e τ hL hτ htr hfaith (fun i => a (n+i))
      (fun i => ha (n+i)) (2*(1/2:ℝ)^n) (hsum n)
  have hdom (n m : ℕ) (hnm : n ≤ m) : a m ≤ p n := by
    simpa only [Nat.add_sub_of_le hnm] using hpa n (m-n)
  refine ⟨p,hp,?_,hdom,?_⟩
  · intro n m hnm
    exact hpl m (p n) (hp n) (fun i => hdom n (m+i) (by omega))
  · have ht : Tendsto (fun n : ℕ => 2*(1/2:ℝ)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ)<1)).const_mul 2
    have hs : Tendsto (fun n => Real.sqrt (2*(1/2:ℝ)^n)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp ht
    change Tendsto (fun n => ‖τ.toPreGNS (p n-0)‖) atTop (𝓝 0)
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hs
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      ((preGNS_sq_le_trace τ (p n) (hp n).nonneg (hp n).le_one).trans (hpt n))

end BoundedHochschild

 

open scoped NNReal
namespace BoundedHochschild
variable {M I : Type*} [CStarAlgebra M]

lemma mul_eq_zero_of_supports (x y p q : M) (hxp : x*p=x) (hqy : q*y=y) (hpq : p*q=0) :
    x*y=0 := by
  calc
    x*y=(x*p)*(q*y) := by rw [hxp,hqy]
    _=x*(p*q)*y := by simp only [mul_assoc]
    _=0 := by rw [hpq,mul_zero,zero_mul]

lemma orthogonal_blocks_norm_sum_le (t : I → M)
    (hleft : ∀ i j, i ≠ j → star (t i)*t j=0)
    (hright : ∀ i j, i ≠ j → t i*star (t j)=0)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, t i‖ ≤ R := by
  classical
  have hdiag : star (∑ i ∈ s, t i)*(∑ i ∈ s, t i) = ∑ i ∈ s, star (t i)*t i := by
    simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_eq_single i (fun j _hj hji => hleft j i hji) (fun h => (h hi).elim)
  have horth : Pairwise (fun i j => (star (t i)*t i)*(star (t j)*t j)=0) := by
    intro i j hij
    calc
      (star (t i)*t i)*(star (t j)*t j) = star (t i)*(t i*star (t j))*t j := by simp only [mul_assoc]
      _ = 0 := by rw [hright i j hij,mul_zero,zero_mul]
  have hs := IsSelfAdjoint.nnnorm_sum_eq_sup s (fun i _hi => IsSelfAdjoint.star_mul_self (t i)) horth
  have hbound : ‖∑ i ∈ s, star (t i)*t i‖₊ ≤ (⟨R^2,sq_nonneg R⟩ : ℝ≥0) := by
    rw [hs]
    apply Finset.sup_le
    intro i hi
    change ‖star (t i)*t i‖ ≤ R^2
    rw [CStarRing.norm_star_mul_self]
    nlinarith [ht i hi,norm_nonneg (t i)]
  change ‖∑ i ∈ s, star (t i)*t i‖ ≤ R^2 at hbound
  rw [← hdiag,CStarRing.norm_star_mul_self] at hbound
  nlinarith [norm_nonneg (∑ i ∈ s, t i)]

lemma supported_sum_norm_le (p t : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (hpt : ∀ i, p i*t i=t i) (htp : ∀ i, t i*p i=t i)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, t i‖ ≤ R := by
  apply orthogonal_blocks_norm_sum_le t _ _ s R hR ht
  · intro i j hij
    apply mul_eq_zero_of_supports _ _ (p i) (p j) _ (hpt j) (horth i j hij)
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg Star.star (hpt i)
  · intro i j hij
    apply mul_eq_zero_of_supports _ _ (p i) (p j) (htp i) _ (horth i j hij)
    simpa only [star_mul,(hp j).isSelfAdjoint.star_eq] using congrArg Star.star (htp j)

lemma supported_smul_sum_norm_le (p t : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (hpt : ∀ i, p i*t i=t i) (htp : ∀ i, t i*p i=t i)
    (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, c i • t i‖ ≤ R := by
  apply supported_sum_norm_le p (fun i => c i • t i) hp horth
    (fun i => by rw [mul_smul_comm,hpt i]) (fun i => by rw [smul_mul_assoc,htp i]) s R hR
  intro i hi
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans (by simpa using ht i hi)

end BoundedHochschild

 

namespace BoundedHochschild
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]

 

lemma exists_signs_energy (n : ℕ) (v : Fin n → H) :
    ∃ c : Fin n → ℂ, (∀ i, c i=1 ∨ c i= -1) ∧
      (∑ i : Fin n, ‖v i‖^2) ≤ ‖∑ i : Fin n, c i • v i‖^2 := by
  induction n with
  | zero => exact ⟨fun _ => 1,fun _ => Or.inl rfl,by simp⟩
  | succ n ih =>
    obtain ⟨c,hc,he⟩ := ih (fun i => v i.succ)
    let w := ∑ i : Fin n, c i • v i.succ
    have hpara := parallelogram_law_with_norm ℂ (v 0) w
    by_cases hplus : ‖v 0‖^2+‖w‖^2 ≤ ‖v 0+w‖^2
    · refine ⟨Fin.cons 1 c,?_,?_⟩
      · intro i
        refine Fin.cases (Or.inl (by simp)) (fun j => ?_) i
        simpa only [Fin.cons_succ] using hc j
      · rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,one_smul]
        exact (add_le_add le_rfl he).trans hplus
    · have hminus : ‖v 0‖^2+‖w‖^2 ≤ ‖v 0-w‖^2 := by linarith
      refine ⟨Fin.cons (-1) c,?_,?_⟩
      · intro i
        refine Fin.cases (Or.inr (by simp)) (fun j => ?_) i
        simpa only [Fin.cons_succ] using hc j
      · rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,neg_one_smul]
        have hn : ‖-v 0+w‖=‖v 0-w‖ := by rw [neg_add_eq_sub,norm_sub_rev]
        change ‖v 0‖^2+(∑ i : Fin n, ‖v i.succ‖^2) ≤ ‖-v 0+w‖^2
        rw [hn]
        exact (add_le_add le_rfl he).trans hminus

lemma sign_bounded_energy (n : ℕ) (v : Fin n → H) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ c : Fin n → ℂ, (∀ i, c i=1 ∨ c i= -1) →
      ‖∑ i : Fin n, c i • v i‖ ≤ C) :
    (∑ i : Fin n, ‖v i‖^2) ≤ C^2 := by
  obtain ⟨c,hc,he⟩ := exists_signs_energy n v
  exact he.trans (pow_le_pow_left₀ (norm_nonneg _) (hbound c hc) 2)

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_compression_le (p x : M) (C R : ℝ) (hC : 0 ≤ C)
    (hp : ‖p‖ ≤ C) (hx : ‖x‖ ≤ R) : ‖p*x*p‖ ≤ C*R*C := by
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans (mul_le_mul hp hx (norm_nonneg _) hC)) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hp (mul_nonneg hC ((norm_nonneg _).trans hx))))

 

theorem no_normal_small_support_sequence
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (B : M →L[ℂ] M) (hB : HasPreadjoint e B)
    (p y : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hpm : Antitone p) (hpt : GNSTendsto τ p atTop 0)
    (hpy : ∀ n, p n*y n=y n) (hyp : ∀ n, y n*p n=y n)
    (R η : ℝ) (hR : 0 ≤ R) (hη : 0 < η)
    (hy : ∀ n, ‖y n‖ ≤ R) (hyB : ∀ n, η ≤ ‖τ.toPreGNS (B (y n))‖) : False := by
  let v (j h : ℕ) := (p j-p h)*y j*(p j-p h)
  have hdn (j h : ℕ) : ‖p j-p h‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [(hp j).norm_le (p j),(hp h).norm_le (p h)])
  have hvn (j h : ℕ) : ‖v j h‖ ≤ 4*R := by
    have hh := norm_compression_le (p j-p h) (y j) 2 R (by norm_num) (hdn j h) (hy j)
    dsimp [v]
    nlinarith
  have hvt (j : ℕ) : GNSTendsto τ (v j) atTop (y j) := by
    have hd : GNSTendsto τ (fun h => p j-p h) atTop (p j) := by
      simpa only [sub_zero] using (GNSTendsto.const τ (p j) atTop).sub τ hpt
    have hdy := hd.mul τ htr (GNSTendsto.const τ (y j) atTop) 2 (hdn j)
    have hh := hdy.mul τ htr hd (2*R) (fun h =>
      (norm_mul_le _ _).trans (mul_le_mul (hdn j h) (hy j) (norm_nonneg _) (by norm_num)))
    simpa only [v,hpy j,hyp j] using hh
  have hnext (j : ℕ) : ∃ h : ℕ, j<h ∧ η/2 < ‖τ.toPreGNS (B (v j h))‖ := by
    by_contra hh
    push Not at hh
    have ht := hB.tendsto e (predual_tendsto_of_preGNS e τ hL hτ hfaith (4*R) (hvn j) (hvt j))
    have hle := preGNS_norm_le_of_predual_tendsto e τ hL hτ (η/2) (half_pos hη).le
      (by filter_upwards [eventually_ge_atTop (j+1)] with h hh'; exact hh h (by omega)) ht
    linarith [hyB j]
  choose next hn hnB using hnext
  let s : ℕ → ℕ := Nat.rec 0 (fun _ k => next k)
  have hsuc (n : ℕ) : s (n+1)=next (s n) := rfl
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun n => by rw [hsuc]; exact hn (s n))
  let q (n : ℕ) := p (s n)-p (s (n+1))
  let t (n : ℕ) := q n*y (s n)*q n
  have hprod (i j : ℕ) (hij : i ≤ j) : p (s i)*p (s j)=p (s j) :=
    ((hp (s j)).le_iff_mul_eq_right (hp (s i))).mp (hpm (hs.monotone hij))
  have hq (n : ℕ) : IsStarProjection (q n) :=
    (hp (s (n+1))).sub_of_mul_eq_right (hp (s n)) (hprod n (n+1) (by omega))
  have hqorth_lt (i j : ℕ) (hij : i<j) : q i*q j=0 := by
    dsimp [q]
    rw [sub_mul,mul_sub,mul_sub,hprod i j (by omega),hprod i (j+1) (by omega),
      hprod (i+1) j (by omega),hprod (i+1) (j+1) (by omega),sub_self]
  have hqorth (i j : ℕ) (hij : i ≠ j) : q i*q j=0 := by
    rcases lt_or_gt_of_ne hij with hij|hij
    · exact hqorth_lt i j hij
    · simpa only [star_mul,(hq i).isSelfAdjoint.star_eq,(hq j).isSelfAdjoint.star_eq,star_zero]
        using congrArg Star.star (hqorth_lt j i hij)
  have hqt (n : ℕ) : q n*t n=t n := by
    dsimp [t]
    rw [← mul_assoc,← mul_assoc,(hq n).isIdempotentElem.eq]
  have htq (n : ℕ) : t n*q n=t n := by
    dsimp [t]
    rw [mul_assoc,(hq n).isIdempotentElem.eq]
  have htn (n : ℕ) : ‖t n‖ ≤ R := by
    simpa only [one_mul,mul_one] using norm_compression_le (q n) (y (s n)) 1 R
      (by norm_num) ((hq n).norm_le _) (hy (s n))
  have htB (n : ℕ) : η/2 ≤ ‖τ.toPreGNS (B (t n))‖ := by
    simpa only [t,q,hsuc,v] using (hnB (s n)).le
  have henergy (N : ℕ) : (N:ℝ)*(η/2)^2 ≤ (‖B‖*R)^2 := by
    let w (i : Fin N) := τ.toPreGNS (B (t i))
    have hsum : (∑ i : Fin N, ‖w i‖^2) ≤ (‖B‖*R)^2 := by
      apply sign_bounded_energy N w (‖B‖*R) (mul_nonneg (norm_nonneg _) hR)
      intro c hc
      have hnorm : ‖∑ i : Fin N, c i • t i‖ ≤ R := by
        apply supported_smul_sum_norm_le (fun i : Fin N => q i) (fun i : Fin N => t i)
          (fun i => hq i) (fun i j hij => hqorth i j (fun h => hij (Fin.ext h)))
          (fun i => hqt i) (fun i => htq i) c _ Finset.univ R hR (fun i _ => htn i)
        intro i
        rcases hc i with h|h <;> simp only [h,norm_one,norm_neg,le_refl]
      have heq : (∑ i : Fin N, c i • w i) = τ.toPreGNS (B (∑ i : Fin N, c i • t i)) := by
        simp only [map_sum,map_smul,w]
      rw [heq]
      exact (preGNS_norm_le τ h1 _).trans ((B.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
    have hle : (N:ℝ)*(η/2)^2 ≤ ∑ i : Fin N, ‖w i‖^2 := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun i _ => pow_le_pow_left₀ (half_pos hη).le (htB i) 2)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
    exact hle.trans hsum
  obtain ⟨N,hN⟩ := exists_nat_gt ((‖B‖*R)^2 / (η/2)^2)
  have hh : (‖B‖*R)^2 < (N:ℝ)*(η/2)^2 := (div_lt_iff₀ (sq_pos_of_pos (half_pos hη))).mp hN
  exact (not_lt_of_ge (henergy N)) hh

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

 

theorem normal_two_norm_modulus
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (B : M →L[ℂ] M) (hB : HasPreadjoint e B) (R ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (B x)‖ < ε := by
  by_contra hh
  push Not at hh
  let α : ℝ := ε/(2*(‖B‖+1))
  have hα : 0 < α := div_pos hε (by positivity)
  have hBα : ‖B‖*α ≤ ε/2 := by
    have heq : α*(2*(‖B‖+1))=ε := div_mul_cancel₀ ε (by positivity)
    nlinarith [norm_nonneg B]
  have hxex (n : ℕ) : ∃ x : M, ‖x‖ ≤ R ∧
      ‖τ.toPreGNS x‖ < (α/2)*(1/2:ℝ)^n ∧ ε ≤ ‖τ.toPreGNS (B x)‖ :=
    hh ((α/2)*(1/2:ℝ)^n) (by positivity)
  choose x hx hxs hxB using hxex
  have hR : 0 ≤ R := (norm_nonneg _).trans (hx 0)
  choose y a ha hay hya hyn hxy hat using fun n =>
    exists_small_two_sided_support e τ hL hτ htr hfaith (x n) α hα
  have hat' (n : ℕ) : (τ (a n)).re ≤ (1/2:ℝ)^n := by
    apply (hat n).trans
    have hr : 0 < (1/2:ℝ)^n := by positivity
    have hr1 : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hx2 : ‖τ.toPreGNS (x n)‖^2 ≤ ((α/2)*(1/2:ℝ)^n)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hxs n).le 2
    have hrr : ((1/2:ℝ)^n)^2 ≤ (1/2:ℝ)^n := by nlinarith
    have hh' : ‖τ.toPreGNS (x n)‖^2 ≤ α^2/4*(1/2:ℝ)^n := by
      nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hrr)]
    rw [← mul_div_assoc,div_le_iff₀ (sq_pos_of_pos hα)]
    nlinarith [mul_pos (sq_pos_of_pos hα) hr]
  obtain ⟨p,hp,hpm,hpa,hpt⟩ := exists_projection_tails e τ hL hτ htr hfaith a ha hat'
  have hpy (n : ℕ) : p n*y n=y n := by
    calc
      p n*y n = p n*(a n*y n) := by rw [hay n]
      _ = y n := by rw [← mul_assoc,((ha n).le_iff_mul_eq_right (hp n)).mp (hpa n n le_rfl),hay n]
  have hyp (n : ℕ) : y n*p n=y n := by
    calc
      y n*p n = (y n*a n)*p n := by rw [hya n]
      _ = y n := by rw [mul_assoc,((ha n).le_iff_mul_eq_left (hp n)).mp (hpa n n le_rfl),hya n]
  have hyB (n : ℕ) : ε/2 ≤ ‖τ.toPreGNS (B (y n))‖ := by
    have hdiff : ‖τ.toPreGNS (B (x n-y n))‖ ≤ ε/2 :=
      (preGNS_norm_le τ h1 _).trans ((B.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (hxy n) (norm_nonneg _)).trans hBα))
    have hh' := norm_sub_le (τ.toPreGNS (B (x n))) (τ.toPreGNS (B (x n-y n)))
    have heq : τ.toPreGNS (B (x n))-τ.toPreGNS (B (x n-y n))=τ.toPreGNS (B (y n)) := by
      simp only [map_sub,sub_sub_cancel]
    rw [heq] at hh'
    have htri := norm_add_le (τ.toPreGNS (B (y n))) (τ.toPreGNS (B (x n-y n)))
    have heq' : τ.toPreGNS (B (y n))+τ.toPreGNS (B (x n-y n))=τ.toPreGNS (B (x n)) := by
      simp only [map_sub]; abel
    rw [heq'] at htri
    linarith [hxB n]
  exact no_normal_small_support_sequence e τ hL hτ htr hfaith h1 B hB p y hp hpm hpt hpy hyp
    R (ε/2) hR (half_pos hε) (fun n => (hyn n).trans (hx n)) hyB

end BoundedHochschild

 

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower HochschildRare
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

 

theorem primitive_of_normal_finite_tests
    (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ)
    (label : Label → unitary M)
    (htests : StageTests (fun g => ‖τ (FreeGroup.lift label g : M)‖))
    (hdense : ∀ u : unitary M, ∃ j : ℕ → ℕ,
      Tendsto (fun k => ‖τ.toPreGNS ((label (Sum.inl (j k)):M)-(u:M))‖) atTop (𝓝 0))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  refine primitive_of_walk_and_last_modulus e τ h1 htr hfaith hL hR hτ
    (FreeGroup.lift label) walkWeights walkEnum walkWeights_nonneg walkWeights_sum
    ?_ time stages_time_atTop ?_ ?_ f hf ?_
  · rw [walkLaw_eq_atomic]
    exact walkLaw_symmetric
  · rw [walkLaw_eq_atomic]
    exact finite_tests_freeMoments _ htests
  · intro u
    obtain ⟨j,hj⟩ := hdense u
    refine ⟨fun k => FreeGroup.of (Sum.inl (j k)),?_,?_⟩
    · intro k
      rw [walkLaw_eq_atomic]
      exact (base_atom_pos (j k)).ne'
    · simpa only [FreeGroup.lift_apply_of] using hj
  · intro a R ε hε
    exact normal_two_norm_modulus e τ hL hτ htr hfaith h1 (f.curryRight a) (hnormal a) R ε hε

end BoundedHochschild

 

open MeasureTheory Filter Topology
namespace HochschildRare
open HochschildWalk

 
abbrev StageAlphabet (k : ℕ) := Fin (baseCut k) ⊕ ((j : Fin (k+1)) × Fin (labels j.val))

def stageEmbedding (k : ℕ) : StageAlphabet k → Label
  | .inl j => .inl j.val
  | .inr a => .inr ⟨a.1.val,a.2⟩

lemma goodPath_label_in_range {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (i : Fin r × Fin (time k)) :
    (w i).1 ∈ Set.range (stageEmbedding k) := by
  classical
  have htail : ¬ ∃ i, (w i).1 ∈ tailSet k := fun h => hw (Or.inl h)
  have hbase : ¬ ∃ i, (w i).1 ∈ baseTail (baseCut k) := fun h => hw (Or.inr (Or.inl h))
  rcases hwi : (w i).1 with j | ⟨s,j⟩
  · have hj : j < baseCut k := by
      by_contra hh
      exact hbase ⟨i,j,by omega,hwi⟩
    exact ⟨Sum.inl ⟨j,hj⟩,by simp [stageEmbedding]⟩
  · have hs : s < k+1 := by
      by_contra hh
      exact htail ⟨i,s,by omega,j,hwi⟩
    exact ⟨Sum.inr ⟨⟨s,hs⟩,j⟩,by simp [stageEmbedding]⟩

 

theorem goodPath_distinguished {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) :
    ∃ (s : Fin r → Fin (time k)) (a : Fin r → Fin (labels k)),
      (∀ i, (w (i,s i)).1 = Sum.inr ⟨k,a i⟩) ∧
      (∀ i z, (w z).1 = Sum.inr ⟨k,a i⟩ → z=(i,s i)) ∧ Function.Injective a := by
  classical
  have hmiss : ¬ ∃ i, ∀ j, (w (i,j)).1 ∉ stageSet k := fun h => hw (Or.inr (Or.inr (Or.inr h)))
  have hhit : ∀ i : Fin r, ∃ j : Fin (time k), ∃ a : Fin (labels k),
      (w (i,j)).1=Sum.inr ⟨k,a⟩ := by
    intro i
    by_contra hh
    push Not at hh
    exact hmiss ⟨i,fun j ⟨a,ha⟩ => hh j a ha⟩
  choose s a ha using hhit
  have huniq : ∀ i z, (w z).1=Sum.inr ⟨k,a i⟩ → z=(i,s i) := by
    intro i z hz
    by_contra hne
    exact hw (Or.inr (Or.inr (Or.inl ⟨z,(i,s i),hne,a i,hz,ha i⟩)))
  refine ⟨s,a,ha,huniq,?_⟩
  intro i j hij
  have hh := huniq i (j,s j) (by rw [ha j,hij])
  exact (Prod.mk.inj hh).1.symm

lemma goodPaths_finite (k r : ℕ) :
    {w : Fin r × Fin (time k) → Increment | w ∉ stageBad k r}.Finite := by
  classical
  let E : StageAlphabet k × Bool → Increment := fun a => (stageEmbedding k a.1,a.2)
  have hf : (Set.pi Set.univ (fun _ : Fin r × Fin (time k) => Set.range E)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_range E)
  apply hf.subset
  intro w hw i _
  obtain ⟨a,ha⟩ := goodPath_label_in_range w hw i
  exact ⟨(a,(w i).2),Prod.ext ha rfl⟩

lemma boundedWords_finite (r N : ℕ) :
    {q : FreeGroup (Fin r) | q ≠ 1 ∧ q.toWord.length ≤ N}.Finite := by
  classical
  apply ((List.finite_length_le (Fin r × Bool) N).preimage FreeGroup.toWord_injective.injOn).subset
  intro q hq
  exact hq.2

end HochschildRare
end

end OAI
