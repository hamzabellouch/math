import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevTail02
import OAI.Combinatorics.SumProduct.Alignment.SmoothBinomial01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
end
 

 
section
noncomputable section
namespace SmoothBinomial
open Set
 

theorem smooth_binomial_increment (j : ℕ) (A C : ℝ) (hC : 0 ≤ C) :
    ∃ B > 0, ∀ L lam : ℝ, 1 ≤ L → |L^j*lam| ≤ C →
      (∀ x : ℝ, |x| ≤ A*L → |lam*Ring.choose x j| ≤ B) ∧
      (∀ x y : ℝ, |x| ≤ A*L → |y| ≤ A*L →
        |lam*Ring.choose x j - lam*Ring.choose y j| ≤ (B/L)*|x-y|) := by
  obtain ⟨B0,hB0,hv⟩ := smooth_binomial_bounds j 0 A C hC
  obtain ⟨B1,hB1,hd⟩ := smooth_binomial_bounds j 1 A C hC
  refine ⟨B0+B1,by positivity,?_⟩
  intro L lam hL hlam
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdiff : Differentiable ℝ (fun x : ℝ => lam*Ring.choose x j) := by
    simp only [choose_eq_product]
    fun_prop
  constructor
  · intro x hx
    have he := hv L lam hL hlam x hx
    simp only [iteratedDeriv_zero,pow_zero,div_one] at he
    linarith
  · intro x y hx hy
    have hbound : ∀ z ∈ Icc (- (A*L)) (A*L), ‖deriv (fun w : ℝ => lam*Ring.choose w j) z‖ ≤ B1/L := by
      intro z hz
      simpa using hd L lam hL hlam z (abs_le.mpr hz)
    have he := Convex.norm_image_sub_le_of_norm_deriv_le (fun z _ => hdiff z)
      hbound (convex_Icc (- (A*L)) (A*L)) (abs_le.mp hy) (abs_le.mp hx)
    change |lam*Ring.choose x j - lam*Ring.choose y j| ≤ (B1/L)*|x-y| at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) hLp.le) (abs_nonneg _))

end SmoothBinomial
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace MalcevTailSection
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n l : ℕ}
variable (c : RealCoordinates G n) (k : Fin n → ℤ) (r : Fin l → ℕ) (j : Fin l → ℕ)

 

lemma binomial_parameters_bounds (A C : ℝ) (hC : 0 ≤ C) :
    ∃ U > 0, ∀ L : ℝ, ∀ lam : Fin l → ℝ, 1 ≤ L → (∀ i, |L^(j i)*lam i| ≤ C) →
      (∀ x : ℝ, |x| ≤ A*L → ‖fun i => lam i*Ring.choose x (j i)‖ ≤ U) ∧
      (∀ x y : ℝ, |x| ≤ A*L → |y| ≤ A*L →
        ‖(fun i => lam i*Ring.choose x (j i))-(fun i => lam i*Ring.choose y (j i))‖ ≤ (U/L)*|x-y|) := by
  classical
  choose b hb hh using (fun i => SmoothBinomial.smooth_binomial_increment (j i) A C hC)
  let U := (∑ i, b i)+1
  have hU : 0 < U := by
    have he : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => (hb i).le)
    dsimp [U]
    linarith
  have hbU (i : Fin l) : b i ≤ U := by
    have he := Finset.single_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin l))) => (hb t).le) (Finset.mem_univ i)
    dsimp [U]
    linarith
  refine ⟨U,hU,?_⟩
  intro L lam hL hlam
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · intro x hx
    apply (pi_norm_le_iff_of_nonneg hU.le).mpr
    intro i
    exact ((hh i L (lam i) hL (hlam i)).1 x hx).trans (hbU i)
  · intro x y hx hy
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact ((hh i L (lam i) hL (hlam i)).2 x y hx hy).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hbU i) hLp.le) (abs_nonneg _))

 

omit [IsTopologicalGroup G] in
theorem smooth_word_bounds (A C : ℝ) (hC : 0 ≤ C) :
    ∃ B > 0, ∀ L : ℝ, ∀ lam : Fin l → ℝ, 1 ≤ L → (∀ i, |L^(j i)*lam i| ≤ C) →
      (∀ x : ℝ, |x| ≤ A*L →
        ‖c.coord (flowWord c k r (fun i => lam i*Ring.choose x (j i)))‖ ≤ B) ∧
      (∀ x y : ℝ, |x| ≤ A*L → |y| ≤ A*L →
        ‖c.coord (flowWord c k r (fun i => lam i*Ring.choose x (j i))) -
          c.coord (flowWord c k r (fun i => lam i*Ring.choose y (j i)))‖ ≤ (B/L)*|x-y|) := by
  obtain ⟨U,hU,hu⟩ := binomial_parameters_bounds j A C hC
  obtain ⟨M,hM,hm,hd⟩ := flowWord_bounds c k r U
  refine ⟨M*(U+1),by positivity,?_⟩
  intro L lam hL hlam
  obtain ⟨hv,he⟩ := hu L lam hL hlam
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · intro x hx
    exact (hm _ (hv x hx)).trans (by nlinarith)
  · intro x y hx hy
    have h1 := hd _ _ (hv x hx) (hv y hy)
    have h2 := mul_le_mul_of_nonneg_left (he x y hx hy) hM.le
    apply h1.trans (h2.trans _)
    have h3 : M*U ≤ M*(U+1) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h3 hLp.le) (abs_nonneg (x-y))
    convert h4 using 1; ring

end MalcevTailSection
end
end
 

 
section
noncomputable section
namespace MalcevTailSection
open RationalLattice RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n l : ℕ}
variable (c : RealCoordinates G n) (k : Fin n → ℤ) (r : Fin l → ℕ)

def flowDifference (t : (Fin l ⊕ Fin l) → ℝ) : G :=
  flowWord c k r (fun i => t (Sum.inl i)) * (flowWord c k r (fun i => t (Sum.inr i)))⁻¹

omit [IsTopologicalGroup G] in
lemma polynomialMap_flowDifference : IsPolynomialMap c (flowDifference c k r) := by
  apply polynomialMap_mul
  · exact polynomialMap_comp c (polynomialMap_flowWord c k r) (fun i => RationalPolynomialMap.coordinate (Sum.inl i))
  · apply polynomialMap_inv
    exact polynomialMap_comp c (polynomialMap_flowWord c k r) (fun i => RationalPolynomialMap.coordinate (Sum.inr i))

omit [IsTopologicalGroup G] in
lemma flowDifference_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => c.coord (flowDifference c k r x)) := by
  apply contDiff_pi.mpr
  intro i
  exact RationalPolynomialMap.contDiff (polynomialMap_flowDifference c k r i)

 

omit [IsTopologicalGroup G] in
theorem flow_displacement_bounds (R : ℝ) :
    ∃ M > 0, ∀ x y : Fin l → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖c.coord (flowWord c k r x * (flowWord c k r y)⁻¹)‖ ≤ M*‖x-y‖ := by
  have hd := flowDifference_contDiff c k r
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : (Fin l ⊕ Fin l) → ℝ) R).exists_bound_of_continuousOn
    (hd.continuous_fderiv (by simp)).continuousOn
  refine ⟨max D 0+1,by positivity,?_⟩
  intro x y hx hy
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have hb (u v : Fin l → ℝ) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) : ‖Sum.elim u v‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    cases i with
    | inl i => exact (norm_le_pi_norm u i).trans hu
    | inr i => exact (norm_le_pi_norm v i).trans hv
  have hdiff : ‖Sum.elim x y - Sum.elim y y‖ ≤ ‖x-y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    cases i with
    | inl i => exact norm_le_pi_norm (x-y) i
    | inr i => simp
  have hid : c.coord (flowDifference c k r (Sum.elim y y)) = 0 := by
    funext i
    simp only [flowDifference,Sum.elim_inl,Sum.elim_inr,mul_inv_cancel,c.one_coord,Pi.zero_apply]
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x (_ : x ∈ Metric.closedBall (0 : (Fin l ⊕ Fin l) → ℝ) R) => hd.differentiable (by simp) x)
    (fun x hx => (hD x hx).trans (show D ≤ max D 0+1 by grind))
    (convex_closedBall (0 : (Fin l ⊕ Fin l) → ℝ) R)
    (by simpa using hb y y hy hy) (by simpa using hb x y hx hy)
  rw [hid,sub_zero] at he
  exact he.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))

end MalcevTailSection
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace MalcevTailSection
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n l : ℕ}
variable (c : RealCoordinates G n) (k : Fin n → ℤ) (r : Fin l → ℕ) (j : Fin l → ℕ)

 

omit [IsTopologicalGroup G] in
theorem smooth_word_displacement (A C : ℝ) (hC : 0 ≤ C) :
    ∃ B > 0, ∀ L : ℝ, ∀ lam : Fin l → ℝ, 1 ≤ L → (∀ i, |L^(j i)*lam i| ≤ C) →
      ∀ x y : ℝ, |x| ≤ A*L → |y| ≤ A*L →
        ‖c.coord (flowWord c k r (fun i => lam i*Ring.choose x (j i)) *
          (flowWord c k r (fun i => lam i*Ring.choose y (j i)))⁻¹)‖ ≤ (B/L)*|x-y| := by
  obtain ⟨U,hU,hu⟩ := binomial_parameters_bounds j A C hC
  obtain ⟨M,hM,hm⟩ := flow_displacement_bounds c k r U
  refine ⟨M*U,by positivity,?_⟩
  intro L lam hL hlam x y hx hy
  obtain ⟨hv,he⟩ := hu L lam hL hlam
  have h1 := hm _ _ (hv x hx) (hv y hy)
  have h2 := mul_le_mul_of_nonneg_left (he x y hx hy) hM.le
  apply h1.trans
  convert h2 using 1; ring

end MalcevTailSection

namespace MalcevTailFactor
open RationalLattice RationalFactorPeriods MalcevCharacters MalcevTailSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n l : ℕ}
variable (c : RealCoordinates G n) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (k : Fin n → ℤ) (r : Fin l → ℕ) (j : Fin l → ℕ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma error_abs (a : Fin l → G) (i : Fin l) :
    |error χ a i| = ‖(beta χ a i : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  rfl

include hsk in
 

omit [IsTopologicalGroup G] in
theorem small_word_smooth (A C : ℝ) (hC : 0 ≤ C) :
    ∃ B > 0, ∀ L : ℝ, ∀ a : Fin l → G, 1 ≤ L →
      (∀ i, L^(j i)*‖(beta χ a i : UnitAddCircle)‖ ≤ C) →
      (∀ z : ℤ, |(z:ℝ)| ≤ A*L →
        ‖c.coord (orderedWord (smallCoeff c χ k r a) j z)‖ ≤ B) ∧
      (∀ z w : ℤ, |(z:ℝ)| ≤ A*L → |(w:ℝ)| ≤ A*L →
        ‖c.coord (orderedWord (smallCoeff c χ k r a) j z *
          (orderedWord (smallCoeff c χ k r a) j w)⁻¹)‖ ≤ (B/L)*|(z:ℝ)-(w:ℝ)|) := by
  obtain ⟨B,hB,hb⟩ := smooth_word_bounds c k r j A C hC
  obtain ⟨D,hD,hd⟩ := smooth_word_displacement c k r j A C hC
  refine ⟨B+D,by positivity,?_⟩
  intro L a hL ha
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have he : ∀ i, |L^(j i)*error χ a i| ≤ C := by
    intro i
    rw [abs_mul,abs_of_nonneg (pow_nonneg hLp.le _),error_abs]
    exact ha i
  have hv (z : ℤ) : flowWord c k r (fun i => error χ a i*Ring.choose (z:ℝ) (j i)) =
      orderedWord (smallCoeff c χ k r a) j z := flowWord_integer c k r hsk _ j z
  constructor
  · intro z hz
    rw [← hv z]
    exact ((hb L _ hL he).1 z hz).trans (by linarith)
  · intro z w hz hw
    rw [← hv z,← hv w]
    exact (hd L _ hL he z w hz hw).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hLp.le) (abs_nonneg _))

end MalcevTailFactor

end
end
end
end
end

end OAI
