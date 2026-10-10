import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval

namespace TriangularCovering.AngularSampling

def nodeAlpha (q : ℝ) : ℝ := (1 + q^2) / 4
def nodeBeta (q : ℝ) : ℝ := q / 2
def nodeSpeed (q : ℝ) : ℝ := (nodeAlpha q)^2 + 2 * (nodeBeta q)^2

def sampleTerm (ε a b q : ℝ) : ℝ :=
  (b-a) * (1/2 + ε^2 * (η + d q))^2 /
    Real.sqrt (1 + ε^2 * nodeSpeed q)

lemma node_bounds {q : ℝ} (hq : |q| ≤ 1) :
    0 ≤ nodeAlpha q ∧ nodeAlpha q ≤ 1/2 ∧ |nodeBeta q| ≤ 1/2 ∧
    0 ≤ nodeSpeed q ∧ nodeSpeed q ≤ 1 := by
  have hq2 : q^2 ≤ 1 := by nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have ha0 : 0 ≤ nodeAlpha q := by unfold nodeAlpha; positivity
  have ha1 : nodeAlpha q ≤ 1/2 := by unfold nodeAlpha; linarith only [hq2]
  have hb : |nodeBeta q| ≤ 1/2 := by
    unfold nodeBeta
    rw [abs_div]
    norm_num
    linarith only [hq]
  refine ⟨ha0, ha1, hb, ?_, ?_⟩
  · unfold nodeSpeed; positivity
  · have ha2 : (nodeAlpha q)^2 ≤ 1/4 := by nlinarith only [ha0, ha1]
    have hb2 : (nodeBeta q)^2 ≤ 1/4 := by
      nlinarith only [(abs_le.mp hb).1, (abs_le.mp hb).2]
    unfold nodeSpeed
    linarith only [ha2, hb2]

lemma nodeAlpha_lipschitz {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |nodeAlpha p - nodeAlpha q| ≤ |p-q|/2 := by
  have hsum : |p+q| ≤ 2 := (abs_add_le _ _).trans (by linarith only [hp,hq])
  have heq : nodeAlpha p - nodeAlpha q = (p-q)*(p+q)/4 := by
    unfold nodeAlpha; ring
  rw [heq, abs_div, abs_mul]
  norm_num
  nlinarith only [mul_le_mul_of_nonneg_left hsum (abs_nonneg (p-q))]

lemma nodeBeta_lipschitz (p q : ℝ) :
    |nodeBeta p - nodeBeta q| = |p-q|/2 := by
  unfold nodeBeta
  rw [← sub_div, abs_div]
  norm_num

lemma density_lipschitz {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |areaDensity p - areaDensity q| ≤ 2*|p-q| := by
  have hpB := node_bounds hp
  have hqB := node_bounds hq
  have ha := sq_error (by rw [abs_of_nonneg hpB.1]; exact hpB.2.1)
    (by rw [abs_of_nonneg hqB.1]; exact hqB.2.1) (nodeAlpha_lipschitz hp hq)
  have hb := sq_error hpB.2.2.1 hqB.2.2.1 (le_of_eq (nodeBeta_lipschitz p q))
  have hs : |nodeSpeed p-nodeSpeed q| ≤ 3/2*|p-q| := by
    have hid : nodeSpeed p-nodeSpeed q =
        ((nodeAlpha p)^2-(nodeAlpha q)^2) + 2*((nodeBeta p)^2-(nodeBeta q)^2) := by
      unfold nodeSpeed; ring
    rw [hid]
    have hsum := abs_add_le ((nodeAlpha p)^2-(nodeAlpha q)^2)
      (2*((nodeBeta p)^2-(nodeBeta q)^2))
    rw [abs_mul] at hsum
    norm_num at hsum
    linarith only [hsum,ha,hb]
  have hd := d_lipschitz hp hq
  have hid : areaDensity p-areaDensity q = (d p-d q)-(nodeSpeed p-nodeSpeed q)/8 := by
    unfold areaDensity nodeSpeed nodeAlpha nodeBeta; ring
  rw [hid]
  have hsum := abs_add_le (d p-d q) (-((nodeSpeed p-nodeSpeed q)/8))
  rw [← sub_eq_add_neg,abs_neg,abs_div] at hsum
  norm_num at hsum
  linarith only [hsum,hd,hs,abs_nonneg (p-q)]

lemma sample_term_remainder {ε a b q : ℝ} (he : |ε| ≤ 1)
    (hq : |q| ≤ 1) (hab : a ≤ b) :
    |sampleTerm ε a b q - (b-a)*(1/4 + ε^2*areaDensity q)| ≤
      (b-a)*5*ε^4 := by
  have hqB := node_bounds hq
  have hd := d_bounds hq
  have hM0 : 0 ≤ η+d q := by unfold η; linarith only [hd.1]
  have hM1 : η+d q ≤ 1 := by unfold η; linarith only [hd.2]
  have he2 : ε^2 ≤ 1 := by nlinarith only [(abs_le.mp he).1,(abs_le.mp he).2]
  have h := bounded_product_remainder (sq_nonneg ε) he2 hM0 hM1 hqB.2.2.2.1 hqB.2.2.2.2
  have hid : sampleTerm ε a b q - (b-a)*(1/4+ε^2*areaDensity q) =
      (b-a)*((1/2+ε^2*(η+d q))^2 / Real.sqrt (1+ε^2*nodeSpeed q) -
        (1/4+ε^2*((η+d q)-nodeSpeed q/8))) := by
    unfold sampleTerm areaDensity nodeSpeed nodeAlpha nodeBeta; ring
  rw [hid,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    _ ≤ (b-a)*(5*(ε^2)^2) := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hab)
    _ = (b-a)*5*ε^4 := by ring

lemma sample_integral_error {a b q δ : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hq : a ≤ q ∧ q ≤ b)
    (hδ : ∀ x ∈ Icc a b, |q-x| ≤ δ) :
    |(b-a)*areaDensity q - ∫ x in a..b, areaDensity x| ≤ 2*δ*(b-a) := by
  have hab : a ≤ b := hq.1.trans hq.2
  have hqb : |q| ≤ 1 := abs_le.mpr ⟨(abs_le.mp ha).1.trans hq.1,hq.2.trans (abs_le.mp hb).2⟩
  have hu : ∀ x ∈ Ι a b, ‖areaDensity q-areaDensity x‖ ≤ 2*δ := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hxb : |x| ≤ 1 := abs_le.mpr ⟨(abs_le.mp ha).1.trans hx.1.le,hx.2.trans (abs_le.mp hb).2⟩
    rw [Real.norm_eq_abs]
    exact (density_lipschitz hqb hxb).trans (by linarith only [hδ x ⟨hx.1.le,hx.2⟩])
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hu
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => areaDensity q)
    (g := areaDensity) (continuous_const.intervalIntegrable _ _)
    (continuous_areaDensity.intervalIntegrable _ _), intervalIntegral.integral_const,
    Real.norm_eq_abs,smul_eq_mul,abs_of_nonneg (sub_nonneg.mpr hab)] at h
  nlinarith only [h]

lemma partition_width_sum (v : ℕ → ℝ) (n : ℕ) :
    (∑ j : Fin n, (v (j+1) - v j)) = v n-v 0 := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := v) (n := n) (μ := volume) (f := fun _ : ℝ => (1 : ℝ))
    (fun _ _ => continuous_const.intervalIntegrable _ _)
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫ x in v j..v (j+1), (1 : ℝ)) n] at h
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one] using h

lemma partition_density_sum (v : ℕ → ℝ) (n : ℕ)
    (h0 : v 0 = -1) (hn : v n = 1) :
    (∑ j : Fin n, ∫ x in v j..v (j+1), areaDensity x) = -13/6000 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫ x in v j..v (j+1), areaDensity x) n]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun _ _ => continuous_areaDensity.intervalIntegrable _ _),h0,hn,areaDensity_integral]

theorem sampled_sum_error {ε : ℝ} {n : ℕ} (v : ℕ → ℝ) (q : Fin n → ℝ)
    (he : |ε| ≤ 1) (h0 : v 0 = -1) (hn : v n = 1)
    (hv : ∀ j, j ≤ n → |v j| ≤ 1)
    (hq : ∀ j : Fin n, v j ≤ q j ∧ q j ≤ v (j+1))
    (hmesh : ∀ j : Fin n, ∀ x ∈ Icc (v j) (v (j+1)), |q j-x| ≤ ε^2) :
    |(∑ j : Fin n, sampleTerm ε (v j) (v (j+1)) (q j)) -
      (1/2-(13/6000:ℝ)*ε^2)| ≤ 14*ε^4 := by
  have hwidth : (∑ j : Fin n, (v (j+1)-v j)) = 2 := by
    rw [partition_width_sum,h0,hn]
    norm_num
  have hpoly : (∑ j : Fin n, ((v (j+1)-v j)/4 +
      ε^2*(∫ x in v j..v (j+1), areaDensity x))) =
      1/2-(13/6000:ℝ)*ε^2 := by
    rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum,
      hwidth,partition_density_sum v n h0 hn]
    ring
  rw [← hpoly,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin n, |sampleTerm ε (v j) (v (j+1)) (q j) -
        ((v (j+1)-v j)/4+ε^2*(∫ x in v j..v (j+1),areaDensity x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, (v (j+1)-v j)*7*ε^4 := by
      apply Finset.sum_le_sum
      intro j _
      have ha := hv j j.isLt.le
      have hb := hv (j+1) j.isLt
      have hab := (hq j).1.trans (hq j).2
      have htag : |q j| ≤ 1 :=
        abs_le.mpr ⟨(abs_le.mp ha).1.trans (hq j).1,(hq j).2.trans (abs_le.mp hb).2⟩
      have ht := sample_term_remainder he htag hab
      have hi := sample_integral_error ha hb (hq j) (hmesh j)
      have hmul : |ε^2*((v (j+1)-v j)*areaDensity (q j)-
          ∫ x in v j..v (j+1),areaDensity x)| ≤
          ε^2*(2*ε^2*(v (j+1)-v j)) := by
        rw [abs_mul,abs_of_nonneg (sq_nonneg ε)]
        exact mul_le_mul_of_nonneg_left hi (sq_nonneg ε)
      have hid : sampleTerm ε (v j) (v (j+1)) (q j) -
          ((v (j+1)-v j)/4+ε^2*(∫ x in v j..v (j+1),areaDensity x)) =
          (sampleTerm ε (v j) (v (j+1)) (q j)-
            (v (j+1)-v j)*(1/4+ε^2*areaDensity (q j))) +
          ε^2*((v (j+1)-v j)*areaDensity (q j)-
            ∫ x in v j..v (j+1),areaDensity x) := by ring
      rw [hid]
      exact (abs_add_le _ _).trans (by nlinarith only [ht,hmul])
    _ = 14*ε^4 := by
      rw [← Finset.sum_mul,← Finset.sum_mul,hwidth]
      ring

end TriangularCovering.AngularSampling

end

end OAI
