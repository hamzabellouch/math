import Mathlib
import OAI.NumberTheory.CubicGauss.Cutoffs

namespace OAI

/-! Cube extraction for cubic operators and weighted sums over cube factors. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
open HeckeTheta

lemma norm_pow_eq (a : Eisenstein) (n : ℕ) : norm (a^n) = (norm a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

def cubicRowEnergy (S : Finset Eisenstein) (u : Eisenstein → ℂ) (m : Eisenstein) : ℝ :=
  ‖∑ b ∈ S, u b * cubicSymbol b m‖^2

lemma cubicRowEnergy_nonneg (S : Finset Eisenstein) (u : Eisenstein → ℂ) (m : Eisenstein) :
    0 ≤ cubicRowEnergy S u m := sq_nonneg _

lemma cubic_cube_row_twist (S : Finset Eisenstein) (hS : ∀ b ∈ S,primary b)
    (u : Eisenstein → ℂ) (w c t s : Eisenstein) :
    cubicRowEnergy S u (w*s*t^2*c^3) =
      cubicRowEnergy S (fun b => u b * cubicSymbol b (w*t^2*c^3)) s := by
  unfold cubicRowEnergy
  congr 2
  apply Finset.sum_congr rfl
  intro b hb
  rw [show w*s*t^2*c^3 = (w*t^2*c^3)*s by ring,cubicSymbol_mul_upper (hS b hb)]
  ring

lemma cubic_cube_row_twist_conj (S : Finset Eisenstein) (hS : ∀ b ∈ S,primary b)
    (u : Eisenstein → ℂ) (w c t s : Eisenstein) :
    cubicRowEnergy S u (w*t*s^2*c^3) =
      cubicRowEnergy S (fun b => star (u b * cubicSymbol b (w*t*c^3))) s := by
  unfold cubicRowEnergy
  have he : (∑ b ∈ S, u b * cubicSymbol b (w*t*s^2*c^3)) =
      star (∑ b ∈ S, star (u b * cubicSymbol b (w*t*c^3)) * cubicSymbol b s) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [star_mul,star_star,show w*t*s^2*c^3 = (w*t*c^3)*s^2 by ring,
      cubicSymbol_mul_upper (hS b hb),cubicSymbol_pow_upper (hS b hb),cubicSymbol_sq_eq_star (hS b hb)]
    ring
  rw [he,norm_star]

lemma cubic_twist_energy_le (S : Finset Eisenstein) (hS : ∀ b ∈ S,primary b)
    (u : Eisenstein → ℂ) (m : Eisenstein) :
    ∑ b ∈ S, ‖u b * cubicSymbol b m‖^2 ≤ ∑ b ∈ S, ‖u b‖^2 := by
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul,mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (by
    simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS b hb) m) 2)

lemma cubic_cube_box_bound (S : Finset Eisenstein) (hS : ∀ b ∈ S,primary b)
    (u : Eisenstein → ℂ) (w c t : Eisenstein) (Y K : ℝ) (hK : 0 ≤ K)
    (hop : ∀ v : Eisenstein → ℂ, ∑ s ∈ squarefreePrimaryBall Y,
      cubicRowEnergy S v s ≤ K * ∑ b ∈ S, ‖v b‖^2) :
    (∑ s ∈ squarefreePrimaryBall Y, cubicRowEnergy S u (w*s*t^2*c^3)) +
      (∑ s ∈ squarefreePrimaryBall Y, cubicRowEnergy S u (w*t*s^2*c^3)) ≤
        2*K*∑ b ∈ S, ‖u b‖^2 := by
  simp_rw [cubic_cube_row_twist S hS u w c t,
    cubic_cube_row_twist_conj S hS u w c t]
  have h1 := (hop (fun b => u b * cubicSymbol b (w*t^2*c^3))).trans
    (mul_le_mul_of_nonneg_left (cubic_twist_energy_le S hS u _) hK)
  have h2 := hop (fun b => star (u b * cubicSymbol b (w*t*c^3)))
  simp only [norm_star] at h2
  have h2 := h2.trans (mul_le_mul_of_nonneg_left (cubic_twist_energy_le S hS u _) hK)
  linarith

abbrev CubeIndex := Σ _w : Eisenstein, Σ _c : Eisenstein, Σ _t : Eisenstein, Eisenstein

def cubeIndices (X : ℝ) : Finset CubeIndex :=
  (nonzeroNormBall 9).sigma fun _w =>
    (nonzeroNormBall (X^(1/3:ℝ))).sigma fun c =>
      (squarefreePrimaryBall (X^(1/3:ℝ)/norm c)).sigma fun t =>
        squarefreePrimaryBall (X / ((norm t)^2*(norm c)^3))

def cubeMap₁ (v : CubeIndex) : Eisenstein := v.1 * v.2.2.2 * v.2.2.1^2 * v.2.1^3
def cubeMap₂ (v : CubeIndex) : Eisenstein := v.1 * v.2.2.1 * v.2.2.2^2 * v.2.1^3

lemma cube_parameter_bounds {X a b c : ℝ} (hX : 0 ≤ X) (_ : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hab : b ≤ a) (hprod : a*b^2*c^3 ≤ X) :
    c ≤ X^(1/3:ℝ) ∧ b ≤ X^(1/3:ℝ)/c ∧ a ≤ X/(b^2*c^3) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hd : 0 < b^2*c^3 := by positivity
  have hbc : (b*c)^3 ≤ X := by
    calc
      _ = b*b^2*c^3 := by ring
      _ ≤ a*b^2*c^3 := by gcongr
      _ ≤ X := hprod
  have hrt : b*c ≤ X^(1/3:ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by positivity : 0 ≤ b*c) hX (by norm_num : (0:ℝ)<3)).mpr
    simpa only [show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast] using hbc
  exact ⟨(le_mul_of_one_le_left hc0.le hb).trans hrt,
    (le_div_iff₀ hc0).mpr hrt,(le_div_iff₀ hd).mpr (by simpa [mul_assoc] using hprod)⟩

lemma nonzero_ball_subset_cube_images {X : ℝ} (hX : 1 ≤ X) :
    nonzeroNormBall X ⊆ (cubeIndices X).image cubeMap₁ ∪ (cubeIndices X).image cubeMap₂ := by
  intro n hn
  obtain ⟨hnX,hn0⟩ := mem_nonzeroNormBall.mp hn
  obtain ⟨u,i,s,t,c,hi,hs,ht,hss,htt,hst,hc,he⟩ := full_cube_decomposition_unit hn0
  let w : Eisenstein := u * lambdaE^i
  have hw0 : w ≠ 0 := mul_ne_zero u.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have hnw : norm w = (3:ℝ)^i := by
    rw [norm_mul_eq,norm_of_isUnit u.isUnit,norm_pow_eq,norm_lambdaE,one_mul]
  have nw : w ∈ nonzeroNormBall 9 := mem_nonzeroNormBall.mpr ⟨by
    rw [hnw]; interval_cases i <;> norm_num,hw0⟩
  have hnprod : norm s*(norm t)^2*(norm c)^3 ≤ X := by
    have hnorm : norm n = norm w * (norm s*(norm t)^2*(norm c)^3) := by
      rw [he]
      simp only [norm_mul_eq,norm_pow_eq,w]
      ring
    have hle : norm s*(norm t)^2*(norm c)^3 ≤ norm n := by
      rw [hnorm]
      exact le_mul_of_one_le_left
        (mul_nonneg (mul_nonneg (norm_nonneg s) (sq_nonneg _)) (pow_nonneg (norm_nonneg c) 3))
        (one_le_norm hw0)
    exact hle.trans hnX
  have hs1 := one_le_norm (primary_ne_zero hs)
  have ht1 := one_le_norm (primary_ne_zero ht)
  have hc1 := one_le_norm hc
  by_cases hts : norm t ≤ norm s
  · obtain ⟨hcX,htX,hsX⟩ := cube_parameter_bounds (by linarith) hs1 ht1 hc1 hts hnprod
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨⟨w,c,t,s⟩,?_,he.symm⟩
    simp only [cubeIndices,Finset.mem_sigma]
    exact ⟨nw,mem_nonzeroNormBall.mpr ⟨hcX,hc⟩,
      mem_squarefreePrimaryBall.mpr ⟨ht,htt,htX⟩,
      mem_squarefreePrimaryBall.mpr ⟨hs,hss,hsX⟩⟩
  · have hst' : norm s ≤ norm t := (lt_of_not_ge hts).le
    have hprod' : norm t*(norm s)^2*(norm c)^3 ≤ X := by
      apply le_trans _ hnprod
      have : norm s*norm t*(norm s) ≤ norm s*norm t*(norm t) := by gcongr
      nlinarith [mul_le_mul_of_nonneg_right this (pow_nonneg (norm_nonneg c) 3)]
    obtain ⟨hcX,hsX,htX⟩ := cube_parameter_bounds (by linarith) ht1 hs1 hc1 hst' hprod'
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨⟨w,c,s,t⟩,?_,he.symm⟩
    simp only [cubeIndices,Finset.mem_sigma]
    exact ⟨nw,mem_nonzeroNormBall.mpr ⟨hcX,hc⟩,
      mem_squarefreePrimaryBall.mpr ⟨hs,hss,hsX⟩,
      mem_squarefreePrimaryBall.mpr ⟨ht,htt,htX⟩⟩

lemma cubic_full_cube_sum_le {X : ℝ} (hX : 1 ≤ X)
    (S : Finset Eisenstein) (u : Eisenstein → ℂ) :
    ∑ m ∈ nonzeroNormBall X, cubicRowEnergy S u m ≤
      ∑ w ∈ nonzeroNormBall 9, ∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),
        ∑ t ∈ squarefreePrimaryBall (X^(1/3:ℝ)/norm c),
          ((∑ s ∈ squarefreePrimaryBall (X/((norm t)^2*(norm c)^3)),
              cubicRowEnergy S u (w*s*t^2*c^3)) +
           (∑ s ∈ squarefreePrimaryBall (X/((norm t)^2*(norm c)^3)),
              cubicRowEnergy S u (w*t*s^2*c^3))) := by
  let f := cubicRowEnergy S u
  let I := cubeIndices X
  have hn (m : Eisenstein) : 0 ≤ f m := cubicRowEnergy_nonneg S u m
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg
    (nonzero_ball_subset_cube_images hX) (fun m _ _ => hn m)
  have h2 : ∑ m ∈ I.image cubeMap₁ ∪ I.image cubeMap₂, f m ≤
      (∑ m ∈ I.image cubeMap₁, f m) + (∑ m ∈ I.image cubeMap₂, f m) := by
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => hn m))
  have h3 := add_le_add
    (Finset.sum_image_le_of_nonneg (s := I) (g := cubeMap₁) (fun m _ => hn m))
    (Finset.sum_image_le_of_nonneg (s := I) (g := cubeMap₂) (fun m _ => hn m))
  apply (h1.trans h2).trans
  convert h3 using 1
  simp only [I,cubeIndices,Finset.sum_sigma,cubeMap₁,cubeMap₂,Finset.sum_add_distrib,f]

theorem cubic_full_cube_bound {X : ℝ} (hX : 1 ≤ X)
    (S : Finset Eisenstein) (hS : ∀ b ∈ S,primary b) (u : Eisenstein → ℂ)
    (K : ℝ → ℝ) (hK : ∀ Y, 0 ≤ K Y)
    (hop : ∀ (Y : ℝ) (v : Eisenstein → ℂ),
      ∑ s ∈ squarefreePrimaryBall Y, cubicRowEnergy S v s ≤
        K Y * ∑ b ∈ S, ‖v b‖^2) :
    ∑ m ∈ nonzeroNormBall X, cubicRowEnergy S u m ≤
      2 * ((nonzeroNormBall 9).card : ℝ) *
        (∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),
          ∑ t ∈ squarefreePrimaryBall (X^(1/3:ℝ)/norm c),
             K (X/((norm t)^2*(norm c)^3))) * ∑ b ∈ S, ‖u b‖^2 := by
  apply (cubic_full_cube_sum_le hX S u).trans
  have hb := Finset.sum_le_sum (s := nonzeroNormBall 9) (fun w _ =>
    Finset.sum_le_sum (s := nonzeroNormBall (X^(1/3:ℝ))) (fun c _ =>
      Finset.sum_le_sum (s := squarefreePrimaryBall (X^(1/3:ℝ)/norm c)) (fun t _ =>
        cubic_cube_box_bound S hS u w c t (X/((norm t)^2*(norm c)^3)) _ (hK _) (hop _))))
  convert hb using 1
  simp only [← Finset.mul_sum,← Finset.sum_mul,Finset.sum_const, nsmul_eq_mul]
  ring

end CubicFirstMoment

namespace CubicFirstMoment

def latticeZeta (r : ℝ) : ℝ := ∑' a : Eisenstein,(norm a)^(-r)

lemma latticeZeta_nonneg (r : ℝ) : 0 ≤ latticeZeta r :=
  tsum_nonneg fun a => Real.rpow_nonneg (norm_nonneg a) _

lemma latticeZeta_pos {r : ℝ} (hr : 1<r) : 0<latticeZeta r := by
  have hs := HeckeTheta.lattice_norm_rpow_summable r hr
  have hle := hs.le_tsum (1:Eisenstein) (fun a _ => Real.rpow_nonneg (norm_nonneg a) _)
  have he : (norm (1:Eisenstein))^(-r) = 1 := by simp
  change 0 < ∑' a : Eisenstein,(norm a)^(-r)
  linarith

lemma norm_rpow_finset_le (S : Finset Eisenstein) {r : ℝ} (hr : 1<r) :
    ∑ a ∈ S,(norm a)^(-r) ≤ latticeZeta r :=
  Summable.sum_le_tsum S (fun a _ => Real.rpow_nonneg (norm_nonneg a) _)
    (HeckeTheta.lattice_norm_rpow_summable r hr)

lemma quotient_norm_rpow {X a b p : ℝ} (hX : 0≤X) (ha : 0<a) (hb : 0<b) :
    (X/(a^2*b^3))^p = X^p*a^(-(2*p))*b^(-(3*p)) := by
  rw [Real.div_rpow hX (by positivity),Real.mul_rpow (by positivity) (by positivity)]
  have he2 : (a^2)^p = a^(2*p) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ha.le]
    norm_num
  have he3 : (b^3)^p = b^(3*p) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hb.le]
    norm_num
  rw [he2,he3,Real.rpow_neg ha.le,Real.rpow_neg hb.le]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma cube_rpow_sum_bound {X p : ℝ} (hX : 0≤X) (hp : (2/3:ℝ)≤p) :
    (∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),
      ∑ t ∈ squarefreePrimaryBall (X^(1/3:ℝ)/norm c),
        (X/((norm t)^2*(norm c)^3))^p) ≤ X^p*(latticeZeta (4/3))^2 := by
  have hZ := latticeZeta_nonneg (4/3)
  calc
    _ ≤ ∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),
        ∑ t ∈ squarefreePrimaryBall (X^(1/3:ℝ)/norm c),
          X^p*(norm t)^(-(4/3:ℝ))*(norm c)^(-(4/3:ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      have hc0 := (mem_nonzeroNormBall.mp hc).2
      have hc1 := one_le_norm hc0
      apply Finset.sum_le_sum
      intro t ht
      have ht0 := primary_ne_zero (mem_squarefreePrimaryBall.mp ht).1
      have ht1 := one_le_norm ht0
      rw [quotient_norm_rpow hX (norm_pos_of_ne_zero ht0) (norm_pos_of_ne_zero hc0)]
      gcongr <;> linarith
    _ ≤ ∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),
        X^p*latticeZeta (4/3)*(norm c)^(-(4/3:ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      rw [← Finset.sum_mul,← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_rpow_finset_le _ (by norm_num : (1:ℝ)<4/3))
          (Real.rpow_nonneg hX _)) (Real.rpow_nonneg (norm_nonneg c) _)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply (mul_le_mul_of_nonneg_left (norm_rpow_finset_le _ (by norm_num : (1:ℝ)<4/3))
        (mul_nonneg (Real.rpow_nonneg hX _) hZ)).trans_eq
      ring

lemma squarefreePrimaryBall_card_le {Y : ℝ} (hY : 0≤Y) :
    ((squarefreePrimaryBall Y).card:ℝ) ≤ 18*Y := by
  apply le_trans _ (nonzeroNormBall_card_le hY)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

lemma norm_reciprocal_sum_bound {R δ : ℝ} (hR : 0<R) (hδ : 0<δ) :
    ∑ c ∈ nonzeroNormBall R,1/norm c ≤ R^δ*latticeZeta (1+δ) := by
  calc
    _ ≤ ∑ c ∈ nonzeroNormBall R,R^δ*(norm c)^(-(1+δ)) := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨hcR,hc0⟩ := mem_nonzeroNormBall.mp hc
      have hcpos := norm_pos_of_ne_zero hc0
      have he : 1/norm c = (norm c)^δ*(norm c)^(-(1+δ)) := by
        rw [← Real.rpow_add hcpos]
        rw [show δ+ -(1+δ) = (-1:ℝ) by ring,Real.rpow_neg_one]
        exact one_div _
      rw [he]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hcpos.le hcR hδ.le)
        (Real.rpow_nonneg hcpos.le _)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_rpow_finset_le _ (by linarith)) (Real.rpow_nonneg hR.le _)

lemma cube_pair_count_bound {X δ : ℝ} (hX : 1≤X) (hδ : 0<δ) :
    (∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),
      ((squarefreePrimaryBall (X^(1/3:ℝ)/norm c)).card:ℝ)) ≤
        18*latticeZeta (1+δ)*X^(1/3+δ) := by
  have hX0 : 0<X := by linarith
  have hR : 0<X^(1/3:ℝ) := Real.rpow_pos_of_pos hX0 _
  have hRX : X^(1/3:ℝ) ≤ X := Real.rpow_le_self_of_one_le hX (by norm_num)
  calc
    _ ≤ ∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),18*X^(1/3:ℝ)*(1/norm c) := by
      apply Finset.sum_le_sum
      intro c hc
      have hc0 := norm_pos_of_ne_zero (mem_nonzeroNormBall.mp hc).2
      simpa [div_eq_mul_inv,mul_assoc] using squarefreePrimaryBall_card_le
        (div_nonneg hR.le hc0.le)
    _ = 18*X^(1/3:ℝ)*∑ c ∈ nonzeroNormBall (X^(1/3:ℝ)),1/norm c := by rw [Finset.mul_sum]
    _ ≤ 18*X^(1/3:ℝ)*((X^(1/3:ℝ))^δ*latticeZeta (1+δ)) :=
      mul_le_mul_of_nonneg_left (norm_reciprocal_sum_bound hR hδ) (by positivity)
    _ ≤ 18*X^(1/3:ℝ)*(X^δ*latticeZeta (1+δ)) := by
      have hZ := latticeZeta_nonneg (1+δ)
      gcongr
    _ = _ := by rw [Real.rpow_add hX0]; ring

end CubicFirstMoment
end

end OAI
