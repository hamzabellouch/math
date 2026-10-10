import OAI.Combinatorics.HoneycombChords.Resolvents
import OAI.Combinatorics.HoneycombChords.StripPolynomial
import OAI.Combinatorics.HoneycombChords.FamilyGram

namespace OAI

/-!
# Polynomial characteristic products for the strip density

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Real MeasureTheory Filter Topology
lemma squaredPoleDensity_moments {z : ℝ} (hz : 0 < z) (k : ℕ) :
    IntegrableOn (fun p : ℝ=>p^k*squaredPoleDensity z p) (Set.Ioi 0) := by
  obtain ⟨A,hA,h⟩:=squaredPoleDensity_bounds hz (le_refl z)
  have hb : 0 < 3*angle := by unfold angle;positivity
  apply ((pow_sech_integrable k hb).const_mul A).mono'
  · exact (by unfold squaredPoleDensity stripDensity;fun_prop : Measurable (fun p : ℝ=>p^k*squaredPoleDensity z p)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hp.le k) (squaredPoleDensity_pos hz hp).le)]
    have hh:=mul_le_mul_of_nonneg_left (h p hp).2 (pow_nonneg hp.le k)
    exact hh.trans_eq (by ring)
/-- Christoffel estimates for the strip measure divided by `(x + z²)²`. -/
theorem stripPolynomialChristoffel_bounds {z y : ℝ} (hz : 0 < z) (hy : 0 < y) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(3*y/4) ≤ weightedPolynomialChristoffel (squaredPoleDensity z) n (-(y^2)) ∧
      weightedPolynomialChristoffel (squaredPoleDensity z) n (-(y^2)) ≤ C*((n:ℝ)+1)^(3*y/4) := by
  let b : ℝ := 3*angle
  have hb : 0 < b := by dsimp [b];unfold angle;positivity
  let Y : ℝ := z+y+2*Real.pi/b
  have hY : 0 < Y := by dsimp [Y];positivity
  have hzY : z ≤ Y := by
    dsimp [Y]
    have hh : 0 < 2*Real.pi/b := by positivity
    linarith
  have hgap : b*y/Real.pi+1 < b*Y/Real.pi := by
    dsimp [Y]
    have he : b*(z+y+2*Real.pi/b)/Real.pi=b*z/Real.pi+b*y/Real.pi+2 := by field_simp
    rw [he]
    have hp : 0 < b*z/Real.pi := by positivity
    linarith
  have hexp : 2*b*y/Real.pi=3*y/4 := by dsimp [b];unfold angle;field_simp;ring
  obtain ⟨A,hA,hweight⟩:=squaredPoleDensity_bounds hz hzY
  let d : ℝ := 2*b/Real.pi
  have hd : 0 < d := by dsimp [d];positivity
  let l : ℝ := (1/(8*angle))/d
  have hl : 0 < l := by dsimp [l,d,b];unfold angle;positivity
  let u : ℝ := d/A
  have hu : 0 < u := by dsimp [u];positivity
  have hlow (p : ℝ) (hp : 0 < p) : l*rationalSechWeight b Y p ≤ squaredPoleDensity z p := by
    have he : l*rationalSechWeight b Y p=(1/(8*angle))/((p^2+Y^2)^2*Real.cosh (3*angle*p)) := by
      dsimp [l,d,rationalSechWeight,sechWeight,b]
      field_simp
    rw [he]
    exact (hweight p hp).1
  have hupp (p : ℝ) (hp : 0 < p) : u*squaredPoleDensity z p ≤ sechWeight b p := by
    have h:=mul_le_mul_of_nonneg_left (hweight p hp).2 hu.le
    have he : u*(A/Real.cosh (3*angle*p))=sechWeight b p := by dsimp [u,d,sechWeight,b];field_simp
    rwa [he] at h
  obtain ⟨a₀,C₀,ha₀,hC₀,hsech⟩:=scaledPolynomialChristoffel_bounds hb hy
  obtain ⟨C₁,hC₁,hrat⟩:=weightedKernel_rationalSech_upper hb hY hy hgap
  refine ⟨u*a₀,C₁/l,by positivity,by positivity,?_⟩
  filter_upwards [hsech,hrat] with n hn hn'
  have hcL:=weightedPolynomialChristoffel_comparison n (-(y^2)) hu
    (fun p hp=>squaredPoleDensity_pos hz hp) (fun p _=>sechWeight_pos hb p)
    (squaredPoleDensity_moments hz) (sechWeight_moments hb) hupp
  have hcU:=weightedPolynomialChristoffel_comparison n (-(y^2)) hl
    (fun p _=>rationalSechWeight_pos hb hY p) (fun p hp=>squaredPoleDensity_pos hz hp)
    (rationalSechWeight_moments hb hY) (squaredPoleDensity_moments hz) hlow
  rw [weightedKernel_sech] at hcL
  rw [hexp] at hn hn'
  constructor
  · have h := (le_div_iff₀ hu).mp (hn.1.trans hcL)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  · exact hcU.trans (by simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hn' hl.le)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset MeasureTheory Filter Topology
lemma polynomial_compression_ratio (n : ℕ) (a b : ℝ) (w : ℝ → ℝ)
    (hw : ∀ p,0 < p → 0 < w p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) :
    (monomialGram n (fun p=>(p^2-a)^2*w p)).det /
      (monomialGram n (fun p=>(p^2-b)^2*w p)).det =
      weightedPolynomialChristoffel w n a / weightedPolynomialChristoffel w n b := by
  rw [weightedPolynomialChristoffel_eq n a w hw hi,
      weightedPolynomialChristoffel_eq n b w hw hi,
      ←polynomial_compression_cofactor n a w hi,
      ←polynomial_compression_cofactor n b w hi]
  exact (div_div_div_cancel_right₀ (ne_of_gt (monomialGram_posDef (n+1) w hw hi).det_pos) _ _).symm
lemma squaredPole_restore {z : ℝ} (hz : 0 < z) :
    (fun p : ℝ=>(p^2-(-(z^2)))^2*squaredPoleDensity z p)=stripDensity := by
  funext p
  have hd : p^2+z^2 ≠ 0 := ne_of_gt (by positivity)
  dsimp [squaredPoleDensity]
  field_simp; ring
lemma squaredPole_tilt (y z : ℝ) :
    (fun p : ℝ=>(p^2-(-(y^2)))^2*squaredPoleDensity z p)=
      (fun p=>characteristicRatio y z p^2*stripDensity p) := by
  funext p
  dsimp [squaredPoleDensity,characteristicRatio]
  rw [div_pow]
  ring
/-- Exact square-product identity, with the actual strip measure. -/
theorem strip_polynomial_square_product (n : ℕ) {y z : ℝ} (hz : 0 < z) :
    (monomialGram n (fun p=>characteristicRatio y z p^2*stripDensity p)).det /
      (monomialGram n stripDensity).det =
      weightedPolynomialChristoffel (squaredPoleDensity z) n (-(y^2)) /
      weightedPolynomialChristoffel (squaredPoleDensity z) n (-(z^2)) := by
  have h:=polynomial_compression_ratio n (-(y^2)) (-(z^2)) (squaredPoleDensity z)
    (fun p hp=>squaredPoleDensity_pos hz hp) (squaredPoleDensity_moments hz)
  rwa [squaredPole_restore hz,squaredPole_tilt] at h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Filter Topology
lemma characteristicRatio_pos {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (p : ℝ) :
    0 < characteristicRatio y z p := by unfold characteristicRatio;positivity
lemma characteristicRatio_bounds (y : ℝ) {z : ℝ} (hz : 0 < z) (p : ℝ) :
    min 1 (y^2/z^2) ≤ characteristicRatio y z p ∧
    characteristicRatio y z p ≤ max 1 (y^2/z^2) := by
  have hz2 : 0 < z^2 := sq_pos_of_pos hz
  have hd : 0 < p^2+z^2 := by positivity
  have hl := (le_div_iff₀ hz2).mp (min_le_right (1:ℝ) (y^2/z^2))
  have hu := (div_le_iff₀ hz2).mp (le_max_right (1:ℝ) (y^2/z^2))
  unfold characteristicRatio
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (y^2/z^2)) (sq_nonneg p)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) (y^2/z^2)) (sq_nonneg p)]
lemma weightedPolynomial_moments_bounded (w r : ℝ → ℝ) (hw : ∀ p,0 < p → 0 ≤ w p)
    (hr : Measurable r) (hr0 : ∀ p,0 < p → 0 ≤ r p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0))
    {C : ℝ} (hb : ∀ p,0 < p → r p ≤ C) (k : ℕ) :
    IntegrableOn (fun p : ℝ=>p^k*(r p*w p)) (Set.Ioi 0) := by
  apply ((hi k).const_mul C).mono'
  · exact (hr.aestronglyMeasurable.mul (hi k).aestronglyMeasurable).congr
      (Filter.Eventually.of_forall (fun p=>by dsimp;ring))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hp.le k) (mul_nonneg (hr0 p hp) (hw p hp)))]
    nlinarith [mul_le_mul_of_nonneg_right (hb p hp) (mul_nonneg (pow_nonneg hp.le k) (hw p hp))]
lemma tilted_squaredPole_moments {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (k : ℕ) :
    IntegrableOn (fun p : ℝ=>p^k*(characteristicRatio y z p*squaredPoleDensity z p)) (Set.Ioi 0) := by
  apply weightedPolynomial_moments_bounded (squaredPoleDensity z) (characteristicRatio y z)
    (fun p hp=>(squaredPoleDensity_pos hz hp).le)
    (by unfold characteristicRatio;fun_prop)
    (fun p _=>(characteristicRatio_pos hy hz p).le) (squaredPoleDensity_moments hz)
    (fun p _=>(characteristicRatio_bounds y hz p).2)
/-- Kernel exponent is unchanged by the bounded positive characteristic tilt. -/
theorem tilted_stripPolynomialChristoffel_bounds {y z v : ℝ} (hy : 0 < y) (hz : 0 < z) (hv : 0 < v) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(3*v/4) ≤ weightedPolynomialChristoffel
        (fun p=>characteristicRatio y z p*squaredPoleDensity z p) n (-(v^2)) ∧
      weightedPolynomialChristoffel
        (fun p=>characteristicRatio y z p*squaredPoleDensity z p) n (-(v^2)) ≤ C*((n:ℝ)+1)^(3*v/4) := by
  let l : ℝ := min 1 (y^2/z^2)
  let u : ℝ := max 1 (y^2/z^2)
  have hl : 0 < l := lt_min (by norm_num) (by positivity)
  have hu : 0 < u := (by norm_num : (0:ℝ) < 1).trans_le (le_max_left _ _)
  let w' : ℝ → ℝ := fun p=>characteristicRatio y z p*squaredPoleDensity z p
  have hw p hp : 0 < w' p := mul_pos (characteristicRatio_pos hy hz p) (squaredPoleDensity_pos hz hp)
  have hcL (n : ℕ) :=weightedPolynomialChristoffel_comparison n (-(v^2)) (inv_pos.mpr hu)
    hw (fun p hp=>squaredPoleDensity_pos hz hp) (tilted_squaredPole_moments hy hz) (squaredPoleDensity_moments hz)
    (fun p hp=>by
      have h := mul_le_mul_of_nonneg_right (characteristicRatio_bounds y hz p).2 (squaredPoleDensity_pos hz hp).le
      change u⁻¹*(characteristicRatio y z p*squaredPoleDensity z p) ≤ squaredPoleDensity z p
      exact (inv_mul_le_iff₀ hu).mpr h)
  have hcU (n : ℕ) :=weightedPolynomialChristoffel_comparison n (-(v^2)) hl
    (fun p hp=>squaredPoleDensity_pos hz hp) hw (squaredPoleDensity_moments hz) (tilted_squaredPole_moments hy hz)
    (fun p hp=>mul_le_mul_of_nonneg_right (characteristicRatio_bounds y hz p).1 (squaredPoleDensity_pos hz hp).le)
  obtain ⟨a,C,ha,hC,h⟩:=stripPolynomialChristoffel_bounds hz hv
  refine ⟨a/u,C/l,by positivity,by positivity,?_⟩
  filter_upwards [h] with n hn
  constructor
  · have hh := (div_le_iff₀ hu).mpr (hn.1.trans (by simpa using hcL n))
    simpa only [div_mul_eq_mul_div] using hh
  · exact (hcU n).trans (by simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hn.2 hl.le)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Filter Topology
lemma power_ratio_bounds (f g : ℕ → ℝ) (α β : ℝ)
    (hf : ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^α ≤ f n ∧ f n ≤ C*((n:ℝ)+1)^α)
    (hg : ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^β ≤ g n ∧ g n ≤ C*((n:ℝ)+1)^β) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(α-β) ≤ f n/g n ∧ f n/g n ≤ C*((n:ℝ)+1)^(α-β) := by
  obtain ⟨a₁,C₁,ha₁,hC₁,hf⟩:=hf
  obtain ⟨a₂,C₂,ha₂,hC₂,hg⟩:=hg
  refine ⟨a₁/C₂,C₁/a₂,by positivity,by positivity,?_⟩
  filter_upwards [hf,hg] with n hn hn'
  have hn0 : 0 < (n:ℝ)+1 := by positivity
  have hgn : 0 < g n := (mul_pos ha₂ (rpow_pos_of_pos hn0 β)).trans_le hn'.1
  have hfn : 0 < f n := (mul_pos ha₁ (rpow_pos_of_pos hn0 α)).trans_le hn.1
  rw [rpow_sub hn0]
  constructor
  · have h:=div_le_div₀ hfn.le hn.1 hgn hn'.2
    exact (by ring : (a₁/C₂)*(((n:ℝ)+1)^α/((n:ℝ)+1)^β) =
      (a₁*((n:ℝ)+1)^α)/(C₂*((n:ℝ)+1)^β)).le.trans h
  · have h:=div_le_div₀ (mul_pos hC₁ (rpow_pos_of_pos hn0 α)).le hn.2
      (mul_pos ha₂ (rpow_pos_of_pos hn0 β)) hn'.1
    exact h.trans_eq (by ring)
/-- Polynomial square-product exponent for the genuine strip density. -/
theorem strip_polynomial_square_product_bounds {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(3*(y-z)/4) ≤
        (monomialGram n (fun p=>characteristicRatio y z p^2*stripDensity p)).det/(monomialGram n stripDensity).det ∧
      (monomialGram n (fun p=>characteristicRatio y z p^2*stripDensity p)).det/(monomialGram n stripDensity).det ≤
        C*((n:ℝ)+1)^(3*(y-z)/4) := by
  have h:=power_ratio_bounds
    (fun n=>weightedPolynomialChristoffel (squaredPoleDensity z) n (-(y^2)))
    (fun n=>weightedPolynomialChristoffel (squaredPoleDensity z) n (-(z^2)))
    (3*y/4) (3*z/4) (stripPolynomialChristoffel_bounds hz hy) (stripPolynomialChristoffel_bounds hz hz)
  simpa only [←strip_polynomial_square_product (y:=y) _ hz,show 3*y/4-3*z/4=3*(y-z)/4 by ring] using h
lemma tilted_squaredPole_restore {y z : ℝ} (hz : 0 < z) :
    (fun p : ℝ=>(p^2-(-(z^2)))^2*(characteristicRatio y z p*squaredPoleDensity z p))=
    (fun p=>characteristicRatio y z p*stripDensity p) := by
  funext p
  have h:=congrFun (squaredPole_restore hz) p
  rw [←h]
  ring
lemma tilted_squaredPole_tilt (y z : ℝ) :
    (fun p : ℝ=>(p^2-(-(y^2)))^2*(characteristicRatio y z p*squaredPoleDensity z p))=
    (fun p=>characteristicRatio y z p^2*(characteristicRatio y z p*stripDensity p)) := by
  funext p
  have h:=congrFun (squaredPole_tilt y z) p
  rw [←mul_assoc, mul_comm ((p^2-(-(y^2)))^2) (characteristicRatio y z p),mul_assoc,h]
  ring
lemma tilted_strip_polynomial_square_product (n : ℕ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (monomialGram n (fun p=>characteristicRatio y z p^2*(characteristicRatio y z p*stripDensity p))).det /
      (monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det =
    weightedPolynomialChristoffel (fun p=>characteristicRatio y z p*squaredPoleDensity z p) n (-(y^2)) /
    weightedPolynomialChristoffel (fun p=>characteristicRatio y z p*squaredPoleDensity z p) n (-(z^2)) := by
  have h:=polynomial_compression_ratio n (-(y^2)) (-(z^2))
    (fun p=>characteristicRatio y z p*squaredPoleDensity z p)
    (fun p hp=>mul_pos (characteristicRatio_pos hy hz p) (squaredPoleDensity_pos hz hp))
    (tilted_squaredPole_moments hy hz)
  rwa [tilted_squaredPole_restore hz,tilted_squaredPole_tilt] at h
/-- The second square-product estimate needed for the Cauchy--Schwarz squeeze. -/
theorem tilted_strip_polynomial_square_product_bounds {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(3*(y-z)/4) ≤
        (monomialGram n (fun p=>characteristicRatio y z p^2*(characteristicRatio y z p*stripDensity p))).det /
          (monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det ∧
      (monomialGram n (fun p=>characteristicRatio y z p^2*(characteristicRatio y z p*stripDensity p))).det /
          (monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det ≤ C*((n:ℝ)+1)^(3*(y-z)/4) := by
  have h:=power_ratio_bounds
    (fun n=>weightedPolynomialChristoffel (fun p=>characteristicRatio y z p*squaredPoleDensity z p) n (-(y^2)))
    (fun n=>weightedPolynomialChristoffel (fun p=>characteristicRatio y z p*squaredPoleDensity z p) n (-(z^2)))
    (3*y/4) (3*z/4) (tilted_stripPolynomialChristoffel_bounds hy hz hy) (tilted_stripPolynomialChristoffel_bounds hy hz hz)
  simpa only [←tilted_strip_polynomial_square_product _ hy hz,show 3*y/4-3*z/4=3*(y-z)/4 by ring] using h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Equiv MeasureTheory Filter
noncomputable def monomialPointDensity (n : ℕ) (w : ℝ → ℝ) (p : Fin n → ℝ) : ℝ :=
  (∏ i,w (p i))*(evaluationMatrix (fun i : Fin n=>fun q : ℝ=>(q^2)^i.val) p).det^2
lemma monomial_gram_andreief (n : ℕ) (w : ℝ → ℝ)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0)) :
    Integrable (monomialPointDensity n w) (Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))) ∧
    (∫ p,monomialPointDensity n w p ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))))=
      Fintype.card (Perm (Fin n))*(monomialGram n w).det := by
  let F : Fin n → ℝ → ℝ := fun i p=>(p^2)^i.val*w p
  let G : Fin n → ℝ → ℝ := fun i p=>(p^2)^i.val
  have hiFG i j : Integrable (fun p=>F i p*G j p) (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply (monomial_pair_integrable w hi i.val j.val).congr
    filter_upwards with p
    dsimp [F,G]
    ring
  have he p : (evaluationMatrix F p).det*(evaluationMatrix G p).det=monomialPointDensity n w p := by
    have hF : evaluationMatrix F p=Matrix.of (fun i j=>w (p j)*evaluationMatrix G p i j) := by
      ext i j
      dsimp [evaluationMatrix,F,G]
      ring
    rw [hF,Matrix.det_mul_row]
    dsimp [monomialPointDensity,G]
    ring
  have hg : gramMatrix (volume.restrict (Set.Ioi (0:ℝ))) F G=monomialGram n w := by
    ext i j
    apply integral_congr_ae
    filter_upwards with p
    dsimp [F,G]
    ring
  constructor
  · simpa only [he] using integrable_det_evaluation_product _ F G hiFG
  · simpa only [he,hg] using andreief _ F G hiFG
lemma monomialPointDensity_tilt (n : ℕ) (w r : ℝ → ℝ) (p : Fin n → ℝ) :
    monomialPointDensity n (fun q=>r q*w q) p=(∏ i,r (p i))*monomialPointDensity n w p := by
  simp only [monomialPointDensity,prod_mul_distrib]
  ring
lemma monomialPointDensity_nonneg (n : ℕ) (w : ℝ → ℝ) (hw : ∀ p,0 < p → 0 ≤ w p) :
    ∀ᵐ p ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))),0 ≤ monomialPointDensity n w p := by
  have hae : ∀ᵐ p ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))),∀ i,0 < p i := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (i:=i)).eventually (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hae] with p hp
  exact mul_nonneg (prod_nonneg (fun i _=>hw _ (hp i))) (sq_nonneg _)
lemma integral_weighted_square {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ f : α → ℝ)
    (hρ : Integrable ρ μ) (h1 : Integrable (fun x=>f x*ρ x) μ)
    (h2 : Integrable (fun x=>f x^2*ρ x) μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    (hI : 0 < ∫ x,ρ x ∂μ) :
    (∫ x,f x*ρ x ∂μ)^2 ≤ (∫ x,f x^2*ρ x ∂μ)*(∫ x,ρ x ∂μ) := by
  let a : ℝ := (∫ x,f x*ρ x ∂μ)/(∫ x,ρ x ∂μ)
  have he : (fun x=>(f x-a)^2*ρ x)=
      (fun x=>f x^2*ρ x-2*a*(f x*ρ x)+a^2*ρ x) := by funext x;ring
  have hh : 0 ≤ ∫ x,(f x-a)^2*ρ x ∂μ := integral_nonneg_of_ae (hρ0.mono (fun x hx=>mul_nonneg (sq_nonneg _) hx))
  have hadd:=integral_add (h2.sub (h1.const_mul (2*a))) (hρ.const_mul (a^2))
  have hsub:=integral_sub h2 (h1.const_mul (2*a))
  simp only [Pi.sub_apply] at hadd hsub
  rw [he,hadd,hsub,integral_const_mul,integral_const_mul] at hh
  have he' : a*(∫ x,ρ x ∂μ)=∫ x,f x*ρ x ∂μ := div_mul_cancel₀ _ hI.ne'
  nlinarith [mul_nonneg hh hI.le]
/-- Cauchy--Schwarz for the genuine polynomial determinant density. -/
theorem monomialGram_tilt_square (n : ℕ) (w r : ℝ → ℝ)
    (hw : ∀ p,0 < p → 0 < w p)
    (hi : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*w p) (Set.Ioi 0))
    (hi1 : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*(r p*w p)) (Set.Ioi 0))
    (hi2 : ∀ k : ℕ,IntegrableOn (fun p : ℝ=>p^k*(r p^2*w p)) (Set.Ioi 0)) :
    (monomialGram n (fun p=>r p*w p)).det^2 ≤
      (monomialGram n (fun p=>r p^2*w p)).det*(monomialGram n w).det := by
  obtain ⟨h0,he0⟩:=monomial_gram_andreief n w hi
  obtain ⟨h1,he1⟩:=monomial_gram_andreief n (fun p=>r p*w p) hi1
  obtain ⟨h2,he2⟩:=monomial_gram_andreief n (fun p=>r p^2*w p) hi2
  change Integrable (fun p=>monomialPointDensity n (fun p=>r p*w p) p) _ at h1
  change Integrable (fun p=>monomialPointDensity n (fun p=>r p^2*w p) p) _ at h2
  simp_rw [monomialPointDensity_tilt] at h1 h2 he1 he2
  simp_rw [Finset.prod_pow] at h2 he2
  have hpos : 0 < ∫ p,monomialPointDensity n w p ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) := by
    rw [he0]
    exact mul_pos (by positivity) (monomialGram_posDef n w hw hi).det_pos
  have h:=integral_weighted_square _ (monomialPointDensity n w) (fun p=>∏ i,r (p i)) h0 h1 h2
    (monomialPointDensity_nonneg n w (fun p hp=>(hw p hp).le)) hpos
  rw [he0,he1,he2] at h
  have hn : (0:ℝ) < Fintype.card (Perm (Fin n)) := by positivity
  have hh : ((Fintype.card (Perm (Fin n)) : ℝ)^2)*(monomialGram n (fun p=>r p*w p)).det^2 ≤
      ((Fintype.card (Perm (Fin n)) : ℝ)^2)*((monomialGram n (fun p=>r p^2*w p)).det*(monomialGram n w).det) := by nlinarith only [h]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hh
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Filter Topology
lemma stripDensity_moments (k : ℕ) :
    IntegrableOn (fun p : ℝ=>p^k*stripDensity p) (Set.Ioi 0) := by
  have h:=strip_jet_pair_moment_integrable (b:=0) (c:=0) (le_refl _) (le_refl _)
    (sq_nonneg _) (sq_nonneg _) 0 0 k
  simpa only [cosineKernelJet_zero_zero_cosh (le_refl (0:ℝ)) (sq_nonneg _),
    Real.sqrt_zero,zero_mul,Real.cosh_zero,mul_one] using h
lemma characteristic_tilt_moments {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (j k : ℕ) :
    IntegrableOn (fun p : ℝ=>p^k*(characteristicRatio y z p^j*stripDensity p)) (Set.Ioi 0) := by
  apply weightedPolynomial_moments_bounded stripDensity (fun p=>characteristicRatio y z p^j)
    (fun p hp=>(stripDensity_pos hp).le) (by unfold characteristicRatio;fun_prop)
    (fun p _=>pow_nonneg (characteristicRatio_pos hy hz p).le j) stripDensity_moments
    (fun p _=>pow_le_pow_left₀ (characteristicRatio_pos hy hz p).le (characteristicRatio_bounds y hz p).2 j)
lemma square_le_power_upper {u x C t : ℝ} (hu : 0 ≤ u) (hx : 0 < x) (hC : 0 < C)
    (h : u^2 ≤ C*x^(2*t)) : u ≤ Real.sqrt C*x^t := by
  apply (sq_le_sq₀ hu (mul_nonneg (Real.sqrt_nonneg _) (rpow_nonneg hx.le _))).mp
  have he : (Real.sqrt C*x^t)^2=C*x^(2*t) := by
    rw [mul_pow,Real.sq_sqrt hC.le,show 2*t=t*2 by ring,rpow_mul hx.le,rpow_two]
  rwa [he]
lemma polynomial_product_squeeze (G S T : ℕ → ℝ) (t : ℝ)
    (hG : ∀ n,0 < G n) (hS : ∀ n,0 ≤ S n)
    (hCS : ∀ n,(G n)^2 ≤ S n) (hCST : ∀ n,(S n/G n)^2 ≤ T n)
    (hSb : ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(2*t) ≤ S n ∧ S n ≤ C*((n:ℝ)+1)^(2*t))
    (hTb : ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(2*t) ≤ T n ∧ T n ≤ C*((n:ℝ)+1)^(2*t)) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^t ≤ G n ∧ G n ≤ C*((n:ℝ)+1)^t := by
  obtain ⟨a,C,ha,hC,hs⟩:=hSb
  obtain ⟨a',C',_,hC',ht⟩:=hTb
  have hc' : 0 < Real.sqrt C' := Real.sqrt_pos.mpr hC'
  refine ⟨a/Real.sqrt C',Real.sqrt C,by positivity,by positivity,?_⟩
  filter_upwards [hs,ht] with n hn hn'
  have hx : 0 < (n:ℝ)+1 := by positivity
  have hv : 0 < ((n:ℝ)+1)^t := rpow_pos_of_pos hx t
  constructor
  · have hh:=square_le_power_upper (div_nonneg (hS n) (hG n).le) hx hC' ((hCST n).trans hn'.2)
    have hh':= (div_le_iff₀ (hG n)).mp hh
    have hl:=hn.1.trans hh'
    rw [show 2*t=t*2 by ring,rpow_mul hx.le,rpow_two] at hl
    have hl' : a*((n:ℝ)+1)^t ≤ Real.sqrt C'*G n := by
      by_contra h
      have hlt:=mul_lt_mul_of_pos_right (lt_of_not_ge h) hv
      nlinarith only [hl,hlt]
    calc a/Real.sqrt C'*((n:ℝ)+1)^t=(a*((n:ℝ)+1)^t)/Real.sqrt C' := by ring
         _ ≤ G n := (div_le_iff₀ hc').mpr (by simpa only [mul_comm] using hl')
  · exact square_le_power_upper (hG n).le hx hC ((hCS n).trans hn.2)
/-- Characteristic product estimates for the strip density. -/
theorem strip_polynomial_characteristic_product_bounds {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    ∃ a C : ℝ,0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      a*((n:ℝ)+1)^(3*(y-z)/8) ≤
        (monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det/(monomialGram n stripDensity).det ∧
      (monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det/(monomialGram n stripDensity).det ≤
        C*((n:ℝ)+1)^(3*(y-z)/8) := by
  let d (n j : ℕ) : ℝ := (monomialGram n (fun p=>characteristicRatio y z p^j*stripDensity p)).det
  have hd n j : 0 < d n j := (monomialGram_posDef n _
    (fun p hp=>mul_pos (pow_pos (characteristicRatio_pos hy hz p) j) (stripDensity_pos hp))
    (characteristic_tilt_moments hy hz j)).det_pos
  have hd0 n : d n 0=(monomialGram n stripDensity).det := by simp only [d,pow_zero,one_mul]
  have hd1 n : d n 1=(monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det := by simp only [d,pow_one]
  have hd3 n : d n 3=(monomialGram n (fun p=>characteristicRatio y z p^2*(characteristicRatio y z p*stripDensity p))).det := by
    dsimp [d]
    congr 2
    funext p
    ring
  have hCS n : (d n 1/d n 0)^2 ≤ d n 2/d n 0 := by
    have h:=monomialGram_tilt_square n stripDensity (characteristicRatio y z)
      (fun p hp=>stripDensity_pos hp) stripDensity_moments
      (by simpa only [pow_one] using characteristic_tilt_moments hy hz 1)
      (characteristic_tilt_moments hy hz 2)
    rw [←hd0 n,←hd1 n] at h
    change (d n 1)^2 ≤ d n 2*d n 0 at h
    rw [div_pow]
    have hh:=div_le_div_of_nonneg_right h (sq_nonneg (d n 0))
    exact hh.trans_eq (by field_simp [(hd n 0).ne'])
  have hCST n : ((d n 2/d n 0)/(d n 1/d n 0))^2 ≤ d n 3/d n 1 := by
    rw [div_div_div_cancel_right₀ (hd n 0).ne']
    have hi j k : IntegrableOn (fun p : ℝ=>p^k*(characteristicRatio y z p^j*(characteristicRatio y z p*stripDensity p))) (Set.Ioi 0) := by
      apply (characteristic_tilt_moments hy hz (j+1) k).congr
      filter_upwards with p
      rw [pow_succ]
      ring
    have h:=monomialGram_tilt_square n (fun p=>characteristicRatio y z p*stripDensity p) (characteristicRatio y z)
      (fun p hp=>mul_pos (characteristicRatio_pos hy hz p) (stripDensity_pos hp))
      (by simpa only [pow_one] using characteristic_tilt_moments hy hz 1)
      (by simpa only [pow_one] using hi 1) (hi 2)
    have he : (fun p=>characteristicRatio y z p*(characteristicRatio y z p*stripDensity p))=
      (fun p=>characteristicRatio y z p^2*stripDensity p) := by funext p;ring
    rw [he,←hd1 n,←hd3 n] at h
    change (d n 2)^2 ≤ d n 3*d n 1 at h
    rw [div_pow]
    have hh:=div_le_div_of_nonneg_right h (sq_nonneg (d n 1))
    exact hh.trans_eq (by field_simp [(hd n 1).ne'])
  have hs:=strip_polynomial_square_product_bounds hy hz
  have ht:=tilted_strip_polynomial_square_product_bounds hy hz
  have he : 3*(y-z)/4=2*(3*(y-z)/8) := by ring
  simp only [←hd0,←hd1,←hd3,he] at hs ht
  have h:=polynomial_product_squeeze (fun n=>d n 1/d n 0) (fun n=>d n 2/d n 0) (fun n=>d n 3/d n 1)
    (3*(y-z)/8) (fun n=>div_pos (hd n 1) (hd n 0)) (fun n=>(div_pos (hd n 2) (hd n 0)).le)
    hCS hCST hs ht
  simpa only [hd0,hd1] using h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Finset
/-- A parameter-uniform bound for growing arguments of order `N^(3/4)`. -/
lemma meixner_even_coefficient_uniform {s:ℝ} (hs : (1 : ℝ) / 2  ≤  s) (n j:ℕ) (hj : j  ≤  n) :
    meixnerCoeff s (2*j) ≤ ((n:ℝ)+1)*(4*((n:ℝ)+1))^(s+1/2) := by
  let u:ℝ:=1-1/(2*((n:ℝ)+1))
  have hn:0<(n:ℝ)+1:=by positivity
  have hd:0<2*((n:ℝ)+1):=by positivity
  have ht:0<1/(2*((n:ℝ)+1)):=by positivity
  have ht':1/(2*((n:ℝ)+1)) ≤ 1/2:=by apply one_div_le_one_div_of_le (by norm_num); nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hu:0<u:=by dsimp [u];linarith
  have hu1:u<1:=by dsimp [u];linarith
  have hab:|u|<1:=by rwa [abs_of_pos hu]
  have hsum:=meixnerCoeff_hasSum s hab
  have hterm:meixnerCoeff s (2*j)*u^(2*j) ≤ meixnerGenerator s u:=by
    rw [←hsum.tsum_eq]
    exact hsum.summable.le_tsum (2*j) (fun k _=>mul_nonneg (meixnerCoeff_nonneg (by linarith) k) (pow_nonneg hu.le k))
  have hpow:1/((n:ℝ)+1) ≤ u^(2*j):=by
    have hb:=one_add_mul_le_pow (a:=-(1/(2*((n:ℝ)+1)))) (by linarith : (-2:ℝ) ≤ -(1/(2*((n:ℝ)+1)))) (2*j)
    change 1+(2*j:ℕ)*(-(1/(2*((n:ℝ)+1)))) ≤ u^(2*j) at hb
    have hj':(j:ℝ) ≤ n:=by exact_mod_cast hj
    have he:1+(2*j:ℕ)*(-(1/(2*((n:ℝ)+1))))=((n:ℝ)+1-j)/((n:ℝ)+1):=by push_cast;field_simp;ring
    rw [he] at hb
    exact (div_le_div_of_nonneg_right (by linarith : (1:ℝ) ≤ (n:ℝ)+1-j) hn.le).trans hb
  have hgen:meixnerGenerator s u ≤ (4*((n:ℝ)+1))^(s+1/2):=by
    have he:1-u=1/(2*((n:ℝ)+1)):=by dsimp [u];ring
    have hfactor:(1-u)^(-s-1/2)=(2*((n:ℝ)+1))^(s+1/2):=by
      rw [he,show -s-1/2=-(s+1/2) by ring,Real.rpow_neg,one_div,Real.inv_rpow,inv_inv] <;> positivity
    unfold meixnerGenerator
    rw [hfactor]
    have ha:(1+u)^(s-1/2) ≤ (2:ℝ)^(s+1/2):=by
      calc
        _ ≤ (2:ℝ)^(s-1/2):=Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        _ ≤ _:=Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc
      _ ≤ (2:ℝ)^(s+1/2)*(2*((n:ℝ)+1))^(s+1/2):=mul_le_mul_of_nonneg_right ha (by positivity)
      _=(4*((n:ℝ)+1))^(s+1/2):=by rw [←Real.mul_rpow (by norm_num) (by positivity)];congr 1;ring
  have hc:=meixnerCoeff_nonneg (show 0 ≤ s by linarith) (2*j)
  have ht'':meixnerCoeff s (2*j)/((n:ℝ)+1) ≤ (4*((n:ℝ)+1))^(s+1/2):=by
    calc
      _=meixnerCoeff s (2*j)*(1/((n:ℝ)+1)):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hpow hc
      _ ≤ _:=hterm.trans hgen
  exact (by simpa only [mul_comm] using (div_le_iff₀ hn).mp ht'')
theorem evenCoefficientKernel_uniform {s:ℝ} (hs : (1 : ℝ) / 2  ≤  s) (n:ℕ) :
    evenCoefficientKernel s n ≤ ((n:ℝ)+1)^3*(4*((n:ℝ)+1))^(2*s+1) := by
  unfold evenCoefficientKernel
  calc
    _ ≤ ∑ j∈range (n+1),(((n:ℝ)+1)*(4*((n:ℝ)+1))^(s+1/2))^2:=by
      apply sum_le_sum
      intro j hj
      exact pow_le_pow_left₀ (meixnerCoeff_nonneg (by linarith) _) (meixner_even_coefficient_uniform hs n j (by have := mem_range.mp hj; omega)) 2
    _=((n:ℝ)+1)^3*(4*((n:ℝ)+1))^(2*s+1):=by
      simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_pow]
      rw [←Real.rpow_natCast ((4*((n:ℝ)+1))^(s+1/2)) 2,←Real.rpow_mul (by positivity)]
      norm_num only [Nat.cast_ofNat]
      rw [show (s+1/2)*(2:ℝ)=2*s+1 by ring]
      ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory
lemma stripDensity_exponential_lower {p : ℝ} (hp : 0<p) :
    (1/(8*angle))*Real.exp (-3*angle*p)≤ stripDensity p := by
  have hL:0<angle:=by unfold angle;positivity
  have hcos:Real.cosh (3*angle*p)≤Real.exp (3*angle*p) := by
    have hh:=Analytic.cosh_abs_le_exp_abs (3*angle*p)
    simpa only [abs_of_pos (Real.cosh_pos _),abs_of_pos (by positivity : 0<3*angle*p)] using hh
  calc
    _ = 1/(8*angle*Real.exp (3*angle*p)) := by rw [show -3*angle*p=-(3*angle*p) by ring,Real.exp_neg];ring
    _ ≤ 1/(8*angle*Real.cosh (3*angle*p)) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
    _ ≤ _ := (stripDensity_sech_bounds hp).1
lemma stripDensity_slower_sech_upper {c : ℝ} (hc:0<c) (hcL:c<3*angle) :
    ∃ A:ℝ,0<A ∧ ∀ p:ℝ,0<p → stripDensity p≤A/Real.cosh (c*p) := by
  let d:=3*angle-c
  have hd:0<d:=by dsimp [d];linarith
  have hL:0<angle:=by unfold angle;positivity
  refine ⟨2*(1/d+1/angle),by positivity,?_⟩
  intro p hp
  have hC:Real.cosh (c*p)≤Real.exp (c*p) := by
    simpa only [abs_of_pos (Real.cosh_pos _),abs_of_pos (mul_pos hc hp)] using Analytic.cosh_abs_le_exp_abs (c*p)
  have hD:Real.exp (3*angle*p)/2≤Real.cosh (3*angle*p):=by
    rw [Real.cosh_eq];linarith [Real.exp_pos (-(3*angle*p))]
  have he:Real.exp (-d*p)≤1:=Real.exp_le_one_iff.mpr (by nlinarith)
  have hep:p*Real.exp (-d*p)≤1/d := by
    have hh : d*p≤Real.exp (d*p):= by linarith [Real.add_one_le_exp (d*p)]
    apply (le_div_iff₀ hd).mpr
    have hmul:=mul_le_mul_of_nonneg_right hh (Real.exp_pos (-d*p)).le
    rw [←Real.exp_add,show d*p+-d*p=0 by ring,Real.exp_zero] at hmul
    nlinarith
  apply (le_div_iff₀ (Real.cosh_pos _)).mpr
  calc
    stripDensity p*Real.cosh (c*p) ≤ ((p+1/angle)/Real.cosh (3*angle*p))*Real.exp (c*p) :=
      mul_le_mul (stripDensity_sech_bounds hp).2 hC (Real.cosh_pos _).le (by positivity)
    _ ≤ ((p+1/angle)/(Real.exp (3*angle*p)/2))*Real.exp (c*p) := by gcongr
    _ = 2*(p+1/angle)*Real.exp (-d*p) := by dsimp [d];rw [show -(3*angle-c)*p=c*p-3*angle*p by ring,Real.exp_sub];ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0≤1/angle)]
noncomputable def scaledStripDensity (s p:ℝ):ℝ:=s*stripDensity (s*p)
lemma scaledStripDensity_sech_bounds {s:ℝ} (hs:0<s) (hsL:Real.pi<3*angle*s) :
    ∃ A a β:ℝ,0<A ∧ 0<a ∧ 0<β ∧
      (∀ p:ℝ,0<p → scaledStripDensity s p≤A/Real.cosh (Real.pi*p)) ∧
      (∀ R p:ℝ,0<p → p≤R → a*Real.exp (-β*R)/Real.cosh (Real.pi*p)≤ scaledStripDensity s p) := by
  have hL:0<angle:=by unfold angle;positivity
  obtain ⟨A,hA,hbound⟩:=stripDensity_slower_sech_upper (by positivity : 0<Real.pi/s) ((div_lt_iff₀ hs).mpr hsL)
  refine ⟨s*A,s/(8*angle),3*angle*s,by positivity,by positivity,by positivity,?_,?_⟩
  · intro p hp
    have hh:=mul_le_mul_of_nonneg_left (hbound (s*p) (mul_pos hs hp)) hs.le
    simpa only [show Real.pi/s*(s*p)=Real.pi*p by field_simp,scaledStripDensity,mul_div_assoc] using hh
  · intro R p hp hpR
    have he:Real.exp (-(3*angle*s)*R)≤Real.exp (-3*angle*(s*p)):=Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left hpR (show 0≤3*angle*s by positivity)
      nlinarith only [hh])
    calc
      _ ≤ (s/(8*angle))*Real.exp (-(3*angle*s)*R) := div_le_self (by positivity) (Real.one_le_cosh _)
      _ ≤ (s/(8*angle))*Real.exp (-3*angle*(s*p)) := mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := by
        have hh:=mul_le_mul_of_nonneg_left (stripDensity_exponential_lower (mul_pos hs hp)) hs.le
        convert hh using 1 <;> first | rfl | ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Polynomial
lemma growing_pole_denominator {p z : ℝ} (hp : 0 < p) (hz : 1 ≤ z) :
    (p^2+z^2)^2 ≤ z^4*Real.exp (4*p) := by
  have hz2 : 1 ≤ z^2 := by nlinarith
  have hbase : p^2+z^2 ≤ z^2*(p+1)^2 := by
    nlinarith [mul_nonneg (show 0≤z^2-1 by linarith) (sq_nonneg p),mul_nonneg (sq_nonneg z) hp.le]
  have he : (Real.exp p)^4=Real.exp (4*p) := by
    rw [show (Real.exp p)^4=((Real.exp p)^2)^2 by ring,
      pow_two, pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (z^2*(p+1)^2)^2 := pow_le_pow_left₀ (by positivity) hbase 2
    _ = z^4*(p+1)^4 := by ring
    _ ≤ z^4*(Real.exp p)^4 := by
      gcongr
      exact Real.add_one_le_exp p
    _ = _ := by rw [he]
/-- Parameter-uniform pole comparison needed in strip-asymptotics:107.
The constants do not depend on the pole z, which may grow with N. -/
lemma growing_squaredPole_lower :
    ∃ c a : ℝ, 0<c ∧ 0<a ∧ ∀ z : ℝ, 1 ≤ z → ∀ p : ℝ, 0<p →
      (a/z^4)*sechWeight c p ≤ squaredPoleDensity z p := by
  let c : ℝ := 3*angle+4
  let a : ℝ := Real.pi/(32*angle*c)
  have hL : 0<angle := by unfold angle;positivity
  have hc : 0<c := by dsimp [c];positivity
  have ha : 0<a := by dsimp [a];positivity
  refine ⟨c,a,hc,ha,?_⟩
  intro z hz p hp
  have hz0 : 0<z := by linarith
  have hden : 0<(p^2+z^2)^2 := by positivity
  have hW := stripDensity_exponential_lower hp
  have hC : Real.exp (c*p)/2 ≤ Real.cosh (c*p) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(c*p))]
  have hsech : sechWeight c p ≤ (4*c/Real.pi)*Real.exp (-c*p) := by
    calc
      _ ≤ (2*c/Real.pi)/(Real.exp (c*p)/2) := by unfold sechWeight;gcongr
      _ = _ := by rw [show -c*p=-(c*p) by ring,Real.exp_neg];ring
  have he : (a/z^4)*((4*c/Real.pi)*Real.exp (-c*p))=
      ((1/(8*angle))*Real.exp (-3*angle*p))/(z^4*Real.exp (4*p)) := by
    dsimp [a,c]
    rw [show -(3*angle+4)*p=-3*angle*p-4*p by ring, Real.exp_sub]
    field_simp
    ring
  calc
    (a/z^4)*sechWeight c p ≤ (a/z^4)*((4*c/Real.pi)*Real.exp (-c*p)) :=
      mul_le_mul_of_nonneg_left hsech (by positivity)
    _ = _ := he
    _ ≤ ((1/(8*angle))*Real.exp (-3*angle*p))/(p^2+z^2)^2 :=
      div_le_div_of_nonneg_left (by positivity) hden (growing_pole_denominator hp hz)
    _ ≤ squaredPoleDensity z p := div_le_div_of_nonneg_right hW (sq_nonneg _)
lemma squaredPole_le_strip {z p : ℝ} (hz : 1 ≤ z) (hp : 0<p) :
    squaredPoleDensity z p ≤ stripDensity p := by
  have h : 1 ≤ (p^2+z^2)^2 := by nlinarith [sq_nonneg p,sq_nonneg (p^2+z^2-1)]
  exact div_le_self (stripDensity_pos hp).le h
lemma growing_squaredPole_kernel_lower (n : ℕ) (x : ℝ) {z : ℝ} (hz : 1 ≤ z) :
    1/weightedPolynomialNorm stripDensity 1 ≤
      weightedPolynomialChristoffel (squaredPoleDensity z) n x := by
  have hz0 : 0<z := by linarith
  have hnorm : weightedPolynomialNorm (squaredPoleDensity z) 1 ≤ weightedPolynomialNorm stripDensity 1 := by
    apply integral_mono_ae
      (weightedPolynomialNorm_integrable _ (squaredPoleDensity_moments hz0) 1)
      (weightedPolynomialNorm_integrable _ stripDensity_moments 1)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    simpa only [Polynomial.eval_one,one_pow,one_mul] using squaredPole_le_strip hz hp
  have hpole := weightedPolynomialNorm_pos _ (fun p hp=>squaredPoleDensity_pos hz0 hp)
    (squaredPoleDensity_moments hz0) (one_ne_zero : (1:Polynomial ℝ)≠0)
  have hk := weightedPolynomial_ratio_bound n x (squaredPoleDensity z)
    (fun p hp=>squaredPoleDensity_pos hz0 hp) (squaredPoleDensity_moments hz0) 1 (by simp)
  simp only [Polynomial.eval_one,one_pow] at hk
  exact (div_le_div_of_nonneg_left (by norm_num) hpole hnorm).trans hk
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Polynomial MeasureTheory
/-- Growing-argument square-product bound for the literal strip measure. No
fixed-parameter asymptotic is applied to a moving evaluation point. -/
theorem strip_polynomial_square_product_uniform :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ y z : ℝ, 1 ≤ z → 1/2 ≤ c*y/Real.pi → ∀ n : ℕ,
      (monomialGram n (fun p=>characteristicRatio y z p^2*stripDensity p)).det /
        (monomialGram n stripDensity).det ≤
      C*z^4*((n:ℝ)+1)^3*(4*((n:ℝ)+1))^(2*c*y/Real.pi+1) := by
  obtain ⟨c,a,hc,ha,hweight⟩:=growing_squaredPole_lower
  let B : ℝ := weightedPolynomialNorm stripDensity 1
  have hB : 0<B := weightedPolynomialNorm_pos stripDensity (fun p hp=>stripDensity_pos hp)
    stripDensity_moments (one_ne_zero : (1:Polynomial ℝ)≠0)
  refine ⟨c,B/a,hc,by positivity,?_⟩
  intro y z hz hs n
  have hz0 : 0<z := by linarith
  have hz4 : 0<z^4 := by positivity
  have hlow := growing_squaredPole_kernel_lower n (-(z^2)) hz
  have hkpos : 0<weightedPolynomialChristoffel (squaredPoleDensity z) n (-(z^2)) :=
    (show 0<1/B by positivity).trans_le hlow
  have hu := weightedPolynomialChristoffel_comparison n (-(y^2)) (div_pos ha hz4)
    (fun p _=>sechWeight_pos hc p) (fun p hp=>squaredPoleDensity_pos hz0 hp)
    (sechWeight_moments hc) (squaredPoleDensity_moments hz0) (hweight z hz)
  have he : weightedPolynomialChristoffel (sechWeight c) n (-(y^2))=
      evenCoefficientKernel (c*y/Real.pi) n := by
    rw [weightedKernel_sech,scaledPolynomialChristoffel_eq hc,
      show (c/Real.pi)^2*-(y^2)=-((c*y/Real.pi)^2) by ring,polynomialChristoffel_negative]
  rw [he] at hu
  have hkernel := evenCoefficientKernel_uniform hs n
  have hnum : weightedPolynomialChristoffel (squaredPoleDensity z) n (-(y^2)) ≤
      (((n:ℝ)+1)^3*(4*((n:ℝ)+1))^(2*(c*y/Real.pi)+1))/(a/z^4) :=
    hu.trans (div_le_div_of_nonneg_right hkernel (div_pos ha hz4).le)
  rw [strip_polynomial_square_product n hz0]
  have hb : 0 ≤ (((n:ℝ)+1)^3*(4*((n:ℝ)+1))^(2*(c*y/Real.pi)+1))/(a/z^4) := by positivity
  calc
    _ ≤ ((((n:ℝ)+1)^3*(4*((n:ℝ)+1))^(2*(c*y/Real.pi)+1))/(a/z^4)) /
        weightedPolynomialChristoffel (squaredPoleDensity z) n (-(z^2)) :=
      div_le_div_of_nonneg_right hnum hkpos.le
    _ ≤ ((((n:ℝ)+1)^3*(4*((n:ℝ)+1))^(2*(c*y/Real.pi)+1))/(a/z^4))/(1/B) :=
      div_le_div_of_nonneg_left hb (by positivity) hlow
    _ = _ := by rw [show 2*(c*y/Real.pi)+1=2*c*y/Real.pi+1 by ring];field_simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
