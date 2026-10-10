import OAI.Analysis.PlaneSpectrum.Energy
import OAI.Analysis.PlaneSpectrum.Selections

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
lemma equal_moduli_quadratic (A B L : ℝ) (hL : L^2 = A*B) (u : Circle) :
    ‖(A : ℂ) - B*(u : ℂ)^2‖ =
      ‖-(L : ℂ) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2‖ := by
  have hu : (u : ℂ) * conj (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hreal : (u : ℂ).re^2 + (u : ℂ).im^2 = 1 := by
    simpa only [Complex.normSq_apply, sq] using Circle.normSq_coe u
  have hleft : (A : ℂ) - B*(u : ℂ)^2 =
      (u : ℂ) * ((A : ℂ)*conj (u : ℂ) - B*(u : ℂ)) := by
    calc
      _ = A*((u : ℂ)*conj (u : ℂ)) - B*(u : ℂ)^2 := by rw [hu, mul_one]
      _ = _ := by ring
  have hright : -(L : ℂ) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2 =
      (u : ℂ) * (((A-B : ℝ) : ℂ) + L*((u : ℂ)-conj (u : ℂ))) := by
    calc
      _ = -L*((u : ℂ)*conj (u : ℂ)) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2 := by rw [hu, mul_one]
      _ = _ := by ring
  rw [hleft, hright, norm_mul, norm_mul, Circle.norm_coe, one_mul, one_mul]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.mul_im,
    Complex.add_re, Complex.add_im, zero_mul, sub_zero, zero_add, add_zero]
  nlinarith [mul_self_nonneg (A-B), mul_self_nonneg (A+B),
    congrArg (fun x : ℝ => (A-B)^2*x) hreal,
    congrArg (fun x : ℝ => 4*x*(u : ℂ).im^2) hL]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

include hq hqcov in
lemma projectedMass_pair_mean [IsProbabilityMeasure (μ.map q)] (M : Amenable.Mean Rot) (a b : E) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q
      (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b)))) =
      projectedMass μ q a * projectedMass μ q b := by
  exact conditional_pair_energy μ q hq (fun g : Rot => hqcov (rotMul g)) M
    (scaleHom (G := Rot) 2) (rot_zsmul_surjective 2 (by decide)) (char a) (char b)

lemma kCoeff_scale_two (g : Rot) : kCoeff (rotMul ((scaleHom (G := Rot) 2) g)) = kCoeff (rotMul g)^2 := by
  change kCoeff ((rotMul g)^2) = _
  simp only [pow_two, kCoeff_mul]
lemma kCoeff_scale_one (g : Rot) : kCoeff (rotMul ((scaleHom (G := Rot) 1) g)) = kCoeff (rotMul g) := by
  change kCoeff (rotMul ((1:ℤ) • g)) = _
  rw [one_zsmul]
lemma char_two_term (a b : E) (g : Rot) :
    (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b)) g =
      char (a + kCoeff (rotMul g)^2*b) := by
  simp only [Family.mul_apply, Family.const_apply, Family.orbit_apply, char_act,
    kCoeff_scale_two, char_add]
lemma char_three_term (a b c : E) (g : Rot) :
    (Family.orbit (scaleHom (G := Rot) 0) (char a) * Family.orbit (scaleHom (G := Rot) 1) (char b) *
      Family.orbit (scaleHom (G := Rot) 2) (char c)) g =
      char (a+kCoeff (rotMul g)*b+kCoeff (rotMul g)^2*c) := by
  simp only [Family.mul_apply, Family.orbit_apply, char_act, kCoeff_scale_one, kCoeff_scale_two,
    char_add]
  congr 2
  change char (kCoeff (rotMul ((0:ℤ) • g))*a) = char a
  simp only [zero_zsmul]
  change char (1*a) = char a
  rw [one_mul]

include hq hqcov in
lemma quadratic_mass_inequality (a b l h k : E)
    (hn : ∀ u : K, ‖((a + kCoeff u^2*b : E) : ℂ)‖ =
      ‖((l+kCoeff u*h+kCoeff u^2*k : E) : ℂ)‖) :
    projectedMass μ q a * projectedMass μ q b ≤ projectedMass μ q h := by
  let : ErgodicVAdd Rot Y (μ.map q) := factor_ergodic μ q hq (fun g : Rot => hqcov (rotMul g))
  let M : Amenable.Mean Rot := MovingMean.toMean (fun _ => 0)
  have he : Family.energy (μ.map q) (Family.conditional μ q
      (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b))) =
      Family.energy (μ.map q) (Family.conditional μ q
        (Family.orbit (scaleHom (G := Rot) 0) (char l) * Family.orbit (scaleHom (G := Rot) 1) (char h) *
          Family.orbit (scaleHom (G := Rot) 2) (char k))) := by
    ext g
    simp only [Family.energy_apply, Family.conditional_apply, char_two_term, char_three_term]
    exact projectedMass_radial μ q hq hqcov (hn (rotMul g))
  rw [← projectedMass_pair_mean μ q hq hqcov M a b, he,
    conditional_integer_triple_energy μ q hq (fun g : Rot => hqcov (rotMul g)) rot_zsmul_surjective]
  calc
    _ ≤ M.map (BoundedContinuousFunction.const Rot (projectedMass μ q h)) := by
      apply M.mono
      intro g
      simp only [Family.energy_apply, Family.mul_apply, Family.orbit_apply,
        BoundedContinuousFunction.const_apply]
      have h1 := l2_mul_norm_le (μ.map q)
        (act (scaleHom (G := Rot) 0 g) (conditional μ q (char l)) * act (scaleHom (G := Rot) 1 g) (conditional μ q (char h)))
        (act (scaleHom (G := Rot) 2 g) (conditional μ q (char k)))
        (fun y => projected_char_bound μ q k ((scaleHom (G := Rot) 2 g) +ᵥ y))
      have h2 := l2_norm_mul_le (μ.map q)
        (act (scaleHom (G := Rot) 0 g) (conditional μ q (char l))) (act (scaleHom (G := Rot) 1 g) (conditional μ q (char h)))
        (fun y => projected_char_bound μ q l ((scaleHom (G := Rot) 0 g) +ᵥ y))
      simp only [one_mul, l2_act, LinearIsometryEquiv.norm_map] at h1 h2
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    _ = _ := M.map_const _
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

def sqrtF (a : F) : F := ⟨Real.sqrt a, mem_algebraicClosure_iff.mpr (by
  by_cases ha : 0 ≤ (a : ℝ)
  · apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [Real.sq_sqrt ha]
    exact mem_algebraicClosure_iff.mp a.property
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ha)]
    exact isAlgebraic_zero)⟩
lemma sqrtF_sq (a : F) (ha : 0 ≤ a) : sqrtF a ^ 2 = a := by
  apply Subtype.ext
  exact Real.sq_sqrt ha
lemma norm_ofF (a : F) : ‖((ofF a : E) : ℂ)‖ = |(a : ℝ)| := by
  change ‖((a : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs]

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
def massReal (a : F) : ℝ := projectedMass μ q (ofF a)
include hq hqcov in
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
lemma projectedMass_neg (a : E) : projectedMass μ q (-a) = projectedMass μ q a := by
  apply projectedMass_radial μ q hq hqcov
  exact norm_neg (a : ℂ)
include hq hqcov in
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
lemma massReal_abs (a : F) : massReal μ q |a| = massReal μ q a := by
  apply projectedMass_radial μ q hq hqcov
  rw [norm_ofF, norm_ofF]
  change abs (abs (a : ℝ)) = abs (a : ℝ)
  exact abs_abs _
include hq hqcov in
lemma massReal_difference (A B : F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    massReal μ q A * massReal μ q B ≤ massReal μ q |A-B| := by
  let l := sqrtF (A*B)
  have hl : (l : ℝ)^2 = (A : ℝ)*(B : ℝ) := by
    exact congrArg (fun x : F => (x : ℝ)) (sqrtF_sq (A*B) (mul_nonneg hA hB))
  have he := quadratic_mass_inequality μ q hq hqcov (ofF A) (-ofF B) (-ofF l) (ofF (A-B)) (ofF l) (fun u => by
    have hh := equal_moduli_quadratic (A : ℝ) (B : ℝ) (l : ℝ) hl u.val
    convert hh using 1 <;> congr 1 <;> simp only [map_sub, ofF, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, kCoeff] <;> push_cast <;> ring)
  rw [projectedMass_neg μ q hq hqcov] at he
  rw [massReal_abs μ q hq hqcov]
  exact he
end PlaneFiveColor.Spectral
end

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.Arithmetic

lemma reF_sum {ι : Type*} (s : Finset ι) (z : ι → E) : reF (∑ i ∈ s,z i) = ∑ i ∈ s,reF (z i) := by
  apply Subtype.ext
  simp [reF]
lemma reF_zsmul (a : ℤ) (z : E) : reF (a • z) = a • reF z := by
  apply Subtype.ext
  simp only [reF, zsmul_eq_mul]
  push_cast
  simp
lemma reF_nsmul (a : ℕ) (z : E) : reF (a • z) = a • reF z := by
  apply Subtype.ext
  simp only [reF,nsmul_eq_mul]
  push_cast
  simp

/-- The signed capped-residue conclusion for any integral transverse selection. -/
lemma selected_mass_bound (m : F → ℝ) (hm0 : m 0 = 1)
    (hd : ∀ a b : F, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (r : F) (hr : 0 < r) {n : ℕ} (k : Fin n → E) (a b : Fin n → ℤ)
    (D M : ℕ) (hD : 0 < D) (hM : 0 < M)
    (ha : (∑ j, a j • k j) = D • (1:E))
    (hb : (∑ j, b j • k j) = D • imagUnit)
    (hab : (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M)
    (v : E) (hv : ‖(v:ℂ)‖ = 1) (hsmall : |reF v| < (M:F)⁻¹)
    (hgood : ∀ j, c ≤ m |2*r*reF (k j*v)|) :
    c^(4*M) ≤ m |2*r*D*reF v| := by
  classical
  have hac : (∑ j, a j • (k j:ℂ)) = D • (1:ℂ) := by
    have he := congrArg (fun z : E => (z:ℂ)) ha
    simpa using he
  have hbc : (∑ j, b j • (k j:ℂ)) = D • Complex.I := by
    have he := congrArg (fun z : E => (z:ℂ)) hb
    simpa [imagUnit] using he
  obtain ⟨i,hi⟩ := selection_transverse (fun j => (k j:ℂ)) a b D M hD hac hbc hab (v:ℂ) hv
  have hmax (j : Fin n) : |reF (k j*v)| ≤ |reF (k i*v)| := by
    exact_mod_cast (hi j).1
  have htrans : (D:F) ≤ (M:F)*|reF (k i*v)| := by exact_mod_cast (hi i).2
  have hDp : (0:F) < D := Nat.cast_pos.mpr hD
  have hMp : (0:F) < M := Nat.cast_pos.mpr hM
  have hip : 0 < |reF (k i*v)| := by nlinarith
  let x := fun j => 2*r*reF (k j*v)
  let p := |x i|
  have hx (j : Fin n) : |x j| = 2*r*|reF (k j*v)| := by
    dsimp [x]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2*r)]
  have hp : 0 < p := by dsimp [p]; rw [hx]; positivity
  have hsum : (∑ j, a j • x j) = 2*r*D*reF v := by
    have he := congrArg reF (congrArg (fun z : E => z*v) ha)
    simp only [Finset.sum_mul,reF_sum,smul_mul_assoc,reF_zsmul,one_mul,reF_nsmul] at he
    calc
      (∑ j, a j • x j) = 2*r * ∑ j, a j • reF (k j*v) := by
        simp only [x,Finset.mul_sum,zsmul_eq_mul]; congr 1; ext j; ring_nf
      _ = 2*r*D*reF v := by rw [he,nsmul_eq_mul]; ring
  have hz : |∑ j, a j • x j| < p := by
    rw [hsum,abs_mul,abs_of_pos (by positivity : (0:F) < 2*r*D)]
    dsimp only [p]
    rw [hx]
    have hvM : (M:F)*|reF v| < 1 := by
      have hh := mul_lt_mul_of_pos_left hsmall hMp
      rwa [mul_inv_cancel₀ hMp.ne'] at hh
    have ht : (D:F)*|reF v| < |reF (k i*v)| := by
      have hh := mul_le_mul_of_nonneg_right htrans (abs_nonneg (reF v))
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left ht (by positivity : (0:F) < 2*r)]
  have hcap := CappedResidues.integer_abs_cap m hm0 hd c hc0 hc1 hp
    (by simpa only [CappedResidues.Good,p,pow_one] using hgood i)
    Finset.univ a x (fun j _ => ⟨by dsimp only [p]; rw [hx,hx]; exact mul_le_mul_of_nonneg_left (hmax j) (by positivity),
      by simpa only [CappedResidues.Good,pow_one] using hgood j⟩) hz
  have hlen : ∑ j, (a j).natAbs ≤ M := by
    calc
      _ ≤ ∑ j, ((a j).natAbs+(b j).natAbs) := Finset.sum_le_sum (fun j _ => Nat.le_add_right _ _)
      _ ≤ M := hab
  have hpow : c^(4*M) ≤ c^(4*∑ j,(a j).natAbs) :=
    pow_le_pow_of_le_one hc0 hc1 (Nat.mul_le_mul_left 4 hlen)
  exact hpow.trans (by simpa only [CappedResidues.Good,hsum] using hcap)
end PlaneFiveColor.Spectral
end

noncomputable section
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.Arithmetic

lemma circle_realPart (t : F) (ht : |t| ≤ 1) :
    ∃ v : E, ‖(v:ℂ)‖ = 1 ∧ reF v = t := by
  let y := sqrtF (1-t^2)
  have hy : y^2 = 1-t^2 := sqrtF_sq _ (by have hh := sq_le_sq₀ (abs_nonneg t) zero_le_one |>.mpr ht; nlinarith [sq_abs t])
  let v := ofF t + imagUnit * ofF y
  have hv : (v:ℂ) = (t:ℝ) + Complex.I*(y:ℝ) := rfl
  refine ⟨v,?_,?_⟩
  · have hh : ‖(v:ℂ)‖^2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq,hv]
      simp only [Complex.normSq_apply, Complex.add_re,Complex.add_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        zero_mul,one_mul,mul_zero,sub_zero,add_zero,zero_add]
      have hyc : (y:ℝ)^2 = 1-(t:ℝ)^2 := by exact_mod_cast hy
      nlinarith
    nlinarith [norm_nonneg (v:ℂ)]
  · apply Subtype.ext
    change (v:ℂ).re = (t:ℝ)
    simp [hv]

/-- Arithmetic propagation: one syndetic positive mass level forces uniformly
positive mass at every sufficiently small positive algebraic radius. -/
lemma cover_mass_positive (m : F → ℝ) (hm0 : m 0 = 1)
    (hd : ∀ a b : F, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (r : F) (hr : 0 < r) (Q : Finset E) (hQ : ∀ q ∈ Q, ‖(q:ℂ)‖ = 1)
    (hcover : ∀ v : E, ‖(v:ℂ)‖ = 1 → ∃ q ∈ Q, c ≤ m |2*r*reF (q*v)|) :
    ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ s : F, 0 < s → s < δ → ε ≤ m s := by
  classical
  let A : ℂ → Prop := fun w => ∃ z : E, (z:ℂ) = w ∧ c ≤ m |2*r*reF z|
  have hQN : ∀ q ∈ Q.image (fun z : E => (z:ℂ)), ‖q‖ = 1 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    exact hQ z hz
  have hQA : ∀ q ∈ Q.image (fun z : E => (z:ℂ)), IsAlgebraic ℚ q := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    exact mem_algebraicClosure_iff.mp z.property
  have hA : ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v → ∃ q ∈ Q.image (fun z : E => (z:ℂ)), A (q*v) := by
    intro v hv hva
    let v' : E := ⟨v,mem_algebraicClosure_iff.mpr hva⟩
    obtain ⟨q,hq,hgood⟩ := hcover v' hv
    exact ⟨q,Finset.mem_image.mpr ⟨q,hq,rfl⟩,q*v',rfl,hgood⟩
  obtain ⟨D,M,hD,hM,hsel⟩ := uniform_selection _ hQN hQA A hA
  have hDp : (0:F) < D := Nat.cast_pos.mpr hD
  have hMp : (0:F) < M := Nat.cast_pos.mpr hM
  let δ : F := 2*r*D/(M+1)
  refine ⟨δ,by dsimp [δ]; positivity,c^(4*M),pow_pos hc0 _,pow_le_one₀ hc0.le hc1,?_⟩
  intro s hs hsδ
  let t := s/(2*r*D)
  have ht : 0 < t := div_pos hs (by positivity)
  have htM : t < ((M:F)+1)⁻¹ := by
    dsimp [t,δ] at *
    apply (div_lt_iff₀ (by positivity : (0:F) < 2*r*D)).mpr
    simpa only [div_eq_mul_inv,mul_comm] using hsδ
  have ht1 : |t| ≤ 1 := by
    rw [abs_of_pos ht]
    have hh : ((M:F)+1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
    exact htM.le.trans hh
  obtain ⟨v,hv,hvt⟩ := circle_realPart t ht1
  obtain ⟨n,k,a,b,hkg,ha,hb,hab⟩ := hsel (v:ℂ) hv (mem_algebraicClosure_iff.mp v.property)
  let k' : Fin n → E := fun j => ⟨k j,mem_algebraicClosure_iff.mpr (hkg j).2.1⟩
  have ha' : (∑ j, a j • k' j) = D • (1:E) := by
    apply Subtype.ext
    simpa [k'] using ha
  have hb' : (∑ j, b j • k' j) = D • imagUnit := by
    apply Subtype.ext
    simpa [k',imagUnit] using hb
  have hgood (j : Fin n) : c ≤ m |2*r*reF (k' j*v)| := by
    obtain ⟨z,hz,hg⟩ := (hkg j).2.2
    have he : z = k' j*v := Subtype.ext hz
    rwa [he] at hg
  have hsmall : |reF v| < (M:F)⁻¹ := by
    rw [hvt,abs_of_pos ht]
    exact htM.trans (inv_lt_inv₀ (by positivity : (0:F) < M+1) hMp |>.mpr (by linarith))
  have hh := selected_mass_bound m hm0 hd c hc0.le hc1 r hr k' a b D M hD hM ha' hb' hab v hv hsmall hgood
  convert hh using 1
  have he : 2*r*(D:F)*reF v = s := by rw [hvt]; dsimp [t]; field_simp
  rw [he,abs_of_pos hs]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
lemma kCoeff_scale_neg_one (g : Rot) :
    ((kCoeff (rotMul (scaleHom (G := Rot) (-1) g)) : E) : ℂ) = conj ((kCoeff (rotMul g) : E) : ℂ) := by
  change ((rotMul ((-1:ℤ) • g)).val : ℂ) = _
  rw [neg_one_zsmul]
  exact Circle.coe_inv_eq_conj _
lemma char_symmetric (r : F) (g : Rot) :
    (Family.orbit (scaleHom (G := Rot) 1) (char (ofF r)) *
      Family.orbit (scaleHom (G := Rot) (-1)) (char (ofF r))) g =
      char (ofF (2*r*reF (kCoeff (rotMul g)))) := by
  simp only [Family.mul_apply, Family.orbit_apply, char_act, kCoeff_scale_one, ← char_add]
  congr 1
  apply Subtype.ext
  change ((kCoeff (rotMul g) : E) : ℂ)*(r : ℝ) +
    ((kCoeff (rotMul (scaleHom (G := Rot) (-1) g)) : E) : ℂ)*(r : ℝ) =
    ((2*r*reF (kCoeff (rotMul g)) : F) : ℝ)
  rw [kCoeff_scale_neg_one]
  push_cast
  change _ = 2*(r : ℝ)*(((kCoeff (rotMul g) : E) : ℂ).re : ℂ)
  apply Complex.ext <;> simp
  ring

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
def radiusFamily (r : F) : Rot →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => massReal μ q (2*r*reF (kCoeff (rotMul g)))) continuous_of_discreteTopology 1
    (fun g => by
      rw [Real.norm_eq_abs]
      change |projectedMass μ q (ofF _)| ≤ 1
      rw [abs_of_nonneg (projectedMass_nonneg _ _ _)]
      exact projectedMass_le_one μ q hq _)
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicSMul K D μ]
  [MulAction K Y] [MeasurableConstSMul K Y]
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
@[simp] lemma radiusFamily_apply (r : F) (g : Rot) :
    radiusFamily μ q hq r g = massReal μ q (2*r*reF (kCoeff (rotMul g))) := rfl
include hq hqcov in
lemma radiusFamily_mean (r : F) (M : Amenable.Mean Rot) :
    M.map (radiusFamily μ q hq r) = massReal μ q r ^2 := by
  have he : radiusFamily μ q hq r = Family.energy (μ.map q) (Family.conditional μ q
      (Family.orbit (scaleHom (G := Rot) 1) (char (ofF r)) *
        Family.orbit (scaleHom (G := Rot) (-1)) (char (ofF r)))) := by
    ext g
    simp only [radiusFamily_apply, Family.energy_apply, Family.conditional_apply, char_symmetric]
    rfl
  rw [he, conditional_integer_pair_energy μ q hq (fun g : Rot => hqcov (rotMul g))
    rot_zsmul_surjective M (by decide : (1:ℤ) ≠ -1)]
  exact (pow_two _).symm
include hq hqcov in
lemma radius_syndetic (r : F) (c : ℝ) (hc : c < massReal μ q r ^2) :
    ∃ S : Finset Rot, ∀ v : Rot, ∃ s ∈ S,
      c < massReal μ q (2*r*reF (kCoeff (rotMul (v+s)))) := by
  apply MovingMean.syndetic_of_all_means (radiusFamily μ q hq r) c
  intro M
  rwa [radiusFamily_mean μ q hq hqcov r M]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

include hq hqcov in
lemma radial_positive_near_zero (r : F) (hr : 0 < r) (hm : massReal μ q r ≠ 0) :
    ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ s : F, 0 < s → s < δ → ε ≤ massReal μ q s := by
  classical
  let c := massReal μ q r ^2/2
  have hp : 0 < massReal μ q r := lt_of_le_of_ne (projectedMass_nonneg μ q _) (Ne.symm hm)
  have hc : 0 < c := div_pos (sq_pos_of_pos hp) (by norm_num)
  have hc1 : c ≤ 1 := by
    have h := projectedMass_le_one μ q hq (ofF r)
    change massReal μ q r ≤ 1 at h
    dsimp [c]; nlinarith
  obtain ⟨S,hS⟩ := radius_syndetic μ q hq hqcov r c (by dsimp [c]; nlinarith)
  let Q := S.image (fun s => kCoeff (rotMul s))
  apply cover_mass_positive (massReal μ q) (projectedMass_zero μ q hq)
    (massReal_difference μ q hq hqcov) c hc hc1 r hr Q
  · intro z hz
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    exact Circle.norm_coe _
  · intro v hv
    let u : K := ⟨⟨(v:ℂ),mem_sphere_zero_iff_norm.mpr hv⟩,mem_algebraicClosure_iff.mp v.property⟩
    obtain ⟨s,hs,hsg⟩ := hS (mulRot u)
    refine ⟨kCoeff (rotMul s),Finset.mem_image.mpr ⟨s,hs,rfl⟩,?_⟩
    rw [massReal_abs μ q hq hqcov]
    have he : kCoeff (rotMul (mulRot u+s)) = kCoeff (rotMul s)*v := by
      change kCoeff (u*rotMul s) = _
      rw [kCoeff_mul,mul_comm]
      rfl
    rw [he] at hsg
    exact hsg.le

include hq hqcov in
lemma massReal_vanish (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (r : F) (hr : 0 < r) : massReal μ q r = 0 := by
  by_contra hn
  obtain ⟨δ,hδ,ε,hε,hε1,hpos⟩ := radial_positive_near_zero μ q hq hqcov r hr hn
  let ν := DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)
  have he (t : F) : lineFourier ν 1 t = (massReal μ q t : ℂ) := by
    simpa only [ν,massReal,lineFourier_eq,one_mul] using differenceFourier_projectedMass μ q hq (ofF t)
  obtain ⟨t,ht,htδ,htε⟩ := exists_small_wild_parameter ({()} : Finset Unit) (by simp)
    ν hw (fun _ => (1:E)) (fun _ => one_ne_zero)
    (fun i t => by rw [he,Complex.ofReal_re]; exact projectedMass_nonneg μ q _)
    (show 0 < (δ:ℝ) from hδ) hε hε1
  have htest : massReal μ q t < ε := by
    have hh := htε () (by simp)
    rwa [he,Complex.ofReal_re] at hh
  have hgood := hpos |t| (abs_pos.mpr ht) (by exact_mod_cast htδ)
  rw [massReal_abs μ q hq hqcov] at hgood
  exact (not_lt_of_ge hgood) htest
end PlaneFiveColor.Spectral
end

end OAI
