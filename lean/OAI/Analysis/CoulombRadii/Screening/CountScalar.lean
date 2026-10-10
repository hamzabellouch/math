import Mathlib
import OAI.Analysis.CoulombRadii.Screening.SharpThinScreening

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma screenMass_inv_cube_le (δ : ℝ) (a : ℝ) : (a^3)⁻¹ ≤ screenMass δ a :=
  (le_max_left _ _).trans (screenMass_ge_base δ a)

lemma screenMass_square_ge (δ a : ℝ) : screenMass δ a ≤ (screenMass δ a)^2 := by
  nlinarith [screenMass_ge_one δ a]

lemma screenMass_pairscale (δ : ℝ) {a : ℝ} (ha : 0 < a) : screenMass δ a/a ≤ (screenMass δ a)^2 := by
  apply (div_le_iff₀ ha).mpr
  have H := mul_le_mul_of_nonneg_left (screenMass_scale δ ha) (screenMass_pos δ a).le
  nlinarith

lemma screenMass_kinetic_scale (δ : ℝ) {a : ℝ} (ha : 0 < a) :
    (screenMass δ a)^(4/3:ℝ)/a ≤ (screenMass δ a)^2 := by
  let m := screenMass δ a
  have hm : 0  <  m := screenMass_pos δ a
  have h13 : 1 ≤ a*m^(1/3:ℝ) := (screenBaseMass_cuberoot_scale ha).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (screenBaseMass_nonneg a) (screenMass_ge_base δ a) (by norm_num)) ha.le)
  have h23 : 1 ≤ a*m^(2/3:ℝ) := h13.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (screenMass_ge_one δ a) (by norm_num : (1/3:ℝ) ≤ 2/3)) ha.le)
  have H := mul_le_mul_of_nonneg_left h23 (Real.rpow_nonneg hm.le (4/3:ℝ))
  have he : m^(4/3:ℝ)*(a*m^(2/3:ℝ))=m^2*a := by
    calc
      _ = a*(m^(4/3:ℝ)*m^(2/3:ℝ)) := by ring
      _ = _ := by rw [←Real.rpow_add hm]; norm_num; ring
  rw [mul_one,he] at H
  exact (div_le_iff₀ ha).mpr H

lemma sqrt_cap_expression {C P m a : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hm : 0 ≤ m) (ha : 0 < a) :
    Real.sqrt (C*P*m^2/a^2)=Real.sqrt C*Real.sqrt P*m/a := by
  rw [Real.sqrt_div (mul_nonneg (mul_nonneg hC hP) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hC hP),Real.sqrt_mul hC,Real.sqrt_sq hm,Real.sqrt_sq ha.le]

lemma sqrt_deleted_expression {C D P m a β : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : 0 ≤ P) (hm : 0 ≤ m) (ha : 0 < a) (hβ : 0 ≤ β) :
    Real.sqrt ((C*P*m^2/a^2)*(18*D*(β*a/a)*P*m^2))=
      Real.sqrt (18*C*D)*Real.sqrt β*P*m^2/a := by
  have he : (C*P*m^2/a^2)*(18*D*(β*a/a)*P*m^2)=(18*C*D)*β*(P*m^2/a)^2 := by field_simp
  rw [he,Real.sqrt_mul (mul_nonneg (by positivity) hβ),Real.sqrt_mul (by positivity),
    Real.sqrt_sq (div_nonneg (mul_nonneg hP (pow_nonneg hm 2)) ha.le)]
  ring

lemma sqrt_out_expression {C P m : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hm : 0 ≤ m) :
    Real.sqrt (C*P*m^2)=Real.sqrt C*Real.sqrt P*m := by
  rw [Real.sqrt_mul (mul_nonneg hC hP),Real.sqrt_mul hC,Real.sqrt_sq hm]

lemma fine_count_expression {C P m : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hm : 0 ≤ m) :
    (C*P*m^2)^(2/3:ℝ)=C^(2/3:ℝ)*P^(2/3:ℝ)*m^(4/3:ℝ) := by
  rw [Real.mul_rpow (mul_nonneg hC hP) (sq_nonneg _),Real.mul_rpow hC hP,←Real.rpow_natCast,←Real.rpow_mul hm]
  norm_num

def countBootstrapA : ℝ := 2*tfInteriorCountConstant^2+6*max countTestEnergy 0
 def countBootstrapB : ℝ := 6*max countTestEnergy 0*Real.sqrt (18*atomicPhysicalCapConstant*atomicPatchCountFactor)
 def countBootstrapC : ℝ := 6*max countTestEnergy 0*(thinReserveFactor+12*unitWindowKinetic*Real.sqrt atomicPhysicalCapConstant)
 def countBootstrapD : ℝ := 3*max countTestEnergy 0*(2*Real.pi+1)*Real.sqrt atomicPatchCountFactor
 def countBootstrapE : ℝ := 6*max countTestEnergy 0*((Real.pi^2/2)*neumannBoundary)*atomicPatchCountFactor^(2/3:ℝ)

def countBootstrapMajorant (β P : ℝ) : ℝ := countBootstrapA+countBootstrapB*Real.sqrt β*P+
  (countBootstrapC/β^2+countBootstrapD/β)*Real.sqrt P+countBootstrapE/β^2*P^(2/3:ℝ)

lemma countBootstrap_coefficients_nonneg : 0 ≤ countBootstrapA ∧ 0 ≤ countBootstrapB ∧
    0 ≤ countBootstrapC ∧ 0 ≤ countBootstrapD ∧ 0 ≤ countBootstrapE := by
  have hM : 0 ≤ max countTestEnergy 0 := le_max_right _ _
  have hK := unitWindowKinetic_nonneg
  have hR := thinReserveFactor_nonneg
  have hN := neumannBoundary_nonneg
  have hD := atomicPatchCountFactor_nonneg
  unfold countBootstrapA countBootstrapB countBootstrapC countBootstrapD countBootstrapE
  exact ⟨by positivity,by positivity,by positivity,by positivity [Real.pi_pos],by positivity⟩

lemma atomicComparisonExpression_le_majorant {δ P a β : ℝ} (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (ha : 0 < a) (hβ : 0 < β) :
    atomicComparisonExpression δ P a (β*a) ≤ countBootstrapMajorant β P*(screenMass δ a)^2 := by
  let m := screenMass δ a
  let M := max countTestEnergy 0
  let C := atomicPhysicalCapConstant
  let D := atomicPatchCountFactor
  have hm : 0  <  m := screenMass_pos δ a
  have hM : 0 ≤ M := le_max_right _ _
  have hC : 0 ≤ C := atomicPhysicalCapConstant_nonneg
  have hD : 0 ≤ D := atomicPatchCountFactor_nonneg
  have hK : 0 ≤ unitWindowKinetic := unitWindowKinetic_nonneg
  have hN : 0 ≤ neumannBoundary := neumannBoundary_nonneg
  have hR : 0 ≤ thinReserveFactor := thinReserveFactor_nonneg
  have h1 : 2*(tfInteriorCountConstant/a^3)^2 ≤ 2*tfInteriorCountConstant^2*m^2 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ (a^3)⁻¹)
      (screenMass_inv_cube_le δ a) 2) (show 0 ≤ 2*tfInteriorCountConstant^2 by positivity)
    simpa only [m, div_pow, div_eq_mul_inv, inv_pow, mul_pow, mul_assoc] using H
  have h2 : 6*a*M*δ ≤ 6*M*m^2 := by
    have H := (le_div_iff₀ ha).mp (screenEnergy_ge_offset hδ ha)
    change δ*a ≤ m^2 at H
    nlinarith [mul_le_mul_of_nonneg_left H (show 0 ≤ 6*M by positivity)]
  have h3 := mul_le_mul_of_nonneg_left (screenMass_pairscale δ ha)
    (show 0 ≤ 6*M*thinReserveFactor/β^2*Real.sqrt P by positivity)
  have h4 := mul_le_mul_of_nonneg_left (screenMass_pairscale δ ha)
    (show 0 ≤ 72*M*unitWindowKinetic*Real.sqrt C/β^2*Real.sqrt P by positivity)
  have h5 := mul_le_mul_of_nonneg_left (screenMass_kinetic_scale δ ha)
    (show 0 ≤ 6*M*((Real.pi^2/2)*neumannBoundary)*D^(2/3:ℝ)/β^2*P^(2/3:ℝ) by positivity)
  have h6 := mul_le_mul_of_nonneg_left (screenMass_square_ge δ a)
    (show 0 ≤ 3*M*(2*Real.pi+1)*Real.sqrt D/β*Real.sqrt P by positivity [Real.pi_pos])
  have he : atomicComparisonExpression δ P a (β*a)=
      2*(tfInteriorCountConstant/a^3)^2+6*a*M*δ+
      (6*M*thinReserveFactor/β^2*Real.sqrt P)*(m/a)+
      (72*M*unitWindowKinetic*Real.sqrt C/β^2*Real.sqrt P)*(m/a)+
      (6*M*Real.sqrt (18*C*D)*Real.sqrt β*P)*m^2+
      (6*M*((Real.pi^2/2)*neumannBoundary)*D^(2/3:ℝ)/β^2*P^(2/3:ℝ))*(m^(4/3:ℝ)/a)+
      (3*M*(2*Real.pi+1)*Real.sqrt D/β*Real.sqrt P)*m := by
    unfold atomicComparisonExpression
    rw [sqrt_cap_expression hC hP hm.le ha,sqrt_deleted_expression hC hD hP hm.le ha hβ.le,
      sqrt_out_expression hD hP hm.le,fine_count_expression hD hP hm.le]
    dsimp only [M,C,D,m]
    field_simp
    ring
  rw [he]
  have HH := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) (le_refl ((6*M*Real.sqrt (18*C*D)*Real.sqrt β*P)*m^2))) h5) h6
  apply HH.trans_eq
  unfold countBootstrapMajorant countBootstrapA countBootstrapB countBootstrapC countBootstrapD countBootstrapE
  dsimp only [M,C,D,m]
  ring

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma countBootstrap_small_parameter : ∃ β : ℝ, 0 < β ∧ 18*β ≤ 1 ∧ countBootstrapB*Real.sqrt β < 1/4 := by
  have hB := countBootstrap_coefficients_nonneg.2.1
  let u : ℝ := 1/(100*(countBootstrapB+1))
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1/100 := by
    dsimp [u]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  refine ⟨u^2,by positivity,by nlinarith,?_⟩
  rw [Real.sqrt_sq hu.le]
  have H : countBootstrapB*u < 1/100 := by
    dsimp [u]
    rw [←mul_div_assoc,mul_one]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  linarith

lemma countBootstrap_ratio_limit (β : ℝ) :
    Tendsto (fun P : ℝ => countBootstrapA*P^(-(1:ℝ))+countBootstrapB*Real.sqrt β+
      (countBootstrapC/β^2+countBootstrapD/β)*P^(-(1/2:ℝ))+
      countBootstrapE/β^2*P^(-(1/3:ℝ))) atTop (𝓝 (countBootstrapB*Real.sqrt β)) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul countBootstrapA
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).const_mul (countBootstrapC/β^2+countBootstrapD/β)
  have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).const_mul (countBootstrapE/β^2)
  simpa only [mul_zero,zero_add,add_zero] using ((h1.add tendsto_const_nhds).add h2).add h3

lemma countBootstrap_ratio_identity {β P : ℝ} (hP : 0 < P) :
    countBootstrapMajorant β P=
    (countBootstrapA*P^(-(1:ℝ))+countBootstrapB*Real.sqrt β+
      (countBootstrapC/β^2+countBootstrapD/β)*P^(-(1/2:ℝ))+
      countBootstrapE/β^2*P^(-(1/3:ℝ)))*P := by
  have h (r : ℝ) : P^r*P=P^(r+1) := by
    nth_rw 2 [←Real.rpow_one P]
    rw [←Real.rpow_add hP]
  have h1 := h (-(1:ℝ))
  have h2 := h (-(1/2:ℝ))
  have h3 := h (-(1/3:ℝ))
  norm_num at h1 h2 h3
  calc
    _ = countBootstrapA*(P^(-(1:ℝ))*P)+countBootstrapB*Real.sqrt β*P+
        (countBootstrapC/β^2+countBootstrapD/β)*(P^(-(1/2:ℝ))*P)+
        countBootstrapE/β^2*(P^(-(1/3:ℝ))*P) := by
      rw [h1,h2,h3]
      simp only [countBootstrapMajorant,Real.sqrt_eq_rpow,mul_one]
    _ = _ := by ring

theorem countBootstrap_threshold : ∃ β P₀ : ℝ, 0 < β ∧ 18*β ≤ 1 ∧ 2 ≤ P₀ ∧
    ∀ P ≥ P₀, 1 ≤ β^2*Real.sqrt P ∧ countBootstrapMajorant β P ≤ P/2 := by
  obtain ⟨β,hβ,hβsmall,hβB⟩ := countBootstrap_small_parameter
  obtain ⟨q,hq⟩ := eventually_atTop.mp ((countBootstrap_ratio_limit β).eventually_lt_const
    (show countBootstrapB*Real.sqrt β < 1/2 by linarith))
  let P₀ := max 2 (max q ((β^2)⁻¹^2))
  refine ⟨β,P₀,hβ,hβsmall,le_max_left _ _,?_⟩
  intro P hP
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hP
  have hP0 : 0 < P := by linarith
  have hPq : q ≤ P := (le_max_left _ _).trans ((le_max_right _ _).trans hP)
  have hPt : (β^2)⁻¹^2 ≤ P := (le_max_right _ _).trans ((le_max_right _ _).trans hP)
  constructor
  · have H := Real.sqrt_le_sqrt hPt
    rw [Real.sqrt_sq (by positivity)] at H
    have H' := mul_le_mul_of_nonneg_left H (sq_nonneg β)
    simpa only [mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hβ))] using H'
  · rw [countBootstrap_ratio_identity hP0]
    have H := mul_le_mul_of_nonneg_right (hq P hPq).le hP0.le
    simpa only [one_div,mul_comm (2:ℝ)⁻¹ P,←div_eq_mul_inv] using H

theorem atomic_screenCountParameter_uniform : ∃ P₀ : ℝ, 2 ≤ P₀ ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
      screenCountParameter ψ δ ≤ P₀ := by
  obtain ⟨β,P₀,hβ,hβsmall,hP₀,hthreshold⟩ := countBootstrap_threshold
  refine ⟨P₀,hP₀,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ
  by_contra hbound
  have hPbig : P₀ < screenCountParameter ψ δ := lt_of_not_ge hbound
  let P := screenCountParameter ψ δ
  have hP2 : 2 ≤ P := hP₀.trans hPbig.le
  have hP := screenCountParameter_ge_one ψ δ
  obtain ⟨hcondP,himp⟩ := hthreshold P hPbig.le
  have hbetter : screenCountParameter ψ δ ≤ P/2 := by
    apply screenCountParameter_le_of ψ δ (by dsimp [P] at *; linarith)
    intro y hy
    let a := atomicCellScale y
    have ha : 0 < a := atomicCellScale_pos hy
    have hb : 0 < β*a := mul_pos hβ ha
    have hs : 18*(β*a) ≤ a := by nlinarith [mul_le_mul_of_nonneg_right hβsmall ha.le]
    have hcond : a ≤ (β*a)^2*Real.sqrt P*screenMass δ a := by
      have H := mul_le_mul hcondP (screenMass_scale δ ha) (by norm_num : (0:ℝ)≤1)
        (mul_nonneg (sq_nonneg β) (Real.sqrt_nonneg P))
      have H' := mul_le_mul_of_nonneg_left H ha.le
      nlinarith
    have H := atomic_physical_count_comparison S hatom ψ hψ hm hE hstate hδ hy hb hs hcond
    exact H.trans ((atomicComparisonExpression_le_majorant hδ (by linarith) ha hβ).trans
      (mul_le_mul_of_nonneg_right himp (sq_nonneg _)))
  dsimp [P] at hbetter hP2
  linarith

end Coulomb

end

end OAI
