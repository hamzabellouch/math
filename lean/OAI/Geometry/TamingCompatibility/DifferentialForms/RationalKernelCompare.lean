import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationKernel

namespace OAI

section

noncomputable section
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V]
lemma rationalKernel_compare {r C : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (z w : V)
    (hz : ‖w‖ ≤ C*‖z‖) : rationalKernel r z ≤ C^6*rationalKernel r w := by
  have hCp : 0 ≤ C := le_trans zero_le_one hC
  have hd : r^2+‖w‖^2 ≤ C^2*(r^2+‖z‖^2) := by
    have hs : ‖w‖^2 ≤ (C*‖z‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hc : 1 ≤ C^2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
    nlinarith
  have hd3 := pow_le_pow_left₀ (by positivity : 0 ≤ r^2+‖w‖^2) hd 3
  have hh : (r^2+‖w‖^2)^3 ≤ C^6*(r^2+‖z‖^2)^3 := by
    simpa only [mul_pow,←pow_mul] using hd3
  unfold rationalKernel
  rw [←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ r^4*(C^6*(r^2+‖z‖^2)^3) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring
end TamingCompatibility.Concentration

namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V]
lemma rationalKernel_profile {r : ℝ} (hr : 0 < r) (z : V) :
    rationalKernel r z ≤ (8/r^2)*((1+‖z‖/r)⁻¹)^6 := by
  have hs : 0 < r^2+‖z‖^2 := by positivity
  have ht : 0 < r+‖z‖ := by positivity
  have he : ((1+‖z‖/r)⁻¹)^6 = r^6/(r+‖z‖)^6 := by field_simp
  rw [he,rationalKernel]
  have he' : (8/r^2)*(r^6/(r+‖z‖)^6) = 8*r^4/(r+‖z‖)^6 := by field_simp
  rw [he']
  apply (div_le_div_iff₀ (pow_pos hs 3) (pow_pos ht 6)).mpr
  have hsq : (r+‖z‖)^2 ≤ 2*(r^2+‖z‖^2) := by nlinarith [sq_nonneg (r-‖z‖)]
  have hh := pow_le_pow_left₀ (sq_nonneg (r+‖z‖)) hsq 3
  have hh' : (r+‖z‖)^6 ≤ 8*(r^2+‖z‖^2)^3 := by nlinarith [hh]
  nlinarith [mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤ r^4)]
end TamingCompatibility.Concentration

end
end

section

noncomputable section
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V]
lemma profile_le_rationalKernel {r C d : ℝ} (hr : 0 < r) (hC : 1 ≤ C)
    (hd : 0 ≤ d) (z : V) (hz : ‖z‖ ≤ C*d) :
    (1/r^2)*((1+d/r)⁻¹)^6 ≤ C^6*rationalKernel r z := by
  have ht : 0 < r+d := by positivity
  have hs : 0 < r^2+‖z‖^2 := by positivity
  have hCp : 0 ≤ C := le_trans zero_le_one hC
  have he : (1/r^2)*((1+d/r)⁻¹)^6 = r^4/(r+d)^6 := by field_simp
  rw [he,rationalKernel,←mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos ht 6) (pow_pos hs 3)).mpr
  have hsq : r^2+‖z‖^2 ≤ C^2*(r+d)^2 := by
    have hz2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hc : 1 ≤ C^2 := by nlinarith
    have ht' := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
    have hrd := mul_nonneg (mul_nonneg hCp hCp) (mul_nonneg hr.le hd)
    nlinarith
  have hpow := pow_le_pow_left₀ hs.le hsq 3
  have hpow' : (r^2+‖z‖^2)^3 ≤ C^6*(r+d)^6 := by
    simpa only [mul_pow,←pow_mul] using hpow
  calc
    _ ≤ r^4*(C^6*(r+d)^6) := mul_le_mul_of_nonneg_left hpow' (by positivity)
    _ = _ := by ring

lemma profile_away {r d δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hd : δ ≤ d) :
    (1/r^2)*((1+d/r)⁻¹)^6 ≤ r^4/δ^6 := by
  have ht : 0 < r+d := by linarith
  have he : (1/r^2)*((1+d/r)⁻¹)^6 = r^4/(r+d)^6 := by field_simp
  rw [he]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hδ.le (by linarith : δ ≤ r+d) 6)
end TamingCompatibility.Concentration

end
end

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def skew (a b w : V) : V := ⟪b,w⟫ • a - ⟪a,w⟫ • b

def transverse (u v z : V) : V := z - ⟪u,z⟫ • u - ⟪v,z⟫ • v

def detInner (u v a b : V) : ℝ := ⟪u,a⟫*⟪v,b⟫-⟪u,b⟫*⟪v,a⟫

lemma norm_skew_sq (a b w : V) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    ‖skew a b w‖^2 = ⟪a,w⟫^2+⟪b,w⟫^2 := by
  have hba : ⟪b,a⟫ = 0 := (real_inner_comm _ _).trans hab
  rw [← real_inner_self_eq_norm_sq]
  simp only [skew,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,ha,hb,hab,hba,one_pow]
  ring

lemma norm_transverse_sq (u v z : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖transverse u v z‖^2 = ‖z‖^2-⟪u,z⟫^2-⟪v,z⟫^2 := by
  have hvu : ⟪v,u⟫ = 0 := (real_inner_comm _ _).trans huv
  rw [← real_inner_self_eq_norm_sq]
  simp only [transverse,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu,hv,huv,hvu,
    real_inner_comm z u,real_inner_comm z v,one_pow]
  ring

lemma norm_skew_le (a b w : V) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    ‖skew a b w‖ ≤ ‖w‖ := by
  have hh := norm_skew_sq a b w ha hb hab
  have ht := norm_transverse_sq a b w ha hb hab
  nlinarith [sq_nonneg ‖transverse a b w‖,norm_nonneg w,norm_nonneg (skew a b w)]

lemma skew_orthogonal (a b w : V) : ⟪w,skew a b w⟫ = 0 := by
  simp only [skew,inner_sub_right,real_inner_smul_right,real_inner_comm w a,real_inner_comm w b]
  ring

lemma inner_skew (u v a b : V) : ⟪u,skew a b v⟫ = detInner u v a b := by
  simp only [skew,inner_sub_right,real_inner_smul_right,detInner,real_inner_comm b v,real_inner_comm a v]
  ring

lemma first_variation_bound (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    |⟪z,u-skew a b v⟫| ≤
      (1-detInner u v a b)*‖z‖ +
        Real.sqrt (2*(1-detInner u v a b))*‖transverse u v z‖ := by
  let e := u-skew a b v
  have hesq : ‖e‖^2 ≤ 2*(1-detInner u v a b) := by
    have hh := norm_skew_le a b v ha hb hab
    rw [hv] at hh
    have heq : ‖e‖^2 = 1+‖skew a b v‖^2-2*detInner u v a b := by
      dsimp [e]
      rw [norm_sub_sq_real,hu,inner_skew]
      ring
    nlinarith [norm_nonneg (skew a b v)]
  have hd : 0 ≤ 1-detInner u v a b := by nlinarith [sq_nonneg ‖e‖]
  have hen : ‖e‖ ≤ Real.sqrt (2*(1-detInner u v a b)) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hesq
  have heu : ⟪u,e⟫ = 1-detInner u v a b := by
    simp only [e,inner_sub_right,real_inner_self_eq_norm_sq,hu,one_pow,inner_skew]
  have hev : ⟪v,e⟫ = 0 := by
    rw [show e = u-skew a b v from rfl,inner_sub_right,skew_orthogonal,sub_zero,real_inner_comm,huv]
  have heq : ⟪z,e⟫ = ⟪u,z⟫*(1-detInner u v a b)+⟪transverse u v z,e⟫ := by
    simp only [transverse,inner_sub_left,real_inner_smul_left,heu,hev,mul_zero,sub_zero]
    ring
  calc
    |⟪z,e⟫| ≤ |⟪u,z⟫*(1-detInner u v a b)|+|⟪transverse u v z,e⟫| := by
      rw [heq]; exact abs_add_le _ _
    _ ≤ ‖z‖*(1-detInner u v a b)+‖transverse u v z‖*‖e‖ := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg hd]
        have hh := abs_real_inner_le_norm u z
        rw [hu,one_mul] at hh
        exact mul_le_mul_of_nonneg_right hh hd
      · exact abs_real_inner_le_norm _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hen (norm_nonneg (transverse u v z))
      nlinarith
end TamingCompatibility.PlaneVariation

end
end

end OAI
