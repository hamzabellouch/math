import Mathlib
import OAI.Probability.ThreeStateClauses.RadialBounds

namespace OAI

/-! Radial Calculus. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set
namespace ThreeState.TreeClauses.Radial

def rayG₀ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ Real.log (1+t*v i))
def rayG₁ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ v i/(1+t*v i))
def rayG₂ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ -v i^2/(1+t*v i)^2)
def rayG₃ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ 2*v i^3/(1+t*v i)^3)

def rayI₀ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ (1+t*v i)*Real.log (1+t*v i))
def rayI₁ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ v i*Real.log (1+t*v i))
def rayI₂ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ v i^2/(1+t*v i))
def rayI₃ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ -v i^3/(1+t*v i)^2)

def rayH₀ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ (1+t*v i)*Real.log (1+t*v i)^2)
def rayH₁ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ v i*(Real.log (1+t*v i)^2+2*Real.log (1+t*v i)))
def rayH₂ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ (2*v i^2/(1+t*v i))*(Real.log (1+t*v i)+1))
def rayH₃ (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ -2*v i^3*Real.log (1+t*v i)/(1+t*v i)^2)

lemma hasDerivAt_avg {f : ℝ → Vec} {df : Vec} {t : ℝ}
    (hf : ∀ i, HasDerivAt (fun s ↦ f s i) (df i) t) :
    HasDerivAt (fun s ↦ avg (f s)) (avg df) t :=
  (((hf 0).add (hf 1)).add (hf 2)).div_const 3

lemma hasDerivAt_ray_coord (v : Vec) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s : ℝ ↦ 1+s*v i) (v i) t := by
  simpa using (hasDerivAt_mul_const (v i)).const_add (1:ℝ)

lemma hasDerivAt_rayG₀ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayG₀ v) (rayG₁ v t) t :=
  hasDerivAt_avg (fun i ↦ hasDerivAt_log_edge i (hp i))

lemma hasDerivAt_rayG₁ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayG₁ v) (rayG₂ v t) t := by
  apply hasDerivAt_avg
  intro i
  apply ((hasDerivAt_const t (v i)).div (hasDerivAt_ray_coord v t i) (hp i)).congr_deriv
  simp only [zero_mul, zero_sub]; ring

lemma hasDerivAt_rayG₂ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayG₂ v) (rayG₃ v t) t := by
  apply hasDerivAt_avg
  intro i
  apply ((hasDerivAt_const t (-v i^2)).div ((hasDerivAt_ray_coord v t i).pow 2) (pow_ne_zero 2 (hp i))).congr_deriv
  dsimp
  field_simp [hp i]; ring

lemma hasDerivAt_rayI₀ {v : Vec} (hv : avg v = 0) {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayI₀ v) (rayI₁ v t) t := by
  have hd := hasDerivAt_avg (fun i ↦
    (hasDerivAt_ray_coord v t i).mul (hasDerivAt_log_edge i (hp i)))
  apply hd.congr_deriv
  simp only [rayI₁, avg] at *
  have he (i : Fin 3) : (1+t*v i)*(v i/(1+t*v i)) = v i := by field_simp [hp i]
  simp_rw [he]
  linarith

lemma hasDerivAt_rayI₁ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayI₁ v) (rayI₂ v t) t := by
  apply hasDerivAt_avg
  intro i
  apply ((hasDerivAt_log_edge i (hp i)).const_mul (v i)).congr_deriv
  ring

lemma hasDerivAt_rayI₂ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayI₂ v) (rayI₃ v t) t := by
  apply hasDerivAt_avg
  intro i
  apply ((hasDerivAt_const t (v i^2)).div (hasDerivAt_ray_coord v t i) (hp i)).congr_deriv
  simp only [zero_mul, zero_sub]; ring

lemma hasDerivAt_rayH₀ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayH₀ v) (rayH₁ v t) t := by
  apply hasDerivAt_avg
  intro i
  apply ((hasDerivAt_ray_coord v t i).mul ((hasDerivAt_log_edge i (hp i)).pow 2)).congr_deriv
  dsimp
  have he : (1+t*v i)*(v i/(1+t*v i)) = v i := by field_simp [hp i]
  calc
    _ = v i*Real.log (1+t*v i)^2 + 2*Real.log (1+t*v i)*((1+t*v i)*(v i/(1+t*v i))) := by ring
    _ = _ := by rw [he]; ring

lemma hasDerivAt_rayH₁ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayH₁ v) (rayH₂ v t) t := by
  apply hasDerivAt_avg
  intro i
  have hl := hasDerivAt_log_edge i (hp i)
  apply (((hl.pow 2).add (hl.const_mul 2)).const_mul (v i)).congr_deriv
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring

lemma hasDerivAt_rayH₂ {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayH₂ v) (rayH₃ v t) t := by
  apply hasDerivAt_avg
  intro i
  have hl := hasDerivAt_log_edge i (hp i)
  have ha := hasDerivAt_ray_coord v t i
  apply (((hasDerivAt_const t (2*v i^2)).div ha (hp i)).mul (hl.add_const 1)).congr_deriv
  simp only [Pi.div_apply]
  field_simp [hp i]; ring

def rayF₀ (v : Vec) (t : ℝ) : ℝ :=
  rayG₀ v t + 2*rayI₀ v t + (2/5)*rayH₀ v t - (4/5)*rayG₀ v t*rayI₀ v t + (2/5)*rayG₀ v t^2

def rayF₁ (v : Vec) (t : ℝ) : ℝ :=
  rayG₁ v t + 2*rayI₁ v t + (2/5)*rayH₁ v t -
  (4/5)*(rayG₁ v t*rayI₀ v t+rayG₀ v t*rayI₁ v t) + (4/5)*rayG₀ v t*rayG₁ v t

def rayF₂ (v : Vec) (t : ℝ) : ℝ :=
  rayG₂ v t + 2*rayI₂ v t + (2/5)*rayH₂ v t -
  (4/5)*(rayG₂ v t*rayI₀ v t+2*rayG₁ v t*rayI₁ v t+rayG₀ v t*rayI₂ v t) +
  (4/5)*(rayG₁ v t^2+rayG₀ v t*rayG₂ v t)

def rayF₃ (v : Vec) (t : ℝ) : ℝ :=
  rayG₃ v t + 2*rayI₃ v t + (2/5)*rayH₃ v t -
  (4/5)*(rayG₃ v t*rayI₀ v t+3*rayG₂ v t*rayI₁ v t+
    3*rayG₁ v t*rayI₂ v t+rayG₀ v t*rayI₃ v t) +
  (4/5)*(3*rayG₁ v t*rayG₂ v t+rayG₀ v t*rayG₃ v t)

lemma hasDerivAt_rayF₀ {v : Vec} (hv : avg v = 0) {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayF₀ v) (rayF₁ v t) t := by
  have hg := hasDerivAt_rayG₀ hp
  have hi := hasDerivAt_rayI₀ hv hp
  have hh := hasDerivAt_rayH₀ hp
  apply (((hg.add (hi.const_mul 2)).add (hh.const_mul (2/5))).sub
    ((hg.const_mul (4/5)).mul hi) |>.add ((hg.pow 2).const_mul (2/5))).congr_deriv
  dsimp only [rayF₁, Pi.pow_apply]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

lemma hasDerivAt_rayF₁ {v : Vec} (hv : avg v = 0) {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayF₁ v) (rayF₂ v t) t := by
  have hg₀ := hasDerivAt_rayG₀ hp
  have hg₁ := hasDerivAt_rayG₁ hp
  have hi₀ := hasDerivAt_rayI₀ hv hp
  have hi₁ := hasDerivAt_rayI₁ hp
  have hh₁ := hasDerivAt_rayH₁ hp
  apply (((hg₁.add (hi₁.const_mul 2)).add (hh₁.const_mul (2/5))).sub
    (((hg₁.mul hi₀).add (hg₀.mul hi₁)).const_mul (4/5)) |>.add
      ((hg₀.const_mul (4/5)).mul hg₁)).congr_deriv
  dsimp only [rayF₂, Pi.add_apply]
  ring

lemma hasDerivAt_rayF₂ {v : Vec} (hv : avg v = 0) {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (rayF₂ v) (rayF₃ v t) t := by
  have hg₀ := hasDerivAt_rayG₀ hp
  have hg₁ := hasDerivAt_rayG₁ hp
  have hg₂ := hasDerivAt_rayG₂ hp
  have hi₀ := hasDerivAt_rayI₀ hv hp
  have hi₁ := hasDerivAt_rayI₁ hp
  have hi₂ := hasDerivAt_rayI₂ hp
  have hh₂ := hasDerivAt_rayH₂ hp
  apply (((hg₂.add (hi₂.const_mul 2)).add (hh₂.const_mul (2/5))).sub
    ((((hg₂.mul hi₀).add ((hg₁.const_mul 2).mul hi₁)).add (hg₀.mul hi₂)).const_mul (4/5)) |>.add
      (((hg₁.pow 2).add (hg₀.mul hg₂)).const_mul (4/5))).congr_deriv
  dsimp only [rayF₃, Pi.add_apply]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

lemma rayF₀_eq_functional {v : Vec} (hv : avg v = 0) (t : ℝ) :
    rayF₀ v t = functional (fun i ↦ 1+t*v i) := by
  rw [functional_eq]
  simp only [rayF₀, rayG₀, rayI₀, rayH₀, logAverage, symEntropy, correction, logCentered, avg]
  rw [third_eq hv]
  ring

lemma rayF₀_zero (v : Vec) : rayF₀ v 0 = 0 := by
  norm_num [rayF₀, rayG₀, rayI₀, rayH₀, avg]

lemma rayF₁_zero {v : Vec} (hv : avg v = 0) : rayF₁ v 0 = 0 := by
  simpa [rayF₁, rayG₀, rayG₁, rayI₀, rayI₁, rayH₁, avg] using hv

lemma rayG₁_scaled {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    t*rayG₁ v t = 1-invMoment (fun i ↦ 1+t*v i) 1 := by
  have he (i : Fin 3) : t*(v i/(1+t*v i)) = 1-(1+t*v i)⁻¹ := by
    field_simp [hp i]; ring
  rw [rayG₁, ← avg_mul]
  simp_rw [he]
  simp only [avg, invMoment, pow_one]; ring

lemma rayG₂_scaled {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    t^2*rayG₂ v t = -1+2*invMoment (fun i ↦ 1+t*v i) 1-invMoment (fun i ↦ 1+t*v i) 2 := by
  have he (i : Fin 3) : t^2*(-v i^2/(1+t*v i)^2) = -1+2*(1+t*v i)⁻¹-(1+t*v i)⁻¹^2 := by
    field_simp [hp i]; ring
  rw [rayG₂, ← avg_mul]
  simp_rw [he]
  simp only [avg, invMoment, pow_one]; ring

lemma rayG₃_scaled {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    t^3*rayG₃ v t = 2-6*invMoment (fun i ↦ 1+t*v i) 1+
      6*invMoment (fun i ↦ 1+t*v i) 2-2*invMoment (fun i ↦ 1+t*v i) 3 := by
  have he (i : Fin 3) : t^3*(2*v i^3/(1+t*v i)^3) =
      2-6*(1+t*v i)⁻¹+6*(1+t*v i)⁻¹^2-2*(1+t*v i)⁻¹^3 := by
    field_simp [hp i]; ring
  rw [rayG₃, ← avg_mul]
  simp_rw [he]
  simp only [avg, invMoment, pow_one]; ring

lemma rayI₁_scaled (v : Vec) (t : ℝ) : t*rayI₁ v t = rayI₀ v t-rayG₀ v t := by
  simp only [rayI₁, rayI₀, rayG₀, avg]; ring

lemma rayI₂_scaled {v : Vec} (hv : avg v = 0) {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    t^2*rayI₂ v t = invMoment (fun i ↦ 1+t*v i) 1-1 := by
  have he (i : Fin 3) : t^2*(v i^2/(1+t*v i)) = (1+t*v i)-2+(1+t*v i)⁻¹ := by
    field_simp [hp i]; ring
  rw [rayI₂, ← avg_mul]
  simp_rw [he]
  simp only [avg, invMoment, pow_one]
  rw [third_eq hv]; ring

lemma rayI₃_scaled {v : Vec} (hv : avg v = 0) {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    t^3*rayI₃ v t = 2-3*invMoment (fun i ↦ 1+t*v i) 1+invMoment (fun i ↦ 1+t*v i) 2 := by
  have he (i : Fin 3) : t^3*(-v i^3/(1+t*v i)^2) =
      -(1+t*v i)+3-3*(1+t*v i)⁻¹+(1+t*v i)⁻¹^2 := by
    field_simp [hp i]; ring
  rw [rayI₃, ← avg_mul]
  simp_rw [he]
  simp only [avg, invMoment, pow_one]
  rw [third_eq hv]; ring

lemma rayH₃_scaled {v : Vec} {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    t^3*rayH₃ v t = -2*(rayI₀ v t-3*rayG₀ v t+
      3*(logInvMoment (fun i ↦ 1+t*v i) 1+rayG₀ v t*invMoment (fun i ↦ 1+t*v i) 1)-
      (logInvMoment (fun i ↦ 1+t*v i) 2+rayG₀ v t*invMoment (fun i ↦ 1+t*v i) 2)) := by
  have he (i : Fin 3) : t^3*(-2*v i^3*Real.log (1+t*v i)/(1+t*v i)^2) =
      -2*((1+t*v i)*Real.log (1+t*v i)-3*Real.log (1+t*v i)+
        3*Real.log (1+t*v i)*(1+t*v i)⁻¹-Real.log (1+t*v i)*(1+t*v i)⁻¹^2) := by
    field_simp [hp i]; ring
  rw [rayH₃, ← avg_mul]
  simp_rw [he]
  simp only [avg, rayI₀, rayG₀, logInvMoment, logCentered, logAverage, invMoment, pow_one]
  ring

lemma logMoment_ray {v : Vec} (hv : avg v = 0) (t : ℝ) :
    logMoment (fun i ↦ 1+t*v i) = rayI₀ v t-rayG₀ v t := by
  simp only [logMoment, rayI₀, rayG₀, logCentered, logAverage, avg]
  rw [third_eq hv]; ring

lemma rayF₃_scaled {v : Vec} (hv : avg v = 0) {t : ℝ} (hp : ∀ i, 1+t*v i ≠ 0) :
    t^3*rayF₃ v t = radialG (fun i ↦ 1+t*v i) := by
  calc
    _ = t^3*rayG₃ v t + 2*(t^3*rayI₃ v t) + (2/5)*(t^3*rayH₃ v t) -
      (4/5)*((t^3*rayG₃ v t)*rayI₀ v t+3*(t^2*rayG₂ v t)*(t*rayI₁ v t)+
        3*(t*rayG₁ v t)*(t^2*rayI₂ v t)+rayG₀ v t*(t^3*rayI₃ v t)) +
      (4/5)*(3*(t*rayG₁ v t)*(t^2*rayG₂ v t)+rayG₀ v t*(t^3*rayG₃ v t)) := by
      unfold rayF₃; ring
    _ = _ := by
      rw [rayG₁_scaled hp, rayG₂_scaled hp, rayG₃_scaled hp,
        rayI₁_scaled, rayI₂_scaled hv hp, rayI₃_scaled hv hp, rayH₃_scaled hp]
      rw [radialG, logMoment_ray hv]
      ring

end ThreeState.TreeClauses.Radial

end 

noncomputable section
open Set
namespace ThreeState.TreeClauses.Radial

lemma monotoneOn_Icc_of_hasDerivAt_nonneg {a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hn : ∀ t ∈ Ioo a b, 0 ≤ f' t) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
  · intro t ht
    rw [interior_Icc] at ht
    exact (hf t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt
  · simpa only [interior_Icc] using hn

lemma radial_calculus {f f₁ f₂ f₃ : ℝ → ℝ} {x : ℝ}
    (h₀ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₁ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (h₂ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f₂ (f₃ t) t)
    (hf0 : f 0 = 0) (hf1 : f₁ 0 = 0)
    (hb : ∀ t ∈ Ioo (0:ℝ) 1, 12*t*x^2 ≤ f₃ t)
    {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1) :
    (1-lam^2)/2*x^2 ≤ f 1-(lam^2)⁻¹*f lam := by
  let Y : ℝ → ℝ := fun t ↦ t*f₁ t-2*f t-t^4*x^2
  let Y₁ : ℝ → ℝ := fun t ↦ t*f₂ t-f₁ t-4*t^3*x^2
  let Y₂ : ℝ → ℝ := fun t ↦ t*f₃ t-12*t^2*x^2
  have dY (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt Y (Y₁ t) t := by
    apply ((((hasDerivAt_id t).mul (h₁ t ht)).sub ((h₀ t ht).const_mul 2)).sub
      (((hasDerivAt_id t).pow 4).mul_const (x^2))).congr_deriv
    dsimp [Y₁]; ring
  have dY₁ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt Y₁ (Y₂ t) t := by
    apply ((((hasDerivAt_id t).mul (h₂ t ht)).sub (h₁ t ht)).sub
      ((((hasDerivAt_id t).pow 3).const_mul 4).mul_const (x^2))).congr_deriv
    dsimp [Y₂]; ring
  have hm₁ : MonotoneOn Y₁ (Icc (0:ℝ) 1) := by
    apply monotoneOn_Icc_of_hasDerivAt_nonneg dY₁
    intro t ht
    have h := mul_le_mul_of_nonneg_left (hb t ht) ht.1.le
    dsimp only [Y₂]; nlinarith
  have hn₁ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ Y₁ t := by
    have h := hm₁ (by norm_num : (0:ℝ) ∈ Icc 0 1) ht ht.1
    simpa [Y₁, hf1] using h
  have hm : MonotoneOn Y (Icc (0:ℝ) 1) :=
    monotoneOn_Icc_of_hasDerivAt_nonneg dY (fun t ht ↦ hn₁ t ⟨ht.1.le, ht.2.le⟩)
  have hn (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ Y t := by
    have h := hm (by norm_num : (0:ℝ) ∈ Icc 0 1) ht ht.1
    simpa [Y, hf0] using h
  let q : ℝ → ℝ := fun t ↦ (f t-(1/2)*t^4*x^2)/t^2
  have dq (t : ℝ) (ht : t ∈ Icc lam 1) : HasDerivAt q (Y t/t^3) t := by
    have ht0 : 0 < t := lt_of_lt_of_le hl₀ ht.1
    have hti : t ∈ Icc (0:ℝ) 1 := ⟨ht0.le, ht.2⟩
    apply (((h₀ t hti).sub ((((hasDerivAt_id t).pow 4).const_mul (1/2)).mul_const (x^2))).div
      ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 (ne_of_gt ht0))).congr_deriv
    dsimp [Y]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [ne_of_gt ht0]; ring
  have hmq : MonotoneOn q (Icc lam 1) := by
    apply monotoneOn_Icc_of_hasDerivAt_nonneg dq
    intro t ht
    exact div_nonneg (hn t ⟨(lt_trans hl₀ ht.1).le, ht.2.le⟩)
      (pow_nonneg (lt_trans hl₀ ht.1).le 3)
  have hr := hmq (by exact ⟨le_rfl, hl₁.le⟩ : lam ∈ Icc lam 1)
    (by exact ⟨hl₁.le, le_rfl⟩ : (1:ℝ) ∈ Icc lam 1) hl₁.le
  have hr' : f lam/lam^2-lam^2/2*x^2 ≤ f 1-(1/2)*x^2 := by
    calc
      f lam/lam^2-lam^2/2*x^2 = q lam := by
        dsimp [q]; field_simp [ne_of_gt hl₀]
      _ ≤ q 1 := hr
      _ = _ := by norm_num [q]
  rw [inv_mul_eq_div]
  linarith

lemma positive_edge {m : Vec} (hm : PositiveMessage m) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    PositiveMessage (edge t m) := by
  refine ⟨fun i ↦ edge_pos hm ht i, ?_⟩
  change avg (fun i ↦ 1+t*centered m i) = 1
  rw [avg_add, avg_const, avg_mul, avg_centered hm]
  ring

lemma momentX_edge (m : Vec) (t : ℝ) :
    momentX (centered (edge t m)) = t^2*momentX (centered m) := by
  simp only [momentX, centered, edge, avg]; ring

lemma rayF₃_lower {m : Vec} (hm : PositiveMessage m) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    12*t*momentX (centered m)^2 ≤ rayF₃ (centered m) t := by
  have h := radialG_bound (positive_edge hm ⟨ht.1.le, ht.2.le⟩)
  have hp (i : Fin 3) : 1+t*centered m i ≠ 0 :=
    ne_of_gt (edge_pos hm ⟨ht.1.le, ht.2.le⟩ i)
  rw [momentX_edge] at h
  have he : t^3*rayF₃ (centered m) t = radialG (edge t m) :=
    rayF₃_scaled (avg_centered hm) hp
  rw [← he] at h
  have h' : 0 ≤ t^3*(rayF₃ (centered m) t-12*t*momentX (centered m)^2) := by nlinarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (pow_pos ht.1 3)).mp h')

theorem radial_inequality : RadialInequality := by
  intro m hm lam hl₀ hl₁
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (i : Fin 3) : 1+t*centered m i ≠ 0 :=
    ne_of_gt (edge_pos hm ht i)
  have h := radial_calculus
    (fun t ht ↦ hasDerivAt_rayF₀ (avg_centered hm) (hp t ht))
    (fun t ht ↦ hasDerivAt_rayF₁ (avg_centered hm) (hp t ht))
    (fun t ht ↦ hasDerivAt_rayF₂ (avg_centered hm) (hp t ht))
    (rayF₀_zero (centered m)) (rayF₁_zero (avg_centered hm))
    (fun _ ht ↦ rayF₃_lower hm ht) hl₀ hl₁
  rw [rayF₀_eq_functional (avg_centered hm), rayF₀_eq_functional (avg_centered hm)] at h
  have he1 : (fun i ↦ 1+(1:ℝ)*centered m i) = m := by funext i; simp [centered]
  rw [he1] at h
  exact h

end ThreeState.TreeClauses.Radial

end

end OAI
