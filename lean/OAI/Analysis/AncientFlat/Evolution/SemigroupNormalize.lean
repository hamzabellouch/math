import OAI.Analysis.AncientFlat.Evolution.AncientMild

namespace OAI
noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma normalized_circle (P : E →L[ℂ] E) {q : ℝ} (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) :
    ∀ z : ℂ, ‖z‖=1 → z ∈ resolventSet ℂ ((q⁻¹ : ℂ) • P) := by
  intro z hz
  have hqc : (q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hh := hc ((q:ℂ)*z) (by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq,hz,mul_one])
  let a : ℂˣ := Units.mk0 (q:ℂ) hqc
  have hi := IsUnit.smul a⁻¹ hh
  change IsUnit (algebraMap ℂ (E →L[ℂ] E) z-(q⁻¹:ℂ) • P)
  convert hi using 1
  change algebraMap ℂ (E →L[ℂ] E) z-(q⁻¹:ℂ) • P=
    (q:ℂ)⁻¹ • (algebraMap ℂ (E →L[ℂ] E) ((q:ℂ)*z)-P)
  rw [smul_sub,Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,smul_smul,
    ←mul_assoc,inv_mul_cancel₀ hqc,one_mul]
def normalize (γ : ℝ) (S : ℝ → E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  (Real.exp (γ*t) : ℂ) • S t
@[simp] lemma normalize_apply (γ : ℝ) (S : ℝ → E →L[ℂ] E) (t : ℝ) (v : E) :
    normalize γ S t v=(Real.exp (γ*t) : ℂ) • S t v := rfl
lemma normalize_zero (γ : ℝ) (S : ℝ → E →L[ℂ] E)
    (h0 : S 0=ContinuousLinearMap.id ℂ E) : normalize γ S 0=ContinuousLinearMap.id ℂ E := by
  simp only [normalize,mul_zero,Real.exp_zero,Complex.ofReal_one,one_smul,h0]
lemma normalize_continuous (γ : ℝ) (S : ℝ → E →L[ℂ] E)
    (hc : ∀ v : E, ContinuousOn (fun t => S t v) (Ici (0:ℝ))) :
    ∀ v : E, ContinuousOn (fun t => normalize γ S t v) (Ici (0:ℝ)) := by
  intro v
  exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn).smul (hc v)
lemma normalize_add (γ : ℝ) (S : ℝ → E →L[ℂ] E)
    (ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s+t)=(S s).comp (S t)) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → normalize γ S (s+t)=(normalize γ S s).comp (normalize γ S t) := by
  intro s t hs ht
  ext v
  simp only [normalize_apply,ha s t hs ht,ContinuousLinearMap.comp_apply,map_smul,smul_smul]
  congr 1
  rw [mul_add,Real.exp_add,Complex.ofReal_mul,mul_comm]
lemma normalize_bound (γ K : ℝ) (hγ : 0≤γ) (_hK : 0≤K) (S : ℝ → E →L[ℂ] E)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖S t‖≤K) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖normalize γ S t‖≤Real.exp γ*K := by
  intro t ht
  rw [normalize,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_of_le_one_right hγ ht.2)) (hb t ht)
    (norm_nonneg _) (Real.exp_pos _).le
end AncientMild

end

end OAI
