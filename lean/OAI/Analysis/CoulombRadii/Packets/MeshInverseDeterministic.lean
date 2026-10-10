import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TFResponseMargins

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma exists_height_brackets {hl hh ξ : ℝ} (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ t : Finset ℝ,(∀ v∈t,v∈Icc (hl/2) (2*hh)) ∧
      ∀ h∈Icc hl hh,
        (∃ v∈t,h-ξ/4 ≤ v ∧ v ≤ h-ξ/8) ∧
        (∃ v∈t,h+ξ/8 ≤ v ∧ v ≤ h+ξ/4) := by
  obtain ⟨S,hSf,hS⟩ := Metric.totallyBounded_iff.mp
    (isCompact_Icc : IsCompact (Icc (hl-ξ) (hh+ξ))).totallyBounded (ξ/64) (by positivity)
  let t := hSf.toFinset.filter (fun v => v∈Icc (hl/2) (2*hh))
  refine ⟨t,fun v hv => (Finset.mem_filter.mp hv).2,?_⟩
  intro h hh'
  have H (a : ℝ) (ha : a∈Icc (hl-ξ) (hh+ξ)) : ∃ v∈S,|a-v| < ξ/64 := by
    obtain ⟨v,hv⟩ := mem_iUnion.mp (hS ha)
    obtain ⟨hvs,hva⟩ := mem_iUnion.mp hv
    exact ⟨v,hvs,by simpa only [Metric.mem_ball,Real.dist_eq] using hva⟩
  obtain ⟨u,hu,hu'⟩ := H (h-3*ξ/16) ⟨by linarith [hh'.1],by linarith [hh'.2]⟩
  obtain ⟨v,hv,hv'⟩ := H (h+3*ξ/16) ⟨by linarith [hh'.1],by linarith [hh'.2]⟩
  have huabs := abs_lt.mp hu'
  have hvabs := abs_lt.mp hv'
  constructor
  · refine ⟨u,Finset.mem_filter.mpr ⟨hSf.mem_toFinset.mpr hu,?_⟩,by linarith,by linarith⟩
    constructor <;> linarith [hh'.1,hh'.2]
  · refine ⟨v,Finset.mem_filter.mpr ⟨hSf.mem_toFinset.mpr hv,?_⟩,by linarith,by linarith⟩
    constructor <;> linarith [hh'.1,hh'.2]

lemma exists_density_mesh_margin {hl hh ξ : ℝ} (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ ε : ℝ,0 < ε ∧ ∀ h∈Icc hl hh,
      Coulomb.tfScalarDensity (h-ξ/8)+ε < Coulomb.tfScalarDensity h ∧
      Coulomb.tfScalarDensity h+ε < Coulomb.tfScalarDensity (h+ξ/8) := by
  obtain ⟨ε,hε,hε1,H⟩ := Coulomb.exists_tf_response_margins
    (show 0 < ξ/8 by positivity) (show ξ/8 < hl by linarith) hlh
  refine ⟨ε,hε,?_⟩
  intro h hh'
  have HH := H (θ:=0) (δ:=0) (e:=ε) hh' le_rfl hε.le le_rfl hε.le hε.le le_rfl
  simp only [add_zero,mul_one,sub_zero] at HH
  constructor <;> linarith [HH.1,HH.2]

lemma negative_modulus_low_transfer {u v δ lam h ξ : ℝ}
    (hξ : 0 < ξ) (hh : ξ < h) (_ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδl : δ*lam ≤ ξ/8) (hmod : |v-u| ≤ δ*(lam+max (-u) 0)) (hu : u < h-ξ) :
    v < h-3*ξ/4 := by
  have H := (abs_le.mp hmod).2
  by_cases hu0 : 0 ≤ u
  · rw [max_eq_right (by linarith)] at H
    linarith
  · have hu0 : u < 0 := lt_of_not_ge hu0
    rw [max_eq_left (by linarith)] at H
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-δ) (neg_nonneg.mpr hu0.le)]

lemma negative_modulus_high_transfer {u v δ lam h ξ : ℝ}
    (hξ : 0 < ξ) (hh : 0 ≤ h) (hδl : δ*lam ≤ ξ/8)
    (hmod : |v-u| ≤ δ*(lam+max (-u) 0)) (hu : h+ξ < u) :
    h+3*ξ/4 < v := by
  have H := (abs_le.mp hmod).1
  rw [max_eq_right (by linarith)] at H
  linarith

theorem inverse_of_space_height_mesh {S : Set Position} {t : Finset Position}
    {heights : Finset ℝ} {u d : Position → ℝ} {hl hh ξ ε δ lam η : ℝ}
    (hξ : 0 < ξ) (hξl : ξ < hl) (_ : 0 < ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδl : δ*lam ≤ ξ/8) (hη : 0 < η) (hηξ : η ≤ ξ/4)
    (hheights : ∀ h∈Icc hl hh,
      (∃ v∈heights,h-ξ/4 ≤ v ∧ v ≤ h-ξ/8) ∧
      (∃ v∈heights,h+ξ/8 ≤ v ∧ v ≤ h+ξ/4))
    (hmargin : ∀ h∈Icc hl hh,
      Coulomb.tfScalarDensity (h-ξ/8)+ε < Coulomb.tfScalarDensity h ∧
      Coulomb.tfScalarDensity h+ε < Coulomb.tfScalarDensity (h+ξ/8))
    (hmesh : ∀ y∈S,∃ z∈t,|d z-d y| ≤ ε ∧
      |u z-u y| ≤ δ*(lam+max (-u y) 0))
    (hinv : ∀ z∈t,∀ h∈heights,
      (Coulomb.tfScalarDensity h ≤ d z → h-η < u z) ∧
      (d z ≤ Coulomb.tfScalarDensity h → u z < h+η)) :
    ∀ y∈S,∀ h∈Icc hl hh,
      (Coulomb.tfScalarDensity h ≤ d y → h-ξ ≤ u y) ∧
      (d y ≤ Coulomb.tfScalarDensity h → u y ≤ h+ξ) := by
  intro y hy h hh'
  obtain ⟨z,hz,hden,hfield⟩ := hmesh y hy
  obtain ⟨hlo,hhi⟩ := hheights h hh'
  obtain ⟨hmlo,hmhi⟩ := hmargin h hh'
  have hhξ : ξ < h := hξl.trans_le hh'.1
  have hden' := abs_le.mp hden
  constructor
  · intro hdy
    by_contra hn
    have hu : u y < h-ξ := lt_of_not_ge hn
    obtain ⟨v,hv,hv0,hv1⟩ := hlo
    have hdv : Coulomb.tfScalarDensity v ≤ d z := by
      have H := Coulomb.tfScalarDensity_mono hv1
      linarith
    have H := (hinv z hz v hv).1 hdv
    have H' := negative_modulus_low_transfer hξ hhξ hδ hδ1 hδl hfield hu
    linarith
  · intro hdy
    by_contra hn
    have hu : h+ξ < u y := lt_of_not_ge hn
    obtain ⟨v,hv,hv0,hv1⟩ := hhi
    have hdv : d z ≤ Coulomb.tfScalarDensity v := by
      have H := Coulomb.tfScalarDensity_mono hv0
      linarith
    have H := (hinv z hz v hv).2 hdv
    have H' := negative_modulus_high_transfer hξ (by linarith : 0 ≤ h) hδl hfield hu
    linarith
end NeutralAtom
end

end

end OAI
