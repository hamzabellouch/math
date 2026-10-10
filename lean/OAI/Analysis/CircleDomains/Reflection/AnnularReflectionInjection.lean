import OAI.Analysis.CircleDomains.Reflection.AnnularCircleReflection

namespace OAI

/-! The explicit annular reflection preserves injectivity and keeps
uniform bounds from the exterior side. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma annularCircleReflect_outer_iff {U:Set ℂ} {f:ℂ→ℂ}
    (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hp:∀z∈U,1<‖z‖→1<‖f z‖)
    (hb:∀z∈U,‖z‖=1→‖f z‖=1) {z:ℂ} (hzU:z∈U) :
    1≤‖annularCircleReflect f z‖ ↔ 1≤‖z‖ := by
  by_cases hzo : 1≤‖z‖
  · refine iff_of_true ?_ hzo
    rw [annularCircleReflect,ite_eq_left hzo]
    rcases eq_or_lt_of_le hzo with he|he
    · exact (hb z hzU he.symm).ge
    · exact (hp z hzU he).le
  · have hsmall : ‖z‖<1 := lt_of_not_ge hzo
    have href := unitCircleReflection_strict_outer (hz z hzU) hsmall
    have hf := hp _ (hs z hzU) href
    have hlt : ‖annularCircleReflect f z‖<1 := by
      rw [annularCircleReflect,ite_eq_right hzo,unitCircleReflection_norm]
      exact (inv_lt_one₀ (zero_lt_one.trans hf)).mpr hf
    exact iff_of_false (not_le_of_gt hlt) hzo

lemma injOn_annularCircleReflect {U:Set ℂ} {f:ℂ→ℂ}
    (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hi:InjOn f (U∩{z | 1≤‖z‖}))
    (hp:∀z∈U,1<‖z‖→1<‖f z‖)
    (hb:∀z∈U,‖z‖=1→‖f z‖=1) : InjOn (annularCircleReflect f) U := by
  intro z hzU w hwU he
  have hside : (1≤‖z‖) ↔ 1≤‖w‖ := by
    rw [←annularCircleReflect_outer_iff hz hs hp hb hzU,
      ←annularCircleReflect_outer_iff hz hs hp hb hwU,he]
  by_cases hzo : 1≤‖z‖
  · have hwo := hside.mp hzo
    rw [annularCircleReflect,ite_eq_left hzo,annularCircleReflect,ite_eq_left hwo] at he
    exact hi ⟨hzU,hzo⟩ ⟨hwU,hwo⟩ he
  · have hwo : ¬1≤‖w‖ := fun h => hzo (hside.mpr h)
    rw [annularCircleReflect,ite_eq_right hzo,annularCircleReflect,ite_eq_right hwo] at he
    have he' := unitCircleReflection_involutive.injective he
    have he'' := hi ⟨hs z hzU,unitCircleReflection_outer (hz z hzU) (lt_of_not_ge hzo).le⟩
      ⟨hs w hwU,unitCircleReflection_outer (hz w hwU) (lt_of_not_ge hwo).le⟩ he'
    exact unitCircleReflection_involutive.injective he''

lemma annularCircleReflect_norm_le {U:Set ℂ} {f:ℂ→ℂ} {M:ℝ}
    (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U) (hM:1≤M)
    (hf:∀z∈U,1≤‖z‖→1≤‖f z‖ ∧ ‖f z‖≤M) {z:ℂ} (hzU:z∈U) :
    ‖annularCircleReflect f z‖≤M := by
  by_cases hzo : 1≤‖z‖
  · rw [annularCircleReflect,ite_eq_left hzo]
    exact (hf z hzU hzo).2
  · rw [annularCircleReflect,ite_eq_right hzo,unitCircleReflection_norm]
    have hh := (hf _ (hs z hzU)
      (unitCircleReflection_outer (hz z hzU) (lt_of_not_ge hzo).le)).1
    exact ((inv_le_one₀ (zero_lt_one.trans_le hh)).mpr hh).trans hM

end CircleDomainRigidity

end

end OAI
