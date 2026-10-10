import OAI.Geometry.NodalSets.Charts.SphereIndexedIntrinsic
import OAI.Geometry.NodalSets.Spectral.FiniteEigenframeSimplicity

namespace OAI

noncomputable section

namespace Yau.Target

section

open Manifold MeasureTheory Yau.Analysis
open scoped ContDiff
local instance sphereGapSimpleMeasurable : MeasurableSpace Base := borel Base
local instance sphereGapSimpleBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_indexed_resolvent_simple_of_gaps (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (N : ℕ)
    (hleft : ∀ M : ℕ, M < N → sphereIndexedEigenvalue d M < sphereIndexedEigenvalue d N)
    (hright : sphereIndexedEigenvalue d N < sphereIndexedEigenvalue d (N+1)) :
    ∃ u : SphereEnergySmooth d, ‖sphereEnergyL2Linear d u‖=1 ∧
      (∀ p z, -intrinsicWeightedChartOperator d.tensor d.density
        (SphereEnergySmooth.toSmooth d u) p z =
          sphereIndexedEigenvalue d N * (SphereEnergySmooth.toSmooth d u : Base → ℝ)
            ((extChartAt (𝓡 4) p).symm z)) ∧
      ∀ f : SphereWeightedL2 d,
        sphereL2Resolvent d f=(sphereIndexedEigenvalue d N+1)⁻¹ • f →
        f=(inner ℝ (sphereEnergyL2Linear d u) f) • sphereEnergyL2Linear d u := by
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+2)
  let i : Fin (N+2) := ⟨N,by omega⟩
  let k : Fin (N+2) := ⟨N+1,by omega⟩
  have hval (j : Fin (N+2)) := sphereIndexedEigenvalue_eq_frame_index d u mu ho
    (fun l ↦ (he l).1) (fun l ↦ (he l).2.2) hanti hmax j
  have hi : sphereIndexedEigenvalue d N = (mu i)⁻¹-1 := hval i
  have hk : sphereIndexedEigenvalue d (N+1) = (mu k)⁻¹-1 := hval k
  have hgap : mu k < mu i := by
    apply (inv_lt_inv₀ (he i).1 (he k).1).mp
    rw [hi,hk] at hright
    linarith
  have hunique : ∀ j, j < k → j ≠ i → mu j ≠ mu i := by
    intro j hj hji heq
    have hjN : j.val < N := by
      have hjk : j.val < N+1 := hj
      have hjne : j.val ≠ N := fun h ↦ hji (Fin.ext h)
      omega
    have hlt := hleft j.val hjN
    rw [hval j,hi,heq] at hlt
    exact (lt_irrefl _) hlt
  refine ⟨u i,ho.norm_eq_one i,?_,?_⟩
  · rw [hi]
    exact sphere_smooth_resolvent_to_intrinsic d (u i) (mu i) (he i).1.ne' (he i).2.2
  · intro f hf
    rw [hi,sub_add_cancel,inv_inv] at hf
    exact finite_eigenframe_simple_from_gap (sphereL2Resolvent d) (sphereL2Resolvent_symmetric d)
      (fun j ↦ sphereEnergyL2Linear d (u j)) mu ho (fun j ↦ (he j).2.2)
      hmax i k hgap hunique f hf

theorem sphere_indexed_intrinsic_simple_of_gaps (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (N : ℕ)
    (hleft : ∀ M : ℕ, M < N → sphereIndexedEigenvalue d M < sphereIndexedEigenvalue d N)
    (hright : sphereIndexedEigenvalue d N < sphereIndexedEigenvalue d (N+1)) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
      sphereWeightedPairing d.density u u=1 ∧
      (∀ p z, -intrinsicWeightedChartOperator d.tensor d.density u p z =
        sphereIndexedEigenvalue d N * u ((extChartAt (𝓡 4) p).symm z)) ∧
      ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        (∀ p z, -intrinsicWeightedChartOperator d.tensor d.density v p z =
          sphereIndexedEigenvalue d N * v ((extChartAt (𝓡 4) p).symm z)) →
        ∃ c : ℝ, v=c • u := by
  obtain ⟨u,hn,he,hsimple⟩ := sphere_indexed_resolvent_simple_of_gaps d
    (fun p ↦ (hr.comp (sphereChartCoordMap_smooth p)).contDiff) N hleft hright
  have hnorm : sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u)
      (SphereEnergySmooth.toSmooth d u)=1 := by rw [← sphereEnergyL2Linear_norm_sq,hn,one_pow]
  refine ⟨SphereEnergySmooth.toSmooth d u,(SphereEnergySmooth.toSmooth d u).property,?_,hnorm,he,?_⟩
  · intro hz
    simp only [hz,sphereWeightedPairing,Pi.zero_apply,mul_zero,integral_zero] at hnorm
    norm_num at hnorm
  · intro v hv heig
    by_cases hv0 : v=0
    · exact ⟨0,by rw [hv0,zero_smul]⟩
    let w : SphereEnergySmooth d := (⟨v,hv⟩ : sphereSmoothFunctions)
    have hw0 : w ≠ 0 := fun h ↦ hv0 (congrArg (fun z : SphereEnergySmooth d ↦
      (SphereEnergySmooth.toSmooth d z : Base → ℝ)) h)
    have hwe := (sphere_smooth_intrinsic_eigen_to_resolvent d hr w hw0 _ heig).2.2
    let c := inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d w)
    have heq : sphereEnergyL2Linear d w = c • sphereEnergyL2Linear d u := hsimple _ hwe
    have hzero : sphereEnergyL2Linear d (w-c • u)=0 := by rw [map_sub,map_smul,heq,sub_self]
    have hw : w=c • u := sub_eq_zero.mp ((sphereEnergyL2Linear_eq_zero_iff d _).mp hzero)
    exact ⟨c,congrArg (fun z : SphereEnergySmooth d ↦ (SphereEnergySmooth.toSmooth d z : Base → ℝ)) hw⟩

end

open Manifold MeasureTheory Yau.Analysis
open scoped ContDiff
local instance sphereSimpleIndexMeasurable : MeasurableSpace Base := borel Base
local instance sphereSimpleIndexBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_simple_eigenvalue_unique_index (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p z, -intrinsicWeightedChartOperator d.tensor d.density v p z =
        lam * v ((extChartAt (𝓡 4) p).symm z)) → ∃ c : ℝ, v = c • u)
    (N M : ℕ) (hN : sphereIndexedEigenvalue d N=lam)
    (hM : sphereIndexedEigenvalue d M=lam) : N=M := by
  obtain ⟨v,ho,he⟩ := sphere_indexed_finite_intrinsic_frame d hrho (N+M+1)
  let i : Fin (N+M+1) := ⟨N,by omega⟩
  let j : Fin (N+M+1) := ⟨M,by omega⟩
  let w : SphereEnergySmooth d := (⟨u,hu⟩ : sphereSmoothFunctions)
  obtain ⟨a,ha⟩ := hsimple (SphereEnergySmooth.toSmooth d (v i))
    (SphereEnergySmooth.toSmooth d (v i)).property (by simpa only [i,hN] using he i)
  obtain ⟨b,hb⟩ := hsimple (SphereEnergySmooth.toSmooth d (v j))
    (SphereEnergySmooth.toSmooth d (v j)).property (by simpa only [j,hM] using he j)
  have hi : sphereEnergyL2Linear d (v i) = a • sphereEnergyL2Linear d w := by
    rw [← map_smul]
    exact congrArg (sphereEnergyL2Linear d) (Subtype.ext ha)
  have hj : sphereEnergyL2Linear d (v j) = b • sphereEnergyL2Linear d w := by
    rw [← map_smul]
    exact congrArg (sphereEnergyL2Linear d) (Subtype.ext hb)
  exact congrArg Fin.val (orthonormal_indices_eq_of_common_line _ ho i j
    (sphereEnergyL2Linear d w) a b hi hj)

theorem sphere_simple_indexed_strict_gaps (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p z, -intrinsicWeightedChartOperator d.tensor d.density v p z =
        lam * v ((extChartAt (𝓡 4) p).symm z)) → ∃ c : ℝ, v = c • u)
    (N : ℕ) (hN : sphereIndexedEigenvalue d N=lam) :
    (∀ M : ℕ, M < N → sphereIndexedEigenvalue d M < lam) ∧
      lam < sphereIndexedEigenvalue d (N+1) := by
  have hmono := sphereIndexedEigenvalue_monotone d hrho
  constructor
  · intro M hM
    have hle : sphereIndexedEigenvalue d M ≤ lam := hN ▸ hmono hM.le
    apply lt_of_le_of_ne hle
    intro heq
    have he := sphere_simple_eigenvalue_unique_index d hrho u hu lam hsimple M N heq hN
    omega
  · have hle : lam ≤ sphereIndexedEigenvalue d (N+1) := hN ▸ hmono (Nat.le_succ N)
    apply lt_of_le_of_ne hle
    intro heq
    have he := sphere_simple_eigenvalue_unique_index d hrho u hu lam hsimple N (N+1) hN heq.symm
    omega

end Yau.Target

end

end OAI
