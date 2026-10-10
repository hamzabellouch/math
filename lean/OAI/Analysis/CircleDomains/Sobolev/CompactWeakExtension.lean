import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! A weak derivative whose function and field are supported on one compact
subset of an open set is a global weak derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_global_of_compact_support
    {U K : Set EuclideanPlane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f g : EuclideanPlane → ℝ} {i : Fin 2}
    (hw : DeGiorgi.HasWeakPartialDeriv i g f U)
    (hf : ∀ x ∉ K, f x = 0) (hg : ∀ x ∉ K, g x = 0) :
    DeGiorgi.HasWeakPartialDeriv i g f univ := by
  obtain ⟨η, V, hη, hsη, _, hsU, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hU hKU
  intro φ hφ hsφ _
  let ψ : EuclideanPlane → ℝ := fun x => η x * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hη.mul hφ
  have hsψ : HasCompactSupport ψ := hsη.mul_right
  have hψU : tsupport ψ ⊆ U := tsupport_mul_subset_left.trans hsU
  have he := hw ψ hψ hsψ hψU
  have hdη (x : EuclideanPlane) (hx : x ∈ K) : fderiv ℝ η x = 0 := by
    have heq : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      exact hone y hy
    rw [heq.fderiv_eq]
    exact fderiv_const_apply 1
  have hleft (x : EuclideanPlane) :
      f x * fderiv ℝ ψ x (EuclideanSpace.single i 1) =
        f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    by_cases hx : x ∈ K
    · rw [show fderiv ℝ ψ x = η x • fderiv ℝ φ x + φ x • fderiv ℝ η x from
        fderiv_fun_mul (hη.differentiable (by simp)).differentiableAt
          (hφ.differentiable (by simp)).differentiableAt]
      rw [hdη x hx, hone x (hKV hx)]
      simp
    · rw [hf x hx, zero_mul, zero_mul]
  have hright (x : EuclideanPlane) : g x * ψ x = g x * φ x := by
    by_cases hx : x ∈ K
    · simp only [ψ, hone x (hKV hx), one_mul]
    · rw [hg x hx, zero_mul, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hf x (fun h => hx (hKU h)), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hg x (fun h => hx (hKU h)), zero_mul])] at he
  simp only [hleft, hright] at he
  simpa only [Measure.restrict_univ] using he

end CircleDomainRigidity

end

end OAI
