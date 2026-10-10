import Mathlib

namespace OAI

/-! A compactly supported smooth extension agreeing near a prescribed
compact subset of an open set. Its pointwise bound preserves bounded
harmonic tests during Brownian localization. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma exists_compact_smooth_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : E → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x∈K, f =ᶠ[𝓝 x] u) ∧
      (∀ x, |f x|≤|u x|) ∧ ∀ x∉U, f x=0 := by
  obtain ⟨V,hV,hKV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨O,hO,hVO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨χ,hχ,hχrange,hχsupport,hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO isClosed_closure hVO
  have hχc : HasCompactSupport χ := by
    change IsCompact (closure (support χ))
    rw [hχsupport]
    exact hOc
  have hχU : tsupport χ ⊆ U := by simpa only [tsupport,hχsupport] using hOU
  have hχb (x) : 0≤χ x ∧ χ x≤1 := hχrange (mem_range_self x)
  let f : E → ℝ := fun x => χ x*u x
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x∈U
    · exact hχ.contDiffAt.mul ((hu x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x∉tsupport χ := fun h => hx (hχU h)
      have he : f =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hn] with y hy
        have hz : χ y=0 := notMem_support.mp (fun hs => hy ((subset_tsupport χ) hs))
        simp only [f,hz,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨f,hf,hχc.mul_right,?_,?_,?_,?_⟩
  · exact (tsupport_mul_subset_left (f := χ) (g := u)).trans hχU
  · intro x hx
    filter_upwards [hV.mem_nhds (hKV hx)] with y hy
    have he : χ y=1 := (hχone y).mp (subset_closure hy)
    simp only [f,he,one_mul]
  · intro x
    dsimp only [f]
    rw [abs_mul,abs_of_nonneg (hχb x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχb x).2
  · intro x hx
    have hz : χ x=0 := notMem_support.mp (fun hs => hx (hχU ((subset_tsupport χ) hs)))
    simp only [f,hz,zero_mul]

end SLEExactGauge

end

end OAI
