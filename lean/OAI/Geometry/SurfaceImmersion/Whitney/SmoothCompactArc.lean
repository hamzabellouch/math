import OAI.Geometry.SurfaceImmersion.Whitney.CompactArcJoin

namespace OAI

/-! Compact regular embedded smooth arcs, and the actual joining operation
for arcs meeting through an oriented smooth parameter germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (N : Type*) [TopologicalSpace N] [ChartedSpace H N]

structure SmoothCompactArc where
  curve : ℝ → N
  start : ℝ
  finish : ℝ
  start_lt_finish : start < finish
  domain : Set ℝ
  domain_open : IsOpen domain
  interval_subset : Icc start finish ⊆ domain
  smooth : ContMDiffOn 𝓘(ℝ) I ∞ curve domain
  regular : ∀ t ∈ domain, Function.Injective (mfderiv 𝓘(ℝ) I curve t)
  injective : (Icc start finish).InjOn curve

namespace SmoothCompactArc
variable {I N}

theorem join_with_parameter (P Q : SmoothCompactArc I N) (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hem : StrictMono e)
    (hea : e P.finish = Q.start)
    (hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ e)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ R : SmoothCompactArc I N,
      R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve = joinedCurve P.finish P.curve (Q.curve ∘ e) ∧
      R.curve '' Icc R.start R.finish =
        P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish := by
  have haw : P.finish < e.symm Q.finish := by
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  let V := e ⁻¹' Q.domain
  let U := (P.domain ∩ Iio P.finish) ∪ (V ∩ Ioi P.finish) ∪ (P.domain ∩ V)
  have hV : IsOpen V := Q.domain_open.preimage e.continuous
  have hU : IsOpen U := (P.domain_open.inter isOpen_Iio).union (hV.inter isOpen_Ioi) |>.union (P.domain_open.inter hV)
  have hleft : ∀ t ∈ U, t ≤ P.finish → t ∈ P.domain := by
    intro t ht hta
    rcases ht with (ht | ht) | ht
    · exact ht.1
    · exact False.elim (not_lt_of_ge hta ht.2)
    · exact ht.1
  have hright : ∀ t ∈ U, P.finish ≤ t → e t ∈ Q.domain := by
    intro t ht hat
    rcases ht with (ht | ht) | ht
    · exact False.elim (not_lt_of_ge hat ht.2)
    · exact ht.1
    · exact ht.2
  have hsub : Icc P.start (e.symm Q.finish) ⊆ U := by
    intro t ht
    rcases lt_trichotomy t P.finish with h | rfl | h
    · exact Or.inl (Or.inl ⟨P.interval_subset ⟨ht.1,h.le⟩,h⟩)
    · exact Or.inr ⟨P.interval_subset (right_mem_Icc.mpr P.start_lt_finish.le),by
        change e P.finish ∈ Q.domain
        rw [hea]
        exact Q.interval_subset (left_mem_Icc.mpr Q.start_lt_finish.le)⟩
    · refine Or.inl (Or.inr ⟨?_,h⟩)
      apply Q.interval_subset
      refine ⟨?_,?_⟩
      · rw [← hea]; exact (hem h).le
      · simpa only [e.apply_symm_apply] using hem.monotone ht.2
  have hdif : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  have hsmooth : ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve P.finish P.curve (Q.curve ∘ e)) U := by
    apply joinedCurve_smooth_on
    · intro t ht hta
      exact P.smooth.contMDiffAt (P.domain_open.mem_nhds (hleft t ht hta))
    · intro t ht hat
      exact (Q.smooth.contMDiffAt (Q.domain_open.mem_nhds (hright t ht hat))).comp t hes.contMDiff.contMDiffAt
    · exact hmatch
  have hregular : ∀ t ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ) I (joinedCurve P.finish P.curve (Q.curve ∘ e)) t) := by
    apply joinedCurve_regular_on
    · intro t ht hta
      exact P.regular t (hleft t ht hta)
    · intro t ht hat
      rw [mfderiv_comp t
        ((Q.smooth.contMDiffAt (Q.domain_open.mem_nhds (hright t ht hat))).mdifferentiableAt (by simp))
        (hes.contMDiff.mdifferentiable (by simp) t)]
      exact (Q.regular _ (hright t ht hat)).comp (hdif.mfderiv_injective (mem_univ t))
    · exact hmatch
  have hinj := joinedCurve_compact_injective P.curve Q.curve e hem P.injective
    (by simpa only [hea] using Q.injective) (by simpa only [hea] using hcross)
  let R : SmoothCompactArc I N := ⟨_,P.start,e.symm Q.finish,
    P.start_lt_finish.trans haw,U,hU,hsub,hsmooth,hregular,hinj⟩
  refine ⟨R,rfl,rfl,rfl,?_⟩
  exact (joinedCurve_compact_image P.curve Q.curve e hem P.start_lt_finish.le
    (by rw [hea]; exact Q.start_lt_finish) hmatch.eq_of_nhds).trans (by rw [hea])

theorem join (P Q : SmoothCompactArc I N) {h : ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hh : ContDiffOn ℝ ∞ h V) (haV : P.finish ∈ V)
    (hpos : 0 < deriv h P.finish) (hea : h P.finish = Q.start)
    (hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ h)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ (R : SmoothCompactArc I N) (e : ℝ ≃ₜ ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      e P.finish = Q.start ∧ R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve = joinedCurve P.finish P.curve (Q.curve ∘ e) ∧
      R.curve '' Icc R.start R.finish =
        P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish := by
  obtain ⟨e,hes,hei,hem,he⟩ := local_increasing_diffeomorphism hV hh haV hpos
  have he' : e P.finish = Q.start := he.eq_of_nhds.trans hea
  have hm : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ e := by
    filter_upwards [hmatch,he] with t ht ht'
    exact ht.trans (congrArg Q.curve ht'.symm)
  obtain ⟨R,hR⟩ := P.join_with_parameter Q e hes hei hem he' hm hcross
  exact ⟨R,e,hes,hei,hem,he',hR⟩

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
