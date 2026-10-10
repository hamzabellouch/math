import OAI.Geometry.SurfaceImmersion.Geometry.CompactPlaneJet
import OAI.Geometry.SurfaceImmersion.Geometry.CompactAxisRectangle

namespace OAI

/-! Uniform zero isolation along the normalized connecting axis. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma compact_nonzero_locus_open {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → Base → Base} (hF : Continuous (fun z : ℝ × Base => F z.1 z.2)) :
    IsOpen {x | ∀ t ∈ K, F t x ≠ 0} := by
  let O := {z : ℝ × Base | F z.1 z.2 ≠ 0}
  have hO : IsOpen O := isOpen_ne.preimage hF
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hsub : K ×ˢ {x} ⊆ O := by
    rintro ⟨t,y⟩ ⟨ht,hy⟩
    have he : y = x := hy
    subst y
    exact hx t ht
  obtain ⟨V,U,_hV,hU,hKV,hxU,hVU⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  apply Filter.mem_of_superset (hU.mem_nhds (hxU (by simp)))
  intro y hy t ht
  exact hVU (show (t,y) ∈ V ×ˢ U from ⟨hKV ht,hy⟩)

theorem compact_plane_zero_isolation {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → Base → Base) (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hD : Continuous (fun z : ℝ × Base => fderiv ℝ (F z.1) z.2)) (p : Base)
    (hI : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) p))
    (hz : ∀ t ∈ K, F t p = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, ∀ x ∈ ball p r, F t x = 0 ↔ x = p := by
  obtain ⟨r,hr,hri⟩ := compact_plane_jet_injectivity hK F hF hD p hI
  refine ⟨r,hr,?_⟩
  intro t ht x hx
  constructor
  · intro he
    exact hri t ht hx (mem_ball_self hr) (he.trans (hz t ht).symm)
  · rintro rfl
    exact hz t ht

theorem compact_two_zero_rectangle {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → Base → Base) (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hFc : Continuous (fun z : ℝ × Base => F z.1 z.2))
    (hD : Continuous (fun z : ℝ × Base => fderiv ℝ (F z.1) z.2))
    {p q : ℝ} (hpq : p < q)
    (haxis : ∀ t ∈ K, ∀ s ∈ Icc p q, F t (crosscapAxis s) = ![(s-p)*(s-q),0])
    (hIp : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) (crosscapAxis p)))
    (hIq : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) (crosscapAxis q))) :
    ∃ (r : ℝ) (O : Set Base), 0 < r ∧ IsOpen O ∧
      (∀ x ∈ Icc (-r) r, ∀ s ∈ Icc (p-r) (q+r), (![x,s] : Base) ∈ O) ∧
      ∀ t ∈ K, ∀ x ∈ O, F t x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q := by
  have hzp : ∀ t ∈ K, F t (crosscapAxis p) = 0 := by
    intro t ht
    rw [haxis t ht p (left_mem_Icc.mpr hpq.le)]
    ext i
    fin_cases i <;> simp
  have hzq : ∀ t ∈ K, F t (crosscapAxis q) = 0 := by
    intro t ht
    rw [haxis t ht q (right_mem_Icc.mpr hpq.le)]
    ext i
    fin_cases i <;> simp
  obtain ⟨rp,hrp,hp⟩ := compact_plane_zero_isolation hK F hF hD _ hIp hzp
  obtain ⟨rq,hrq,hq⟩ := compact_plane_zero_isolation hK F hF hD _ hIq hzq
  let U : Set Base := {x | ∀ t ∈ K, F t x ≠ 0}
  let O := (ball (crosscapAxis p) rp ∪ ball (crosscapAxis q) rq) ∪ U
  have hO : IsOpen O := (isOpen_ball.union isOpen_ball).union (compact_nonzero_locus_open hK hFc)
  have hAO : ∀ s ∈ Icc p q, crosscapAxis s ∈ O := by
    intro s hs
    by_cases hsp : s = p
    · subst s
      exact Or.inl (Or.inl (mem_ball_self hrp))
    by_cases hsq : s = q
    · subst s
      exact Or.inl (Or.inr (mem_ball_self hrq))
    apply Or.inr
    intro t ht he
    have he0 := congrFun he 0
    rw [haxis t ht s hs] at he0
    have hmul : (s-p)*(s-q) = 0 := he0
    rcases mul_eq_zero.mp hmul with hh | hh
    · exact hsp (sub_eq_zero.mp hh)
    · exact hsq (sub_eq_zero.mp hh)
  obtain ⟨r,hr,hrect⟩ := compact_axis_rectangle hpq.le hO
    (by simpa only [crosscapAxis_apply] using hAO)
  refine ⟨r,O,hr,hO,hrect,?_⟩
  intro t ht x hx
  constructor
  · intro hz
    rcases hx with (hxp | hxq) | hxU
    · exact Or.inl ((hp t ht x hxp).mp hz)
    · exact Or.inr ((hq t ht x hxq).mp hz)
    · exact False.elim (hxU t ht hz)
  · rintro (rfl | rfl)
    · exact hzp t ht
    · exact hzq t ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
