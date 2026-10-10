import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! Replace only the exterior germ of a compact smooth arc, retaining
its entire closed trace and its opposite endpoint germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
namespace SmoothCompactArc

theorem replace_start_germ (P : SmoothCompactArc I N) {γ : ℝ → N} {U : Set ℝ}
    (hU : IsOpen U) (hsU : P.start ∈ U)
    (hsmooth : ContMDiffOn 𝓘(ℝ) I ∞ γ U)
    (hregular : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I γ t))
    (hEq : EqOn γ P.curve (U ∩ Icc P.start P.finish)) :
    ∃ R : SmoothCompactArc I N, R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      R.curve =ᶠ[𝓝 P.start] γ ∧ R.curve =ᶠ[𝓝 P.finish] P.curve := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU P.start hsU
  let d := min (r/2) ((P.finish-P.start)/2)
  have hd : 0 < d := lt_min (half_pos hr) (half_pos (sub_pos.mpr P.start_lt_finish))
  let b := P.start+d
  have hsb : P.start < b := by dsimp [b]; linarith
  have hbf : b < P.finish := by
    have h := min_le_right (r/2) ((P.finish-P.start)/2)
    dsimp [b,d]; linarith
  have hbr : b-P.start < r := by
    have h := min_le_left (r/2) ((P.finish-P.start)/2)
    dsimp [b,d]; linarith
  have hBU : Icc P.start b ⊆ U := by
    intro t ht
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hbU := hBU (right_mem_Icc.mpr hsb.le)
  have hmatch : γ =ᶠ[𝓝 b] P.curve := by
    filter_upwards [hU.mem_nhds hbU,Ioo_mem_nhds hsb hbf] with t htU ht
    exact hEq ⟨htU,ht.1.le,ht.2.le⟩
  let W := (U ∩ Iio b) ∪ (P.domain ∩ Ioi b) ∪ (U ∩ P.domain)
  have hW : IsOpen W := ((hU.inter isOpen_Iio).union
    (P.domain_open.inter isOpen_Ioi)).union (hU.inter P.domain_open)
  have hleft : ∀ t ∈ W, t ≤ b → t ∈ U := by
    intro t ht htb
    rcases ht with (ht | ht) | ht
    · exact ht.1
    · exact False.elim (not_lt_of_ge htb ht.2)
    · exact ht.1
  have hright : ∀ t ∈ W, b ≤ t → t ∈ P.domain := by
    intro t ht hbt
    rcases ht with (ht | ht) | ht
    · exact False.elim (not_lt_of_ge hbt ht.2)
    · exact ht.1
    · exact ht.2
  have hsub : Icc P.start P.finish ⊆ W := by
    intro t ht
    rcases lt_trichotomy t b with h | rfl | h
    · exact Or.inl (Or.inl ⟨hBU ⟨ht.1,h.le⟩,h⟩)
    · exact Or.inr ⟨hbU,P.interval_subset ⟨hsb.le,hbf.le⟩⟩
    · exact Or.inl (Or.inr ⟨P.interval_subset ht,h⟩)
  have hs : ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve b γ P.curve) W := by
    apply joinedCurve_smooth_on
    · intro t ht htb
      exact hsmooth.contMDiffAt (hU.mem_nhds (hleft t ht htb))
    · intro t ht hbt
      exact P.smooth.contMDiffAt (P.domain_open.mem_nhds (hright t ht hbt))
    · exact hmatch
  have hr' : ∀ t ∈ W, Function.Injective (mfderiv 𝓘(ℝ) I (joinedCurve b γ P.curve) t) := by
    apply joinedCurve_regular_on
    · intro t ht htb
      exact hregular t (hleft t ht htb)
    · intro t ht hbt
      exact P.regular t (hright t ht hbt)
    · exact hmatch
  have he : EqOn (joinedCurve b γ P.curve) P.curve (Icc P.start P.finish) := by
    intro t ht
    by_cases htb : t ≤ b
    · simp only [joinedCurve,ite_eq_left htb]
      exact hEq ⟨hBU ⟨ht.1,htb⟩,ht⟩
    · simp only [joinedCurve,ite_eq_right htb]
  have hi : (Icc P.start P.finish).InjOn (joinedCurve b γ P.curve) := by
    intro s hs t ht hst
    apply P.injective hs ht
    rw [← he hs,← he ht]
    exact hst
  let R : SmoothCompactArc I N := ⟨_,P.start,P.finish,P.start_lt_finish,W,hW,hsub,hs,hr',hi⟩
  exact ⟨R,rfl,rfl,he,joinedCurve_germ_left b γ P.curve hsb,
    joinedCurve_germ_right b γ P.curve hbf⟩

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
