import Mathlib

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section Chambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def safeNormals (Z : Set E) : Set E := {x | ∀ z ∈ Z, ⟪x,z⟫ ≠ 0}

def signChamber (Z : Set E) (c : E) : Set E := {x | ∀ z ∈ Z, 0 < ⟪c,z⟫ * ⟪x,z⟫}

lemma mem_signChamber_self {Z : Set E} {c : E} (hc : c ∈ safeNormals Z) :
    c ∈ signChamber Z c := by
  intro z hz
  exact mul_self_pos.mpr (hc z hz)

lemma signChamber_subset_safeNormals (Z : Set E) (c : E) :
    signChamber Z c ⊆ safeNormals Z := by
  intro x hx z hz h
  simpa [h] using hx z hz

lemma signChamber_convex (Z : Set E) (c : E) : Convex ℝ (signChamber Z c) := by
  intro x hx y hy a b ha hb hab z hz
  simp only [inner_add_left,real_inner_smul_left,mul_add]
  have h1 := hx z hz
  have h2 := hy z hz
  have hn1 := mul_nonneg ha h1.le
  have hn2 := mul_nonneg hb h2.le
  have he : ⟪c,z⟫ * (a * ⟪x,z⟫) + ⟪c,z⟫ * (b * ⟪y,z⟫) =
      a * (⟪c,z⟫ * ⟪x,z⟫) + b * (⟪c,z⟫ * ⟪y,z⟫) := by ring
  rw [he]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' h1) hn2
  · have hb' : b = 1 := by linarith
    simp [← ha',hb',h2]

lemma signChamber_eq_of_mem {Z : Set E} {c d x : E}
    (hc : x ∈ signChamber Z c) (hd : x ∈ signChamber Z d) :
    signChamber Z c = signChamber Z d := by
  ext y
  constructor <;> intro hy z hz
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h2.1 h3.2 | exact mul_pos_of_neg_of_neg h2.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h1.1 h3.2 | exact mul_pos_of_neg_of_neg h1.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

lemma signChamber_eq_or_disjoint (Z : Set E) (c d : E) :
    signChamber Z c = signChamber Z d ∨ Disjoint (signChamber Z c) (signChamber Z d) := by
  by_cases h : Disjoint (signChamber Z c) (signChamber Z d)
  · exact Or.inr h
  · rw [Set.disjoint_left] at h
    push Not at h
    obtain ⟨x,hc,hd⟩ := h
    exact Or.inl (signChamber_eq_of_mem hc hd)

lemma interior_safe_mem_chamber {Z : Set E} {c x : E}
    (hx : x ∈ interior (safeNormals Z)) (hxc : x ∈ signChamber Z c) :
    x ∈ interior (signChamber Z c) := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hε)
  intro y hy z hz
  have hc := hxc z hz
  have hn : ∀ w ∈ Metric.ball x ε, ⟪w,z⟫ ≠ 0 := fun w hw => hball hw z hz
  have hf : ContinuousOn (fun w : E => ⟪w,z⟫) (Metric.ball x ε) :=
    (continuous_id.inner continuous_const).continuousOn
  have hxball : x ∈ Metric.ball x ε := Metric.mem_ball_self hε
  rcases mul_pos_iff.mp hc with hc | hc
  · exact mul_pos hc.1 ((convex_ball x ε).isPreconnected.lt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)
  · exact mul_pos_of_neg_of_neg hc.1 ((convex_ball x ε).isPreconnected.gt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)

lemma interior_safe_mem_own_chamber {Z : Set E} {c : E}
    (hc : c ∈ interior (safeNormals Z)) : c ∈ interior (signChamber Z c) :=
  interior_safe_mem_chamber hc (mem_signChamber_self (interior_subset hc))

lemma signChamber_interior_pairwise (Z : Set E) :
    Pairwise (fun U W : {U : Set E // ∃ c, U = interior (signChamber Z c)} =>
      Disjoint (U.val) (W.val)) := by
  intro U W hne
  obtain ⟨c,hc⟩ := U.property
  obtain ⟨d,hd⟩ := W.property
  rcases signChamber_eq_or_disjoint Z c d with he | hdj
  · exact False.elim (hne (Subtype.ext (hc.trans ((congrArg interior he).trans hd.symm))))
  · rw [hc,hd]
    exact hdj.mono interior_subset interior_subset

lemma compact_finite_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧ K ⊆ ⋃ c ∈ (↑C : Set E), interior (signChamber Z c) := by
  classical
  obtain ⟨C,hCK,hCf,hcover⟩ := hK.elim_finite_subcover_image
    (b := K) (c := fun c : E => interior (signChamber Z c)) (fun _ _ => isOpen_interior)
    (fun c hc => Set.mem_iUnion₂.mpr ⟨c,hc,interior_safe_mem_own_chamber (hsub hc)⟩)
  exact ⟨hCf.toFinset,by simpa using hCK,by simpa using hcover⟩

end Chambers
end BorsukNine

end OAI
