import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
noncomputable section

namespace SepticProfile.ODEGlue
open Set Filter
open scoped Topology ContDiff

def join (c : ℝ) (u v : ℝ → ℝ) (t : ℝ) : ℝ := if t≤c then u t else v t

lemma join_left {a c : ℝ} (u v : ℝ → ℝ) : EqOn (join c u v) u (Icc a c) := by
  intro t ht
  simp only [join,ite_eq_left ht.2]

lemma join_right {c b : ℝ} {u v : ℝ → ℝ} (h : u c=v c) :
    EqOn (join c u v) v (Icc c b) := by
  intro t ht
  by_cases htc : t≤c
  · have htc' : t=c := le_antisymm htc ht.1
    simp [join,htc',h]
  · simp only [join,ite_eq_right htc]

/-- Joining ODE arcs at the same value gives an ODE arc, including the joining
point. No uniqueness or a missing continuation is assumed. -/
theorem hasDerivWithinAt_join {a c b : ℝ} (hac : a≤c) (hcb : c≤b)
    {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc a c, HasDerivWithinAt u (f t (u t)) (Icc a c) t)
    (hv : ∀ t ∈ Icc c b, HasDerivWithinAt v (f t (v t)) (Icc c b) t)
    (h : u c=v c) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (join c u v) (f t (join c u v t)) (Icc a b) t := by
  have hul (x:ℝ) (hx:x ∈ Icc a c) :
      HasDerivWithinAt (join c u v) (f x (join c u v x)) (Icc a c) x := by
    rw [join_left u v hx]
    exact (hu x hx).congr_of_mem (join_left u v) hx
  have hvr (x:ℝ) (hx:x ∈ Icc c b) :
      HasDerivWithinAt (join c u v) (f x (join c u v x)) (Icc c b) x := by
    rw [join_right h hx]
    exact (hv x hx).congr_of_mem (join_right h) hx
  rcases lt_trichotomy t c with htc | htc | hct
  · apply (hul t ⟨ht.1,htc.le⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc)))
    exact fun x hx => ⟨hx.1.1,hx.2.le⟩
  · subst t
    have hs : Icc a c ∪ Icc c b=Icc a b := by
      ext x
      simp only [mem_union,mem_Icc]
      constructor
      · rintro (⟨hax,hxc⟩ | ⟨hcx,hxb⟩)
        · exact ⟨hax,hxc.trans hcb⟩
        · exact ⟨hac.trans hcx,hxb⟩
      · intro hx
        by_cases hxc : x≤c
        · exact Or.inl ⟨hx.1,hxc⟩
        · exact Or.inr ⟨(le_of_not_ge hxc),hx.2⟩
    rw [← hs]
    exact (hul c ⟨hac,le_rfl⟩).union (hvr c ⟨le_rfl,hcb⟩)
  · apply (hvr t ⟨hct.le,ht.2⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hct)))
    exact fun x hx => ⟨hx.2.le,hx.1.2⟩

/-- Smoothness of an arc follows from its actual nonsingular smooth field. -/
theorem smooth_arc {a b : ℝ} {f : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {s : Set ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ s))
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (f t (u t)) (Icc a b) t)
    (hr : MapsTo u (Icc a b) s) : ContDiffOn ℝ ∞ u (Icc a b) :=
  ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hf hu hr

end SepticProfile.ODEGlue

end
end

end OAI
