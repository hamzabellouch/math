import OAI.Analysis.AncientFlat.Regularity.InterpolationEpsilon

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicInitial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def timeAffineExtension (a b : ℝ) (u v : ℝ → E) (t : ℝ) : E :=
  if t<a then (t-a) • v a+u a else if b<t then (t-b) • v b+u b else u t
lemma timeAffineExtension_eq (a b : ℝ) (u v : ℝ → E) {t : ℝ} (ht : t∈Icc a b) :
    timeAffineExtension a b u v t=u t := by
  simp [timeAffineExtension,not_lt_of_ge ht.1,not_lt_of_ge ht.2]
lemma timeAffineExtension_hasDerivAt (a b : ℝ) (hab : a<b) (u v : ℝ → E)
    (hd : ∀ t∈Icc a b, HasDerivWithinAt u (v t) (Icc a b) t) :
    ∀ t∈Icc a b, HasDerivAt (timeAffineExtension a b u v) (v t) t := by
  intro t ht
  have hint (s : ℝ) (hs : s∈Icc a b) :
      HasDerivWithinAt (timeAffineExtension a b u v) (v s) (Icc a b) s :=
    (hd s hs).congr_of_mem (fun t ht => timeAffineExtension_eq a b u v ht) hs
  by_cases hta : t=a
  · subst t
    have hr := (hint a ⟨le_rfl,hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
    have hl : HasDerivWithinAt (timeAffineExtension a b u v) (v a) (Iic a) a := by
      have H : HasDerivAt (fun t : ℝ => (t-a) • v a+u a) (v a) a := by
        simpa using (((hasDerivAt_id a).sub_const a).smul_const (v a)).add_const (u a)
      apply (H.hasDerivWithinAt (s := Iic a)).congr_of_mem _ (by simp)
      intro s hs
      by_cases hsa : s<a
      · simp [timeAffineExtension,hsa]
      · have he : s=a := le_antisymm hs (le_of_not_gt hsa)
        subst s
        simp [timeAffineExtension,not_lt_of_ge hab.le]
    have he : Iic a∪Ici a=(univ : Set ℝ) := by ext s; simp
    simpa only [he,hasDerivWithinAt_univ] using hl.union hr
  by_cases htb : t=b
  · subst t
    have hl := (hint b ⟨hab.le,le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
    have hr : HasDerivWithinAt (timeAffineExtension a b u v) (v b) (Ici b) b := by
      have H : HasDerivAt (fun t : ℝ => (t-b) • v b+u b) (v b) b := by
        simpa using (((hasDerivAt_id b).sub_const b).smul_const (v b)).add_const (u b)
      apply (H.hasDerivWithinAt (s := Ici b)).congr_of_mem _ (by simp)
      intro s hs
      have hsa : ¬s<a := not_lt_of_ge (hab.le.trans hs)
      by_cases hbs : b<s
      · simp [timeAffineExtension,hsa,hbs]
      · have he : s=b := le_antisymm (le_of_not_gt hbs) hs
        subst s
        simp [timeAffineExtension,not_lt_of_ge hab.le]
    have he : Iic b∪Ici b=(univ : Set ℝ) := by ext s; simp
    simpa only [he,hasDerivWithinAt_univ] using hl.union hr
  exact (hint t ht).hasDerivAt (Icc_mem_nhds
    (lt_of_le_of_ne ht.1 (Ne.symm hta)) (lt_of_le_of_ne ht.2 htb))
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace E]
open ParabolicInterior ParabolicInterpolation

theorem within_lower_jet_interpolation (α ε r R : ℝ) (hα : 0<α) (hα1 : α<1)
    (hε : 0<ε) (hrR : r<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (u ut : ℝ → V → E) (a b : ℝ), a<b →
      ∀ (U M : ℝ), 0≤U → 0≤M →
      (∀ t∈Icc a b, ContDiff ℝ 4 (u t)) →
      (∀ t∈Icc a b, ∀ x, ‖x‖<R → HasDerivWithinAt (fun t => u t x) (ut t x) (Icc a b) t) →
      (∀ t∈Icc a b, ∀ x, ‖x‖<R → ‖ut t x‖≤M) →
      (∀ t∈Icc a b, ∀ x, ‖x‖<R → ‖u t x‖≤U) →
      (∀ t∈Icc a b, ∀ x, ‖x‖<R → ‖iteratedFDeriv ℝ 4 (u t) x‖≤M) →
      ∀ j : ℕ, j≤3 → HolderBound α {p : V × ℝ | ‖p.1‖<r ∧ p.2∈Icc a b}
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (ε*M+C*U) := by
  obtain ⟨C,hC,H⟩ := lower_jet_interpolation (V := V) (E := E) α ε r R hα hα1 hε hrR
  refine ⟨C,hC,?_⟩
  intro u ut a b hab U M hU hM hs hd hut hu hD j hj
  let v : ℝ → V → E := fun t x => timeAffineExtension a b (fun t => u t x) (fun t => ut t x) t
  have he (t : ℝ) (ht : t∈Icc a b) : v t=u t :=
    funext (fun x => timeAffineExtension_eq a b (fun t => u t x) (fun t => ut t x) ht)
  have hv := H v ut (Icc a b) ordConnected_Icc U M hU hM
    (fun t ht => by rw [he t ht]; exact hs t ht)
    (fun t ht x hx => timeAffineExtension_hasDerivAt a b hab (fun t => u t x)
      (fun t => ut t x) (fun s hs => hd s hs x hx) t ht) hut
    (fun t ht x hx => by rw [he t ht]; exact hu t ht x hx)
    (fun t ht x hx => by rw [he t ht]; exact hD t ht x hx) j hj
  exact ⟨fun p hp => by simpa only [he p.2 hp.2] using hv.1 p hp,
    fun p hp q hq => by simpa only [he p.2 hp.2,he q.2 hq.2] using hv.2 p hp q hq⟩
end ParabolicInitial

end

end OAI
