import OAI.Geometry.Convex.GeneralMahler.Brouwer.Simplex

namespace OAI
/-! General fixed point for compact convex subsets of real normed spaces. -/
noncomputable section
open Set Filter Metric Real
open scoped Topology
namespace GeneralMahler
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma approx_fixedpoint (K : Set X) (hk : IsCompact K) (hc : Convex ℝ K)
    (he : K.Nonempty) (f:X→X) (hf : ContinuousOn f K) (hm : MapsTo f K K)
    {ε : ℝ} (hp : 0 < ε) :
    ∃ x∈K, ‖f x - x‖ ≤ ε := by
  classical
  obtain ⟨t,htk,ht,hcov⟩ := hk.finite_cover_balls hp
  let I := t
  let : Fintype I := ht.fintype
  have hec (x : X) (hx : x ∈ K) : ∃ i : I, dist x i.val < ε := by
    have h := hcov hx
    simp only [mem_iUnion] at h
    obtain ⟨z,hz,ha⟩ := h; exact ⟨⟨z,hz⟩,ha⟩
  let : Nonempty I := by
    obtain ⟨x,hx⟩ := he
    obtain ⟨i,_⟩ := hec x hx; exact ⟨i⟩
  let g (x:X) (i:I) := max 0 (ε-dist x i.val)
  let T (x:X) := ∑ i,g x i
  let r (x:X) (i:I) := g x i / T x
  have hg (x:X) (i:I) : 0 ≤ g x i := le_max_left ..
  have hT (x:X) (hx:x∈K) : 0<T x := by
    obtain ⟨i,hi⟩ := hec _ hx
    apply lt_of_lt_of_le _ (Finset.single_le_sum (f := g x)
      (fun j _=>hg x j) (Finset.mem_univ i))
    exact lt_of_lt_of_le (sub_pos.mpr hi) (le_max_right ..)
  have hmR (x) (hx:x∈K) : r x ∈ simplexSet I :=
    ⟨fun i=>div_nonneg (hg x i) (hT x hx).le,
      by dsimp only [r]; rw [← Finset.sum_div]; exact div_self (hT x hx).ne'⟩
  have hRc : ContinuousOn r K := by
    refine continuousOn_pi.mpr (fun i=>ContinuousOn.div ?_ ?_ ?_)
    · apply Continuous.continuousOn
      unfold g; fun_prop
    · apply Continuous.continuousOn
      unfold T g; fun_prop
    exact fun x hx=>(hT x hx).ne'
  let s (w:I→ℝ) := ∑ i:I,w i • i.val
  have hs : MapsTo s (simplexSet I) K :=
    fun x hx=>hc.sum_mem (fun i _ => hx.1 i) hx.2 (fun i _=>htk i.property)
  have hsc : Continuous s := by unfold s; fun_prop
  obtain ⟨w,hw,hew⟩ := BrouwerSimplex (r ∘ f ∘ s) (fun x hx=>hmR _ (hm (hs hx)))
    (hRc.comp (hf.comp hsc.continuousOn hs) (hm.comp hs))
  let x := s w
  have hx : x∈K := hs hw
  refine ⟨x,hx,?_⟩
  have he : ∑ i:I,w i • (f x - i.val) = f x - x := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw.2,one_smul]
    rfl
  calc
    _ = ‖∑ i:I,w i • (f x - i.val)‖ := by rw [he]
    _ ≤ ∑ i:I, ‖w i • (f x - i.val)‖ := norm_sum_le ..
    _ ≤ ∑ i:I,w i*ε := by
      apply Finset.sum_le_sum; intro i _
      rw [norm_smul,Real.norm_of_nonneg (hw.1 i)]
      by_cases h : dist (f x) i.val < ε
      · rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left h.le (hw.1 i)
      · have he : w i=0 := by
          have he : r (f x) i = w i := congrFun hew _
          rw [← he]
          unfold r g
          rw [max_eq_left (by linarith)]
          simp
        rw [he,zero_mul,zero_mul]
    _ = ε := by rw [← Finset.sum_mul,hw.2,one_mul]

theorem compact_fixedpoint (K : Set X) (hk : IsCompact K) (hc : Convex ℝ K)
    (he : K.Nonempty) (f:X→X) (hf : ContinuousOn f K) (hm : MapsTo f K K) :
    ∃ x∈K,f x=x := by
  obtain ⟨z,hz,h⟩ := hk.exists_isMinOn he (hf.sub continuous_id.continuousOn).norm
  by_cases hi : f z=z
  · exact ⟨z,hz,hi⟩
  have hpos : 0 < ‖f z-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hi)
  obtain ⟨x,hx,hx'⟩ := approx_fixedpoint K hk hc he f hf hm
    (ε:=‖f z-z‖/2) (by positivity)
  have hb : ‖f z-z‖ ≤ ‖f x-x‖ := h hx
  exfalso
  linarith
end GeneralMahler

end

end OAI
