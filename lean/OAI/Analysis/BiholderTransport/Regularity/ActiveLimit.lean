import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.CompactConfigurations
import OAI.Analysis.BiholderTransport.Regularity.FiniteSimplexRepresentation

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma fixed_simplex_representation {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {x : E} (hx : x∈convexHull ℝ S) :
    ∃ z : Fin (Module.finrank ℝ E+1) → E, ∃ w : Fin (Module.finrank ℝ E+1) → ℝ,
      (∀ i,z i∈S) ∧ (∀ i,0≤w i) ∧ ∑ i,w i=1 ∧ ∑ i,w i • z i=x := by
  classical
  obtain ⟨m,hm,hN,z,w,hz,hw,hs,hb⟩ := finite_simplex_representation hx
  obtain ⟨r,he⟩ := Nat.exists_eq_add_of_le hN
  rw [he]
  refine ⟨Fin.addCases z (fun _ : Fin r => z ⟨0,hm⟩),
    Fin.addCases w (fun _ : Fin r => 0),?_,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.addCases_left] using hz j
    · simpa only [Fin.addCases_right] using hz ⟨0,hm⟩
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.addCases_left] using hw j
    · simp only [Fin.addCases_right,le_refl]
  · simpa only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,Finset.sum_const_zero,
      add_zero] using hs
  · simpa only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,zero_smul,
      Finset.sum_const_zero,add_zero] using hb

lemma compact_barycentric_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set (E×E)} (hC : IsCompact C)
    {a v : ℕ → E} {a₀ v₀ : E} (ha : Tendsto a atTop (𝓝 a₀))
    (hv : Tendsto v atTop (𝓝 v₀))
    (hrep : ∀ k,v k∈convexHull ℝ {p | (a k,p)∈C}) :
    ∃ z : ℕ → Fin (Module.finrank ℝ E+1) → E,
    ∃ w : ℕ → Fin (Module.finrank ℝ E+1) → ℝ,
    ∃ z₀ : Fin (Module.finrank ℝ E+1) → E,
    ∃ w₀ : Fin (Module.finrank ℝ E+1) → ℝ,
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ k,(∀ i,(a k,z k i)∈C) ∧ (∀ i,0≤w k i) ∧
         ∑ i,w k i=1 ∧ ∑ i,w k i • z k i=v k) ∧
      Tendsto (z ∘ σ) atTop (𝓝 z₀) ∧ Tendsto (w ∘ σ) atTop (𝓝 w₀) ∧
      (∀ i,(a₀,z₀ i)∈C) ∧ (∀ i,0≤w₀ i) ∧ ∑ i,w₀ i=1 ∧ ∑ i,w₀ i • z₀ i=v₀ := by
  classical
  choose z w hz hw hs hb using (fun k=>fixed_simplex_representation (hrep k))
  let d : ℕ → EnvelopeData E (Fin (Module.finrank ℝ E+1)) :=
    fun k=>((a k,z k),(w k,0))
  have hcompact := compact_common_base_configurations
    (ι := Fin (Module.finrank ℝ E+1)) hC 0
  have hd : ∀ k,d k∈{q : EnvelopeData E (Fin (Module.finrank ℝ E+1)) |
      (∀ i,(q.1.1,q.1.2 i)∈C) ∧ (∀ i,0≤q.2.1 i) ∧ ∑ i,q.2.1 i=1 ∧ q.2.2∈Icc 0 0} :=
    fun k=>⟨hz k,hw k,hs k,le_refl _,le_refl _⟩
  obtain ⟨q,hq,σ,hσ,hlim⟩ := hcompact.tendsto_subseq hd
  have ha' : Tendsto (a ∘ σ) atTop (𝓝 q.1.1) := hlim.fst_nhds.fst_nhds
  have hae : q.1.1=a₀ := tendsto_nhds_unique ha' (ha.comp hσ.tendsto_atTop)
  refine ⟨z,w,q.1.2,q.2.1,σ,hσ,(fun k=>⟨hz k,hw k,hs k,hb k⟩),
    hlim.fst_nhds.snd_nhds,hlim.snd_nhds.fst_nhds,?_,hq.2.1,hq.2.2.1,?_⟩
  · simpa only [hae] using hq.1
  · have hsum : Tendsto (fun k=>∑ i,w (σ k) i • z (σ k) i) atTop
        (𝓝 (∑ i,q.2.1 i • q.1.2 i)) := by
      apply tendsto_finsetSum
      intro i _
      exact ((tendsto_pi_nhds.mp hlim.snd_nhds.fst_nhds) i).smul
        ((tendsto_pi_nhds.mp hlim.fst_nhds.snd_nhds) i)
    simp only [hb] at hsum
    exact tendsto_nhds_unique hsum (hv.comp hσ.tendsto_atTop)

lemma positive_barycentric_restriction {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) :
    let κ := {i : ι // 0<w i}
    Nonempty κ ∧ (∑ i:κ,w i=1) ∧
      (∑ i:κ,w i • p i=∑ i,w i • p i) ∧
      ∀ f : ι → ℝ,∑ i:κ,w i*f i=∑ i,w i*f i := by
  classical
  dsimp only
  have he (f : ι → E) : (∑ i:{i : ι // 0<w i},w i • f i)=∑ i,w i • f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i • f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_smul])
  have hr (f : ι → ℝ) : (∑ i:{i : ι // 0<w i},w i*f i)=∑ i,w i*f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i*f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_mul])
  have hsum : (∑ i:{i : ι // 0<w i},w i)=1 := by
    simpa only [mul_one] using (hr (fun _=>1)).trans (by simpa only [mul_one] using hs)
  refine ⟨?_,hsum,he p,hr⟩
  by_contra hn
  have : IsEmpty {i : ι // 0<w i} := not_nonempty_iff.mp hn
  simp at hsum

end WeakMTWTransport

end

end OAI
