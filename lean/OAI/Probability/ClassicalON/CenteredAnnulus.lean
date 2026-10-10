import OAI.Probability.ClassicalON.AnnulusCrossing

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph

theorem centered_crossing_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph) (z : Site),
      (∀ v : G.vertices,siteRadius z v.val≤2*(2^k:ℕ)) →
      ∀ (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (I O : Set G.vertices),(∀ v∈I,siteRadius z v.val≤(2^k:ℕ)) →
        (∀ v∈O,2*(2^k:ℕ)≤ siteRadius z v.val) →
      poleBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (I∪O) (fun _ => true)
        (crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O)≤ε := by
  obtain ⟨k,hk,hsmall⟩ := annulus_crossing_small β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G z hG b hb I O hI hO
  let H := G.translate z
  let ev : G.vertices ≃ H.vertices := G.translateVertexEquiv z
  let ee : G.edges ≃ H.edges := G.translateEdgeEquiv z
  let I' : Set H.vertices := ev.symm ⁻¹' I
  let O' : Set H.vertices := ev.symm ⁻¹' O
  have hi (v : G.vertices) : ev v∈I' ↔ v∈I := by simp only [I',mem_preimage,Equiv.symm_apply_apply]
  have ho (v : G.vertices) : ev v∈O' ↔ v∈O := by simp only [O',mem_preimage,Equiv.symm_apply_apply]
  have hl (e : G.edges) : (ee e).val.1=ev e.val.1 := rfl
  have hr (e : G.edges) : (ee e).val.2=ev e.val.2 := rfl
  have he (η : H.edges → Bool) :
      crossingIndicator (fun e : H.edges => e.val.1) (fun e => e.val.2) I' O' η=
        crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O (fun e => η (ee e)) := by
    unfold crossingIndicator
    rw [bondCrossing_reindex ev ee _ _ _ _ hl hr I O I' O' hi ho]
  have hmean := poleBondMean_reindex ev ee (fun e : G.edges => e.val.1) (fun e => e.val.2)
    (fun e : H.edges => e.val.1) (fun e => e.val.2) b (fun e => b (ee.symm e)) (I∪O) (I'∪O')
    (fun e => by simp) hl hr (fun v => by simp only [mem_union,hi,ho])
    (crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O)
  have hbox : H.WithinDyadicBox k := by
    intro v
    obtain ⟨v,rfl⟩ := ev.surjective v
    change |v.val.1-z.1|≤2*(2^k:ℕ) ∧ |v.val.2-z.2|≤2*(2^k:ℕ)
    exact (siteRadius_le_iff z v.val _).mp (hG v)
  have hinner : I'⊆H.innerSet k := by
    intro v hv
    obtain ⟨v,rfl⟩ := ev.surjective v
    have hv' := (siteRadius_le_iff z v.val _).mp (hI v ((hi v).mp hv))
    have hn : (0:ℝ)<2^k := by positivity
    change |((v.val.1-z.1:ℤ):ℝ)/(2:ℝ)^k|≤1 ∧ |((v.val.2-z.2:ℤ):ℝ)/(2:ℝ)^k|≤1
    simp only [abs_div,abs_of_pos hn,div_le_one hn]
    exact ⟨by exact_mod_cast hv'.1,by exact_mod_cast hv'.2⟩
  have houter : O'⊆H.outerSet k := by
    intro v hv
    obtain ⟨v,rfl⟩ := ev.surjective v
    have hv' := hO v ((ho v).mp hv)
    have hn : (0:ℝ)<2^k := by positivity
    change 2≤|((v.val.1-z.1:ℤ):ℝ)/(2:ℝ)^k| ∨ 2≤|((v.val.2-z.2:ℤ):ℝ)/(2:ℝ)^k|
    simp only [abs_div,abs_of_pos hn,le_div_iff₀ hn]
    change _≤ max _ _ at hv'
    rcases le_max_iff.mp hv' with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hs := hsmall H hbox (fun e => b (ee.symm e)) (fun e => hb _) I' O' hinner houter
  rw [show crossingIndicator (fun e : H.edges => e.val.1) (fun e => e.val.2) I' O'=
    (fun η => crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O
      (fun e => η (ee e))) from funext he] at hs
  rwa [hmean] at hs

theorem local_annulus_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ z : Site,let H := G.annulusGraph (2^k:ℕ) z
      poleBondMean (fun e : H.edges => e.val.1) (fun e => e.val.2) (G.annulusCoupling b (2^k:ℕ) z)
        (G.annulusPins (2^k:ℕ) z) (fun _ => true)
        (crossingIndicator (fun e : H.edges => e.val.1) (fun e => e.val.2)
          (G.annulusInner (2^k:ℕ) z) (G.annulusOuter (2^k:ℕ) z))≤ε := by
  obtain ⟨k,hk,hs⟩ := centered_crossing_small β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G b hb z
  apply hs (G.annulusGraph (2^k:ℕ) z) z
  · intro v
    exact ((Finset.mem_filter.mp v.property).2).2
  · intro e
    exact hb (G.restrictEdge _ e)
  · intro v hv
    exact le_of_eq hv
  · intro v hv
    exact le_of_eq hv.symm

end ClassicalON.LatticeGraph

end

end OAI
