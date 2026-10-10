import Mathlib
import OAI.Analysis.Conductivity.Flux.CompactBoxDivergence

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma compact_image_inner_interval {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : ContinuousOn f K)
    {a b : ℝ} (hab : a<b) (hv : ∀ x∈K, a<f x ∧ f x<b) :
    ∃ a' b' : ℝ, a<a' ∧ a'<b' ∧ b'<b ∧ ∀ x∈K, a'<f x ∧ f x<b' := by
  by_cases hn : K.Nonempty
  · obtain ⟨m,hm,hmin⟩ := hK.exists_isMinOn hn hf
    obtain ⟨M,hM,hmax⟩ := hK.exists_isMaxOn hn hf
    refine ⟨(a+f m)/2,(b+f M)/2,by linarith [(hv m hm).1],?_,by linarith [(hv M hM).2],?_⟩
    · have hmM : f m≤f M := hmin hM; linarith [(hv m hm).1,(hv M hM).2]
    · intro x hx
      have hmx : f m≤f x := hmin hx
      have hxM : f x≤f M := hmax hx
      constructor <;> linarith [(hv m hm).1,(hv M hM).2]
  · refine ⟨(2*a+b)/3,(a+2*b)/3,by linarith,by linarith,by linarith,?_⟩
    intro x hx; exact (hn ⟨x,hx⟩).elim

theorem compact_box_divergence_inside {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    {r : Box3 → ℝ} (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r) (hs : HasCompactSupport r)
    (hv : tsupport r⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hz : (∫ p, r p)=0) :
    ∃ F₁ F₂ F₃ : Box3 → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) F₃ ∧
      HasCompactSupport F₁ ∧ HasCompactSupport F₂ ∧ HasCompactSupport F₃ ∧
      (∀ p, cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
        cubePartial F₃ ((0,0),1) p=r p) ∧
      tsupport F₁∪tsupport F₂∪tsupport F₃⊆
        (Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) := by
  obtain ⟨a₀,b₀,ha₀,hab₀,hb₀,hv₀⟩ := compact_image_inner_interval hs
    (continuous_fst.fst.continuousOn) (hab 0) (fun p hp => (hv hp).1.1)
  obtain ⟨a₁,b₁,ha₁,hab₁,hb₁,hv₁⟩ := compact_image_inner_interval hs
    (continuous_fst.snd.continuousOn) (hab 1) (fun p hp => (hv hp).1.2)
  obtain ⟨a₂,b₂,ha₂,hab₂,hb₂,hv₂⟩ := compact_image_inner_interval hs
    (continuous_snd.continuousOn) (hab 2) (fun p hp => (hv hp).2)
  let a' : Fin 3 → ℝ := ![a₀,a₁,a₂]
  let b' : Fin 3 → ℝ := ![b₀,b₁,b₂]
  have hab' : ∀ i,a' i<b' i := by intro i; fin_cases i <;> assumption
  obtain ⟨F₁,F₂,F₃,h₁,h₂,h₃,hs₁,hs₂,hs₃,hd,ht⟩ := compact_box_divergence hab' hr hs
    (fun p hp => ⟨⟨hv₀ p hp,hv₁ p hp⟩,hv₂ p hp⟩) hz
  refine ⟨F₁,F₂,F₃,h₁,h₂,h₃,hs₁,hs₂,hs₃,hd,ht.trans ?_⟩
  intro p hp
  exact ⟨⟨⟨ha₀.trans_le hp.1.1.1,hp.1.1.2.trans_lt hb₀⟩,
    ⟨ha₁.trans_le hp.1.2.1,hp.1.2.2.trans_lt hb₁⟩⟩,
    ⟨ha₂.trans_le hp.2.1,hp.2.2.trans_lt hb₂⟩⟩

lemma cubePartial_tsupport {f : Box3 → ℝ} (v : Box3) :
    tsupport (cubePartial f v)⊆tsupport f := tsupport_fderiv_apply_subset ℝ v

end ScalarConductivity

end

end OAI
