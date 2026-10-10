import OAI.Dynamics.StandardMap.CoverContraction

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma volume_preimage_rescale (L b : ℝ) (hL : 0 < L) (S : Set ℝ) :
    volume ((fun x => (x-b)*L) ⁻¹' S)=ENNReal.ofReal (1/L)*volume S := by
  have he : (fun x => (x-b)*L) ⁻¹' S =
      (fun x => x+(-b)) ⁻¹' ((fun x => L*x) ⁻¹' S) := by
    ext x
    simp only [mem_preimage]
    simp [sub_eq_add_neg,mul_comm]
  rw [he,measure_preimage_add_right,Real.volume_preimage_mul_left (ne_of_gt hL)]
  simp [abs_of_pos (inv_pos.mpr hL),one_div]
lemma CommonGood.matchedScale_pos {k q θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q θ jm jp) (hM : 1 < growthBase k) :
    0 < matchedScale k q θ jm jp := by
  obtain ⟨b,hm,hp⟩:=hg
  exact (abs_pos.mpr (hm.t_ne_zero hM)).trans_le (le_max_left _ _)

lemma local_group_scarcity (k q : ℝ) (jm jp : ℕ) (F : Set ℝ)
    (s : ℝ → ℝ) (η η' ε : ℝ)
    (hM : 1 < growthBase k) (hη : 0 ≤ η) (hε0 : 0 ≤ ε) (hε : ε/5 < η')
    (hg : ∀ a ∈ F, CommonGood k q a jm jp)
    (hsmall : ∀ a ∈ F, s a ≤ ε/(10*matchedScale k q a jm jp))
    (hscarce : ∀ b ∈ F,
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'} ≤ ENNReal.ofReal η) :
    ∀ b ∈ F,
      volume (⋃ a ∈ F, ⋃ (_ : dist a b < 3/(10*matchedScale k q b jm jp) ∧
        1/(10*matchedScale k q a jm jp) ≤ 2/(10*matchedScale k q b jm jp)), ball a (s a))  ≤
      ENNReal.ofReal (5*η)*volume (ball b (1/(10*matchedScale k q b jm jp))) := by
  intro b hb
  let L:=matchedScale k q b jm jp
  have hL : 0 < L := (hg b hb).matchedScale_pos hM
  let S := {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'}
  have hsub : (⋃ a ∈ F, ⋃ (_ : dist a b < 3/(10*L) ∧
      1/(10*matchedScale k q a jm jp) ≤ 2/(10*L)), ball a (s a))  ⊆
      (fun x => (x-b)*L) ⁻¹' S := by
    intro x hx
    obtain ⟨a,ha,hx⟩:=mem_iUnion₂.mp hx
    obtain ⟨⟨hd,hr⟩,hx⟩:=mem_iUnion.mp hx
    have hLa : 0 < matchedScale k q a jm jp := (hg a ha).matchedScale_pos hM
    have hs : s a < η'/L := by
      have hrad : s a ≤ ε*(2/(10*L)) := by
        calc
          _  ≤  ε/(10*matchedScale k q a jm jp) := hsmall a ha
          _ = ε*(1/(10*matchedScale k q a jm jp)) := by ring
          _  ≤  _ := mul_le_mul_of_nonneg_left hr hε0
      have hlt : ε*(2/(10*L)) < η'/L := by
        field_simp
        nlinarith
      exact hrad.trans_lt hlt
    refine ⟨(a-b)*L,?_,?_⟩
    · constructor
      · have hd' : |a-b| *L < 3/10 := by
          rw [Real.dist_eq] at hd
          have := (lt_div_iff₀ (by positivity : 0 < 10*L)).mp hd
          nlinarith
        have habs : |(a-b)*L| < 3/10 := by simpa only [abs_mul,abs_of_pos hL] using hd'
        exact abs_le.mp (habs.le.trans (by norm_num : (3/10:ℝ) ≤ 1))
      · have he : b+((a-b)*L)/matchedScale k q b jm jp=a := by
          dsimp [L] at hL
          field_simp
          ring
        rw [he]
        exact hg a ha
    · have hx' : |x-a| < η'/L := by
        have := mem_ball.mp hx
        rw [Real.dist_eq] at this
        exact this.trans hs
      rw [Real.dist_eq]
      have he : (x-b)*L-(a-b)*L=(x-a)*L := by ring
      rw [he,abs_mul,abs_of_pos hL]
      exact (lt_div_iff₀ hL).mp hx'
  calc
    _  ≤  volume ((fun x => (x-b)*L) ⁻¹' S) := measure_mono hsub
    _ = ENNReal.ofReal (1/L)*volume S := volume_preimage_rescale L b hL S
    _  ≤  ENNReal.ofReal (1/L)*ENNReal.ofReal η := by
      gcongr
      exact hscarce b hb
    _ = _ := by
      rw [Real.volume_ball,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [L]
      ring
end StandardMapEntropy

end OAI
