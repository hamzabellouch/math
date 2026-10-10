import OAI.Geometry.Perimeter.Regularity.UniformFlatness
import OAI.Geometry.Perimeter.Regularity.PhaseRestoration
import OAI.Geometry.Perimeter.Regularity.SlabScaling

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem exists_slab_contraction (hn : 1 < n) {v₀ : Euc n} (hv₀ : ‖v₀‖=1)
    (hH : IsLocallyPerimeterMinimizing {x : Euc n | inner ℝ x v₀ < 0}) :
    ∃ q M δ : ℝ, 0 < q ∧ q < 1/64 ∧ 0≤M ∧ 0 < δ ∧ δ≤1 ∧
      ∀ (E : Set (Euc n)), IsLocallyPerimeterMinimizing E →
        (0:Euc n)∈perimeterSupport E → ∀ (v : Euc n), ‖v‖=1 →
          ∀ a : ℝ, 0 < a → a < δ → FullSlab E v 8 a →
            ∃ w : Euc n, ‖w‖=1 ∧ ‖w-v‖≤M*a ∧
              FullSlab (blownUpSet E 0 q) w 8 (a/2) := by
  obtain ⟨K,B,hK,hB,himp⟩ := exists_uniform_normal_height_improvement hn hv₀ hH
  let r := min (1/16) (1/(32*(K+1)))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hr16 : r≤1/16 := min_le_left _ _
  have hr8 : r<1/8 := by linarith
  have hKr : K*r≤1/16 := by
    have hh : r≤1/(32*(K+1)) := min_le_right _ _
    have hp : 0 < 32*(K+1) := by positivity
    have hb := (le_div_iff₀ hp).mp hh
    nlinarith
  obtain ⟨d,hd,hdimp⟩ := himp r hr hr8
  let δ := min d (min (r/16) (min 1 (1/(16*(B+1)))))
  have hδ : 0 < δ := lt_min hd (lt_min (by positivity) (lt_min zero_lt_one (by positivity)))
  have hδd : δ≤d := min_le_left _ _
  have hδr : δ≤r/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ≤1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδB : δ≤1/(16*(B+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r/8,2*B,δ,by positivity,by linarith,by positivity,hδ,hδ1,
    fun E hmin hzero v hv a ha haδ hs ↦ ?_⟩
  obtain ⟨w,hw,hwd,hheight⟩ := hdimp v hv E hmin hzero a ha (haδ.trans_le hδd) hs
  have hab : a < r/8 := by linarith [haδ.trans_le hδr]
  have ha1 : a < 1 := haδ.trans_le hδ1
  have hdist : ‖w-v‖≤1/4 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 16*(B+1))).mp (haδ.trans_le hδB)
    nlinarith
  have hb : 0≤a*r/16 := by positivity
  have hbr : a*r/16<r/8 := by nlinarith
  have hh : ∀ x∈perimeterSupport E ∩ Metric.ball 0 r, |inner ℝ w x|≤a*r/16 := by
    intro x hx
    apply (hheight x hx).trans
    have hmul := mul_le_mul_of_nonneg_left hKr (mul_nonneg ha.le hr.le)
    nlinarith
  have hslab := hs.restore_phase hn hmin hv hr (by linarith) hab hb hbr hdist hh
  have hscaled := hslab.dilate hmin.1 (by positivity : 0 < r/8)
  have hR : r/(r/8)=8 := by field_simp
  have hA : (a*r/16)/(r/8)=a/2 := by field_simp; ring
  rw [hR,hA] at hscaled
  exact ⟨w,hw,by nlinarith [hwd],hscaled⟩

end RPISingularHarnack

end

end OAI
