import OAI.Geometry.Perimeter.Regularity.GraphExistence

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem fiber_chord_norm {v : Euc n} (hv : ‖v‖=1)
    (y z : normalPlane v) (s t : ℝ) :
    ‖((y:Euc n)+s•v)-((z:Euc n)+t•v)‖≤‖y-z‖+|s-t| := by
  have he : ((y:Euc n)+s•v)-((z:Euc n)+t•v)=((y-z:normalPlane v):Euc n)+(s-t)•v := by
    simp only [Submodule.coe_sub,sub_smul]; abel
  rw [he]
  simpa only [norm_smul,Real.norm_eq_abs,hv,mul_one,Submodule.norm_coe] using
    norm_add_le ((y-z:normalPlane v):Euc n) ((s-t)•v)

theorem single_graph_from_slab (hn : 1<n) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {v : Euc n} (hv : ‖v‖=1)
    {a : ℝ} (ha : 0≤a) (ha4 : a<1/4) (hs : FullSlab E v 8 a)
    (hchord : ∀ p∈perimeterSupport E ∩ Metric.ball 0 1,
      ∀ x∈perimeterSupport E ∩ Metric.ball 0 1,
        |inner ℝ v (x-p)|≤(1/2)*‖x-p‖) :
    ∃ f : normalPlane v → ℝ,
      (∀ y, ‖y‖<1/4 → |f y|≤a ∧ (y:Euc n)+f y•v∈perimeterSupport E ∩ Metric.ball 0 1) ∧
      (∀ y z, ‖y‖<1/4 → ‖z‖<1/4 → |f y-f z|≤‖y-z‖) ∧
      (∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
        ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y)) := by
  have hex (y : normalPlane v) : ∃ t : ℝ, ‖y‖<1/4 →
      |t|≤a ∧ (y:Euc n)+t•v∈perimeterSupport E ∩ Metric.ball 0 1 := by
    by_cases hy : ‖y‖<1/4
    · obtain ⟨t,ht⟩ := hs.central_fiber_meets_support hn hmin hv ha ha4 y hy
      exact ⟨t,fun _ ↦ ht⟩
    · exact ⟨0,fun h ↦ (hy h).elim⟩
  choose f hf using hex
  refine ⟨f,hf,?_,?_⟩
  · intro y z hy hz
    have hh := hchord _ (hf z hz).2 _ (hf y hy).2
    rw [inner_sub_right,normal_fiber_inner hv,normal_fiber_inner hv] at hh
    have hn := fiber_chord_norm hv y z (f y) (f z)
    linarith
  · intro y t hy hyt
    constructor
    · intro hsT
      have hh := hchord _ (hf y hy).2 _ ⟨hsT,by simpa only [Metric.mem_ball,dist_zero_right] using hyt⟩
      rw [inner_sub_right,normal_fiber_inner hv,normal_fiber_inner hv] at hh
      have hn := fiber_chord_norm hv y y t (f y)
      simp only [sub_self,norm_zero,zero_add] at hn
      have hz : |t-f y|=0 := by linarith [abs_nonneg (t-f y)]
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    · rintro rfl
      exact (hf y hy).2.1

end RPISingularHarnack

end

end OAI
