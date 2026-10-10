import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly
import OAI.Analysis.Conductivity.Variational.ParametricDiffeomorph
import OAI.Analysis.Conductivity.Variational.SmoothNormalizedEndFamily

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_axial_normalization
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P) (x : Coord3)
    {V : Coord3 → ℝ} (hV : ContDiff ℝ (↑(⊤:ℕ∞)) V)
    (hub : ∀ y,u (p,y)=y 0) (hvb : ∀ y,v (p,y)=V y) :
    ∃ Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3),
      (p,x)∈Y.source ∧ (∀ q y,Y (q,y)=(q,![u (q,y),y 1,y 2])) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target ∧
      ∃ w : P×Coord3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) w ∧
        (∀ y,w (p,y)=V y) ∧ ∀ᶠ z in 𝓝 (p,x),w (Y z)=v z := by
  let φ : P×Coord3 → Coord3 := fun q => ![u q,q.2 1,q.2 2]
  have hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact hu
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => q.2 1)
      exact (contDiff_apply ℝ ℝ (1:Fin 3)).comp contDiff_snd
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => q.2 2)
      exact (contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd
  have hφbase (y : Coord3) : φ (p,y)=y := by
    ext i
    fin_cases i <;> simp [φ,hub]
  have hφd : fderiv ℝ (fun y => φ (p,y)) x=(ContinuousLinearEquiv.refl ℝ Coord3 : Coord3 →L[ℝ] Coord3) := by
    rw [show (fun y => φ (p,y))=id from funext hφbase,fderiv_id]
    rfl
  obtain ⟨Y,hYs,_,hY,hsm,hinv⟩ := exists_parametric_diffeomorph hφ p x
    (ContinuousLinearEquiv.refl ℝ Coord3) hφd isOpen_univ (mem_univ _)
  have hbase (y : Coord3) : Y (p,y)=(p,y) := by rw [hY,hφbase]
  have hYt : (p,x)∈Y.target := by simpa only [hbase] using Y.map_source hYs
  let N := Y.source∩Y.target
  have hN : IsOpen N := Y.open_source.inter Y.open_target
  have hpN : (p,x)∈N := ⟨hYs,hYt⟩
  let Ω := N∩Metric.ball (p,x) 1
  have hΩ : IsOpen Ω := hN.inter Metric.isOpen_ball
  have hpΩ : (p,x)∈Ω := ⟨hpN,Metric.mem_ball_self zero_lt_one⟩
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton hΩ
    (Metric.isBounded_ball.subset inter_subset_right) (singleton_subset_iff.mpr hpΩ)
  let f : P×Coord3 → ℝ := fun z => v (Y.symm z)-V z.2
  have hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f N :=
    (hv.contDiffOn.comp (hinv.mono inter_subset_right) (fun _ _ => mem_univ _)).sub
      (hV.comp contDiff_snd).contDiffOn
  let w : P×Coord3 → ℝ := fun z => V z.2+χ z*f z
  have hw : ContDiff ℝ (↑(⊤:ℕ∞)) w :=
    (hV.comp contDiff_snd).add (smooth_mul_of_support_in_open hN hf hχ (hχs.trans inter_subset_left))
  refine ⟨Y,hYs,hY,hsm,hinv,w,hw,?_,?_⟩
  · intro y
    by_cases hc : χ (p,y)=0
    · simp only [w,hc,zero_mul,add_zero]
    · have he : Y.symm (p,y)=(p,y) := by
        simpa only [hbase] using Y.left_inv (hχs (subset_tsupport χ hc)).1.1
      simp only [w,f,he,hvb,sub_self,mul_zero,add_zero]
  · have hh : Tendsto Y (𝓝 (p,x)) (𝓝 (p,x)) := by
      simpa only [hbase] using hsm.continuous.tendsto (p,x)
    filter_upwards [Y.open_source.mem_nhds hYs,hh.eventually (hχone (p,x) (mem_singleton _))]
      with z hz hχz
    simp only [w,f,hχz,one_mul,Y.left_inv hz,add_sub_cancel]

end ScalarConductivity

end
end

end OAI
