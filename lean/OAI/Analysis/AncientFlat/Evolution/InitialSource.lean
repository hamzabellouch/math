import OAI.Analysis.AncientFlat.Evolution.InitialCore
import OAI.Analysis.AncientFlat.Regularity.HolderExtension
import OAI.Analysis.AncientFlat.Regularity.HolderProducts
import OAI.Analysis.AncientFlat.Geometry.InteriorCutoff

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction
namespace ParabolicInitial
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def initialBump (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : ContDiffBump (0 : V) :=
  ⟨3/2,7/4,by norm_num,by norm_num⟩
lemma initialBump_holder (α : ℝ) (hα : 0<α) (hα1 : α≤1) :
    ∃ C : ℝ, 0<C ∧ HolderBound α univ (fun p : V × ℝ => initialBump V p.1) C := by
  have hs := compact_separated_smul (initialBump V) (baseBump ℝ)
    (initialBump V).hasCompactSupport (baseBump ℝ).hasCompactSupport
  obtain ⟨C,hC,H⟩ := compact_contDiff_holder α hα hα1
    (fun p : V × ℝ => baseBump ℝ p.2 • initialBump V p.1)
    (((baseBump ℝ).contDiff.comp contDiff_snd).smul
      ((initialBump V).contDiff.comp contDiff_fst)) hs
  have hzero : baseBump ℝ 0=1 := by
    exact (baseBump ℝ).one_of_mem_closedBall (by simp [baseBump])
  refine ⟨C,hC,⟨?_,?_⟩⟩
  · intro p _
    simpa only [hzero,one_smul] using H.1 (p.1,0) (mem_univ _)
  · intro p _ q _
    have hh := H.2 (p.1,0) (mem_univ _) (q.1,0) (mem_univ _)
    simp only [hzero,one_smul] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow (pdist_nonneg _ _) _ hα.le
    simp only [pdist,sub_self,abs_zero,
      Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),add_zero]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)

theorem exists_initial_source (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ C : ℝ, 0<C ∧ ∀ h : ℝ, 0≤h → ∀ (f : V × ℝ → ℂ) (F : ℝ), 0≤F →
      HolderBound α (slab 2 h) f F →
      ∃ g : C₀(V,ℂ), ‖g‖≤C*F ∧
        (∀ x y, ‖g x-g y‖≤C*F*‖x-y‖^α) ∧
        (∀ x, ‖x‖≤3/2 → g x=f (x,0)) := by
  obtain ⟨A,hA,HA⟩ := initialBump_holder (V := V) α hα hα1.le
  refine ⟨10*A,by positivity,?_⟩
  intro h hh f F hF hf
  let g : V → ℂ := fun x => initialBump V x • f (x,0)
  have HF : HolderBound α {p : V × ℝ | ‖p.1‖<2} (fun p => f (p.1,0)) F := by
    refine ⟨fun p hp => hf.1 (p.1,0) ⟨hp,le_rfl,hh⟩,?_⟩
    intro p hp q hq
    have H := hf.2 (p.1,0) ⟨hp,le_rfl,hh⟩ (q.1,0) ⟨hq,le_rfl,hh⟩
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ hF
    apply Real.rpow_le_rpow (pdist_nonneg _ _) _ hα.le
    simp only [pdist,sub_self,abs_zero,
      Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),add_zero]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
  have HM := (HA.restrict (subset_univ _)).smul HF hA.le hF
  have HG : HolderBound α {p : V × ℝ | p.2∈(univ : Set ℝ)} (fun p => g p.1) (10*A*F) := by
    have H := holder_globalize α (2*A*F) (2*A*F) hα.le hα1.le (by positivity) (by positivity)
      univ (fun p : V × ℝ => g p.1)
      (fun p _ hp => by
        dsimp [g]
        rw [(initialBump V).zero_of_le_dist (by simpa [initialBump,dist_zero_right] using hp)]
        simp)
      (fun p _ hp => HM.1 p hp)
      (fun p _ hp q _ hq => HM.2 p hp q hq)
    convert H using 1
    ring
  have HGu : HolderBound α univ (fun p : V × ℝ => g p.1) (10*A*F) := by
    simpa only [mem_univ,ofPred_true] using HG
  have hc : Continuous g := by
    have H := continuousOn_univ.mp (HGu.continuousOn hα)
    exact H.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : V => (0:ℝ))))
  have hs : HasCompactSupport g := (initialBump V).hasCompactSupport.smul_right
  let G : C₀(V,ℂ) := ⟨⟨g,hc⟩,hs.is_zero_at_infty⟩
  refine ⟨G,?_,?_,?_⟩
  · change ‖G.toBCF‖≤10*A*F
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    exact HGu.1 (x,0) (mem_univ _)
  · intro x y
    simpa [G,g,pdist] using HGu.2 (x,0) (mem_univ _) (y,0) (mem_univ _)
  · intro x hx
    change initialBump V x • f (x,0)=f (x,0)
    rw [(initialBump V).one_of_mem_closedBall (by simpa [initialBump,dist_zero_right] using hx),one_smul]
end ParabolicInitial

end

end OAI
