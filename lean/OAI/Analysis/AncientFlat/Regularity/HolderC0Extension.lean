import OAI.Analysis.AncientFlat.Regularity.HolderContinuity

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
lemma holder_slice_continuous [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {α H : ℝ} (hα : 0<α) (I : Set ℝ) (g : V × ℝ → ℂ)
    (hg : HolderBound α {p : V × ℝ | p.2∈I} g H) (t : ℝ) (ht : t∈I) :
    Continuous (fun x => g (x,t)) :=
  hg.continuousOn hα |>.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ht)
variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma holder_c0_extension {α H a b : ℝ} (hα : 0<α) (hH : 0≤H) (hab : a≤b)
    (g : V × ℝ → ℂ) (hg : HolderBound α {p : V × ℝ | p.2∈Icc a b} g H)
    (hc : ∀ t∈Icc a b, HasCompactSupport (fun x => g (x,t))) :
    ∃ f : ℝ →ᵇ C₀(V,ℂ), (∀ t∈Icc a b, ∀ x, f t x=g (x,t)) ∧
      ∀ t, ‖f t‖≤H := by
  let c : ℝ → ℝ := fun t => (projIcc a b hab t).val
  have hcc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hci (t : ℝ) : c t∈Icc a b := (projIcc a b hab t).property
  let w (t : ℝ) : C₀(V,ℂ) :=
    ⟨⟨fun x => g (x,c t),holder_slice_continuous hα (Icc a b) g hg (c t) (hci t)⟩,
       (hc (c t) (hci t)).is_zero_at_infty⟩
  have hb (t : ℝ) : ‖w t‖≤H := by
    change ‖(w t).toBCF‖≤H
    exact (BoundedContinuousFunction.norm_le hH).mpr (fun x => hg.1 (x,c t) (hci t))
  have ht (s t : ℝ) : ‖w s-w t‖≤H*|c s-c t|^(α/4) := by
    change ‖(w s-w t).toBCF‖≤_
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    exact hg.temporal (hci s) (hci t) x
  have hw : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
    have hpow : 0<α/4 := by positivity
    have hcont : Continuous (fun s => H*|c s-c t|^(α/4)) := continuous_const.mul
      ((hcc.sub continuous_const).abs.rpow_const (fun _ => Or.inr hpow.le))
    have hl : Tendsto (fun s => H*|c s-c t|^(α/4)) (𝓝 t) (𝓝 0) := by
      simpa only [sub_self,abs_zero,Real.zero_rpow hpow.ne',mul_zero] using hcont.tendsto t
    exact squeeze_zero (fun _ => norm_nonneg _) (fun s => ht s t) hl
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup w hw H hb,?_,hb⟩
  intro t hti x
  change g (x,c t)=g (x,t)
  congr 2
  exact congrArg Subtype.val (projIcc_of_mem hab hti)
end ParabolicLocalization

end

end OAI
