import OAI.Probability.FreeIsing.Conditioning.BroadcastFamilyConditional
import OAI.Probability.FreeIsing.Estimates.FreeIsingMeasure
import OAI.Probability.FreeIsing.Estimates.FreeLawStationarity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

local instance (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

theorem freeIsingMeasure_iCondIndepFun_branches (d : ℕ) (theta : ℝ) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun x : TreeVertex d → IsingSpin => x (RootedBroadcast.root d)))
      (measurable_pi_apply (RootedBroadcast.root d)).comap_le
      (fun c x => fun v : RootedBroadcast.BranchVertex c => x v.val)
      (freeIsingMeasure d theta) := by
  have he : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  apply iCondIndepFun_of_comp_measurePreserving (labelMeasure d) (freeIsingMeasure d theta)
    (RootedBroadcast.factor theta) he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun x : TreeVertex d → IsingSpin => x (RootedBroadcast.root d)))
    (measurable_pi_apply (RootedBroadcast.root d)).comap_le
    (fun c => show Measurable (fun x : TreeVertex d → IsingSpin =>
      fun v : RootedBroadcast.BranchVertex c => x v.val) from by fun_prop)
  have hroot : (fun U : TreeVertex d → ℝ =>
      RootedBroadcast.factor theta U (RootedBroadcast.root d)) =
      (fun U => fairSpin (U (RootedBroadcast.root d))) := by
    funext U
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, hroot] using
    RootedBroadcast.iCondIndepFun_factor_branches d theta

theorem HasFreeIsingLaw.iCondIndepFun_branches {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun x : TreeVertex d → IsingSpin => x (RootedBroadcast.root d)))
      (measurable_pi_apply (RootedBroadcast.root d)).comap_le
      (fun c x => fun v : RootedBroadcast.BranchVertex c => x v.val) μ := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_branches d theta

theorem HasFreeIsingLaw.iCondIndepFun_relabel_branches {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (g : TreeAut d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun x : TreeVertex d → IsingSpin => x (g.toEquiv.symm (RootedBroadcast.root d))))
      (measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comap_le
      (fun c x => fun v : RootedBroadcast.BranchVertex c => x (g.toEquiv.symm v.val)) μ := by
  have hpull := iCondIndepFun_comp_measurePreserving μ μ (relabel g)
    (hμ.measurePreserving_relabel g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun x : TreeVertex d → IsingSpin => x (RootedBroadcast.root d)))
    (measurable_pi_apply (RootedBroadcast.root d)).comap_le
    (fun c => show Measurable (fun x : TreeVertex d → IsingSpin =>
      fun v : RootedBroadcast.BranchVertex c => x v.val) from by fun_prop)
    (hμ.iCondIndepFun_branches h0 h1)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, relabel] using hpull

end Problem367

end

end OAI
