import OAI.Analysis.CircleDomains.Topology.RegularLevelCompactOrbit

namespace OAI

/-! Compactness forces a positive return time for each nonstationary
regular-level orbit. Uniqueness turns every return into a true period. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularLevelFlow.return_of_collision {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) {s t : ℝ}
    (hst : F.trajectory x s = F.trajectory x t) :
    F.trajectory x (t-s) = x.val := by
  have h := ODE_solution_unique_univ (v := fun _ : ℝ => F.field)
    (s := fun _ : ℝ => (univ : Set ℂ)) (t₀ := 0)
    (fun _ => F.lipschitz.lipschitzOnWith)
    (fun u => ⟨(F.equation x (u+s)).comp_add_const u s,mem_univ _⟩)
    (fun u => ⟨(F.equation x (u+t)).comp_add_const u t,mem_univ _⟩)
    (by simpa only [zero_add] using hst)
  have he := congrFun h (-s)
  simpa only [neg_add_cancel,neg_add_eq_sub,F.initial] using he.symm

lemma CompactRegularLevelFlow.exists_positive_period {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ∃ p > 0, Periodic (F.trajectory x) p := by
  obtain ⟨s,t,hst,hne⟩ := not_injective_iff.mp (F.not_injective_trajectory hf ha hc x)
  have hp := F.periodic_of_return x (F.return_of_collision x hst)
  have hne' : t-s ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases lt_or_gt_of_ne hne' with hneg | hpos
  · exact ⟨-(t-s),neg_pos.mpr hneg,hp.neg⟩
  · exact ⟨t-s,hpos,hp⟩

end CircleDomainRigidity

end

end OAI
