import OAI.MathematicalPhysics.Transonic.Profile.ExteriorBranchBounds

namespace OAI

section
noncomputable section
namespace SepticProfile.ODEGlue
open Set Filter
open scoped Topology

lemma join_eventually_left {c t : ℝ} {u v : ℝ → ℝ} (ht : t<c) :
    join c u v =ᶠ[𝓝 t] u := by
  filter_upwards [Iio_mem_nhds ht] with x hx
  exact ite_eq_left hx.le

lemma join_eventually_right {c t : ℝ} {u v : ℝ → ℝ} (ht : c<t) :
    join c u v =ᶠ[𝓝 t] v := by
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact ite_eq_right (not_le.mpr hx)

lemma join_eq_right {c t : ℝ} {u v : ℝ → ℝ} (ht : c≤t) (h : u c=v c) :
    join c u v t=v t := by
  exact join_right (b:=t) h ⟨ht,le_rfl⟩

lemma hasDerivWithinAt_join_Ici {a c : ℝ} (hac : a≤c)
    {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ}
    (hu : ∀ t∈Icc a c, HasDerivWithinAt u (f t (u t)) (Icc a c) t)
    (hv : ∀ t∈Ici c, HasDerivWithinAt v (f t (v t)) (Ici c) t)
    (h : u c=v c) (t : ℝ) (ht : t∈Ici a) :
    HasDerivWithinAt (join c u v) (f t (join c u v t)) (Ici a) t := by
  let b := max c t+1
  have hcb : c≤b := by dsimp [b];linarith only [le_max_left c t]
  have htb : t<b := by dsimp [b];linarith only [le_max_right c t]
  have hd := hasDerivWithinAt_join hac hcb hu
    (fun x hx => (hv x hx.1).mono (fun _ hy => hy.1)) h t ⟨ht,htb.le⟩
  apply hd.mono_of_mem_nhdsWithin
  apply Filter.mem_of_superset (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htb)))
  exact fun _ hx => ⟨hx.1,hx.2.le⟩

end SepticProfile.ODEGlue

end
end

end OAI
