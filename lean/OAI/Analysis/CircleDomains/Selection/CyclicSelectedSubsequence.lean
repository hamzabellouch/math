import OAI.Analysis.CircleDomains.Uniformization.CyclicCircularization

namespace OAI

/-! Simultaneous selected-disk compactness along any sequence of cycles. -/
open Set Function Metric Filter
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity.FiniteJordanConfiguration

lemma exists_cyclic_selected_disk_limits_along {m:ℕ}
    (C:FiniteJordanConfiguration (Fin (m+1))) (t:ℕ→ℕ) :
    ∃ (s:ℕ→ℕ) (c:Fin (m+1)→ℂ) (r:Fin (m+1)→ℝ),
      StrictMono s ∧ (∀i,0≤r i) ∧
      (∀i,Tendsto (fun n => selectedCenter C (cyclicSchedule m) (visitTime (t (s n)) i))
        atTop (𝓝 (c i))) ∧
      (∀i,Tendsto (fun n => selectedRadius C (cyclicSchedule m) (visitTime (t (s n)) i))
        atTop (𝓝 (r i))) := by
  obtain ⟨R,hR,hsource⟩ := C.exists_exterior_radius
  obtain ⟨s,c,r,hs,hb,hc,hr⟩ := exists_marked_disk_parameter_limits
    (fun n i => selectedCenter C (cyclicSchedule m) (visitTime (t n) i))
    (fun n i => selectedRadius C (cyclicSchedule m) (visitTime (t n) i))
    (fun n i => (selected_disk_bounded C (cyclicSchedule m) hR hsource (visitTime (t n) i)).1)
    (fun n i => (selected_disk_bounded C (cyclicSchedule m) hR hsource (visitTime (t n) i)).2)
  exact ⟨s,c,r,hs,fun i => (hb i).2.1,hc,hr⟩

end CircleDomainRigidity.FiniteJordanConfiguration

end

end OAI
