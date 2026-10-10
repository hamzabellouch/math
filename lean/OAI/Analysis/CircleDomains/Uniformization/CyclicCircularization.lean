import OAI.Analysis.CircleDomains.Uniformization.CircularizationSelectedDisks

namespace OAI

/-! A fair finite schedule and simultaneous compactness of the actual
round disks selected during its cycles. No assertion of limiting
roundness for the later, deformed configurations is assumed here. -/
open Set Function Metric Filter
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity.FiniteJordanConfiguration

def cyclicSchedule (m : ℕ) (n : ℕ) : Fin (m+1) := ⟨n%(m+1),Nat.mod_lt _ (by omega)⟩

def visitTime {m : ℕ} (n : ℕ) (i : Fin (m+1)) : ℕ := n*(m+1)+i.val

lemma cyclicSchedule_visit {m : ℕ} (n : ℕ) (i : Fin (m+1)) :
    cyclicSchedule m (visitTime n i)=i := by
  apply Fin.ext
  simp [cyclicSchedule,visitTime,Nat.add_mod,Nat.mod_eq_of_lt i.isLt]

lemma visitTime_strictMono {m : ℕ} (i : Fin (m+1)) : StrictMono (fun n => visitTime n i) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [visitTime,Nat.succ_mul]
  omega

lemma exists_cyclic_selected_disk_limits {m : ℕ} (C : FiniteJordanConfiguration (Fin (m+1))) :
    ∃ (s : ℕ → ℕ) (c : Fin (m+1) → ℂ) (r : Fin (m+1) → ℝ),
      StrictMono s ∧ (∀ i, 0≤r i) ∧
      (∀ i, Tendsto (fun n => selectedCenter C (cyclicSchedule m) (visitTime (s n) i))
        atTop (𝓝 (c i))) ∧
      (∀ i, Tendsto (fun n => selectedRadius C (cyclicSchedule m) (visitTime (s n) i))
        atTop (𝓝 (r i))) ∧
      (∀ i, Tendsto (fun n => hausdorffDist
        (closedBall (selectedCenter C (cyclicSchedule m) (visitTime (s n) i))
          (selectedRadius C (cyclicSchedule m) (visitTime (s n) i)))
        (closedBall (c i) (r i))) atTop (𝓝 0)) := by
  obtain ⟨R,hR,hsource⟩ := C.exists_exterior_radius
  obtain ⟨s,c,r,hs,hb,hc,hr⟩ := exists_marked_disk_parameter_limits
    (fun n i => selectedCenter C (cyclicSchedule m) (visitTime n i))
    (fun n i => selectedRadius C (cyclicSchedule m) (visitTime n i))
    (fun n i => (selected_disk_bounded C (cyclicSchedule m) hR hsource (visitTime n i)).1)
    (fun n i => (selected_disk_bounded C (cyclicSchedule m) hR hsource (visitTime n i)).2)
  exact ⟨s,c,r,hs,fun i => (hb i).2.1,hc,hr,fun i => tendsto_hausdorffDist_closedBall
    (fun n => (selectedRadius_pos C (cyclicSchedule m) (visitTime (s n) i)).le)
    (hb i).2.1 (hc i) (hr i)⟩

end CircleDomainRigidity.FiniteJordanConfiguration

end

end OAI
