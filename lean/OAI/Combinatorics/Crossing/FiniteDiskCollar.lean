import OAI.Combinatorics.Crossing.BoundaryCollar
import OAI.Combinatorics.Crossing.RoundDiskVisits

namespace OAI

noncomputable section
namespace Zarankiewicz

def outsideDisks {ι : Type*} (z : ι → Plane) (r : ℝ) : Set Plane :=
  {x | ∀ i, r^2 < squaredLength (x-z i)}

theorem isOpen_disk_exterior (z : Plane) (r : ℝ) :
    IsOpen {x | r^2 < squaredLength (x-z)} := by
  apply isOpen_lt continuous_const
  unfold squaredLength
  fun_prop

theorem isOpen_outsideDisks {ι : Type*} [Finite ι] (z : ι → Plane) (r : ℝ) :
    IsOpen (outsideDisks z r) := by
  have he : outsideDisks z r=⋂ i, {x | r^2 < squaredLength (x-z i)} := by
    ext x
    simp [outsideDisks]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_disk_exterior (z i) r)

theorem exists_finite_disk_collar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k : ι) (x : Plane) (hx : squaredLength (x-z k)=r^2)
    (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z k)) ⊆ U ∩ insert x (outsideDisks z r) ∧
      (∀ y, dist y x < ρ → y ∈ outsideDisks z r →
        segment ℝ (x+α • (x-z k)) y ⊆ U ∩ outsideDisks z r) := by
  let V : Set Plane := U ∩ ⋂ j : {j : ι // j ≠ k}, {y | r^2 < squaredLength (y-z j.val)}
  have hV : IsOpen V := hU.inter (isOpen_iInter_of_finite (fun j => isOpen_disk_exterior (z j.val) r))
  have hxV : x ∈ V := by
    refine ⟨hxu,Set.mem_iInter.mpr (fun j => ?_)⟩
    change r^2 < squaredLength (x-z j.val)
    apply lt_of_not_ge
    intro hh
    exact Set.disjoint_left.mp (hd k j.val (Ne.symm j.property)) (show x ∈ closedRoundDisk (z k) r from hx.le) hh
  obtain ⟨α,ρ,hα,hρ,hspur,hnear⟩ := exists_radial_tip_collar (z k) x r hr hx V hV hxV
  have hout : V ∩ {p | r^2 < squaredLength (p-z k)} ⊆ U ∩ outsideDisks z r := by
    intro p hp
    refine ⟨hp.1.1,fun j => ?_⟩
    by_cases he : j=k
    · simpa [he] using hp.2
    · exact Set.mem_iInter.mp hp.1.2 ⟨j,he⟩
  refine ⟨α,ρ,hα,hρ,?_,?_⟩
  · intro p hp
    obtain ⟨hpV,hpx | hpout⟩ := hspur hp
    · exact ⟨hpV.1,Or.inl hpx⟩
    · exact ⟨hpV.1,Or.inr (hout ⟨hpV,hpout⟩).2⟩
  · intro y hy hyout
    exact (hnear y hy (hyout k)).trans hout

end Zarankiewicz

end

end OAI
