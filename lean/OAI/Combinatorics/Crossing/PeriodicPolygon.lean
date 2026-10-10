import OAI.Combinatorics.Crossing.PolygonalWalks

namespace OAI

noncomputable section
namespace Zarankiewicz

def cyclicIndex (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i%n,Nat.mod_lt i hn⟩

def periodicPolygon (n : ℕ) (hn : 0 < n) (p : Fin n → Plane) (i : ℕ) : Plane := p (cyclicIndex n hn i)

theorem cyclicIndex_of_lt (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i<n) :
    cyclicIndex n hn i = ⟨i,hi⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hi

theorem cyclicIndex_period (n : ℕ) (hn : 0 < n) : cyclicIndex n hn n = cyclicIndex n hn 0 := by
  apply Fin.ext
  simp [cyclicIndex]

theorem periodicPolygon_closed (n : ℕ) (hn : 0 < n) (p : Fin n → Plane) :
    periodicPolygon n hn p n = periodicPolygon n hn p 0 := by
  exact congrArg p (cyclicIndex_period n hn)

theorem cyclicIndex_succ_ne (n : ℕ) (hn : 1 < n) (i : Fin n) :
    cyclicIndex n (by omega) (i.val+1) ≠ cyclicIndex n (by omega) i.val := by
  intro h
  have he := congrArg Fin.val h
  change (i.val+1)%n = i.val%n at he
  rw [Nat.mod_eq_of_lt i.isLt] at he
  by_cases hh : i.val+1=n
  · rw [hh,Nat.mod_self] at he
    omega
  · have hlt : i.val+1<n := by omega
    rw [Nat.mod_eq_of_lt hlt] at he
    omega

theorem periodicPolygon_near (n : ℕ) (hn : 0 < n) (v : ℕ → Plane) (hv : v n=v 0)
    (p : Fin n → Plane) (ε : ℝ) (hp : ∀ i, dist (p i) (v i.val) < ε) :
    ∀ i : Fin (n+1), dist (periodicPolygon n hn p i.val) (v i.val) < ε := by
  intro i
  by_cases hi : i.val<n
  · simpa only [periodicPolygon,cyclicIndex_of_lt n hn i.val hi] using hp ⟨i.val,hi⟩
  · have hin : i.val=n := by omega
    rw [hin,periodicPolygon_closed,hv]
    simpa only [periodicPolygon,cyclicIndex_of_lt n hn 0 hn] using hp ⟨0,hn⟩

end Zarankiewicz

end

end OAI
