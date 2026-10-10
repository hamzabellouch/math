import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoordinateJointLaw

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RectangularBound
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem coordinate_all_eventually (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hSlope : 8000 < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ n, B.CoordinateWindowLaw n := by
  obtain ⟨s,w,z,hs,hsr,hwz,hshort⟩ := exists_symmetric_short_chart a r hr.1
  obtain ⟨N,hN,hstep⟩ := InitialCoverSystem.coordinate_growth (hm := hm) hlarge hr
    s w z hs hsr hwz hshort (show (1000:ℝ) ≤ 1000 from le_rfl)
    (by convert hSlope using 1; norm_num) hconj
  obtain ⟨L₁,hL₁⟩ := coordinateWindowLaw_eventually (a := a) (hm := hm) hr (by omega) N
  obtain ⟨L₂,hL₂⟩ := tangentChartTables_eventually (a := a) (hm := hm) hr (by omega)
    (symmetricWindowLength s) (symmetricWindowStart s) w
  refine ⟨L₁+L₂,?_⟩
  intro M hM B
  apply B.coordinate_iteration N (by omega) (hL₁ M (by omega) B)
  intro n hn g
  exact hstep M B (fun d e z I _ b hb => hL₂ M (by omega) B d e z I b hb) n hn g

theorem exists_coordinate_cover (m : ℕ) (hm : 2 ≤ m) (hlarge : 20 ≤ m+1)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (r : CutRing) (hr : 0 < ordinary r ∧ ordinary r < 1/2) :
    ∃ a : ℕ, 0 < a ∧ ordinary (cutTau^a)*(1/4) > 1000*(1000+1) ∧
      |conjugate (cutTau^a)| < 1/1000 ∧
      ∃ M : ℕ, ∃ B : InitialCoverSystem a r m hm M, ∀ n, B.CoordinateWindowLaw n := by
  obtain ⟨a,ha,hslope,hconj⟩ := exists_source_slope (1/4) 1000 (by norm_num)
  obtain ⟨L₁,hL₁⟩ := coordinate_all_eventually (a := a) (hm := hm) hlarge hr (by linarith) hconj
  obtain ⟨L₂,hL₂⟩ := initialCoverSystem_eventually a r m hm hr (by omega)
  obtain ⟨B⟩ := hL₂ (L₁+L₂) (by omega)
  exact ⟨a,ha,hslope,hconj,L₁+L₂,B,hL₁ (L₁+L₂) (by omega) B⟩

end RectangularBound

section GlobalWindowCoherence

theorem finite_coordinate_windows_container {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (p : ι → Fin 2 → ℤ) :
    ∃ n : ℕ, ∃ q : Fin 2 → ℤ, ∀ i j, q j ≤ p i j ∧ p i j+(k i:ℤ) ≤ q j+n := by
  let N := Finset.univ.sup (fun i => k i+(p i 0).natAbs+(p i 1).natAbs)
  have hb i : k i+(p i 0).natAbs+(p i 1).natAbs ≤ N := Finset.le_sup (f := fun i => k i+(p i 0).natAbs+(p i 1).natAbs) (Finset.mem_univ i)
  refine ⟨3*N+1,fun _ => -(N:ℤ),?_⟩
  intro i j
  have hk : k i ≤ N := by have := hb i; omega
  have hp : (p i j).natAbs ≤ N := by fin_cases j <;> dsimp <;> have := hb i <;> omega
  have hp₀ := (Int.le_natAbs : -p i j ≤ ((-p i j).natAbs : ℤ))
  simp only [Int.natAbs_neg] at hp₀
  have hp₁ := (Int.le_natAbs : p i j ≤ ((p i j).natAbs : ℤ))
  dsimp only
  constructor <;> omega

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem all_windowSector_eq (hlarge : 15 < m+1)
    (h : ∀ n, B.CoordinateWindowLaw n) (k l : ℕ) (p q : Fin 2 → ℤ)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k p) i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives l q) i).val) V.val) :
    B.windowSector hlarge k (h k) p V = B.windowSector hlarge l (h l) q V := by
  obtain ⟨n,z,hz⟩ := finite_coordinate_windows_container (fun b : Bool => if b then l else k)
    (fun b : Bool => if b then q else p)
  have hp j := hz false j
  have hq j := hz true j
  simp only [Bool.false_eq_true,ite_false,ite_true] at hp hq
  rw [B.windowSector_inclusion hlarge n k (h n) (h k) z p (fun j => (hp j).1) (fun j => (hp j).2) V hV,
    B.windowSector_inclusion hlarge n l (h n) (h l) z q (fun j => (hq j).1) (fun j => (hq j).2) V hV']

theorem all_window_control (hlarge : 15 < m+1)
    (h : ∀ n, B.CoordinateWindowLaw n) (k l : ℕ) (p q : Fin 2 → ℤ)
    (V W : polygonAlgebra a) (hVW : V ≤ W)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k p) i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives l q) i).val) W.val) :
    SmallControlled B.c (B.windowSector hlarge k (h k) p V) (B.windowSector hlarge l (h l) q W) := by
  obtain ⟨n,z,hz⟩ := finite_coordinate_windows_container (fun b : Bool => if b then l else k)
    (fun b : Bool => if b then q else p)
  have hp j := hz false j
  have hq j := hz true j
  simp only [Bool.false_eq_true,ite_false,ite_true] at hp hq
  exact B.windowSector_overlap_control hlarge n k l (h n) (h k) (h l) z p q
    (fun j => (hp j).1) (fun j => (hp j).2) (fun j => (hq j).1) (fun j => (hq j).2) V W hVW hV hW

end InitialCoverSystem
end GlobalWindowCoherence

end SimpleAmenable
end
end

end OAI
