import OAI.Analysis.Triangular.Signs.SineGridAnalytic
import OAI.Analysis.Triangular.Signs.SineGridChecks
import OAI.Analysis.Triangular.Signs.SineGridCover

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma realP_local_strict (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1)
    (hy : (localHalf u:ℝ)*x≠0) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2<realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  obtain ⟨k,hk⟩ := unit_grid_cover hx
  exact realP_cell_lower u k (cell_geometry u k) (cell_factors u k).1 (cell_factors u k).2
    (cell_displacement u k hk) hy
lemma realP_local_lower (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2 ≤ realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  by_cases hy : (localHalf u:ℝ)*x=0
  · simpa only [hy,zero_pow (by norm_num : 2≠0),mul_zero,add_zero] using realP_nonneg (localCenter u)
  · exact (realP_local_strict u hx hy).le
lemma cellBarrier_lower (u : Fin 30) : (27/500:ℝ) ≤ cellBarrier u := by
  unfold cellBarrier
  split_ifs <;> norm_num
lemma realP_far_lower {s : ℝ} (hs : (23:ℝ)  ≤  s) :
    ∃ m : Node, 25 ≤ m.val ∧ (27/500:ℝ)*(s-m.val)^2 ≤ realP s := by
  let q : ℕ := ⌊(s+5/2)/36⌋₊
  let t : ℝ := s-36*q
  have hq0 : (q:ℝ) ≤ (s+5/2)/36 := Nat.floor_le (by linarith)
  have hq1 : (s+5/2)/36<(q:ℝ)+1 := Nat.lt_floor_add_one _
  have ht : t∈Ico (-(5/2)) (67/2) := by dsimp [t]; constructor <;> linarith
  obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover ht
  let m : ℤ := 36*(q:ℤ)+localCenter u
  have hm : 25 ≤ m := by
    by_cases hq : q=0
    · have ht0 : t=s := by simp [t,hq]
      have hg := (local_boundary_geometry u).2.2.2.2.2.1
      by_contra! hh
      have hu : localCenter u<25 := by simpa [m,hq] using hh
      have hhB : (localBoundary (u.val+1):ℝ) ≤ 23 := by exact_mod_cast hg hu
      linarith [hcell.2]
    · have hqc : (1:ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      have huc := (local_boundary_geometry u).2.2.2.1
      dsimp [m]
      omega
  have hmres : m%36∈residues := by
    simpa only [m,Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_emod] using
      (local_boundary_geometry u).2.2.2.2.1
  refine ⟨⟨m,by omega,hmres⟩,hm,?_⟩
  have hp := realP_local_lower u hx
  have hp' := mul_le_mul_of_nonneg_right (cellBarrier_lower u) (sq_nonneg ((localHalf u:ℝ)*x))
  have hP : realP t=realP s := by
    convert realP_periodic.sub_nat_mul_eq q using 1
    dsimp [t]
    ring_nf
  have hsm : s-(m:ℝ)=(localHalf u:ℝ)*x := by
    dsimp [m,t] at *
    push_cast
    linarith
  change (27/500:ℝ)*(s-(m:ℝ))^2 ≤ realP s
  rw [hsm,←hP,htu]
  exact hp'.trans hp
lemma strong_local_geometry (u : Fin 30) (hu : 16 ≤ u.val ∧ u.val ≤ 21) :
    localCenter u∈({16,19,21}:Finset ℤ) ∧ cellBarrier u=3 := by
  have hh : ∀ u : Fin 30,16 ≤ u.val ∧ u.val ≤ 21 → localCenter u∈({16,19,21}:Finset ℤ) := by decide +kernel
  exact ⟨hh u hu,by simp [cellBarrier,hu]⟩
lemma realP_middle_lower {s : ℝ} (hs : s∈Icc (29/2) 23) :
    ∃ m : ℤ,m∈({16,19,21}:Finset ℤ) ∧ (3:ℝ)*(s-m)^2 ≤ realP s := by
  by_cases he : s=23
  · subst s
    refine ⟨21,by simp,?_⟩
    have hh := realP_local_lower (21:Fin 30) (x:=1) (by simp)
    have hc : localCenter (21:Fin 30)=21 ∧ localHalf (21:Fin 30)=2 ∧ cellBarrier (21:Fin 30)=3 := by decide +kernel
    rw [hc.1,hc.2.1,hc.2.2] at hh
    norm_num at hh ⊢
    exact hh
  · obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover (t:=s) (by constructor <;> linarith [hs.1,hs.2])
    have hu : 16 ≤ u.val ∧ u.val ≤ 21 := by
      have hg := local_boundary_geometry u
      constructor
      · by_contra! h
        have hh : (localBoundary (u.val+1):ℝ) ≤ 29/2 := by
          have ht := Rat.cast_le (K:=ℝ) |>.mpr (hg.2.2.2.2.2.2.1 h)
          norm_num at ht ⊢
          exact ht
        linarith [hcell.2,hs.1,hs.2]
      · by_contra! h
        have hh : (23:ℝ) ≤ localBoundary u.val := by exact_mod_cast hg.2.2.2.2.2.2.2 h
        have hss : s<23 := lt_of_le_of_ne hs.2 he
        linarith [hcell.1,hss]
    refine ⟨localCenter u,(strong_local_geometry u hu).1,?_⟩
    have hh := realP_local_lower u hx
    rw [(strong_local_geometry u hu).2] at hh
    norm_num only [Rat.cast_ofNat] at hh
    rw [htu]
    simpa only [add_sub_cancel_left] using hh
end AtomicTriangular.Construction
end

end OAI
