import Mathlib.Algebra.Order.Floor.Ring
import OAI.Geometry.NodalSets.Elliptic.CorrugationAssembly

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

def corrugationCubeCenter (o : Coord) (L : ℝ) (n : ℕ) (k : Fin 4 → Fin n) : Coord :=
  fun i ↦ o i + (L/(n:ℝ))*((k i:ℝ)+1/2)

lemma corrugationCubeCenter_mem (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    corrugationCubeCenter o L n k ∈ Set.Icc o (fun i ↦ o i+L) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  constructor <;> intro i
  · dsimp [corrugationCubeCenter]
    have hk : (0:ℝ) ≤ (k i:ℝ) := by positivity
    nlinarith
  · dsimp [corrugationCubeCenter]
    have hk : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

lemma corrugationCube_ball_inside (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) ⊆
      interior (Set.Icc o (fun i ↦ o i+L)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  intro x hx
  rw [← pi_univ_Icc,interior_pi_set Set.finite_univ]
  intro i _
  change x i ∈ interior (Icc (o i) (o i+L))
  rw [interior_Icc]
  constructor
  all_goals
    have hxi : |x i-corrugationCubeCenter o L n k i| < (L/(n:ℝ))/2 := by
      have hnorm := norm_le_pi_norm (x-corrugationCubeCenter o L n k) i
      exact lt_of_le_of_lt hnorm (by simpa [dist_eq_norm] using hx)
    have ha := abs_lt.mp hxi
    dsimp [corrugationCubeCenter] at ha
    have hk0 : (0:ℝ) ≤ (k i:ℝ) := by positivity
    have hk1 : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

lemma corrugationCube_balls_disjoint (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k j : Fin 4 → Fin n) (hkj : k ≠ j) :
    Disjoint (ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2))
      (ball (corrugationCubeCenter o L n j) ((L/(n:ℝ))/2)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ j i := Function.ne_iff.mp hkj
  have hi' : (k i).val ≠ (j i).val := fun h ↦ hi (Fin.ext h)
  have hd : (1:ℝ) ≤ |(k i:ℝ)-(j i:ℝ)| := by
    rcases lt_or_gt_of_ne hi' with h | h
    · have hh : (k i:ℝ)+1 ≤ (j i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j i:ℝ)+1 ≤ (k i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  apply ball_disjoint_ball
  have hcoord := norm_le_pi_norm (corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i
  have he : ‖(corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i‖ =
      (L/(n:ℝ))*|(k i:ℝ)-(j i:ℝ)| := by
    change |(o i+_)-(o i+_)| = _
    rw [add_sub_add_left_eq_sub,← mul_sub,abs_mul,abs_of_pos hR]
    congr 2
    ring
  rw [he] at hcoord
  rw [dist_eq_norm]
  nlinarith

lemma unit_interval_subdivision {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∃ k : Fin n, (k:ℝ) ≤ t ∧ t ≤ (k:ℝ)+1 := by
  by_cases he : t = n
  · refine ⟨⟨n-1,by omega⟩,?_,?_⟩
    all_goals
      have hn1 : ((n-1:ℕ):ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
      change _ ≤ _
      rw [he]
      linarith
  · have ht : t < n := lt_of_le_of_ne htn he
    let k : ℕ := ⌊t⌋₊
    have hk0 : (k:ℝ) ≤ t := Nat.floor_le ht0
    have hk1 : t < (k:ℝ)+1 := Nat.lt_floor_add_one t
    have hkn : k < n := by exact_mod_cast (hk0.trans_lt ht)
    exact ⟨⟨k,hkn⟩,hk0,hk1.le⟩

lemma corrugationCube_closed_cover (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (x : Coord) (hx : x ∈ Set.Icc o (fun i ↦ o i+L)) :
    ∃ k : Fin 4 → Fin n,
      x ∈ closedBall (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  have hk : ∀ i : Fin 4, ∃ k : Fin n,
      (k:ℝ) ≤ (x i-o i)/(L/(n:ℝ)) ∧ (x i-o i)/(L/(n:ℝ)) ≤ (k:ℝ)+1 := by
    intro i
    apply unit_interval_subdivision hn
    · exact div_nonneg (sub_nonneg.mpr (hx.1 i)) hR.le
    · apply (div_le_iff₀ hR).mpr
      have hi := hx.2 i
      nlinarith
  choose k hk using hk
  refine ⟨k,?_⟩
  rw [mem_closedBall,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (L/(n:ℝ))/2)).mpr
  intro i
  have hlo := (le_div_iff₀ hR).mp (hk i).1
  have hhi := (div_le_iff₀ hR).mp (hk i).2
  change |x i-(o i+(L/(n:ℝ))*((k i:ℝ)+1/2))| ≤ _
  rw [abs_le]
  constructor <;> nlinarith

end
end Yau.Geometry

end OAI
