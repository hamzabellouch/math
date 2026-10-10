import OAI.Analysis.CircleDomains.Selection.FiniteLineGaps
import Mathlib.Data.Finset.Card

namespace OAI

/-! An interval meeting at most one deleted hole can meet at most two
retained gaps. This is the exact multiplicity in the tail-disk estimate. -/
open Set Function
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem interval_meets_hole_between_gaps {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {J : Set ℝ} (hJ : OrdConnected J) (i : Fin n) (v : Fin (n+1)) (hiv : i.castSucc < v)
    (hi : (J ∩ Icc (gapsAfterHoles a b H i.castSucc).1
      (gapsAfterHoles a b H i.castSucc).2).Nonempty)
    (hv : (J ∩ Icc (gapsAfterHoles a b H v).1 (gapsAfterHoles a b H v).2).Nonempty) :
    (J ∩ Icc (H i).1 (H i).2).Nonempty := by
  obtain ⟨x,hx,hxi⟩ := hi
  obtain ⟨z,hz,hzv⟩ := hv
  obtain ⟨v',rfl⟩ := Fin.eq_succ_of_ne_zero (show v ≠ 0 by
    intro he; subst v; exact (not_lt_of_ge (Fin.zero_le _)) hiv)
  have hiv' : i ≤ v' := by
    simp only [Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at hiv
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hiv)
  have hxl : x ≤ (H i).1 := by simpa only [gapsAfterHoles_castSucc_snd] using hxi.2
  have hlz : (H i).1 ≤ z := (hfirst hiv').trans ((hvalid v').trans (by
    simpa only [gapsAfterHoles_succ_fst] using hzv.1))
  exact ⟨(H i).1,hJ.out hx hz ⟨hxl,hlz⟩,le_rfl,hvalid i⟩

 theorem at_most_two_gaps_of_at_most_one_hole {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {J : Set ℝ} (hJ : OrdConnected J)
    (hone : ∀ i j, (J ∩ Icc (H i).1 (H i).2).Nonempty →
      (J ∩ Icc (H j).1 (H j).2).Nonempty → i = j) :
    (Finset.univ.filter (fun i => (J ∩ Icc (gapsAfterHoles a b H i).1
      (gapsAfterHoles a b H i).2).Nonempty)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun i => (J ∩ Icc (gapsAfterHoles a b H i).1
      (gapsAfterHoles a b H i).2).Nonempty)
  change S.card ≤ 2
  by_contra h
  have hcard : 2 < S.card := lt_of_not_ge h
  let e := S.orderEmbOfFin rfl
  let x : Fin S.card := ⟨0,by omega⟩
  let y : Fin S.card := ⟨1,by omega⟩
  let z : Fin S.card := ⟨2,by omega⟩
  have hxy : e x < e y := e.strictMono (by change 0 < 1; omega)
  have hyz : e y < e z := e.strictMono (by change 1 < 2; omega)
  have hmem (v : Fin S.card) : (J ∩ Icc (gapsAfterHoles a b H (e v)).1
      (gapsAfterHoles a b H (e v)).2).Nonempty :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl v)).2
  obtain ⟨i,hi⟩ := Fin.eq_castSucc_of_ne_last (show e x ≠ Fin.last n by
    intro he; rw [he] at hxy; exact (not_lt_of_ge (Fin.le_last _)) hxy)
  obtain ⟨j,hj⟩ := Fin.eq_castSucc_of_ne_last (show e y ≠ Fin.last n by
    intro he; rw [he] at hyz; exact (not_lt_of_ge (Fin.le_last _)) hyz)
  have hholei := interval_meets_hole_between_gaps a b H hvalid hfirst hJ i (e z)
    (by rw [hi]; exact hxy.trans hyz) (by rw [hi]; exact hmem x) (hmem z)
  have hholej := interval_meets_hole_between_gaps a b H hvalid hfirst hJ j (e z)
    (by rw [hj]; exact hyz) (by rw [hj]; exact hmem y) (hmem z)
  have heij := hone i j hholei hholej
  have he : e x = e y := by rw [← hi,← hj,heij]
  exact (ne_of_lt hxy) he

end CircleDomainRigidity

end

end OAI
