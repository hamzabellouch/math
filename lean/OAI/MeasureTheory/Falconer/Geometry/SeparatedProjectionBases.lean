import OAI.MeasureTheory.Falconer.Slicing.CommonSliceSelection

namespace OAI

/-! Two separated projection bases with many common large slices. The
separation comes from the original direction-set ball count. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem separated_projection_bases {β : Type*} [DecidableEq β]
    (I : Finset ℝ) (U : Finset β) (A : ℝ → Finset β)
    (hI : I.Nonempty) (hU : U.Nonempty) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 < r)
    (hsub : ∀ i ∈ I, A i ⊆ U)
    (hsize : ∀ i ∈ I, ρ*(U.card:ℝ) ≤ ((A i).card:ℝ))
    (hball : ∀ z : ℝ, scalarBallMass I z r ≤ (ρ^6/128)*(I.card:ℝ)) :
    ∃ a ∈ I, ∃ b ∈ I, r < |b-a| ∧ b ≠ a ∧ ∃ J ⊆ I,
      (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ) ∧
      ∀ j ∈ J, r < |j-a| ∧ r < |j-b| ∧
        (ρ^4/8)*(U.card:ℝ) ≤ (((A a ∩ A b) ∩ A j).card:ℝ) := by
  classical
  obtain ⟨a,ha,J1,hJ1I,hJ1,hpair1⟩ := finite_relative_common_row I U A hI hU hρ hsub hsize
  let F1 := J1.filter fun y => r < |y-a|
  have hF1I : F1 ⊆ I := (Finset.filter_subset _ _).trans hJ1I
  have hpow : ρ^6 ≤ ρ^2 := pow_le_pow_of_le_one hρ.le hρ1 (by omega)
  have hnear : scalarBallMass I a r ≤ (ρ^2/4)*(I.card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show ρ^6/128 ≤ ρ^2/4 by nlinarith [sq_nonneg ρ])
      (Nat.cast_nonneg (α := ℝ) I.card)
    exact (hball a).trans hh
  have hF1count : (ρ^2/4)*(I.card:ℝ) ≤ (F1.card:ℝ) := by
    have hh := finite_delete_interval hJ1I a r
    change (J1.card:ℝ)-scalarBallMass I a r ≤ (F1.card:ℝ) at hh
    nlinarith
  have hF1 : F1.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (ρ^2/4)*(I.card:ℝ) := mul_pos (by positivity)
      (Nat.cast_pos.mpr (Finset.card_pos.mpr hI))
    exact_mod_cast hp.trans_le hF1count
  let B := fun j => A a ∩ A j
  have hBsub : ∀ j ∈ F1, B j ⊆ U := fun _ _ =>
    Finset.inter_subset_left.trans (hsub a ha)
  have hBsize : ∀ j ∈ F1, (ρ^2/2)*(U.card:ℝ) ≤ ((B j).card:ℝ) :=
    fun j hj => hpair1 j (Finset.mem_filter.mp hj).1
  obtain ⟨b,hb,J2,hJ2F,hJ2,hpair2⟩ := finite_relative_common_row F1 U B hF1 hU
    (by positivity : 0 < ρ^2/2) hBsub hBsize
  have hbI : b ∈ I := hF1I hb
  have hba : r < |b-a| := (Finset.mem_filter.mp hb).2
  have hJ2I : J2 ⊆ I := hJ2F.trans hF1I
  have hJ2count : (ρ^6/32)*(I.card:ℝ) ≤ (J2.card:ℝ) := by
    calc
      _ = ((ρ^2/2)^2/2)*((ρ^2/4)*(I.card:ℝ)) := by ring
      _ ≤ ((ρ^2/2)^2/2)*(F1.card:ℝ) := mul_le_mul_of_nonneg_left hF1count (by positivity)
      _ ≤ _ := hJ2
  let J3 := J2.filter fun y => r < |y-a|
  let J := J3.filter fun y => r < |y-b|
  have hJ3I : J3 ⊆ I := (Finset.filter_subset _ _).trans hJ2I
  have hJI : J ⊆ I := (Finset.filter_subset _ _).trans hJ3I
  have hJcount : (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ) := by
    have h0 := finite_delete_interval hJ2I a r
    have h1 := finite_delete_interval hJ3I b r
    change (J2.card:ℝ)-scalarBallMass I a r ≤ (J3.card:ℝ) at h0
    change (J3.card:ℝ)-scalarBallMass I b r ≤ (J.card:ℝ) at h1
    nlinarith [hball a,hball b]
  have hbaNe : b ≠ a := sub_ne_zero.mp (abs_pos.mp (hr.trans hba))
  refine ⟨a,ha,b,hbI,hba,hbaNe,J,hJI,hJcount,?_⟩
  intro j hj
  obtain ⟨hj3,hjb⟩ := Finset.mem_filter.mp hj
  obtain ⟨hj2,hja⟩ := Finset.mem_filter.mp hj3
  refine ⟨hja,hjb,?_⟩
  have hh := hpair2 j hj2
  have he : B b ∩ B j = (A a ∩ A b) ∩ A j := by
    ext x
    simp only [B,Finset.mem_inter]
    tauto
  rw [he] at hh
  convert hh using 1; ring

end Falconer

end OAI
