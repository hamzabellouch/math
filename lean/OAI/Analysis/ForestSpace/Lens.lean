import OAI.Analysis.ForestSpace.FullDual

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Lens
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem bounded_finiteDimensional_pair {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] (v : ℕ → G) (R : ℝ)
    (hv : ∀ j, ‖v j‖ ≤ R) (η : ℝ) (hη : 0 < η) :
    ∃ i j : ℕ, i ≠ j ∧ ‖v i-v j‖ < 2*η := by
  obtain ⟨s,hfin,hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : G) R).totallyBounded η hη
  have hex : ∀ n : ℕ, ∃ a : s, dist (v n) a.val < η := by
    intro n
    have hn : v n ∈ Metric.closedBall (0 : G) R := by simpa using hv n
    obtain ⟨a,ha,hna⟩ := Set.mem_iUnion₂.mp (hcover hn)
    exact ⟨⟨a,ha⟩,hna⟩
  choose a ha using hex
  let := hfin.fintype
  obtain ⟨i,j,hij,he⟩ := Finite.exists_ne_map_eq_of_infinite a
  refine ⟨i,j,hij,?_⟩
  have hj : dist (v j) (a i).val < η := by rw [he]; exact ha j
  have hh := dist_triangle (v i) (a i).val (v j)
  rw [dist_comm (a i).val (v j),dist_eq_norm (v i) (v j)] at hh
  linarith [ha i]

 theorem norm_half_sum_le (a b : E) : ‖(1/2 : ℝ) • (a+b)‖ ≤ (‖a‖+‖b‖)/2 := by
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
  nlinarith [norm_add_le a b]

 theorem norm_le_signed_average (x y : E) : ‖x‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have he : (1/2 : ℝ) • ((x+y)+(x-y)) = x := by module
  have hh := norm_half_sum_le (x+y) (x-y)
  rwa [he] at hh

 theorem norm_right_le_signed_average (x y : E) : ‖y‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have hh := norm_le_signed_average y x
  simpa only [add_comm y x,norm_sub_rev y x] using hh

 theorem main_head_pair (H : Finset Vertex) (hH : IsLowerSet (H : Set Vertex))
    (y : ℕ → FullDual Vertex) (R : ℝ) (hy : ∀ j, ‖y j‖ ≤ R)
    (η : ℝ) (hη : 0 < η) :
    ∃ i j : ℕ, i ≠ j ∧ ‖P (H : Set Vertex) hH (y i-y j)‖ < 2*η := by
  let M := Submodule.span ℝ (eStar '' (H : Set Vertex))
  let : FiniteDimensional ℝ M := FiniteDimensional.span_of_finite ℝ (H.finite_toSet.image eStar)
  let L : FullDual Vertex →L[ℝ] M := (P (H : Set Vertex) hH).codRestrict M (by
    intro z
    rw [P_finite_eq_sum]
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,hv,rfl⟩))
  obtain ⟨i,j,hij,hh⟩ := bounded_finiteDimensional_pair (fun j => L (y j)) R
    (fun j => (norm_P_le (H : Set Vertex) hH (y j)).trans (hy j)) η hη
  refine ⟨i,j,hij,?_⟩
  change ‖P (H : Set Vertex) hH (y i)-P (H : Set Vertex) hH (y j)‖ < 2*η at hh
  simpa only [map_sub] using hh

 theorem main_lens_aprox (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (x : FullDual Vertex) (y : ℕ → FullDual Vertex)
    (hp : ∀ j, ‖x+y j‖ ≤ R) (hm : ∀ j, ‖x-y j‖ ≤ R)
    (hs : ∀ i j, i ≠ j → ε ≤ ‖y i-y j‖)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ‖x‖^2+ε^2/48 ≤ R^2+8*(R+1)*η := by
  have hxn : ‖x‖ ≤ R := by linarith [norm_le_signed_average x (y 0),hp 0,hm 0]
  have hyn : ∀ j, ‖y j‖ ≤ R := by
    intro j
    linarith [norm_right_le_signed_average x (y j),hp j,hm j]
  obtain ⟨H,hH,hclose⟩ := exists_main_head_approx x η hη
  obtain ⟨i,j,hij,hijclose⟩ := main_head_pair H hH y R hyn η hη
  let z : FullDual Vertex := (1/2 : ℝ) • (y i-y j)
  have hzp : ‖x+z‖ ≤ R := by
    have he : x+z = (1/2 : ℝ) • ((x+y i)+(x-y j)) := by dsimp [z]; module
    rw [he]
    linarith [norm_half_sum_le (x+y i) (x-y j),hp i,hm j]
  have hzm : ‖x-z‖ ≤ R := by
    have he : x-z = (1/2 : ℝ) • ((x-y i)+(x+y j)) := by dsimp [z]; module
    rw [he]
    linarith [norm_half_sum_le (x-y i) (x+y j),hm i,hp j]
  have hzn : ‖z‖ ≤ R := by linarith [norm_right_le_signed_average x z]
  have hzsep : ε/2 ≤ ‖z‖ := by
    dsimp [z]
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
    linarith [hs i j hij]
  have hzP : ‖P (H : Set Vertex) hH z‖ < η := by
    dsimp [z]
    rw [map_smul,norm_smul,Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
    linarith
  let a := P (H : Set Vertex) hH x
  let b := Q (H : Set Vertex) hH z
  have haR : ‖a‖ ≤ R := (norm_P_le _ _ _).trans hxn
  have hbR : ‖b‖ ≤ R := (norm_Q_le _ _ _).trans hzn
  have hxa : ‖x‖ ≤ ‖a‖+η := by
    have hh := norm_add_le (x-a) a
    rw [sub_add_cancel] at hh
    linarith
  have hzb : ε/2 ≤ ‖b‖+η := by
    have hb : z = b+P (H : Set Vertex) hH z := by dsimp [b]; rw [Q_eq_sub]; abel
    have hh := norm_add_le b (P (H : Set Vertex) hH z)
    rw [← hb] at hh
    linarith
  have hp' : ‖a+b‖ ≤ R+2*η := by
    have he : a+b = (x+z)-(x-a)-P (H : Set Vertex) hH z := by
      dsimp [b]; rw [Q_eq_sub]; abel
    rw [he]
    have hh := norm_sub_le ((x+z)-(x-a)) (P (H : Set Vertex) hH z)
    have hh' := norm_sub_le (x+z) (x-a)
    linarith
  have hm' : ‖a-b‖ ≤ R+2*η := by
    have he : a-b = (x-z)-(x-a)+P (H : Set Vertex) hH z := by
      dsimp [b]; rw [Q_eq_sub]; abel
    rw [he]
    have hh := norm_add_le ((x-z)-(x-a)) (P (H : Set Vertex) hH z)
    have hh' := norm_sub_le (x-z) (x-a)
    linarith
  have hpair := paired_estimate Vertex.forestOrder Vertex.finiteAncestors (H : Set Vertex) hH a b
    (annihilates_P _ _ _) (annihilates_Q _ _ _)
  have hroot : Real.sqrt (‖a‖^2+‖b‖^2/12) ≤ R+2*η := by linarith
  have hsq : ‖a‖^2+‖b‖^2/12 ≤ (R+2*η)^2 := (Real.sqrt_le_iff.mp hroot).2
  have hxsq : ‖x‖^2 ≤ ‖a‖^2+2*R*η+η^2 := by
    nlinarith [norm_nonneg x,norm_nonneg a,mul_nonneg hη.le (sub_nonneg.mpr haR)]
  have hzsq : ε^2/4 ≤ ‖b‖^2+2*R*η+η^2 := by
    nlinarith [norm_nonneg b,mul_nonneg hη.le (sub_nonneg.mpr hbR)]
  have heta : η^2 ≤ η := by nlinarith
  nlinarith [mul_nonneg hR.le hη.le]

/-- The squared separated-midpoint deficit. -/
 theorem main_lens (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (x : FullDual Vertex) (y : ℕ → FullDual Vertex)
    (hp : ∀ j, ‖x+y j‖ ≤ R) (hm : ∀ j, ‖x-y j‖ ≤ R)
    (hs : ∀ i j, i ≠ j → ε ≤ ‖y i-y j‖) :
    ε^2/48 ≤ R^2-‖x‖^2 := by
  have hh : ‖x‖^2+ε^2/48 ≤ R^2 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let η := min 1 (δ/(8*(R+1)))
    have hc : 0 < 8*(R+1) := by positivity
    have hη : 0 < η := lt_min (by norm_num) (div_pos hδ hc)
    have hb := main_lens_aprox R ε hR hε x y hp hm hs η hη (min_le_left _ _)
    have he : 8*(R+1)*η ≤ δ := by
      rw [mul_comm]
      exact (le_div_iff₀ hc).mp (min_le_right _ _)
    linarith
  linarith

end Lens

end

end ForestSpace

end OAI
