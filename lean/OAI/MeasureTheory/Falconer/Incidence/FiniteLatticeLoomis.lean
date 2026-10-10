import OAI.MeasureTheory.Falconer.Incidence.WeightedLoomisBase
import OAI.MeasureTheory.Falconer.Incidence.PublishedLoomisWhitney

namespace OAI

/-! # The finite lattice Loomis–Whitney inequality used in the manuscript -/
namespace Falconer
open scoped BigOperators

theorem finite_loomis_whitney_card {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (hn : 1 ≤ n) (S : Finset (Fin (n+1) → X)) :
    S.card^n ≤ ∏ i : Fin (n+1), (S.image (eraseFinCoordinate i)).card := by
  classical
  let f : Fin (n+1) → (Fin n → X) → ℝ := fun i y =>
    if y ∈ S.image (eraseFinCoordinate i) then 1 else 0
  have hf : ∀ i y, 0 ≤ f i y := by intro i y; dsimp [f]; positivity
  have hpoint : ∀ z : Fin (n+1) → X,
      (if z ∈ S then (1:ℝ) else 0) ≤ ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ)) := by
    intro z
    by_cases hz : z ∈ S
    · have hm : ∀ i : Fin (n+1), eraseFinCoordinate i z ∈ S.image (eraseFinCoordinate i) :=
        fun i => Finset.mem_image.mpr ⟨z,hz,rfl⟩
      simp only [hz,ite_true,f,hm,Real.one_rpow,Finset.prod_const_one,le_refl]
    · simp only [hz,ite_false]
      exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hf _ _) _)
  have hcount : (S.card:ℝ) ≤
      ∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ)^(1/(n:ℝ)) := by
    calc
      _ = ∑ z : Fin (n+1) → X, if z ∈ S then (1:ℝ) else 0 := by simp
      _ ≤ ∑ z : Fin (n+1) → X, ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ)) :=
        Finset.sum_le_sum (fun z _ => hpoint z)
      _ ≤ ∏ i : Fin (n+1), (∑ y : Fin n → X, f i y)^(1/(n:ℝ)) :=
        finite_weighted_loomis_whitney n hn f hf
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        change (∑ y : Fin n → X, if y ∈ S.image (eraseFinCoordinate i) then (1:ℝ) else 0) = _
        simp only [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hcount n
  have hright : (∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ)^(1/(n:ℝ)))^n =
      ∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  rw [hright] at hpower
  exact_mod_cast hpower

theorem published_finite_loomis_whitney : PublishedFiniteLoomisWhitney := by
  classical
  intro n hn S
  let A : Finset ℤ := S.biUnion (fun z => Finset.univ.image z)
  have hA : ∀ z ∈ S, ∀ i : Fin (n+1), z i ∈ A := by
    intro z hz i
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let lift : {z // z ∈ S} → (Fin (n+1) → A) := fun z i => ⟨z.val i,hA z.val z.property i⟩
  let T := S.attach.image lift
  have hlift : Function.Injective lift := by
    intro z w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  have hcard : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  have hproj : ∀ i : Fin (n+1), (T.image (eraseFinCoordinate i)).card =
      (S.image (dropGridCoordinate i)).card := by
    intro i
    let lower : (Fin n → A) → (Fin n → ℤ) := fun z j => (z j).val
    have hlower : Function.Injective lower := by
      intro z w he
      funext j
      exact Subtype.ext (congrFun he j)
    rw [← Finset.card_image_of_injective _ hlower]
    congr 1
    dsimp only [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun z => dropGridCoordinate i z.val) = _
    calc
      _ = (S.attach.image Subtype.val).image (dropGridCoordinate i) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val) (g := dropGridCoordinate i)).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hh := finite_loomis_whitney_card n hn T
  rw [hcard] at hh
  simpa only [hproj] using hh

end Falconer

end OAI
