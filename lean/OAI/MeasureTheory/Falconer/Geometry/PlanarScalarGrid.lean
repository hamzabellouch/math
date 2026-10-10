import OAI.MeasureTheory.Falconer.Estimates.ScalarSumCells
import OAI.MeasureTheory.Falconer.Graphs.GraphBallCover

namespace OAI

/-! Actual scalar grid coordinates for a planar finite set. Rounding is
injective below the separation scale and coordinate counts are exactly the
original scalar cell counts. -/
namespace Falconer

noncomputable def scalarGridFloor (δ x : ℝ) : ℝ := δ*(⌊x/δ⌋:ℝ)

 theorem scalarGridFloor_error {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |x-scalarGridFloor δ x| ≤ δ := by
  have h0 := (le_div_iff₀ hδ).1 (Int.floor_le (x/δ))
  have h1 := (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one (x/δ))
  unfold scalarGridFloor
  rw [abs_of_nonneg (by nlinarith : 0 ≤ x-δ*(⌊x/δ⌋:ℝ))]
  nlinarith

 theorem scalarGridFloor_injective {δ : ℝ} (hδ : δ ≠ 0) :
    Function.Injective (fun k : ℤ => δ*(k:ℝ)) := by
  intro k l h
  exact Int.cast_injective (mul_left_cancel₀ hδ h)

 theorem scalarGridFloor_card {δ : ℝ} (hδ : 0 < δ) (X : Finset ℝ) :
    (X.image (scalarGridFloor δ)).card = (scalarCells δ X).card := by
  have he : X.image (scalarGridFloor δ) = (scalarCells δ X).image (fun k : ℤ => δ*(k:ℝ)) := by
    change X.image (fun x => δ*(⌊x/δ⌋:ℝ)) = _
    simp only [scalarCells,Finset.image_image,Function.comp_def]
  rw [he,Finset.card_image_of_injective _ (scalarGridFloor_injective hδ.ne')]

 theorem scalarGridFloor_separated {δ : ℝ} (hδ : 0 < δ) (X : Finset ℝ) :
    ∀ x ∈ X.image (scalarGridFloor δ), ∀ y ∈ X.image (scalarGridFloor δ),
      x ≠ y → δ ≤ |x-y| := by
  intro x hx y hy hne
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  have hfloor : ⌊a/δ⌋ ≠ ⌊b/δ⌋ := by
    intro h
    exact hne (by simp only [scalarGridFloor,h])
  have hInt : (1:ℤ) ≤ |⌊a/δ⌋-⌊b/δ⌋| := by
    have hh : (0:ℤ) < |⌊a/δ⌋-⌊b/δ⌋| := abs_pos.mpr (sub_ne_zero.mpr hfloor)
    omega
  have hR : (1:ℝ) ≤ |(⌊a/δ⌋:ℝ)-(⌊b/δ⌋:ℝ)| := by exact_mod_cast hInt
  unfold scalarGridFloor
  rw [← mul_sub,abs_mul,abs_of_pos hδ]
  nlinarith

noncomputable def planarGridFloor (δ : ℝ) (x : Space 2) : Space 2 :=
  rowPoint (scalarGridFloor δ (x 0)) (scalarGridFloor δ (x 1))

 theorem planarGridFloor_apply (δ : ℝ) (x : Space 2) (i : Fin 2) :
    planarGridFloor δ x i = scalarGridFloor δ (x i) := by
  fin_cases i <;> rfl

 theorem planarGridFloor_error {δ : ℝ} (hδ : 0 < δ) (x : Space 2) :
    dist x (planarGridFloor δ x) ≤ 2*δ := by
  have hh := planar_dist_le_coordinate_sum x (planarGridFloor δ x)
  change dist x (planarGridFloor δ x) ≤
    |x 0-scalarGridFloor δ (x 0)|+|x 1-scalarGridFloor δ (x 1)| at hh
  linarith [scalarGridFloor_error hδ (x 0),scalarGridFloor_error hδ (x 1)]

 theorem planarGridFloor_injOn {δ σ : ℝ} (hσ : 0 < σ) (hsmall : 4*σ < δ)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    Set.InjOn (planarGridFloor σ) (G:Set (Space 2)) := by
  intro x hx y hy he
  by_contra hne
  have hh := dist_triangle x (planarGridFloor σ x) y
  rw [he,dist_comm (planarGridFloor σ y) y] at hh
  have hxerr := planarGridFloor_error hσ x
  have hyerr := planarGridFloor_error hσ y
  rw [he] at hxerr
  have hdist : dist x y ≤ 4*σ := by
    linarith
  exact (not_lt_of_ge (hsep x hx y hy hne)) (hdist.trans_lt hsmall)

 theorem planarGridFloor_card {δ σ : ℝ} (hσ : 0 < σ) (hsmall : 4*σ < δ)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    (G.image (planarGridFloor σ)).card = G.card :=
  Finset.card_image_of_injOn (planarGridFloor_injOn hσ hsmall G hsep)

 theorem planarGridFloor_coordinate_card {δ : ℝ} (hδ : 0 < δ)
    (G : Finset (Space 2)) (i : Fin 2) :
    ((G.image (planarGridFloor δ)).image (fun x => x i)).card =
      (scalarCells δ (G.image (fun x => x i))).card := by
  have he : (G.image (planarGridFloor δ)).image (fun x => x i) =
      (G.image (fun x => x i)).image (scalarGridFloor δ) := by
    simp only [Finset.image_image,Function.comp_def,planarGridFloor_apply]
  rw [he,scalarGridFloor_card hδ]

 theorem planarGridFloor_coordinate_separated {δ : ℝ} (hδ : 0 < δ)
    (G : Finset (Space 2)) (i : Fin 2) :
    ∀ x ∈ (G.image (planarGridFloor δ)).image (fun p => p i),
      ∀ y ∈ (G.image (planarGridFloor δ)).image (fun p => p i), x ≠ y → δ ≤ |x-y| := by
  have he : (G.image (planarGridFloor δ)).image (fun x => x i) =
      (G.image (fun x => x i)).image (scalarGridFloor δ) := by
    simp only [Finset.image_image,Function.comp_def,planarGridFloor_apply]
  rw [he]
  exact scalarGridFloor_separated hδ _

 theorem planarGridFloor_separated {δ : ℝ} (hδ : 0 < δ) (G : Finset (Space 2)) :
    FiniteSeparatedAt δ (G.image (planarGridFloor δ)) := by
  intro x hx y hy hne
  by_contra hn
  have hd : dist x y < δ := lt_of_not_ge hn
  apply hne
  ext i
  have hx' : x i ∈ (G.image (planarGridFloor δ)).image (fun p => p i) := Finset.mem_image_of_mem _ hx
  have hy' : y i ∈ (G.image (planarGridFloor δ)).image (fun p => p i) := Finset.mem_image_of_mem _ hy
  by_contra hneq
  have hs := planarGridFloor_coordinate_separated hδ G i _ hx' _ hy' hneq
  have hh : |x i-y i| ≤ dist x y := by simpa only [Real.dist_eq] using PiLp.dist_apply_le x y i
  linarith

end Falconer

end OAI
