import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.SetTheory.Cardinal.Finite
import OAI.Geometry.NodalSets.Elliptic.CoordinateNorm

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma same_floor_distance {r : ℝ} (hr : 0 < r) {x y : Coord}
    (h : ∀ i, ⌊x i / r⌋ = ⌊y i / r⌋) : ‖x-y‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr.le).mpr
  intro i
  have hx1 := Int.floor_le (x i/r)
  have hx2 := Int.lt_floor_add_one (x i/r)
  have hy1 := Int.floor_le (y i/r)
  have hy2 := Int.lt_floor_add_one (y i/r)
  rw [← h i] at hy1 hy2
  have h1 : x i/r-y i/r ≤ 1 := by linarith
  have h2 : -(1:ℝ) ≤ x i/r-y i/r := by linarith
  rw [← sub_div] at h1 h2
  have h1' := (div_le_iff₀ hr).mp h1
  have h2' := (le_div_iff₀ hr).mp h2
  change |x i-y i| ≤ r
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem bounded_internal_net {Q : Set Coord} (hQ : Bornology.IsBounded Q) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ E : Set Coord, E ⊆ Q →
      ∃ t : Finset Coord, (↑t : Set Coord) ⊆ E ∧
        (t.card : ℝ) ≤ C*(r⁻¹)^4 ∧
        ∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ r ∧ sourceEuclideanNorm (x-y) ≤ 2*r := by
  classical
  obtain ⟨B,hB,hbound⟩ := hQ.exists_pos_norm_le
  refine ⟨(2*B+5)^4,by positivity,?_⟩
  intro r hr hr1 E hEQ
  let M : ℤ := ⌈B/r⌉+1
  have hM0 : 0 ≤ M := by dsimp [M]; have := Int.ceil_nonneg (div_nonneg hB.le hr.le); omega
  have hceil : B/r ≤ (⌈B/r⌉ : ℝ) := Int.le_ceil _
  have hceil' : (⌈B/r⌉ : ℝ) < B/r+1 := Int.ceil_lt_add_one _
  have hcoords (x : E) (i : Fin 4) : ⌊x.val i/r⌋ ∈ Icc (-M) M := by
    have hi := (norm_le_pi_norm x.val i).trans (hbound x.val (hEQ x.property))
    change |x.val i| ≤ B at hi
    have hxi := abs_le.mp hi
    have hx1 := Int.floor_le (x.val i/r)
    have hx2 := Int.lt_floor_add_one (x.val i/r)
    have hu : x.val i/r ≤ B/r := div_le_div_of_nonneg_right hxi.2 hr.le
    have hl : -B/r ≤ x.val i/r := div_le_div_of_nonneg_right hxi.1 hr.le
    rw [neg_div] at hl
    have hMc : (M:ℝ) = (⌈B/r⌉:ℝ)+1 := by simp [M]
    constructor
    · have : -(M:ℝ) ≤ (⌊x.val i/r⌋:ℝ) := by linarith
      exact_mod_cast this
    · have : (⌊x.val i/r⌋:ℝ) ≤ (M:ℝ) := by linarith
      exact_mod_cast this
  let Box := Fin 4 → Icc (-M) M
  let f : E → Box := fun x i ↦ ⟨⌊x.val i/r⌋,hcoords x i⟩
  let R := Set.range f
  let rep : R → E := fun z ↦ Classical.choose z.property
  have hrep (z : R) : f (rep z) = z.val := Classical.choose_spec z.property
  let t : Finset Coord := Finset.univ.image (fun z : R ↦ (rep z).val)
  refine ⟨t,?_,?_,?_⟩
  · intro y hy
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
    exact (rep z).property
  · have hc : t.card ≤ Fintype.card Box :=
      (Finset.card_image_le).trans (by
        simpa using Fintype.card_le_of_injective (fun z : R ↦ z.val) Subtype.val_injective)
    have hbox : Fintype.card Box = ((2*M+1).toNat)^4 := by
      simp [Box,Int.card_Icc,show M+1- -M = 2*M+1 by ring]
    rw [hbox] at hc
    have hcR : (t.card:ℝ) ≤ ((2*M+1).toNat:ℝ)^4 := by exact_mod_cast hc
    have hcast : ((2*M+1).toNat:ℝ) = 2*(M:ℝ)+1 := by
      have hi : ((2*M+1).toNat:ℤ) = 2*M+1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hi
    rw [hcast] at hcR
    have hri : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
    have hMc : (M:ℝ) < B/r+2 := by dsimp [M]; push_cast; linarith
    have hm : 2*(M:ℝ)+1 ≤ (2*B+5)*r⁻¹ := by
      rw [div_eq_mul_inv] at hMc
      nlinarith
    calc
      (t.card:ℝ) ≤ (2*(M:ℝ)+1)^4 := hcR
      _ ≤ ((2*B+5)*r⁻¹)^4 := pow_le_pow_left₀ (by positivity) hm 4
      _ = (2*B+5)^4*(r⁻¹)^4 := mul_pow _ _ _
  · intro x hx
    let z : R := ⟨f ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩
    refine ⟨(rep z).val,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩,?_⟩
    have he : ∀ i, ⌊x i/r⌋ = ⌊(rep z).val i/r⌋ := by
      intro i
      exact (congrArg Subtype.val (congrFun (hrep z) i)).symm
    have hd := same_floor_distance hr he
    exact ⟨hd,(sourceEuclideanNorm_le _).trans (by linarith)⟩

theorem jet_scale_internal_net {Q : Set Coord} (hQ : Bornology.IsBounded Q) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ E : Set Coord, E ⊆ Q →
      ∃ t : Finset Coord, (↑t : Set Coord) ⊆ E ∧
        (t.card : ℝ) ≤ C*(n:ℝ)^276 ∧
        ∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ (4*(n:ℝ)^69)⁻¹ ∧
          sourceEuclideanNorm (x-y) ≤ (2*(n:ℝ)^69)⁻¹ := by
  obtain ⟨C,hC,hnet⟩ := bounded_internal_net hQ
  refine ⟨C*4^4,by positivity,?_⟩
  intro n hn E hEQ
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by positivity
  have hpow : (1:ℝ) ≤ (n:ℝ)^69 := one_le_pow₀ hnR
  obtain ⟨t,ht,hcard,hcover⟩ := hnet (4*(n:ℝ)^69)⁻¹ (by positivity)
    ((inv_le_one₀ (by positivity)).mpr (by linarith)) E hEQ
  refine ⟨t,ht,?_,?_⟩
  · convert hcard using 1
    simp only [inv_inv,mul_pow,← pow_mul]
    ring
  · intro x hx
    obtain ⟨y,hy,hd,he⟩ := hcover x hx
    refine ⟨y,hy,hd,?_⟩
    convert he using 1
    field_simp
    ring

end
end Yau.Geometry

end OAI
