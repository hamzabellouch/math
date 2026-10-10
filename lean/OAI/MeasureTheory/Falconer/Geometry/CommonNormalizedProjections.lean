import OAI.MeasureTheory.Falconer.Geometry.CommonRatioProjections
import OAI.MeasureTheory.Falconer.Geometry.ScalarProjectionDoubling

namespace OAI

/-! Normalized common-set projection estimates in the balanced Cartesian
case, including the doubling needed for coefficient arithmetic. -/
namespace Falconer
open scoped Pointwise

 theorem normalize_ratio_product_bound {D C K ρ N A : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hN : 0 < N)
    (hA : ρ*N ≤ A)
    (hbound : D*ρ^12*N*N^2 ≤ C*(K*N)^4) :
    D ≤ (C*K^4/ρ^13)*A := by
  have hd : D ≤ C*K^4/ρ^12*N := by
    calc
      _ ≤ C*(K*N)^4/(ρ^12*N*N^2) :=
        (le_div_iff₀ (by positivity : 0 < ρ^12*N*N^2)).2
          (by simpa only [mul_assoc] using hbound)
      _ = _ := by field_simp
  have hstep := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ C*K^4/ρ^13)
  calc
    _ ≤ C*K^4/ρ^12*N := hd
    _ = (C*K^4/ρ^13)*(ρ*N) := by field_simp
    _ ≤ _ := hstep

 theorem common_normalized_ratio_projections {α : Type*} {δ ρ K : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (I : Finset α) (X Y : Finset ℝ) (A B : α → Finset ℝ) (c : α → ℝ)
    (hI : I.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : X.card = Y.card)
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hA : ∀ i ∈ I, A i ⊆ X) (hB : ∀ i ∈ I, B i ⊆ Y)
    (hsizeA : ∀ i ∈ I, ρ*(X.card : ℝ) ≤ ((A i).card : ℝ))
    (hsizeB : ∀ i ∈ I, ρ*(Y.card : ℝ) ≤ ((B i).card : ℝ))
    (M : ℕ) (hc : ∀ i ∈ I, c i ≠ 0 ∧ |c i| ≤ M ∧ |(c i)⁻¹| ≤ M)
    (hproj : ∀ i ∈ I, ((scalarCells δ (A i+(B i).image (fun y => c i*y))).card : ℝ) ≤
      K*(X.card : ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      ρ^4*(I.card : ℝ) ≤ 2*(J.card : ℝ) ∧ (A i₀).Nonempty ∧
      ((scalarCells δ (A i₀+A i₀)).card : ℝ) ≤
        (1024*(2*M+3)^2*K^4/ρ^6)*(scalarCells δ (A i₀)).card ∧
      ∀ j ∈ J,
        ((scalarCells δ (A i₀-(A i₀).image (fun x => (c j/c i₀)*x))).card : ℝ) ≤
          (4096*(2*(M*M)+3)*(2*M+3)^2*K^4/ρ^13)*(scalarCells δ (A i₀)).card := by
  classical
  obtain ⟨i₀,hi₀,J,hJI,hJ,hraw⟩ := common_small_ratio_projections hδ hρ
    (by positivity : 0 ≤ K*(X.card : ℝ)) I X Y A B c hI hX hY hXsep hYsep
    hA hB hsizeA hsizeB M hc hproj
  have hN : 0 < (X.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hAi0 : 0 < ((A i₀).card : ℝ) := (mul_pos hρ hN).trans_le (hsizeA i₀ hi₀)
  have hAi : (A i₀).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hAi0)
  have hAc : (scalarCells δ (A i₀)).card = (A i₀).card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ
      (fun x hx y hy hxy => hXsep x (hA i₀ hi₀ hx) y (hA i₀ hi₀ hy) hxy))
  have hNY : (Y.card : ℝ) = (X.card : ℝ) := by exact_mod_cast hXY.symm
  have hbase : ((scalarCells δ (A i₀+(B i₀).image (fun y => c i₀*y))).card : ℝ) ≤
      (K/ρ)*(scalarCells δ (A i₀)).card := by
    apply (hproj i₀ hi₀).trans
    rw [hAc]
    have hh := mul_le_mul_of_nonneg_left (hsizeA i₀ hi₀) (div_nonneg hK hρ.le)
    calc
      _ = (K/ρ)*(ρ*(X.card : ℝ)) := by field_simp
      _ ≤ _ := hh
  have hBsize : ρ*((scalarCells δ (A i₀)).card : ℝ) ≤ ((B i₀).card : ℝ) := by
    rw [hAc]
    calc
      _ ≤ ρ*(X.card : ℝ) := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card (hA i₀ hi₀))) hρ.le
      _ = ρ*(Y.card : ℝ) := by rw [hNY]
      _ ≤ _ := hsizeB i₀ hi₀
  have hd := scalar_doubling_from_projection hδ (hc i₀ hi₀).1 hρ (A i₀) (B i₀)
    hAi M (hc i₀ hi₀).2.2
    (fun x hx y hy hxy => hYsep x (hB i₀ hi₀ hx) y (hB i₀ hi₀ hy) hxy) hBsize hbase
  refine ⟨i₀,hi₀,J,hJI,hJ,hAi,?_,?_⟩
  · convert hd using 1
    field_simp
  · intro j hj
    have hb := hraw j hj
    rw [hNY] at hb
    have hh := normalize_ratio_product_bound
      (by positivity : 0 ≤ (4096 : ℝ)*(2*(M*M)+3)*(2*M+3)^2)
      hρ hN (hsizeA i₀ hi₀) hb
    rw [hAc]
    exact hh

end Falconer

end OAI
