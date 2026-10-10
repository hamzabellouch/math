import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Estimates.RetainedCardLeft
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasureAeNorm

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Attempt4FullFar
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

def retainedCenterTests (v w x₁ x₂ y₁ y₂ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) : Prop :=
  ‖graphPerpND v (x₁-y₁)‖ ≤ τ ∧ ‖graphPerpND w (x₂-y₂)‖ ≤ τ ∧
    |inner ℝ (x₁-y₁) v + inner ℝ (x₂-y₂) w| ≤ τ

lemma retainedCenterTests_symm (v w x₁ x₂ y₁ y₂ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) :
    retainedCenterTests v w x₁ x₂ y₁ y₂ τ ↔ retainedCenterTests v w y₁ y₂ x₁ x₂ τ := by
  have h₁ : ‖graphPerpND v (x₁-y₁)‖=‖graphPerpND v (y₁-x₁)‖ := by
    simp only [graphPerpND_sub, norm_sub_rev]
  have h₂ : ‖graphPerpND w (x₂-y₂)‖=‖graphPerpND w (y₂-x₂)‖ := by
    simp only [graphPerpND_sub, norm_sub_rev]
  have h₃ : |inner ℝ (x₁-y₁) v + inner ℝ (x₂-y₂) w| =
      |inner ℝ (y₁-x₁) v + inner ℝ (y₂-x₂) w| := by
    rw [show x₁-y₁= -(y₁-x₁) by abel,show x₂-y₂= -(y₂-x₂) by abel]
    simp only [inner_neg_left,← neg_add,abs_neg]
  simp only [retainedCenterTests,h₁,h₂,h₃]

lemma mem_retainedPairs_iff (S T : Finset (CellPath d))
    (v w x y : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (z : CellPath d × CellPath d) :
    z ∈ retainedPairs S T v w x y τ ↔ z ∈ S.product T ∧
      retainedCenterTests v w (treeCenter z.1) (treeCenter z.2) x y τ := by
  classical
  simp only [retainedPairs,Finset.mem_filter,retainedCenterTests]

def retainedHGraph (S T : Finset (CellPath d))
    (v w : EuclideanSpace ℝ (Fin d)) (τ : ℝ)
    (row col : CellPath d × CellPath d) : Prop :=
  row ∈ S.product T ∧ col ∈ S.product T ∧
    retainedCenterTests v w (treeCenter row.1) (treeCenter row.2)
      (treeCenter col.1) (treeCenter col.2) τ

def retainedHFGraph (Sv Sw Tv Tw : Finset (CellPath d))
    (v w : EuclideanSpace ℝ (Fin d)) (τ : ℝ)
    (row col : CellPath d × CellPath d) : Prop :=
  row ∈ Sv.product Tw ∧ col ∈ Sw.product Tv ∧
    retainedCenterTests v w (treeCenter row.1) (treeCenter row.2)
      (treeCenter col.2) (treeCenter col.1) τ

attribute [local instance] Classical.propDecidable

lemma retainedHGraph_row_card (A B S T : Finset (CellPath d))
    (v w : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (row : CellPath d × CellPath d) :
    ((A.product B).filter (retainedHGraph S T v w τ row)).card ≤
      (retainedPairs S T v w (treeCenter row.1) (treeCenter row.2) τ).card := by
  classical
  apply Finset.card_le_card
  intro col hcol
  obtain ⟨_,_,hcolST,htests⟩ := Finset.mem_filter.mp hcol
  exact (mem_retainedPairs_iff _ _ _ _ _ _ _ _).2
    ⟨hcolST,(retainedCenterTests_symm _ _ _ _ _ _ _).1 htests⟩

lemma retainedHGraph_col_card (A B S T : Finset (CellPath d))
    (v w : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (col : CellPath d × CellPath d) :
    ((A.product B).filter (fun row => retainedHGraph S T v w τ row col)).card ≤
      (retainedPairs S T v w (treeCenter col.1) (treeCenter col.2) τ).card := by
  classical
  apply Finset.card_le_card
  intro row hrow
  obtain ⟨_,hrowST,_,htests⟩ := Finset.mem_filter.mp hrow
  exact (mem_retainedPairs_iff _ _ _ _ _ _ _ _).2 ⟨hrowST,htests⟩

lemma retainedHFGraph_row_card (A B Sv Sw Tv Tw : Finset (CellPath d))
    (v w : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (row : CellPath d × CellPath d) :
    ((A.product B).filter (retainedHFGraph Sv Sw Tv Tw v w τ row)).card ≤
      (retainedPairs Tv Sw v w (treeCenter row.1) (treeCenter row.2) τ).card := by
  classical
  let F := (A.product B).filter (retainedHFGraph Sv Sw Tv Tw v w τ row)
  have hsub : F.image Prod.swap ⊆
      retainedPairs Tv Sw v w (treeCenter row.1) (treeCenter row.2) τ := by
    intro z hz
    obtain ⟨col,hcol,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨_,_,hcolST,htests⟩ := Finset.mem_filter.mp hcol
    refine (mem_retainedPairs_iff _ _ _ _ _ _ _ _).2 ⟨?_,?_⟩
    · exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hcolST).2,
        (Finset.mem_product.mp hcolST).1⟩
    · exact (retainedCenterTests_symm _ _ _ _ _ _ _).1 htests
  calc
    _ = (F.image Prod.swap).card := (Finset.card_image_of_injective F Prod.swap_injective).symm
    _ ≤ _ := Finset.card_le_card hsub

lemma retainedHFGraph_col_card (A B Sv Sw Tv Tw : Finset (CellPath d))
    (v w : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (col : CellPath d × CellPath d) :
    ((A.product B).filter (fun row => retainedHFGraph Sv Sw Tv Tw v w τ row col)).card ≤
      (retainedPairs Sv Tw v w (treeCenter col.2) (treeCenter col.1) τ).card := by
  classical
  apply Finset.card_le_card
  intro row hrow
  obtain ⟨_,hrowST,_,htests⟩ := Finset.mem_filter.mp hrow
  exact (mem_retainedPairs_iff _ _ _ _ _ _ _ _).2 ⟨hrowST,htests⟩

end CurrentFalconer.TreeND
end
end

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Attempt4FullFar
open scoped ENNReal RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

noncomputable def graphDegreeBound (d a g₁ g₂ p : ℕ) (τ K₁ K₂ : ℝ) : ℝ :=
  min (((2:ℝ)^d)^(g₁-a)*K₁) (((2:ℝ)^d)^(g₂-a)*K₂) * (4*(2:ℝ)^p*τ+5)^d

theorem eligibleGraphDegrees
    (ρ₁ ρ₂ : Measure (EuclideanSpace ℝ (Fin d)))
    (a g₁ g₂ p : ℕ) (X Y : CellPath d) (A B : Finset (CellPath d))
    (ηv ηw : EuclideanSpace ℝ (Fin d) → ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (v w : EuclideanSpace ℝ (Fin d)) (δ τ W₁ W₂ K₁ K₂ : ℝ)
    (hag₁ : a ≤ g₁) (hag₂ : a ≤ g₂) (hg₁p : g₁ ≤ p) (hg₂p : g₂ ≤ p)
    (hv : ‖v‖=1) (hw : ‖w‖=1) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hW₁ : 2*τ+2*((d+1:ℝ)/(2:ℝ)^g₁)*δ ≤ W₁)
    (hW₂ : 2*τ+2*((d+1:ℝ)/(2:ℝ)^g₂)*δ ≤ W₂)
    (hcapv : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖=1 → ηv u ≠ 0 → dist v u ≤ δ)
    (hcapw : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖=1 → ηw u ≠ 0 → dist w u ≤ δ)
    (htest₁ : ImposesParallelTest ρ₁ g₁ p W₁ K₁ b)
    (htest₂ : ImposesParallelTest ρ₂ g₂ p W₂ K₂ c) :
    let Sv := eligibleCells ρ₁ a p X ηv b
    let Sw := eligibleCells ρ₁ a p X ηw b
    let Tv := eligibleCells ρ₂ a p Y ηv c
    let Tw := eligibleCells ρ₂ a p Y ηw c
    let D := graphDegreeBound d a g₁ g₂ p τ K₁ K₂
    (∀ row,
      (((A.product B).filter (retainedHGraph Sv Tw v w τ row)).card : ℝ) ≤ D ∧
      (((A.product B).filter (retainedHFGraph Sv Sw Tv Tw v w τ row)).card : ℝ) ≤ D) ∧
    (∀ col,
      (((A.product B).filter (fun row => retainedHGraph Sv Tw v w τ row col)).card : ℝ) ≤ D ∧
      (((A.product B).filter (fun row => retainedHFGraph Sv Sw Tv Tw v w τ row col)).card : ℝ) ≤ D) := by
  dsimp only
  let Sv := eligibleCells ρ₁ a p X ηv b
  let Sw := eligibleCells ρ₁ a p X ηw b
  let Tv := eligibleCells ρ₂ a p Y ηv c
  let Tw := eligibleCells ρ₂ a p Y ηw c
  have hSv := eligibleCells_tested ρ₁ a g₁ p X ηv b v δ W₁ K₁ hcapv htest₁
  have hSw := eligibleCells_tested ρ₁ a g₁ p X ηw b w δ W₁ K₁ hcapw htest₁
  have hTv := eligibleCells_tested ρ₂ a g₂ p Y ηv c v δ W₂ K₂ hcapv htest₂
  have hTw := eligibleCells_tested ρ₂ a g₂ p Y ηw c w δ W₂ K₂ hcapw htest₂
  have h12 : ∀ x y, ((retainedPairs Sv Tw v w x y τ).card : ℝ) ≤
      graphDegreeBound d a g₁ g₂ p τ K₁ K₂ := by
    intro x y
    exact retained_degree d ρ₁ ρ₂ a g₁ g₂ p X Y Sv Tw v w x y δ τ W₁ W₂ K₁ K₂
      hag₁ hag₂ hg₁p hg₂p hv hw hδ hτ hK₁ hK₂ hW₁ hW₂ hSv hTw
  have h21 : ∀ x y, ((retainedPairs Tv Sw v w x y τ).card : ℝ) ≤
      graphDegreeBound d a g₁ g₂ p τ K₁ K₂ := by
    intro x y
    have hh := retained_degree d ρ₂ ρ₁ a g₂ g₁ p Y X Tv Sw v w x y δ τ W₂ W₁ K₂ K₁
      hag₂ hag₁ hg₂p hg₁p hv hw hδ hτ hK₂ hK₁ hW₂ hW₁ hTv hSw
    simpa only [graphDegreeBound,min_comm] using hh
  constructor
  · intro row
    exact ⟨(Nat.cast_le.mpr (retainedHGraph_row_card A B Sv Tw v w τ row)).trans (h12 _ _),
      (Nat.cast_le.mpr (retainedHFGraph_row_card A B Sv Sw Tv Tw v w τ row)).trans (h21 _ _)⟩
  · intro col
    exact ⟨(Nat.cast_le.mpr (retainedHGraph_col_card A B Sv Tw v w τ col)).trans (h12 _ _),
      (Nat.cast_le.mpr (retainedHFGraph_col_card A B Sv Sw Tv Tw v w τ col)).trans (h12 _ _)⟩

end CurrentFalconer.TreeND
end
end

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma graph_height_mono_left (A : ℕ → ℝ) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p) :
    height A g p ≤ height A a p := by
  obtain ⟨j,hgj,hjp,he⟩ := intervalMin_attained A hgp
  unfold height
  have hm : intervalMin A a p ≤ intervalMin A g p := by
    rw [he]
    exact intervalMin_le A (hag.trans hgj) hjp
  linarith

lemma graph_ancestor_scale {N a g : ℕ} {sig : ℝ}
    (hag : a ≤ g) (hanchor : (g:ℝ) ≤ (a:ℝ)+2*sig*N) :
    ((2:ℝ)^d)^(g-a) ≤ ((2:ℝ)^N)^(2*(d:ℝ)*sig) := by
  have hgap : ((g-a:ℕ):ℝ) ≤ 2*sig*N := by rw [Nat.cast_sub hag]; linarith
  calc
    _ = (2:ℝ)^((d:ℝ)*((g-a:ℕ):ℝ)) := by rw [← Nat.cast_mul,Real.rpow_natCast,pow_mul]
    _ ≤ (2:ℝ)^((N:ℝ)*(2*(d:ℝ)*sig)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith [Nat.cast_nonneg (α:=ℝ) d])
    _ = _ := by rw [← Real.rpow_natCast (2:ℝ) N, ← Real.rpow_mul (by norm_num)]

lemma graph_ball_scale {R sig : ℝ} (hR : 1 ≤ R) (hsig : 0 ≤ sig) (d p : ℕ) :
    (4*(2:ℝ)^p*((2:ℝ)^p)⁻¹*R^(30*sig)+5)^d ≤
      (9:ℝ)^d*R^(30*(d:ℝ)*sig) := by
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hr : 1 ≤ R^(30*sig) := Real.one_le_rpow hR (by positivity)
  have he : 4*(2:ℝ)^p*((2:ℝ)^p)⁻¹*R^(30*sig)+5 = 4*R^(30*sig)+5 := by
    field_simp
  rw [he]
  calc
    _ ≤ (9*R^(30*sig))^d := by gcongr; linarith
    _ = (9:ℝ)^d*(R^(30*sig))^d := mul_pow _ _ _
    _ = _ := by
      rw [← Real.rpow_natCast (R^(30*sig)) d, ← Real.rpow_mul hRp.le]
      congr 2
      ring

lemma graph_profile_factor_scale (A : ℕ → ℝ) {N a g p : ℕ} {sig C : ℝ}
    (hag : a ≤ g) (hgp : g ≤ p)
    (hanchor : (g:ℝ) ≤ (a:ℝ)+2*sig*N) :
    ((2:ℝ)^d)^(g-a) * ((2:ℝ)^N)^(height A g p+C*sig) ≤
      ((2:ℝ)^N)^(height A a p+(C+2*(d:ℝ))*sig) := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  calc
    _ ≤ ((2:ℝ)^N)^(2*(d:ℝ)*sig) * ((2:ℝ)^N)^(height A g p+C*sig) :=
      mul_le_mul_of_nonneg_right (graph_ancestor_scale hag hanchor) (Real.rpow_nonneg hRp.le _)
    _ = ((2:ℝ)^N)^(2*(d:ℝ)*sig+(height A g p+C*sig)) := (Real.rpow_add hRp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by
      have hh := graph_height_mono_left A hag hgp
      linarith)

theorem graphDegreeBound_source_scale (A₁ A₂ : ℕ → ℝ)
    {N a g₁ g₂ p : ℕ} {sig C : ℝ} (hsig : 0 ≤ sig)
    (hag₁ : a ≤ g₁) (hag₂ : a ≤ g₂) (hg₁p : g₁ ≤ p) (hg₂p : g₂ ≤ p)
    (hanchor₁ : (g₁:ℝ) ≤ (a:ℝ)+2*sig*N)
    (hanchor₂ : (g₂:ℝ) ≤ (a:ℝ)+2*sig*N) :
    graphDegreeBound d a g₁ g₂ p (((2:ℝ)^p)⁻¹*((2:ℝ)^N)^(30*sig))
      (((2:ℝ)^N)^(height A₁ g₁ p+C*sig))
      (((2:ℝ)^N)^(height A₂ g₂ p+C*sig)) ≤
      (9:ℝ)^d * ((2:ℝ)^N)^(min (height A₁ a p) (height A₂ a p)+(C+32*(d:ℝ))*sig) := by
  let R := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := by positivity
  have hball : (4*(2:ℝ)^p*(((2:ℝ)^p)⁻¹*R^(30*sig))+5)^d ≤
      (9:ℝ)^d*R^(30*(d:ℝ)*sig) := by
    simpa only [mul_assoc] using graph_ball_scale hR hsig d p
  have hf₁ := graph_profile_factor_scale (d:=d) (C:=C) A₁ hag₁ hg₁p hanchor₁
  have hf₂ := graph_profile_factor_scale (d:=d) (C:=C) A₂ hag₂ hg₂p hanchor₂
  have hmin : min (((2:ℝ)^d)^(g₁-a)*R^(height A₁ g₁ p+C*sig))
      (((2:ℝ)^d)^(g₂-a)*R^(height A₂ g₂ p+C*sig)) ≤
      R^(min (height A₁ a p) (height A₂ a p)+(C+2*(d:ℝ))*sig) := by
    rcases le_total (height A₁ a p) (height A₂ a p) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans hf₁
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hf₂
  calc
    _ ≤ R^(min (height A₁ a p) (height A₂ a p)+(C+2*(d:ℝ))*sig) *
        ((9:ℝ)^d*R^(30*(d:ℝ)*sig)) := by
      unfold graphDegreeBound
      exact mul_le_mul hmin hball (by positivity) (by positivity)
    _ = (9:ℝ)^d * (R^(min (height A₁ a p) (height A₂ a p)+(C+2*(d:ℝ))*sig) *
        R^(30*(d:ℝ)*sig)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hRp]
      congr 2
      ring

end CurrentFalconer.TreeND
end
end

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma graph_width_coverage {R sig Ccap δ : ℝ} {a g p : ℕ}
    (hR : 1 ≤ R) (hsig : 0 ≤ sig) (hCcap : 0 ≤ Ccap) (hag : a ≤ g)
    (hcap : δ ≤ Ccap*(2:ℝ)^a/(2:ℝ)^p*R^(10*sig))
    (hlarge : 2+2*(d+1:ℝ)*Ccap ≤ R^(470*sig)) :
    2*(((2:ℝ)^p)⁻¹*R^(30*sig))+2*((d+1:ℝ)/(2:ℝ)^g)*δ ≤
      ((2:ℝ)^p)⁻¹*R^(500*sig) := by
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hpow : (2:ℝ)^a ≤ (2:ℝ)^g := pow_le_pow_right₀ (by norm_num) hag
  have htube : ((d+1:ℝ)/(2:ℝ)^g)*δ ≤ ((d+1:ℝ)*Ccap/(2:ℝ)^p)*R^(10*sig) := by
    calc
      _ ≤ ((d+1:ℝ)/(2:ℝ)^g)*(Ccap*(2:ℝ)^a/(2:ℝ)^p*R^(10*sig)) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = (((d+1:ℝ)*Ccap/(2:ℝ)^p)*R^(10*sig))*((2:ℝ)^a/(2:ℝ)^g) := by ring
      _ ≤ (((d+1:ℝ)*Ccap/(2:ℝ)^p)*R^(10*sig))*1 :=
        mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr hpow) (by positivity)
      _ = _ := mul_one _
  have h10 : R^(10*sig) ≤ R^(30*sig) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  calc
    _ ≤ 2*(((2:ℝ)^p)⁻¹*R^(30*sig))+2*(((d+1:ℝ)*Ccap/(2:ℝ)^p)*R^(10*sig)) := by
      linarith
    _ ≤ 2*(((2:ℝ)^p)⁻¹*R^(30*sig))+2*(((d+1:ℝ)*Ccap/(2:ℝ)^p)*R^(30*sig)) := by
      gcongr
    _ = (2+2*(d+1:ℝ)*Ccap)/(2:ℝ)^p*R^(30*sig) := by ring
    _ ≤ R^(470*sig)/(2:ℝ)^p*R^(30*sig) := by gcongr
    _ = ((2:ℝ)^p)⁻¹*(R^(470*sig)*R^(30*sig)) := by ring
    _ = _ := by rw [← Real.rpow_add hRp]; congr 2; ring

lemma graph_testWidth_lower {N J i p : ℕ} {sig : ℝ} (hJ : 0 < J) (hi : i ≤ J) :
    ((2:ℝ)^p)⁻¹*((2:ℝ)^N)^(500*sig) ≤ testWidth N J i p sig := by
  have hc : 1 ≤ (2:ℝ)-(i:ℝ)/J := by
    have hdiv : (i:ℝ)/(J:ℝ) ≤ 1 :=
      (div_le_one (Nat.cast_pos.mpr hJ)).mpr (by exact_mod_cast hi)
    linarith
  rw [testWidth,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  calc
    _ = 1*(((2:ℝ)^p)⁻¹*((2:ℝ)^N)^(500*sig)) := by ring
    _ ≤ ((2:ℝ)-(i:ℝ)/J)*(((2:ℝ)^p)⁻¹*((2:ℝ)^N)^(500*sig)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

noncomputable def graphCapScale (N a p : ℕ) (c₀ sig : ℝ) : ℝ :=
  min c₀ ((2:ℝ)^(-((p:ℝ)-a))*((2:ℝ)^N)^(10*sig))
noncomputable def graphTolerance (N p : ℕ) (sig : ℝ) : ℝ :=
  (2:ℝ)^(-(p:ℝ))*((2:ℝ)^N)^(30*sig)

lemma graphCapScale_le {N a p : ℕ} {c₀ sig : ℝ} :
    graphCapScale N a p c₀ sig ≤ (2:ℝ)^a/(2:ℝ)^p*((2:ℝ)^N)^(10*sig) := by
  unfold graphCapScale
  rw [neg_sub,Real.rpow_sub (by norm_num),Real.rpow_natCast,Real.rpow_natCast]
  exact min_le_right _ _

lemma graphCapScale_nonneg {N a p : ℕ} {c₀ sig : ℝ} (hc₀ : 0 ≤ c₀) :
    0 ≤ graphCapScale N a p c₀ sig := by
  unfold graphCapScale
  exact le_min hc₀ (by positivity)

lemma graphTolerance_eq (N p : ℕ) (sig : ℝ) :
    graphTolerance N p sig = ((2:ℝ)^p)⁻¹*((2:ℝ)^N)^(30*sig) := by
  simp only [graphTolerance,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]

end CurrentFalconer.TreeND
end
end

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma graph_eventually_large {sig : ℝ} (hsig : 0 < sig) (Ccap : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (9:ℝ)^d ≤ ((2:ℝ)^N)^sig ∧
      2+2*(d+1:ℝ)*Ccap ≤ ((2:ℝ)^N)^(470*sig) := by
  have hpow : Filter.Tendsto (fun N : ℕ => (2:ℝ)^N) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h₁ := ((tendsto_rpow_atTop hsig).comp hpow).eventually
    (Filter.eventually_ge_atTop ((9:ℝ)^d))
  have h₂ := ((tendsto_rpow_atTop (by positivity : 0 < 470*sig)).comp hpow).eventually
    (Filter.eventually_ge_atTop (2+2*(d+1:ℝ)*Ccap))
  exact Filter.eventually_atTop.mp (h₁.and h₂)

lemma graph_source_degree_scale_absorb (A₁ A₂ : ℕ → ℝ)
    {N a g₁ g₂ p : ℕ} {sig C : ℝ} (hsig : 0 ≤ sig)
    (hag₁ : a ≤ g₁) (hag₂ : a ≤ g₂) (hg₁p : g₁ ≤ p) (hg₂p : g₂ ≤ p)
    (hanchor₁ : (g₁:ℝ) ≤ (a:ℝ)+2*sig*N)
    (hanchor₂ : (g₂:ℝ) ≤ (a:ℝ)+2*sig*N)
    (hlarge : (9:ℝ)^d ≤ ((2:ℝ)^N)^sig) :
    graphDegreeBound d a g₁ g₂ p (graphTolerance N p sig)
      (((2:ℝ)^N)^(height A₁ g₁ p+C*sig))
      (((2:ℝ)^N)^(height A₂ g₂ p+C*sig)) ≤
      ((2:ℝ)^N)^(min (height A₁ a p) (height A₂ a p)+(C+32*(d:ℝ)+1)*sig) := by
  rw [graphTolerance_eq]
  calc
    _ ≤ (9:ℝ)^d * ((2:ℝ)^N)^(min (height A₁ a p) (height A₂ a p)+(C+32*(d:ℝ))*sig) :=
      graphDegreeBound_source_scale A₁ A₂ hsig hag₁ hag₂ hg₁p hg₂p hanchor₁ hanchor₂
    _ ≤ ((2:ℝ)^N)^sig * ((2:ℝ)^N)^(min (height A₁ a p) (height A₂ a p)+(C+32*(d:ℝ))*sig) :=
      mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
      congr 1
      ring

lemma graph_source_width {N J i a g p : ℕ} {sig c₀ Ccap : ℝ}
    (hsig : 0 ≤ sig) (hCcap : 0 ≤ Ccap) (hag : a ≤ g) (hJ : 0 < J) (hi : i ≤ J)
    (hlarge : 2+2*(d+1:ℝ)*Ccap ≤ ((2:ℝ)^N)^(470*sig)) :
    2*graphTolerance N p sig +
      2*((d+1:ℝ)/(2:ℝ)^g)*(Ccap*graphCapScale N a p c₀ sig) ≤ testWidth N J i p sig := by
  rw [graphTolerance_eq]
  apply (graph_width_coverage (one_le_pow₀ (by norm_num)) hsig hCcap hag ?_ hlarge).trans
    (graph_testWidth_lower hJ hi)
  calc
    _ ≤ Ccap*((2:ℝ)^a/(2:ℝ)^p*((2:ℝ)^N)^(10*sig)) :=
      mul_le_mul_of_nonneg_left graphCapScale_le hCcap
    _ = _ := by ring

end CurrentFalconer.TreeND
end
end

end OAI
