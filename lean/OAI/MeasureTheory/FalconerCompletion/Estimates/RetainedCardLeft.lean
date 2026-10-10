import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.TestedCellFamily

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma retained_card_left (S T : Finset (CellPath d)) {p : ℕ}
    (hT : T ⊆ dyadicPaths p)
    (v w x y : EuclideanSpace ℝ (Fin d)) {τ : ℝ}
    (hw : ‖w‖=1) (hτ : 0 ≤ τ) :
    ((retainedPairs S T v w x y τ).card : ℝ) ≤
      ((S.filter fun P => ‖graphPerpND v (treeCenter P-x)‖ ≤ τ).card : ℝ) *
        (4*(2:ℝ)^p*τ+5)^d := by
  classical
  let E := retainedPairs S T v w x y τ
  let F := S.filter fun P => ‖graphPerpND v (treeCenter P-x)‖ ≤ τ
  have hEF : ∀ z ∈ E, z.1 ∈ F := by
    intro z hz
    obtain ⟨hzST,h₁,h₂,h₃⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hzST).1,h₁⟩
  have hfiber : ∀ P ∈ F, (((E.filter fun z => z.1=P).card) : ℝ) ≤
      (4*(2:ℝ)^p*τ+5)^d := by
    intro P _hP
    let E₀ := E.filter fun z => z.1=P
    let T₀ := E₀.image Prod.snd
    have hinj : Set.InjOn Prod.snd (↑E₀ : Set (CellPath d × CellPath d)) := by
      intro z hz z' hz' he
      apply Prod.ext
      · exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm
      · exact he
    have hdepth : T₀ ⊆ dyadicPaths p := by
      intro Q hQ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hQ
      exact hT (Finset.mem_product.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp hz).1).1).2
    have hball : ∀ Q ∈ T₀, dist (treeCenter Q)
        (y-(inner ℝ (treeCenter P-x) v) • w) ≤ 2*τ := by
      intro Q hQ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hzE,hzP⟩ := Finset.mem_filter.mp hz
      obtain ⟨_,_,hperp,hscalar⟩ := Finset.mem_filter.mp hzE
      rw [hzP] at hscalar
      exact graph_scalar_perp_ballND w y (treeCenter z.2) hw hperp hscalar
    calc
      _ = (T₀.card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
      _ ≤ (2*(2:ℝ)^p*(2*τ)+5)^d :=
        treeCenter_ball_card T₀ hdepth _ (by positivity) hball
      _ = _ := by ring
  have he : (E.card : ℝ) = ∑ P ∈ F, (((E.filter fun z => z.1=P).card) : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hEF
  calc
    _ = ∑ P ∈ F, (((E.filter fun z => z.1=P).card) : ℝ) := he
    _ ≤ ∑ _P ∈ F, (4*(2:ℝ)^p*τ+5)^d := Finset.sum_le_sum hfiber
    _ = _ := by simp [F]

lemma retained_card_swap (S T : Finset (CellPath d))
    (v w x y : EuclideanSpace ℝ (Fin d)) (τ : ℝ) :
    (retainedPairs S T v w x y τ).card = (retainedPairs T S w v y x τ).card := by
  classical
  have he : retainedPairs S T v w x y τ =
      (retainedPairs T S w v y x τ).image Prod.swap := by
    ext z
    constructor
    · intro hz
      rcases z with ⟨P,Q⟩
      obtain ⟨hST,hv,hw,hs⟩ := Finset.mem_filter.mp hz
      obtain ⟨hP,hQ⟩ := Finset.mem_product.mp hST
      refine Finset.mem_image.mpr ⟨(Q,P), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hQ,hP⟩,hw,hv,?_⟩
      exact (congrArg (fun t : ℝ => |t|) (_root_.add_comm _ _)).trans_le hs
    · intro hz
      obtain ⟨⟨Q,P⟩,hmem,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hTS,hw,hv,hs⟩ := Finset.mem_filter.mp hmem
      obtain ⟨hQ,hP⟩ := Finset.mem_product.mp hTS
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hP,hQ⟩,hv,hw,?_⟩
      exact (congrArg (fun t : ℝ => |t|) (_root_.add_comm _ _)).trans_le hs
  rw [he,Finset.card_image_of_injective]
  exact Prod.swap_injective

theorem retained_degree : RetainedDegreeTarget := by
  intro d ρ₁ ρ₂ a g₁ g₂ p X Y S T v w x y δ τ W₁ W₂ K₁ K₂
    hag₁ hag₂ hg₁p hg₂p hv hw hδ hτ hK₁ hK₂ hW₁ hW₂ hS hT
  have hpos : 0 ≤ (4*(2:ℝ)^p*τ+5)^d := by positivity
  have h₁ := (retained_card_left S T hT.1 v w x y hw hτ).trans
    (mul_le_mul_of_nonneg_right
      (graph_candidates_card ρ₁ hag₁ hg₁p X S v x hv hδ hK₁ hW₁ hS) hpos)
  have h₂ := (retained_card_left T S hS.1 w v y x hv hτ).trans
    (mul_le_mul_of_nonneg_right
      (graph_candidates_card ρ₂ hag₂ hg₂p Y T w y hw hδ hK₂ hW₂ hT) hpos)
  rw [← retained_card_swap S T v w x y τ] at h₂
  rw [min_mul_of_nonneg _ _ hpos]
  exact le_min h₁ h₂

end CurrentFalconer.TreeND
end
end

end OAI
