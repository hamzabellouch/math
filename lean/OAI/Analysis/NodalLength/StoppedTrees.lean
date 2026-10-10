import OAI.Analysis.NodalLength.Descent

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory

namespace SharpNodal.Descent

structure Label where
  mass : ℝ
  tilt : Plane
  floor : ℝ

inductive Tree (ι : Type*) where
  | stop (root : Label)
  | step (root : Label) (children : ι → Tree ι)

namespace Tree
variable {ι : Type*} [Fintype ι]

def root : Tree ι → Label
  | .stop a => a
  | .step a _ => a

def massCost : Tree ι → ℝ
  | .stop a => a.mass
  | .step a t => a.mass + 𝔼 i, massCost (t i)

def tiltCost : Tree ι → ℝ
  | .stop _ => 0
  | .step a t => 𝔼 i, (‖(root (t i)).tilt-a.tilt‖+tiltCost (t i))

def floorCost : Tree ι → ℝ
  | .stop _ => 0
  | .step a t => a.floor + 𝔼 i, floorCost (t i)

def Valid (C : ℝ) : Tree ι → Prop
  | .stop a => 0 ≤ a.mass ∧ 0 ≤ a.floor
  | .step a t => 0 ≤ a.mass ∧ 0 ≤ a.floor ∧
      (𝔼 i, (root (t i)).mass) ≤ (a.mass+a.floor)/2 ∧
      (𝔼 i, ‖(root (t i)).tilt-a.tilt‖) ≤ C*(a.mass+a.floor) ∧
      ∀i, Valid C (t i)

lemma mass_nonneg {C : ℝ} {t : Tree ι} (h : Valid C t) : 0 ≤ t.root.mass := by
  cases t <;> exact h.1

lemma floor_nonneg {C : ℝ} {t : Tree ι} (h : Valid C t) : 0 ≤ t.root.floor := by
  cases t with
  | stop a => exact h.2
  | step a t => exact h.2.1

lemma cost_nonneg {C : ℝ} {t : Tree ι} (h : Valid C t) :
    0 ≤ t.massCost ∧ 0 ≤ t.tiltCost ∧ 0 ≤ t.floorCost := by
  induction t with
  | stop a => exact ⟨h.1,le_rfl,le_rfl⟩
  | step a t ih =>
    refine ⟨add_nonneg h.1 (Finset.expect_nonneg (fun i _ =>(ih i (h.2.2.2.2 i)).1)),?_,?_⟩
    · exact Finset.expect_nonneg (fun i _ =>add_nonneg (norm_nonneg _) (ih i (h.2.2.2.2 i)).2.1)
    · exact add_nonneg h.2.1 (Finset.expect_nonneg (fun i _ =>(ih i (h.2.2.2.2 i)).2.2))

theorem stopped_descent {C : ℝ} (hC : 0 ≤ C) {t : Tree ι} (h : Valid C t) :
    t.massCost ≤ 2*t.root.mass+t.floorCost ∧
    t.tiltCost ≤ 2*C*t.root.mass+2*C*t.floorCost := by
  induction t with
  | stop a =>
    dsimp [massCost,tiltCost,floorCost,root]
    constructor
    · linarith [h.1]
    · have hm := h.1
      positivity
  | step a t ih =>
    have hm := Finset.expect_le_expect (fun i (_ : i∈(Finset.univ : Finset ι)) =>
      (ih i (h.2.2.2.2 i)).1)
    have ht := Finset.expect_le_expect (fun i (_ : i∈(Finset.univ : Finset ι)) =>
      (ih i (h.2.2.2.2 i)).2)
    simp only [Finset.expect_add_distrib,← Finset.mul_expect] at hm ht
    have hs := h.2.2.1
    have hi := h.2.2.2.1
    change a.mass + (𝔼 i, massCost (t i)) ≤ 2*a.mass+(a.floor+(𝔼 i, floorCost (t i))) ∧
      (𝔼 i, (‖(root (t i)).tilt-a.tilt‖+tiltCost (t i))) ≤
        2*C*a.mass+2*C*(a.floor+(𝔼 i, floorCost (t i)))
    rw [Finset.expect_add_distrib]
    constructor
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hC)]

lemma stopped_total_cost {C F : ℝ} (hC : 0 ≤ C) {t : Tree ι} (h : Valid C t)
    (hF : t.floorCost ≤ F) :
    t.massCost+t.tiltCost ≤ 2*(1+C)*t.root.mass+(1+2*C)*F := by
  obtain ⟨hm,ht⟩ := stopped_descent hC h
  nlinarith [mul_le_mul_of_nonneg_left hF (by positivity : (0:ℝ)≤1+2*C)]

lemma stopped_total_uniform {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    {t : Tree ι} (h : Valid C t) (hfloor : t.floorCost ≤ F) :
    t.massCost+t.tiltCost ≤ (2*(1+C)+(1+2*C)*F)*(t.root.mass+1) := by
  have hh := stopped_total_cost hC h hfloor
  have hm := mass_nonneg h
  nlinarith [mul_nonneg (mul_nonneg (show 0≤1+2*C by positivity) hF) hm]

end Tree
end SharpNodal.Descent

noncomputable section
open scoped BigOperators
namespace SharpNodal.Descent.Tree
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def goodProb (P : Label → Prop) [DecidablePred P] : Tree ι → ℝ
  | .stop a => if P a then 1 else 0
  | .step a t => if P a then 𝔼 i, goodProb P (t i) else 0

lemma goodProb_bounds (P : Label → Prop) [DecidablePred P] (t : Tree ι) :
    0≤goodProb P t ∧ goodProb P t≤1 := by
  induction t with
  | stop a => simp only [goodProb]; split <;> norm_num
  | step a t ih =>
    simp only [goodProb]
    split
    · exact ⟨Finset.expect_nonneg (fun i _ =>(ih i).1),
        Finset.expect_le Finset.univ_nonempty (fun i _ =>(ih i).2)⟩
    · norm_num

theorem failure_cost {C δ : ℝ} (_hδ : 0<δ) (b₀ : Plane) {t : Tree ι}
    (h : Valid C t) :
    δ*(1-goodProb (fun a => a.mass<δ ∧ ‖a.tilt-b₀‖<δ) t) ≤
      t.massCost+t.tiltCost+‖t.root.tilt-b₀‖ := by
  classical
  induction t with
  | stop a =>
    change δ*(1-(if a.mass<δ ∧ ‖a.tilt-b₀‖<δ then 1 else 0)) ≤ a.mass+0+‖a.tilt-b₀‖
    split
    · have hm := h.1
      simp only [sub_self,mul_zero,add_zero]
      positivity
    · rename_i hn
      push Not at hn
      have hn' : δ≤a.mass ∨ δ≤‖a.tilt-b₀‖ := by
        by_cases hm : δ≤a.mass
        · exact Or.inl hm
        · exact Or.inr (hn (lt_of_not_ge hm))
      simp only [sub_zero,mul_one,add_zero]
      rcases hn' with hh|hh <;> linarith [h.1,norm_nonneg (a.tilt-b₀)]
  | step a t ih =>
    change δ*(1-(if a.mass<δ ∧ ‖a.tilt-b₀‖<δ then
      𝔼 i, goodProb (fun a => a.mass<δ ∧ ‖a.tilt-b₀‖<δ) (t i) else 0)) ≤ _
    split
    · have hb (i : ι) := ih i (h.2.2.2.2 i)
      have hn (i : ι) : ‖(t i).root.tilt-b₀‖ ≤ ‖(t i).root.tilt-a.tilt‖+‖a.tilt-b₀‖ :=
        calc
          _ = ‖((t i).root.tilt-a.tilt)+(a.tilt-b₀)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have hh := Finset.expect_le_expect (s:=Finset.univ) (fun i _ =>
        show δ*(1-goodProb (fun a => a.mass<δ ∧ ‖a.tilt-b₀‖<δ) (t i)) ≤
          (t i).massCost+(t i).tiltCost+(‖(t i).root.tilt-a.tilt‖+‖a.tilt-b₀‖) by
            linarith [hb i,hn i])
      simp only [mul_sub,Finset.expect_sub_distrib,Finset.expect_add_distrib,
        ←Finset.mul_expect,Fintype.expect_const] at hh
      change _ ≤ a.mass+(𝔼 i, massCost (t i))+
        (𝔼 i, (‖(t i).root.tilt-a.tilt‖+tiltCost (t i)))+‖a.tilt-b₀‖
      rw [Finset.expect_add_distrib]
      linarith [h.1]
    · rename_i hn
      push Not at hn
      have hn' : δ≤a.mass ∨ δ≤‖a.tilt-b₀‖ := by
        by_cases hm : δ≤a.mass
        · exact Or.inl hm
        · exact Or.inr (hn (lt_of_not_ge hm))
      have hc := cost_nonneg h
      have hm : a.mass ≤ massCost (Tree.step a t) := by
        change a.mass≤a.mass+(𝔼 i, massCost (t i))
        exact le_add_of_nonneg_right (Finset.expect_nonneg (fun i _ =>(cost_nonneg (h.2.2.2.2 i)).1))
      change δ*(1-0) ≤ _
      simp only [sub_zero,mul_one]
      change _ ≤ _+_+‖a.tilt-b₀‖
      rcases hn' with hh|hh <;> linarith [norm_nonneg (a.tilt-b₀)]

theorem stable_probability {C F γ B σ : ℝ} (hC : 0≤C) (hF : 0≤F)
    (hγ : 0<γ) (hB : 0<B) (hσ : 0≤σ) {t : Tree ι} (h : Valid C t)
    (hfloor : t.floorCost≤F) (hm : t.root.mass≤σ*B)
    (hsmall : (2*(1+C)+(1+2*C)*F)*(σ+1/B)≤γ/4) :
    (3:ℝ)/4 ≤ goodProb (fun a => a.mass<γ*B ∧ ‖a.tilt-t.root.tilt‖<γ*B) t := by
  classical
  have hc := stopped_total_uniform hC hF h hfloor
  have hf := failure_cost (mul_pos hγ hB) t.root.tilt h
  rw [sub_self,norm_zero,add_zero] at hf
  have hCt : 0≤2*(1+C)+(1+2*C)*F := by positivity
  have hh := mul_le_mul_of_nonneg_left hm hCt
  have hs := mul_le_mul_of_nonneg_right hsmall hB.le
  have hs' : (2*(1+C)+(1+2*C)*F)*(σ*B+1)≤γ/4*B := by
    calc
      _ = (2*(1+C)+(1+2*C)*F)*(σ+1/B)*B := by field_simp
      _ ≤ _ := hs
  have hpos : 0<γ*B := mul_pos hγ hB
  nlinarith only [hc,hf,hh,hs',hpos]

end SharpNodal.Descent.Tree

end
end

end OAI
