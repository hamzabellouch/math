import Mathlib
import OAI.Geometry.Cannon.Boundary.WordBall

namespace OAI

section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
namespace CannonRelease
open CannonGraph CannonVisual Set

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

lemma relative_polynomial_packing :
    ∃ (Q : ℕ) (C : ℝ), 2 ≤ Q ∧ 0 < C ∧
      ∀ (x : Boundary D) (r s : ℝ), 0 < s → s ≤ r → r ≤ 1 →
      ∀ t : Finset (Boundary D),
      (∀ y ∈ t, boundaryDist D hδ x y ≤ r) →
      (∀ y ∈ t, ∀ z ∈ t, y ≠ z → s ≤ boundaryDist D hδ y z) →
      (t.card : ℝ) ≤ C*(r/s)^Q := by
  classical
  let _ := visualMetricSpace D hδ
  let L := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hL : 1 ≤ L := by
    have : 1 ≤ Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)) :=
      Real.one_le_exp (mul_nonneg (visualExponent_pos δ).le (Nat.cast_nonneg _))
    dsimp [L]; linarith
  have hA : 1 ≤ A := Real.one_le_exp (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hLA : 1 ≤ L*A := by nlinarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hApos : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨Q,hQ,hbound⟩ := global_polynomial_packing D hδ
  let B : ℝ := D.generators.card+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨Q,B*(L*A)^Q,hQ,mul_pos hB (pow_pos (mul_pos hLpos hApos) Q),?_⟩
  intro x r s hs hsr hr t ht hsep
  have hrpos : 0 < r := hs.trans_le hsr
  let e := s/(r*(L*A))
  have he : 0 < e := div_pos hs (mul_pos hrpos (mul_pos hLpos hApos))
  have he₁ : e ≤ 1 := (div_le_one (by positivity)).mpr
    (hsr.trans (le_mul_of_one_le_right hrpos.le hLA))
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hrpos hr
  obtain ⟨r₀,hr₀⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryTranslate D ⟨δ,hδ⟩ (r₀.val k)⁻¹
  have hinj : Function.Injective f := (boundaryHomeomorph D ⟨δ,hδ⟩ (r₀.val k)⁻¹).injective
  have himage := hbound e he he₁ (t.image f) (by
    intro y hy z hz hyz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have huv : u ≠ v := fun heq => hyz (congrArg f heq)
    have hh := (visual_ball_expansion D hδ r₀ k u v ((ht u hu).trans hk) ((ht v hv).trans hk)).2
    change boundaryDist D hδ u v ≤ L*boundaryDist D hδ (f u) (f v)*visualScale δ k at hh
    have hn : 0 ≤ boundaryDist D hδ (f u) (f v) := dist_nonneg
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hk' (mul_nonneg hLpos.le hn))
    apply (div_le_iff₀ (mul_pos hrpos (mul_pos hLpos hApos))).mpr
    calc
      s ≤ boundaryDist D hδ u v := hsep u hu v hv huv
      _ ≤ L*boundaryDist D hδ (f u) (f v)*(A*r) := hh'
      _ = boundaryDist D hδ (f u) (f v)*(r*(L*A)) := by ring)
  rw [Finset.card_image_of_injective t hinj] at himage
  convert himage using 1
  dsimp [e,B]
  rw [one_div_div]
  have hh : r*(L*A)/s = (L*A)*(r/s) := by ring
  rw [hh,mul_pow]
  ring

end CannonRelease

end
end
end
end
section
section
noncomputable section
open Set Metric

namespace CannonPacking

variable {X : Type*} [MetricSpace X]

def PolynomialPacking (Q : ℕ) (C : ℝ) : Prop :=
  ∀ (x : X) (r s : ℝ), 0 < s → s ≤ r → r ≤ 1 →
    ∀ t : Finset X, (∀ y ∈ t, dist x y ≤ r) →
      (∀ y ∈ t, ∀ z ∈ t, y ≠ z → s ≤ dist y z) →
      (t.card : ℝ) ≤ C*(r/s)^Q

lemma indexed_packing {ι : Type*} (Q : ℕ) (C : ℝ)
    (hp : PolynomialPacking (X := X) Q C) (q : ι → X) (S : Finset ι)
    (x : X) (r s : ℝ) (hs : 0 < s) (hsr : s ≤ r) (hr : r ≤ 1)
    (hball : ∀ i ∈ S, dist x (q i) ≤ r)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → s ≤ dist (q i) (q j)) :
    (S.card : ℝ) ≤ C*(r/s)^Q := by
  classical
  have hinj : Set.InjOn q (S : Set ι) := by
    intro i hi j hj heq
    by_contra hne
    have hh := hsep i hi j hj hne
    rw [heq, dist_self] at hh
    exact (not_le_of_gt hs) hh
  have hh := hp x r s hs hsr hr (S.image q) (by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hball i hi) (by
    intro y hy z hz hyz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact hsep i hi j hj (fun heq => hyz (congrArg q heq)))
  rwa [Finset.card_image_of_injOn hinj] at hh

theorem exists_overlap_bound (Q : ℕ) (C A b : ℝ)
    (hp : PolynomialPacking (X := X) Q C) (_hC : 0 ≤ C)
    (hA : 0 < A) (hb : 0 < b) :
    ∃ B : ℕ, ∀ {ι : Type*} (q : ι → X) (S : Finset ι) (x : X) (r : ℝ),
      0 < r → max A b*r ≤ 1 →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → b*r ≤ dist (q i) (q j)) →
      (S.filter (fun i => dist x (q i) ≤ A*r)).card ≤ B := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_ge (C*(max A b/b)^Q)
  refine ⟨B, ?_⟩
  intro ι q S x r hr hscale hsep
  have hAb : 0 < max A b := hA.trans_le (le_max_left ..)
  have hh := indexed_packing Q C hp q (S.filter (fun i => dist x (q i) ≤ A*r))
    x (max A b*r) (b*r) (mul_pos hb hr)
    (mul_le_mul_of_nonneg_right (le_max_right ..) hr.le) hscale (by
      intro i hi
      exact (Finset.mem_filter.mp hi).2 |>.trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) hr.le)) (by
      intro i hi j hj hij
      exact hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
  have heq : max A b*r/(b*r) = max A b/b := by field_simp
  rw [heq] at hh
  exact_mod_cast hh.trans hB

end CannonPacking

end
end
section
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace CannonNet

variable {X : Type*} [MetricSpace X]

theorem exists_finite_separated_net (A : Set X) (hA : TotallyBounded A)
    (r : ℝ) (hr : 0 < r) :
    ∃ T : Finset X, (↑T : Set X) ⊆ A ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → r ≤ dist x y) ∧
      (∀ x ∈ A, ∃ y ∈ T, dist x y ≤ r) := by
  classical
  let ε : ℝ≥0 := ⟨r,hr.le⟩
  have hε : ε / 2 ≠ 0 := div_ne_zero (by
    intro he
    exact hr.ne' (congrArg (fun x : ℝ≥0 => (x : ℝ)) he)) (by norm_num)
  obtain ⟨C,_,hCf,hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded hε hA
  have hfinite : Metric.packingNumber ε A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCf)
    calc
      Metric.packingNumber ε A = Metric.packingNumber (2*(ε/2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε/2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ C.encard := hcover.externalCoveringNumber_le_encard
  let T := Metric.maximalSeparatedSet ε A
  have hTA : T ⊆ A := Metric.maximalSeparatedSet_subset
  have hTf : T.Finite := Set.encard_ne_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard ≠ ⊤
    rwa [Metric.encard_maximalSeparatedSet hfinite])
  have hsep : Metric.IsSeparated ε T := Metric.isSeparated_maximalSeparatedSet
  have htcover : Metric.IsCover ε A T := Metric.isCover_maximalSeparatedSet hfinite
  have hrr : (ε : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.coe_nnreal_eq ε
  refine ⟨hTf.toFinset,?_,?_,?_⟩
  · simpa using hTA
  · intro x hx y hy hxy
    have hh := hsep (by simpa using hx) (by simpa using hy) hxy
    rw [hrr, edist_dist] at hh
    exact le_of_not_gt (fun hh' => (not_lt_of_ge (ENNReal.ofReal_le_ofReal hh'.le)) hh)
  · intro x hx
    obtain ⟨y,hy,hd⟩ := htcover hx
    refine ⟨y,by simpa using hy,?_⟩
    change edist x y ≤ (ε : ℝ≥0∞) at hd
    rw [hrr, edist_dist] at hd
    exact (ENNReal.ofReal_le_ofReal_iff hr.le).mp hd

theorem exists_compact_net [CompactSpace X] (r : ℝ) (hr : 0 < r) :
    ∃ T : Finset X,
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → r ≤ dist x y) ∧
      (∀ x : X, ∃ y ∈ T, dist x y ≤ r) ∧
      (∀ x : X, ∃ y ∈ T, x ∈ Metric.ball y (2*r)) := by
  obtain ⟨T,_,hsep,hcover⟩ := exists_finite_separated_net (univ : Set X) isCompact_univ.totallyBounded r hr
  refine ⟨T,hsep,fun x => hcover x (mem_univ x),?_⟩
  intro x
  obtain ⟨y,hy,hd⟩ := hcover x (mem_univ x)
  exact ⟨y,hy,show dist x y < 2*r by linarith⟩

end CannonNet

end
end
end
end
end
end
end

end OAI
