import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Finite submodular covers and tile entropy summation. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open PolynomialPEPS.PinnedEntropy

open scoped BigOperators
namespace PolynomialPEPS.SubvolumeTiling
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

def unionTiles (C : ι → Finset α) (s : Finset ι) : Finset α := s.biUnion C

omit [DecidableEq ι] in
@[simp] theorem unionTiles_empty (C : ι → Finset α) : unionTiles C ∅=∅ := by simp [unionTiles]
@[simp] theorem unionTiles_insert (C : ι → Finset α) (i : ι) (s : Finset ι) :
    unionTiles C (insert i s)=C i ∪ unionTiles C s := by simp [unionTiles]

omit [DecidableEq ι] in
theorem subset_unionTiles (C : ι → Finset α) (s : Finset ι) (i : ι) (hi : i∈s) :
    C i ⊆ unionTiles C s := Finset.subset_biUnion_of_mem C hi

omit [DecidableEq ι] in
theorem unionTiles_mono (C : ι → Finset α) {s t : Finset ι} (hst : s ⊆ t) :
    unionTiles C s ⊆ unionTiles C t := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨i,hst hi,hx⟩

omit [DecidableEq ι] in
theorem disjoint_unionTiles (C : ι → Finset α) (s : Finset ι) (i : ι)
    (hd : ∀ j∈s, Disjoint (C i) (C j)) : Disjoint (C i) (unionTiles C s) := by
  simp only [unionTiles,Finset.disjoint_biUnion_right]
  exact hd

theorem condition_on_past (S : Finset α → ℝ)
    (hssa : ∀ C X Y, C ⊆ X → X ⊆ Y → S Y-S (Y\C) ≤ S X-S (X\C))
    (C Y B : Finset α) (hCY : C ⊆ Y) (hY : Y\C ⊆ B) (hCB : Disjoint C B) :
    S (B∪C)-S B ≤ S Y-S (Y\C) := by
  have hsub : Y ⊆ B∪C := by
    intro x hx
    by_cases hc : x∈C
    · exact Finset.mem_union_right B hc
    · exact Finset.mem_union_left C (hY (Finset.mem_sdiff.mpr ⟨hx,hc⟩))
  have hdiff : (B∪C)\C=B := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · tauto
    · intro hx
      exact ⟨Or.inl hx,fun hc => Finset.disjoint_left.mp hCB hc hx⟩
  simpa only [hdiff] using hssa C Y (B∪C) hCY hsub

theorem selected_tiles (S : Finset α → ℝ)
    (hssa : ∀ C X Y, C ⊆ X → X ⊆ Y → S Y-S (Y\C) ≤ S X-S (X\C))
    (C Y : ι → Finset α) (B : Finset α) (s : Finset ι)
    (hCY : ∀ i∈s, C i ⊆ Y i) (hY : ∀ i∈s, Y i\C i ⊆ B)
    (hB : ∀ i∈s, Disjoint (C i) B)
    (hdis : (s : Set ι).Pairwise (fun i j => Disjoint (C i) (C j))) :
    S (B∪unionTiles C s) ≤ S B + ∑ i∈s, (S (Y i)-S (Y i\C i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : s ⊆ insert i s := Finset.subset_insert _ _
    have hd : Disjoint (C i) (unionTiles C s) := disjoint_unionTiles C s i
      (fun j hj => hdis (by simp) (Finset.mem_insert_of_mem hj) (by intro h; subst j; exact hi hj))
    have hstep := condition_on_past S hssa (C i) (Y i) (B∪unionTiles C s)
      (hCY i (by simp))
      ((hY i (by simp)).trans Finset.subset_union_left)
      (Finset.disjoint_union_right.mpr ⟨hB i (by simp),hd⟩)
    have hind := ih (fun j hj => hCY j (hs hj)) (fun j hj => hY j (hs hj))
      (fun j hj => hB j (hs hj)) (hdis.mono hs)
    rw [unionTiles_insert,Finset.sum_insert hi]
    have he : B∪(C i∪unionTiles C s)=(B∪unionTiles C s)∪C i := by
      ext x; simp only [Finset.mem_union]; tauto
    rw [he]
    linarith only [hstep,hind]

theorem tiles_subadditive (S : Finset α → ℝ) (hzero : S ∅=0)
    (hssa : ∀ C X Y, C ⊆ X → X ⊆ Y → S Y-S (Y\C) ≤ S X-S (X\C))
    (C : ι → Finset α) (s : Finset ι)
    (hdis : (s : Set ι).Pairwise (fun i j => Disjoint (C i) (C j))) :
    S (unionTiles C s) ≤ ∑ i∈s, S (C i) := by
  have h := selected_tiles S hssa C C ∅ s (fun _ _ => Finset.Subset.refl _)
    (by intro i hi; simp) (by intro i hi; simp) hdis
  simpa only [Finset.empty_union,Finset.sdiff_self,hzero,sub_zero,zero_add] using h

end PolynomialPEPS.SubvolumeTiling

namespace PolynomialPEPS.SubvolumeTiling
open scoped BigOperators
variable {α ι κ : Type*} [DecidableEq α] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem selected_color (S : Finset α → ℝ) (hzero : S ∅=0)
    (hssa : ∀ C X Y, C ⊆ X → X ⊆ Y → S Y-S (Y\C) ≤ S X-S (X\C))
    (C Y : ι → Finset α) (s g : Finset ι) (hg : g ⊆ s)
    (hdis : (s : Set ι).Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCY : ∀ i∈g, C i ⊆ Y i)
    (hY : ∀ i∈g, Y i\C i ⊆ unionTiles C (s\g))
    (b : ℝ) (hc : ∀ i∈g, S (Y i)-S (Y i\C i) ≤ S (C i)/4+b) :
    S (unionTiles C s) ≤ (∑ i∈s, S (C i))-(3/4)*(∑ i∈g, S (C i))+(g.card:ℝ)*b := by
  have hB : ∀ i∈g, Disjoint (C i) (unionTiles C (s\g)) := by
    intro i hi
    apply disjoint_unionTiles
    intro j hj
    exact hdis (hg hi) (Finset.mem_sdiff.mp hj).1 (by
      intro he; subst j; exact (Finset.mem_sdiff.mp hj).2 hi)
  have hs := selected_tiles S hssa C Y (unionTiles C (s\g)) g hCY hY hB (hdis.mono hg)
  have he : unionTiles C (s\g)∪unionTiles C g=unionTiles C s := by
    simp only [unionTiles,← Finset.union_biUnion,Finset.sdiff_union_of_subset hg]
  rw [he] at hs
  have hb := tiles_subadditive S hzero hssa C (s\g) (hdis.mono Finset.sdiff_subset)
  have hsum := Finset.sum_le_sum (fun i hi => hc i hi)
  simp only [Finset.sum_add_distrib,← Finset.sum_div,Finset.sum_const,nsmul_eq_mul] at hsum
  have hsplit : (∑ i∈s\g,S (C i))+(∑ i∈g,S (C i))=∑ i∈s,S (C i) :=
    Finset.sum_sdiff hg
  linarith only [hs,hb,hsum,hsplit]

theorem color_average (S : Finset α → ℝ) (hzero : S ∅=0)
    (hssa : ∀ C X Y, C ⊆ X → X ⊆ Y → S Y-S (Y\C) ≤ S X-S (X\C))
    (C Y : ι → Finset α) (s interior : Finset ι) (hi : interior ⊆ s)
    (color : ι → κ)
    (hdis : (s : Set ι).Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCY : ∀ i∈interior, C i ⊆ Y i)
    (hY : ∀ k : κ, ∀ i∈interior, color i=k →
      Y i\C i ⊆ unionTiles C (s\interior.filter (fun j => color j=k)))
    (b : ℝ) (hc : ∀ i∈interior, S (Y i)-S (Y i\C i) ≤ S (C i)/4+b) :
    (Fintype.card κ:ℝ)*S (unionTiles C s) ≤
      (Fintype.card κ:ℝ)*(∑ i∈s,S (C i))-(3/4)*(∑ i∈interior,S (C i))+
        (interior.card:ℝ)*b := by
  have h (k : κ) := selected_color S hzero hssa C Y s (interior.filter (fun j => color j=k))
    (Finset.filter_subset _ _ |>.trans hi) hdis
    (fun i hi' => hCY i (Finset.mem_filter.mp hi').1)
    (fun i hi' => hY k i (Finset.mem_filter.mp hi').1 (Finset.mem_filter.mp hi').2)
    b (fun i hi' => hc i (Finset.mem_filter.mp hi').1)
  have hf (f : ι → ℝ) : (∑ k : κ, ∑ i∈interior.filter (fun j => color j=k),f i)=
      ∑ i∈interior,f i := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hcard : (∑ k : κ, ((interior.filter (fun j => color j=k)).card:ℝ))=(interior.card:ℝ) := by
    simpa only [Finset.sum_const,one_mul,nsmul_eq_mul,mul_one] using hf (fun _ => 1)
  have hh := Finset.sum_le_sum (fun k (_ :k∈(Finset.univ : Finset κ)) => h k)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    ← Finset.sum_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hf,hcard] at hh
  exact hh

theorem color_recurrence [Nonempty κ] (S : Finset α → ℝ) (hzero : S ∅=0)
    (hssa : ∀ C X Y, C ⊆ X → X ⊆ Y → S Y-S (Y\C) ≤ S X-S (X\C))
    (C Y : ι → Finset α) (s interior : Finset ι) (hi : interior ⊆ s)
    (color : ι → κ)
    (hdis : (s : Set ι).Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCY : ∀ i∈interior, C i ⊆ Y i)
    (hY : ∀ k : κ, ∀ i∈interior, color i=k →
      Y i\C i ⊆ unionTiles C (s\interior.filter (fun j => color j=k)))
    (b F : ℝ) (hc : ∀ i∈interior, S (Y i)-S (Y i\C i) ≤ S (C i)/4+b)
    (hF : ∀ i∈s, S (C i) ≤ F) :
    S (unionTiles C s) ≤
      ((s.card:ℝ)-3/(4*(Fintype.card κ:ℝ))*(interior.card:ℝ))*F+
        (interior.card:ℝ)*b/(Fintype.card κ:ℝ) := by
  let K : ℝ := Fintype.card κ
  have hK : 1≤K := by
    have hh : 1≤Fintype.card κ := Fintype.card_pos
    change (1:ℝ)≤(Fintype.card κ:ℝ)
    exact_mod_cast hh
  have hK0 : 0<K := lt_of_lt_of_le zero_lt_one hK
  have hh := color_average S hzero hssa C Y s interior hi color hdis hCY hY b hc
  have hsplit : (∑ i∈s\interior,S (C i))+(∑ i∈interior,S (C i))=∑ i∈s,S (C i) :=
    Finset.sum_sdiff hi
  have hcard : ((s\interior).card:ℝ)+(interior.card:ℝ)=(s.card:ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hi
  have hbd : (∑ i∈s\interior,S (C i)) ≤ ((s\interior).card:ℝ)*F := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      Finset.sum_le_sum (fun i hi' => hF i (Finset.mem_sdiff.mp hi').1)
  have hin : (∑ i∈interior,S (C i)) ≤ (interior.card:ℝ)*F := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      Finset.sum_le_sum (fun i hi' => hF i (hi hi'))
  have h1 := mul_le_mul_of_nonneg_left hbd (le_of_lt hK0)
  have h2 := mul_le_mul_of_nonneg_left hin (show 0≤K-3/4 by linarith)
  change K*_ ≤ K*_-(3/4)*_+_ at hh
  apply (mul_le_mul_iff_right₀ hK0).mp ?_
  have he : K*(((s.card:ℝ)-3/(4*K)*(interior.card:ℝ))*F+
      (interior.card:ℝ)*b/K) =
      K*((s.card:ℝ)*F)-(3/4)*((interior.card:ℝ)*F)+(interior.card:ℝ)*b := by
    field_simp
  rw [he]
  rw [← hsplit] at hh
  rw [← hcard]
  linarith only [hh,h1,h2]

end PolynomialPEPS.SubvolumeTiling

end

end OAI
