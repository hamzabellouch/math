import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.NormalClosureGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma quotient_word_lower (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)] (n : ℕ) :
    n+1 ≤ ((S^n).image (QuotientGroup.mk' H)).card := by
  let q := QuotientGroup.mk' H
  have hq1 : (1:A ⧸ H)∈S.image q := Finset.mem_image.mpr ⟨1,h1,map_one q⟩
  have hqgen : Subgroup.closure (S.image q : Set (A ⧸ H))=⊤ := by
    rw [Finset.coe_image,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective H)
  have hinf : (Subgroup.closure (S.image q : Set (A ⧸ H)) : Set (A ⧸ H)).Infinite := by
    rw [hqgen,Subgroup.coe_top]
    exact Set.infinite_univ
  rw [Finset.image_pow]
  exact Finset.add_one_le_card_pow hq1 hinf n

lemma subgroup_linear_packing (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)]
    (T : Finset H) (L : ℕ) (hT : T.image H.subtype ⊆ S^L) (n : ℕ) :
    (T^n).card*(n+1) ≤ (S^((L+1)*n)).card := by
  have hTin : (T^n).image H.subtype ⊆ (S^(L*n)).filter (fun a => a∈H) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_filter.mpr ⟨?_,b.property⟩
    have he : (b : A)∈(T.image H.subtype)^n := by
      rw [←Finset.image_pow]
      exact Finset.mem_image.mpr ⟨b,hb,rfl⟩
    rw [pow_mul]
    exact Finset.pow_subset_pow_left hT he
  calc
    _ = (n+1)*((T^n).image H.subtype).card := by
      rw [Finset.card_image_of_injective _ H.subtype_injective,Nat.mul_comm]
    _ ≤ ((S^n).image (QuotientGroup.mk' H)).card *
        ((S^(L*n)).filter (fun a => a∈H)).card :=
      Nat.mul_le_mul (quotient_word_lower S h1 hgen H n) (Finset.card_le_card hTin)
    _ ≤ (S^(n+L*n)).card := Finset.card_pow_quotient_mul_pow_inter_subgroup_le
    _ = (S^((L+1)*n)).card := by congr 2; ring

theorem subgroup_degree_descent (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)]
    (T : Finset H) (L : ℕ) (hT : T.image H.subtype ⊆ S^L)
    (d : ℕ) (hg : HasDegree S (d+1)) : HasDegree T d := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨C*(2*(L+1))^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hL : 0<L+1 := by omega
  have hnr : (L+1)*n≤r := by
    simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hrn : r≤(2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hL
    change r<(L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1)≤(2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : (T^n).card*n ≤ (C*(2*(L+1))^(d+1)*n^d)*n := by
    calc
      _ ≤ (T^n).card*(n+1) := Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ ≤ (S^((L+1)*n)).card := subgroup_linear_packing S h1 hgen H T L hT n
      _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*(L+1))*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = (C*(2*(L+1))^(d+1)*n^d)*n := by rw [mul_pow,pow_succ n]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hb (by omega : 0<n)

theorem HasPolynomialDegree.normalClosure_descent {d : ℕ}
    (h : HasPolynomialDegree A (d+1)) (F : Finset A)
    [Infinite (A ⧸ Subgroup.normalClosure (F : Set A))] :
    HasPolynomialDegree (Subgroup.normalClosure (F : Set A)) d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff (d+1)).mp h
  let H := Subgroup.normalClosure (F : Set A)
  let _ : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr
    (normalClosure_fg_of_sparse_growth S F h1 hs hgen (d+1) hg)
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := H)
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hs hgen (T.image H.subtype)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    subgroup_degree_descent S h1 hgen H T L hL d hg⟩

theorem HasPolynomialDegree.normal_subgroup_descent {d : ℕ}
    (h : HasPolynomialDegree A (d+1)) (H : Subgroup A) [H.Normal]
    [Infinite (A ⧸ H)] [Group.FG H] : HasPolynomialDegree H d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff (d+1)).mp h
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := H)
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hs hgen (T.image H.subtype)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    subgroup_degree_descent S h1 hgen H T L hL d hg⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
