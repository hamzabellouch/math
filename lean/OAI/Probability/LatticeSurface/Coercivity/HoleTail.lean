import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters

namespace OAI

noncomputable section

open scoped BigOperators

open Set MeasureTheory

namespace SparseHoles

open MeasureTheory

def badGraph (A B : Finset Vertex) : SimpleGraph A where
  Adj x y := star.Adj x.val y.val ∧ x.val∈B ∧ y.val∈B
  symm := ⟨by intro x y h;exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro x h;exact h.1.1 rfl⟩

noncomputable def holes (B : Finset Vertex) (lo hi : Vertex) : Finset (Finset Vertex) :=
  outerHulls (badClusters B) lo hi

end SparseHoles

namespace SparseHoles

open MeasureTheory

attribute [local instance] Classical.propDecidable

lemma star_offset {x y : Vertex} (h : star.Adj x y) : y-x∈offsets8 := by
  have hh := h.symm
  have hsmall {a : ℤ} (h : a.natAbs ≤ 1) : a∈({-1,0,1}:Finset ℤ) := by
    have hh : a.natAbs=0 ∨ a.natAbs=1 := by omega
    rcases hh with hh|hh
    · have he := Int.natAbs_eq_zero.mp hh;simp [he]
    · rcases Int.natAbs_eq_iff.mp hh with hh|hh <;> simp [hh]
  simp only [offsets8,Finset.mem_erase,Finset.mem_product]
  exact ⟨fun he => hh.1 (sub_eq_zero.mp he),hsmall hh.2.1,hsmall hh.2.2⟩

lemma finite_star_degree (A : Finset Vertex) (x : A) :
    (Finset.univ.filter ((star.induce (A:Set Vertex)).Adj x)).card ≤ 8 := by
  classical
  let S := Finset.univ.filter ((star.induce (A:Set Vertex)).Adj x)
  let f : S → offsets8 := fun y => ⟨y.val.val-x.val,star_offset (Finset.mem_filter.mp y.property).2⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    apply Subtype.ext
    exact sub_left_inj.mp (congrArg Subtype.val he)
  exact (Finset.card_le_card_of_injective hf).trans_eq offsets8_card

lemma cluster_component_bound (A B C : Finset Vertex) (hCB : C ⊆ B) (hBA : B ⊆ A)
    (hC : (star.induce (C:Set Vertex)).Connected) (c : Vertex) (hc : c∈C) :
    C.card ≤ (SparseClusters.component (badGraph A B) ⟨c,hBA (hCB hc)⟩).card := by
  classical
  let inc : star.induce (C:Set Vertex) →g badGraph A B :=
    ⟨fun x => ⟨x.val,hBA (hCB x.property)⟩,by intro x y h; exact ⟨h,hCB x.property,hCB y.property⟩⟩
  let f : C → SparseClusters.component (badGraph A B) ⟨c,hBA (hCB hc)⟩ :=
    fun x => ⟨inc x,(SparseClusters.mem_component _ _ _).mpr ((hC ⟨c,hc⟩ x).map inc)⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z => z.val.val) he)
  exact Finset.card_le_card_of_injective hf

lemma large_diameter_witness (A B : Finset Vertex) (lo hi : Vertex)
    (hBA : B ⊆ A) (hbox : A ⊆ box lo hi) (z : Vertex) (r : ℕ)
    (hd : 2*r+2 ≤ siteDiameter (holes B lo hi) z) :
    ∃ k : ℕ, ∃ c : A, c.val∈offsetBox z (r+k+2) ∧
      r+k+1 ≤ (SparseClusters.component (badGraph A B) c).card := by
  classical
  have hL : (holes B lo hi).Nonempty := by
    by_contra he
    have hz : siteDiameter (holes B lo hi) z=0 := by simp [siteDiameter,Finset.not_nonempty_iff_eq_empty.mp he]
    omega
  obtain ⟨H,hH,heq⟩ := Finset.exists_mem_eq_sup (s := holes B lo hi)
    (f := fun H => if incidentClosed H z then diameter H else 0) hL
  have hhd : 2*r+2 ≤ if incidentClosed H z then diameter H else 0 := by
    rw [← heq]
    exact hd
  have hz : incidentClosed H z := by
    by_contra h; rw [ite_eq_right h] at hhd;omega
  rw [ite_eq_left hz] at hhd
  obtain ⟨C,hC,hCH⟩ := outer_origin (badClusters B) lo hi hH
  obtain ⟨x,hx,hxC⟩ := Finset.mem_image.mp hC
  have hCB : C ⊆ B := by rw [← hxC];exact badCluster_subset B x
  have hconn : (star.induce (C:Set Vertex)).Connected := by rw [← hxC];exact badCluster_connected B x
  have hCbox : C ⊆ box lo hi := hCB.trans (hBA.trans hbox)
  have hne : C.Nonempty := ⟨x.val,by rw [← hxC];exact badCluster_self B x⟩
  have hdiam := filled_diameter_le C lo hi hCbox hne hconn
  rw [hCH] at hdiam
  have hr : r+1 ≤ C.card := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨c,hc⟩ := hne
  have hcball := incident_filled_location C lo hi hCbox hconn hc (hCH.symm ▸ hz)
  have hcomp := cluster_component_bound A B C hCB hBA hconn c hc
  refine ⟨k,⟨c,hBA (hCB hc)⟩,?_,?_⟩
  · simpa only [hk,show r+1+k+1=r+k+2 by omega] using hcball
  · omega

end SparseHoles

namespace SparseHoles

open MeasureTheory

attribute [local instance] Classical.propDecidable

lemma ambient_component_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Finset Vertex) (B : Ω → Finset Vertex)
    (hsparse : ∀ S : Finset Vertex, μ {ω | S ⊆ B ω} ≤ (1/1024:ENNReal)^S.card)
    (c : A) (m : ℕ) :
    μ {ω | m+1 ≤ (SparseClusters.component (badGraph A (B ω)) c).card} ≤ (1/16:ENNReal)^m := by
  classical
  by_cases hm : m=0
  · simp only [hm,pow_zero];exact prob_le_one
  have hs (S : Finset A) : μ {ω | ∀ x∈S, x.val∈B ω} ≤ (1/1024:ENNReal)^S.card := by
    have he : {ω | ∀ x∈S, x.val∈B ω} = {ω | S.image Subtype.val ⊆ B ω} := by
      ext ω
      constructor
      · intro h y hy
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
        exact h x hx
      · intro h x hx
        exact h (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    rw [he]
    simpa only [Finset.card_image_of_injective S Subtype.val_injective] using hsparse (S.image Subtype.val)
  have ht := SparseClusters.sparse_component_tail μ (star.induce (A:Set Vertex)) 8
    (finite_star_degree A) (fun ω => badGraph A (B ω)) (fun ω => {x : A | x.val∈B ω})
    (by intro ω x y h;exact h.1) (by intro ω x y h;exact h.2)
    (1/1024) (by norm_num) hs c m (by omega)
  have he : (8:ENNReal)^2*(1/1024)=1/16 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  simpa only [Nat.cast_ofNat,he] using ht

lemma quadratic_le_geometric (n : ℕ) : (2*n+5)^2 ≤ 25*4^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      (2*(n+1)+5)^2 ≤ (2*(2*n+5))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4*(2*n+5)^2 := by ring
      _ ≤ 4*(25*4^n) := Nat.mul_le_mul_left 4 ih
      _ = 25*4^(n+1) := by rw [pow_succ];ring

lemma roots_card (A : Finset Vertex) (z : Vertex) (n : ℕ) :
    (Finset.univ.filter fun c : A => c.val∈offsetBox z (n+2)).card ≤ 25*4^n := by
  classical
  let S := Finset.univ.filter fun c : A => c.val∈offsetBox z (n+2)
  have hs : S.image Subtype.val ⊆ offsetBox z (n+2) := by
    intro c hc;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp hx).2
  calc
    S.card = (S.image Subtype.val).card := (Finset.card_image_of_injective S Subtype.val_injective).symm
    _ ≤ (offsetBox z (n+2)).card := Finset.card_le_card hs
    _ = (2*n+5)^2 := by rw [offsetBox_card];congr 1
    _ ≤ _ := quadratic_le_geometric n

lemma hole_diameter_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Finset Vertex) (B : Ω → Finset Vertex) (lo hi : Vertex)
    (hBA : ∀ ω, B ω ⊆ A) (hbox : A ⊆ box lo hi)
    (hsparse : ∀ S : Finset Vertex, μ {ω | S ⊆ B ω} ≤ (1/1024:ENNReal)^S.card)
    (z : Vertex) (r : ℕ) :
    μ {ω | 2*r+2 ≤ siteDiameter (holes (B ω) lo hi) z} ≤ 100*(1/4:ENNReal)^r := by
  classical
  let S (k : ℕ) := Finset.univ.filter fun c : A => c.val∈offsetBox z (r+k+2)
  let E (k : ℕ) (c : A) := {ω | r+k+1 ≤ (SparseClusters.component (badGraph A (B ω)) c).card}
  have hsub : {ω | 2*r+2 ≤ siteDiameter (holes (B ω) lo hi) z} ⊆ ⋃ k, ⋃ c∈S k, E k c := by
    intro ω hω
    obtain ⟨k,c,hc,hh⟩ := large_diameter_witness A (B ω) lo hi (hBA ω) hbox z r hω
    exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨by simpa [S] using hc,hh⟩⟩⟩
  have hEk (k : ℕ) : μ (⋃ c∈S k,E k c) ≤ 25*(1/4:ENNReal)^(r+k) := by
    calc
      _ ≤ ∑ c∈S k,μ (E k c) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _c∈S k,(1/16:ENNReal)^(r+k) := Finset.sum_le_sum fun c hc => ambient_component_tail μ A B hsparse c (r+k)
      _ = ((S k).card:ENNReal)*(1/16:ENNReal)^(r+k) := by simp
      _ ≤ (25*4^(r+k):ℕ)*(1/16:ENNReal)^(r+k) := by
        gcongr
        exact roots_card A z (r+k)
      _ = 25*(1/4:ENNReal)^(r+k) := by
        have he : (4:ENNReal)*(1/16)=1/4 := by
          apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
          norm_num
        push_cast
        rw [mul_assoc,← mul_pow,he]
  calc
    _ ≤ μ (⋃ k, ⋃ c∈S k,E k c) := measure_mono hsub
    _ ≤ ∑' k, μ (⋃ c∈S k,E k c) := measure_iUnion_le _
    _ ≤ ∑' k,25*(1/4:ENNReal)^(r+k) := ENNReal.tsum_le_tsum hEk
    _ = 25*(1/4:ENNReal)^r*∑' k,(1/4:ENNReal)^k := by
      simp only [pow_add,← mul_assoc,ENNReal.tsum_mul_left]
    _ = 25*(1/4:ENNReal)^r*(1-(1/4:ENNReal))⁻¹ := by rw [ENNReal.tsum_geometric]
    _ ≤ 100*(1/4:ENNReal)^r := by
      rw [mul_right_comm]
      gcongr
      have hn : (1-(1/4:ENNReal)) ≠ 0 := by
        rw [ne_eq,tsub_eq_zero_iff_le]
        norm_num [ENNReal.le_inv_iff_mul_le]
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_sub_of_le (by norm_num : (1/4:ENNReal)≤1)]

end SparseHoles

end

end OAI
