import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.BagExtraction

namespace OAI

/-! Metric scale charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical

structure CompactPackage {n : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (X : Fin n → Doubled Coord → ℝ) where
  radius : ℝ
  diameter : ℝ
  family : CompactFamily X radius diameter

namespace CompactPackage
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}
def mass (F : CompactPackage X) : ℝ := F.radius*(∑D ∈ F.family.bags, (D.card : ℝ))

lemma finite_bound {k : ℕ} (hk : G.EdgeConnected k) (hX : ∀v, isProfile (X v))
    {q : ℕ} (F : Fin q → CompactPackage X)
    (hnext : ∀i j : Fin q, i.val+1=j.val → (F j).diameter ≤ (F i).radius/12) :
    (k:ℝ)/4*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  by_cases hq : q=0
  · subst q
    simp only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero]
    exact sum_nonneg (fun e _ => normDistance_nonneg _ _)
  · have hq' : 0 < q := Nat.pos_of_ne_zero hq
    let ind : ℕ → Fin q := fun i => ⟨i%q,Nat.mod_lt _ hq'⟩
    have hh := metric_compact_bound G hk X hX q
      (fun i => (F (ind i)).radius) (fun i => (F (ind i)).diameter)
      (fun i => (F (ind i)).family) (by
        intro i hi
        apply hnext
        simp only [ind,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (show i<q by omega)])
    have he : (∑i : Fin q, (F i).mass) = ∑i ∈ range q, (F (ind i)).mass := by
      rw [←Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i hi
      have hind : ind i.val=i := by apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt
      rw [hind]
    rw [he]
    exact hh

lemma ordered_bound {J : Type*} [LinearOrder J] {k : ℕ} (hk : G.EdgeConnected k) (hX : ∀v, isProfile (X v))
    (S : Finset J) (F : S → CompactPackage X)
    (hgeo : ∀i j : S, j.val < i.val → (F j).diameter ≤ (F i).radius/12) :
    (k:ℝ)/4*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let e := S.orderIsoOfFin rfl
  let f : Fin S.card ≃ S := Fin.revPerm.trans e.toEquiv
  have hh := finite_bound hk hX (fun i => F (f i)) (by
    intro i j hij
    apply hgeo
    change (e j.rev).val < (e i.rev).val
    exact e.strictMono (Fin.rev_lt_rev.mpr (show i<j by omega)))
  rw [f.sum_comp (fun i => (F i).mass)] at hh
  exact hh
end CompactPackage

variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

namespace AssignedBag
variable {δ η η' : ℝ}
def weaken (A : AssignedBag H G X δ η) (hη : η' ≤ η) : AssignedBag H G X δ η' :=
  { A with assignment := (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans A.assignment }
end AssignedBag

namespace AssignedFamily
variable {η η' : ℝ}
def weaken (F : AssignedFamily H G X η) (hη : η' ≤ η) : AssignedFamily H G X η' where
  radius := F.radius
  positive := F.positive
  count := F.count
  bag := fun i => (F.bag i).weaken hη
  owner_injective := F.owner_injective
  separated := F.separated
end AssignedFamily

namespace AssignedSequence
variable {η q ρ : ℝ}

lemma mass_eq (L : List (AssignedFamily H G X η)) : mass L = (L.map AssignedFamily.mass).sum := by
  induction L with
  | nil => rfl
  | cons F L ih => simpa only [mass,List.map_cons,List.sum_cons] using congrArg (F.mass+·) ih

lemma geometric_of_pairwise (hρ : 0 ≤ ρ) (L : List (AssignedFamily H G X η))
    (hL : L.Pairwise (fun F F' => F'.radius ≤ ρ*F.radius)) : GeometricAt ρ L := by
  induction L with
  | nil => trivial
  | cons F L ih =>
    refine ⟨?_,ih (List.pairwise_cons.mp hL).2⟩
    cases L with
    | nil => exact mul_nonneg hρ F.positive.le
    | cons F' L => exact (List.pairwise_cons.mp hL).1 F' (by simp)

lemma ratios_of_mem (L : List (AssignedFamily H G X (6144/q)))
    (hL : ∀F ∈ L, F.BoundaryRatio ρ) : Ratios ρ L := by
  induction L with
  | nil => trivial
  | cons F L ih => exact ⟨hL F (by simp),ih (fun F' hF' => hL F' (by simp [hF']))⟩

lemma fresh_of_pairwise (L : List (AssignedFamily H G X (6144/q)))
    (hL : L.Pairwise (fun F F' => Disjoint F.owners F'.owners))
    (E : Finset (Finset (Fin n))) (hE : ∀F ∈ L, Disjoint E F.owners) : Fresh E L := by
  induction L generalizing E with
  | nil => trivial
  | cons F L ih =>
    refine ⟨hE F (by simp),ih (List.pairwise_cons.mp hL).2 _ ?_⟩
    intro F' hF'
    exact disjoint_union_left.mpr ⟨hE F' (by simp [hF']), (List.pairwise_cons.mp hL).1 F' hF'⟩

lemma finite_bound (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    {r : ℕ} (F : Fin r → AssignedFamily H G X (6144/q))
    (hgeo : ∀i j, i<j → (F j).radius ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).BoundaryRatio ρ)
    (hdis : ∀i j, i<j → Disjoint (F i).owners (F j).owners) :
    (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  have hh := assigned_bound hX hq hconn hρ hρsmall (List.ofFn F)
    (geometric_of_pairwise hρ.le _ (List.pairwise_ofFn.mpr hgeo))
    (ratios_of_mem _ (by
      intro A hA
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
      exact hR i))
    (fresh_of_pairwise _ (List.pairwise_ofFn.mpr hdis) ∅ (by simp))
  rw [mass_eq,List.map_ofFn,List.sum_ofFn] at hh
  exact hh

lemma ordered_bound {J : Type*} [LinearOrder J] (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (S : Finset J) (F : S → AssignedFamily H G X (6144/q))
    (hgeo : ∀i j : S, j.val < i.val → (F j).radius ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).BoundaryRatio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let e := S.orderIsoOfFin rfl
  let f : Fin S.card ≃ S := Fin.revPerm.trans e.toEquiv
  have hh := finite_bound hX hq hconn hρ hρsmall (fun i => F (f i)) (by
    intro i j hij
    apply hgeo
    change (e j.rev).val < (e i.rev).val
    exact e.strictMono (Fin.rev_lt_rev.mpr hij))
    (fun i => hR (f i)) (fun i j hij => hdis _ _ (f.injective.ne hij.ne))
  rw [f.sum_comp (fun i => (F i).mass)] at hh
  exact hh
end AssignedSequence
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

abbrev CapturedFamily (H : Hierarchy n) (G : MultiGraph n m) (X : Fin n → Doubled Coord → ℝ) (η : ℝ) :=
  Sum (CompactPackage X) (AssignedFamily H G X η)

namespace CapturedFamily
variable {η : ℝ}
def radius : CapturedFamily H G X η → ℝ
  | .inl F => F.radius
  | .inr F => F.radius
def upper : CapturedFamily H G X η → ℝ
  | .inl F => F.diameter
  | .inr F => F.radius
def mass : CapturedFamily H G X η → ℝ
  | .inl F => F.mass
  | .inr F => F.mass
def owners : CapturedFamily H G X η → Finset (Finset (Fin n))
  | .inl _ => ∅
  | .inr F => F.owners

def Ratio {q : ℝ} (F : CapturedFamily H G X (6144/q)) (ρ : ℝ) : Prop :=
  match F with
  | .inl _ => True
  | .inr F => F.BoundaryRatio ρ

lemma mass_nonneg (F : CapturedFamily H G X η) : 0 ≤ F.mass := by
  cases F with
  | inl F => exact mul_nonneg F.family.radius_pos.le (sum_nonneg (fun D _ => Nat.cast_nonneg _))
  | inr F => exact mul_nonneg (sum_nonneg (fun i _ => Nat.cast_nonneg _)) F.positive.le

lemma mixed_bound {J : Type*} [LinearOrder J] {q : ℕ}
    (hq : 0 < q) (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q) {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (S : Finset J) (F : S → CapturedFamily H G X (6144/q))
    (hgeo : ∀i j : S, j.val < i.val → (F j).upper ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).Ratio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    ((q:ℝ)/8192)*(∑i, (F i).mass) ≤ 2*∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let C : Finset S := univ.filter (fun i => ∃P, F i=Sum.inl P)
  let A : Finset S := univ\C
  have hexC : ∀i : C, ∃P, F i.val=Sum.inl P := fun i => (mem_filter.mp i.property).2
  have hexA : ∀i : A, ∃P, F i.val=Sum.inr P := by
    intro i
    cases hh : F i.val with
    | inl P =>
      have hi : i.val ∉ C := (mem_sdiff.mp i.property).2
      exact (hi (mem_filter.mpr ⟨mem_univ _,⟨P,hh⟩⟩)).elim
    | inr P => exact ⟨P,rfl⟩
  let FC : C → CompactPackage X := fun i => Classical.choose (hexC i)
  let FA : A → AssignedFamily H G X (6144/q) := fun i => Classical.choose (hexA i)
  have hFC : ∀i : C, F i.val=Sum.inl (FC i) := fun i => Classical.choose_spec (hexC i)
  have hFA : ∀i : A, F i.val=Sum.inr (FA i) := fun i => Classical.choose_spec (hexA i)
  have hC := CompactPackage.ordered_bound hk hX C FC (by
    intro i j hij
    have hh := hgeo i.val j.val hij
    rw [hFC i,hFC j] at hh
    change (FC j).diameter ≤ ρ*(FC i).radius at hh
    have hr : ρ ≤ 1/12 := hρsmall.trans (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hr (FC i).family.radius_pos.le
    exact hh.trans (by nlinarith only [hm]))
  have hA := AssignedSequence.ordered_bound hX (show (0:ℝ)<q by exact_mod_cast hq)
    hconn hρ hρsmall A FA (by
      intro i j hij
      have hh := hgeo i.val j.val hij
      rw [hFA i,hFA j] at hh
      exact hh)
    (by intro i; have hh := hR i.val; rw [hFA i] at hh; exact hh)
    (by
      intro i j hij
      have hh := hdis i.val j.val (Subtype.val_injective.ne hij)
      rw [hFA i,hFA j] at hh
      exact hh)
  have hsumC : (∑i : C, (FC i).mass) = ∑i ∈ C, (F i).mass := by
    rw [←sum_coe_sort C (fun i => (F i).mass)]
    apply sum_congr rfl
    intro i hi
    rw [hFC i]
    rfl
  have hsumA : (∑i : A, (FA i).mass) = ∑i ∈ A, (F i).mass := by
    rw [←sum_coe_sort A (fun i => (F i).mass)]
    apply sum_congr rfl
    intro i hi
    rw [hFA i]
    rfl
  rw [hsumC] at hC
  rw [hsumA] at hA
  have hCn : 0 ≤ ∑i ∈ C, (F i).mass := sum_nonneg (fun i _ => mass_nonneg (F i))
  have hcoef : (q:ℝ)/8192 ≤ (q:ℝ)/4 := by
    have hh : (0:ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  have hC' := (mul_le_mul_of_nonneg_right hcoef hCn).trans hC
  have he : (∑i ∈ A, (F i).mass)+(∑i ∈ C, (F i).mass) = ∑i : S, (F i).mass :=
    sum_sdiff (subset_univ C)
  rw [←he,mul_add]
  linarith only [hA,hC']
end CapturedFamily
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}
namespace CapturedFamily
lemma scale_bound {q : ℕ} (hq : 0 < q) (hk : G.EdgeConnected q)
    (hX : ∀v, isProfile (X v)) (hconn : LocallyConnectedReal H G q)
    {ρ s : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536) (hs : 0 < s)
    {R : ℕ} (hR : 0 < R) (hlog : Real.logb 2 (24/(ρ*s^2)) < R)
    (S : Finset ℤ) (F : S → CapturedFamily H G X (6144/q))
    (hlow : ∀i : S, s*2^(i.val:ℝ) ≤ (F i).radius)
    (hupp : ∀i : S, (F i).upper ≤ 24*2^(i.val:ℝ)/s)
    (hratio : ∀i, (F i).Ratio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    ((q:ℝ)/8192)*(∑i, (F i).mass) ≤
      2*R*(∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let residue : ℤ → Fin R := fun i => ⟨(i%R).toNat, by
    have hn := Int.emod_nonneg i (show (R:ℤ)≠0 by omega)
    have hh := Int.emod_lt_of_pos i (show (0:ℤ)<R by omega)
    omega⟩
  let C : Fin R → Finset S := fun r => univ.filter (fun i => residue i.val=r)
  have hbound : ∀r : Fin R, ((q:ℝ)/8192)*(∑i ∈ C r, (F i).mass) ≤
      2*∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
    intro r
    have hh := mixed_bound hq hk hX hconn hρ hρsmall (C r) (fun i => F i.val) (by
      intro i j hij
      have hi := (mem_filter.mp i.property).2
      have hj := (mem_filter.mp j.property).2
      have hmod : j.val.val%R=i.val.val%R := by
        have he := congrArg Fin.val (hj.trans hi.symm)
        dsimp [residue] at he
        have hn1 := Int.emod_nonneg i.val.val (show (R:ℤ)≠0 by omega)
        have hn2 := Int.emod_nonneg j.val.val (show (R:ℤ)≠0 by omega)
        omega
      have hsep := ScaleSelection.separated_scales hs hρ hlog
        (ScaleSelection.residue_spacing hR hij hmod)
      exact (hupp j.val).trans (hsep.le.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hlow i.val) hρ.le)))
      (fun i => hratio i.val)
      (fun i j hij => hdis i.val j.val (Subtype.val_injective.ne hij))
    rw [←sum_coe_sort (C r) (fun i => (F i).mass)]
    exact hh
  have hh := sum_le_sum (s := univ) (fun r (_ : r ∈ univ) => hbound r)
  rw [←mul_sum] at hh
  have he : (∑r : Fin R, ∑i ∈ C r, (F i).mass) = ∑i : S, (F i).mass := by
    exact sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) (fun i => (F i).mass)
  rw [he] at hh
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_left_comm] using hh
end CapturedFamily
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma capturePackage (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ normDistance (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
    {q : ℕ} {ρ : ℝ}
    (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    ∃B : CapturedFamily H G X (6144/q), B.owners ⊆ T ∧ B.Ratio ρ ∧
      s*c₁ ≤ B.radius ∧ B.upper ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass := by
  obtain hC | hA := homogeneous_family T F Y hTne hT hroot hF hFn hα hγ he he1 hc₁ hc₂
    hcontract hpositive hmin hmax hdmin hdmax hbad hdom hsmall
  · obtain ⟨δ,Δ,B,hl,hu,hg⟩ := hC
    exact ⟨.inl ⟨δ,Δ,B⟩,empty_subset _,trivial,hl,hu,hg⟩
  · obtain ⟨B,hBT,hl,hu,hg⟩ := hA
    refine ⟨.inr (B.weaken hassign),hBT,?_,hl,hu,hg⟩
    intro i
    apply hratio
    apply hBT
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma homogeneous_scale_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q)
    (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (idx : Finset (Fin n) → ℤ) (off : Finset (Fin n) → Fin L)
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε ρ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, 2^(idx t:ℝ) ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*2^(idx t:ℝ))
    (hdmin : ∀t ∈ T, ∀e ∈ F t, 2^((idx t:ℝ)+(off t).val) ≤ normDistance (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ 4*2^((idx t:ℝ)+(off t).val))
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlog : Real.logb 2 (24/(ρ*(α*γ/32)^2)) < R) :
    let s := α*γ/32
    let W := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*(W/(L:ℝ)) ≤
      2*R*(∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let s := α*γ/32
  let w : Finset (Fin n) → ℝ := fun t =>
    (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/((parentBoundary H G t).card : ℝ)
  let c := s^ε/(6912*(1024/ε^2))
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨choice,hchoice⟩ := ScaleSelection.select_fibers T idx off w
  simp only [Fintype.card_fin] at hchoice
  let U := T.filter (fun t => off t=choice (idx t))
  let S := U.image idx
  let B : S → Finset (Finset (Fin n)) := fun i => U.filter (fun t => idx t=i.val)
  have hBT : ∀i : S, B i ⊆ T := fun i => (filter_subset _ _).trans (filter_subset _ _)
  have hBn : ∀i : S, (B i).Nonempty := by
    intro i
    obtain ⟨t,ht,heq⟩ := mem_image.mp i.property
    exact ⟨t,mem_filter.mpr ⟨ht,heq⟩⟩
  have hi : ∀i : S, ∀t ∈ B i, idx t=i.val := fun i t ht => (mem_filter.mp ht).2
  have hoff : ∀i : S, ∀t ∈ B i, off t=choice i.val := by
    intro i t ht
    have hh := (mem_filter.mp (mem_filter.mp ht).1).2
    change off t=choice (idx t) at hh
    rw [hi i t ht] at hh
    exact hh
  have hex : ∀i : S, ∃P : CapturedFamily H G X (6144/q),
      P.owners ⊆ B i ∧ P.Ratio ρ ∧ s*2^(i.val:ℝ) ≤ P.radius ∧
      P.upper ≤ 12*2^(i.val:ℝ)/s ∧ c*(∑t ∈ B i, w t) ≤ P.mass := by
    intro i
    have hp1 : (0:ℝ) < 2^(i.val:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hp2 : (0:ℝ) < 4*2^((i.val:ℝ)+(choice i.val).val) := by positivity
    obtain ⟨P,hP⟩ := capturePackage (B i) F Y (hBn i) ((hBT i).trans hT)
      (fun t ht => hroot t (hBT i ht)) (fun t ht => hF t (hBT i ht))
      (fun t ht => hFn t (hBT i ht)) hα hγ he he1 hp1 hp2 hcontract hpositive
      (by intro t ht e he; simpa only [hi i t ht] using hmin t (hBT i ht) e he)
      (by intro t ht e he; simpa only [hi i t ht] using hmax t (hBT i ht) e he)
      (by
        intro t ht e he
        have hh := hdmin t (hBT i ht) e he
        rw [hi i t ht,hoff i t ht] at hh
        simpa only [mul_div_cancel_left₀ _ (by norm_num : (4:ℝ)≠0)] using hh)
      (by intro t ht e he; simpa only [hi i t ht,hoff i t ht] using hdmax t (hBT i ht) e he)
      (fun t ht => hbad t (hBT i ht)) (fun t ht => hdom t (hBT i ht)) hsmall hassign
      (fun t ht => hratio t (hBT i ht))
    refine ⟨P,hP.1,hP.2.1,hP.2.2.1,hP.2.2.2.1,?_⟩
    simpa only [c,w,div_mul_eq_mul_div] using hP.2.2.2.2
  let P : S → CapturedFamily H G X (6144/q) := fun i => Classical.choose (hex i)
  have hP := fun i => Classical.choose_spec (hex i)
  have hbound := CapturedFamily.scale_bound hq hk hX hconn hρ hρsmall hs hR hlog S P
    (fun i => (hP i).2.2.1)
    (by
      intro i
      apply (hP i).2.2.2.1.trans
      apply div_le_div_of_nonneg_right _ hs.le
      exact mul_le_mul_of_nonneg_right (by norm_num : (12:ℝ)≤24) (Real.rpow_nonneg (by norm_num) _))
    (fun i => (hP i).2.1)
    (by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro t hti htj
      have he := (hi i t ((hP i).1 hti)).symm.trans (hi j t ((hP j).1 htj))
      exact hij (Subtype.ext he))
  have hfiber : (∑i : S, ∑t ∈ B i, w t) = ∑t ∈ U, w t := by
    rw [sum_coe_sort S (fun i => ∑t ∈ U.filter (fun t => idx t=i), w t)]
    exact sum_fiberwise_of_maps_to (fun t ht => mem_image_of_mem idx ht) w
  have hsum : c*(∑t ∈ U, w t) ≤ ∑i : S, (P i).mass := by
    have hh := sum_le_sum (s := univ) (fun i (_ : i ∈ univ) => (hP i).2.2.2.2)
    rw [←mul_sum,hfiber] at hh
    exact hh
  have hgain := (mul_le_mul_of_nonneg_left hchoice hc).trans hsum
  have hq0 : 0 ≤ (q:ℝ)/8192 := by positivity
  have hh := (mul_le_mul_of_nonneg_left hgain hq0).trans hbound
  simpa only [mul_assoc] using hh
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
