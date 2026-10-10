import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

noncomputable def representative (H : Finset Vertex) : Vertex := by
  classical
  let S : Finset (Lex Vertex) := (rimFin H).image toLex
  exact if h : S.Nonempty then ofLex (S.min' h) else (0,0)

noncomputable def fillSite (L : Finset (Finset Vertex)) (z : Vertex) : Vertex := by
  classical
  exact if h : ∃ H∈L, z∈H then representative h.choose else z

noncomputable def extension (L : Finset (Finset Vertex)) (u : Vertex → ℝ) : Vertex → ℝ :=
  fun z => u (fillSite L z)

structure HoleFamily (L : Finset (Finset Vertex)) : Prop where
  nonempty : ∀ H∈L, H.Nonempty
  disjoint : ∀ H∈L, ∀ K∈L, H≠K → Disjoint H K
  separated : ∀ H∈L, ∀ K∈L, H≠K → ∀ x∈H, ∀ y∈K, ¬grid.Adj x y
  rim_good : ∀ H∈L, ∀ K∈L, Disjoint (rim H) (K:Set Vertex)
  paths : ∀ H∈L, ∀ x∈rim H, ∀ y∈rim H, ∃ w : (rimNet H).Walk x y,
    (∀ z∈w.support, z∈rim H) ∧ w.length ≤ 8*H.card

noncomputable def siteDiameter (L : Finset (Finset Vertex)) (z : Vertex) : ℕ := by
  classical
  exact L.sup (fun H => if incidentClosed H z then diameter H else 0)

noncomputable def edgeDiameter (L : Finset (Finset Vertex)) : Edge → ℕ :=
  Sym2.lift ⟨(fun x y => max (siteDiameter L x) (siteDiameter L y)),fun _ _ => max_comm _ _⟩

def goodSite (L : Finset (Finset Vertex)) (z : Vertex) : Prop := ∀ H∈L, z∉H

def goodEdge (L : Finset (Finset Vertex)) (e : Edge) : Prop :=
  e∈grid.edgeSet ∧ ∀ z∈e, goodSite L z

noncomputable def holeCost (p : ℝ) (H : Finset Vertex) : ℝ :=
  4*(H.card:ℝ)*(8*(H.card:ℝ))^(p-1)

noncomputable def holeWeights (L : Finset (Finset Vertex)) (p : ℝ) (e : Edge) : ℝ := by
  classical
  exact 1+∑ H∈L, if e∈rimEdges H then holeCost p H else 0

lemma representative_mem (H : Finset Vertex) (hne : H.Nonempty) : representative H∈rim H := by
  classical
  have hr : (rimFin H).Nonempty := by
    obtain ⟨x,hx⟩ := rim_nonempty H hne
    exact ⟨x,(mem_rimFin H x).mpr hx⟩
  have hs : ((rimFin H).image (toLex : Vertex → Lex Vertex)).Nonempty := hr.image _
  simp only [representative,dite_eq_left hs]
  have hm := Finset.min'_mem _ hs
  obtain ⟨x,hx,hx'⟩ := Finset.mem_image.mp hm
  rw [← hx']
  exact (mem_rimFin H x).mp hx

lemma fillSite_good (L : Finset (Finset Vertex)) {z : Vertex} (hz : goodSite L z) :
    fillSite L z=z := by
  classical
  have hh : ¬∃ H∈L, z∈H := by simpa only [not_exists,not_and] using (show ∀ H∈L, z∉H from hz)
  exact dite_eq_right hh

lemma fillSite_hole (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    {H : Finset Vertex} (hH : H∈L) {z : Vertex} (hz : z∈H) :
    fillSite L z=representative H := by
  classical
  have hh : ∃ K∈L, z∈K := ⟨H,hH,hz⟩
  simp only [fillSite,dite_eq_left hh]
  congr 1
  by_contra hne
  exact Finset.disjoint_left.mp (hL.disjoint hh.choose hh.choose_spec.1 H hH hne)
    hh.choose_spec.2 hz

lemma outer_hole_family (J : Finset (Finset Vertex)) (lo hi : Vertex)
    (hJ : ClusterFamily J lo hi) : HoleFamily (outerHulls J lo hi) := by
  have hg := outer_hull_geometry J lo hi hJ
  constructor
  · intro H hH
    obtain ⟨C,hC,rfl⟩ := outer_origin J lo hi hH
    exact (hJ.nonempty C hC).mono (subset_filled C lo hi (hJ.bounded C hC))
  · exact hg.2.1
  · intro H hH K hK hHK x hx y hy hxy
    exact (outer_separated J lo hi hJ hH hK hHK x hx y hy).2 (grid_le_star hxy)
  · exact hg.2.2.1
  · intro H hH
    exact (hg.2.2.2 H hH).2

lemma neighbor_of_hole_good (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    {H : Finset Vertex} (hH : H∈L) {x y : Vertex} (hx : x∈H) (hxy : grid.Adj x y)
    (hy : y∉H) : goodSite L y := by
  intro K hK hyK
  by_cases he : H=K
  · exact hy (he ▸ hyK)
  · exact hL.separated H hH K hK he x hx y hyK hxy

lemma incident_outside_rim (H : Finset Vertex) {x y : Vertex} (hx : x∈H)
    (hy : y∉H) (hxy : grid.Adj x y) : y∈rim H :=
  (mem_rim_iff_star H y).mpr ⟨hy,x,hx,grid_le_star hxy.symm⟩

lemma crossing_power (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) (p : ℝ) (hp : 1 ≤ p)
    {H : Finset Vertex} (hH : H∈L) {x y : Vertex} (hx : x∈H)
    (hy : y∉H) (hxy : grid.Adj x y) :
    |extension L u y-extension L u x|^p ≤
      (8*(H.card:ℝ))^(p-1)*∑ e∈rimEdges H, (edgeAbs u e)^p := by
  have hyg := neighbor_of_hole_good L hL hH hx hxy hy
  have hyR := incident_outside_rim H hx hy hxy
  obtain ⟨w,hw,hlen⟩ := hL.paths H hH (representative H)
    (representative_mem H (hL.nonempty H hH)) y hyR
  simp only [extension,fillSite_good L hyg,fillSite_hole L hL hH hx]
  exact rim_power H u p hp w hw hlen

lemma same_hole_edge (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) {H : Finset Vertex} (hH : H∈L) {x y : Vertex} (hx : x∈H) (hy : y∈H) :
    edgeAbs (extension L u) s(x,y)=0 := by
  simp [extension,fillSite_hole L hL hH hx,fillSite_hole L hL hH hy]

lemma rim_edge_good (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    {H : Finset Vertex} (hH : H∈L) {e : Edge} (he : e∈rimEdges H) : goodEdge L e := by
  have hh := (mem_rimEdges H e).mp he
  refine ⟨?_,fun z hz K hK hzK => Set.disjoint_left.mp (hL.rim_good H hH K hK) (hh.2 z hz) hzK⟩
  induction e using Sym2.inductionOn with
  | _ x y => exact hh.1.1

lemma diameter_le_site (L : Finset (Finset Vertex)) {H : Finset Vertex} (hH : H∈L)
    {z : Vertex} (hz : incidentClosed H z) : diameter H ≤ siteDiameter L z := by
  classical
  have hh := Finset.le_sup (f := fun H => if incidentClosed H z then diameter H else 0) hH
  simpa only [ite_eq_left hz,siteDiameter] using hh

lemma rim_diameter_le_edge (L : Finset (Finset Vertex)) {H : Finset Vertex} (hH : H∈L)
    {e : Edge} (he : e∈rimEdges H) : diameter H ≤ edgeDiameter L e := by
  have hh := (mem_rimEdges H e).mp he
  induction e using Sym2.inductionOn with
  | _ x y =>
    change diameter H ≤ max (siteDiameter L x) (siteDiameter L y)
    rcases hh.1.2 with hx|hy
    · exact (diameter_le_site L hH (Or.inr hx)).trans (le_max_left _ _)
    · exact (diameter_le_site L hH (Or.inr hy)).trans (le_max_right _ _)

lemma rim_overlap (L : Finset (Finset Vertex)) (hL : HoleFamily L) (e : Edge) :
    (L.filter (fun H => e∈rimEdges H)).card ≤ 8 := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    let S := L.filter (fun H => s(x,y)∈rimEdges H)
    have hex : ∀ H∈S, ∃ b∈H, b∈neighbors x ∪ neighbors y := by
      intro H hH
      have hh := (mem_rimEdges H s(x,y)).mp (Finset.mem_filter.mp hH).2
      rcases hh.1.2 with ⟨b,hb,hbx⟩|⟨b,hb,hby⟩
      · exact ⟨b,hb,Finset.mem_union_left _ ((mem_neighbors x b).mpr hbx.symm)⟩
      · exact ⟨b,hb,Finset.mem_union_right _ ((mem_neighbors y b).mpr hby.symm)⟩
    choose b hb hbN using hex
    let f : S → ↥(neighbors x ∪ neighbors y) := fun H => ⟨b H H.property,hbN H H.property⟩
    have hf : Function.Injective f := by
      intro H K he
      apply Subtype.ext
      by_contra hne
      have hv : b H H.property=b K K.property := congrArg Subtype.val he
      exact Finset.disjoint_left.mp (hL.disjoint H (Finset.mem_filter.mp H.property).1
        K (Finset.mem_filter.mp K.property).1 hne)
        (hb H H.property) (hv.symm ▸ hb K K.property)
    have hc := Finset.card_le_card_of_injective hf
    exact hc.trans ((Finset.card_union_le (s := neighbors x) (t := neighbors y)).trans (by have hx := neighbors_card x;have hy := neighbors_card y;omega))

lemma holeCost_nonneg (p : ℝ) (H : Finset Vertex) : 0 ≤ holeCost p H := by
  unfold holeCost
  positivity

lemma holeCost_bound (p : ℝ) (hp : 1 ≤ p) (H : Finset Vertex) (d : ℕ)
    (hd : diameter H ≤ d) :
    holeCost p H ≤ 16*32^(p-1)*(1+(d:ℝ))^(2*p) := by
  have ht : 0 < 1+(d:ℝ) := by positivity
  have hc0 : 0 ≤ (H.card:ℝ) := by positivity
  have hc : (H.card:ℝ) ≤ 4*(1+(d:ℝ))^2 := by
    have hdiam : (diameter H:ℝ) ≤ d := by exact_mod_cast hd
    have hh : (H.card:ℝ) ≤ (2*(diameter H:ℝ)+1)^2 := by exact_mod_cast card_le_diameter_sq H
    have hd0 : 0 ≤ (diameter H:ℝ) := by positivity
    nlinarith
  have hpow : (8*(H.card:ℝ))^(p-1) ≤ (32*(1+(d:ℝ))^2)^(p-1) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
  have hmul := mul_le_mul (show 4*(H.card:ℝ) ≤ 16*(1+(d:ℝ))^2 by nlinarith)
    hpow (by positivity) (by positivity)
  unfold holeCost
  refine hmul.trans_eq ?_
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 32) (sq_nonneg _)]
  have htwo : (1+(d:ℝ))^2=(1+(d:ℝ))^(2:ℝ) := by rw [Real.rpow_two]
  rw [htwo,← Real.rpow_mul ht.le]
  calc
    16*(1+(d:ℝ))^(2:ℝ)*(32^(p-1)*(1+(d:ℝ))^(2*(p-1))) =
        16*32^(p-1)*((1+(d:ℝ))^(2:ℝ)*(1+(d:ℝ))^(2*(p-1))) := by ring
    _ = _ := by rw [← Real.rpow_add ht];congr 2;ring

lemma weights_bound (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (p : ℝ) (hp : 1 ≤ p) (e : Edge) :
    1 ≤ holeWeights L p e ∧
      holeWeights L p e ≤ (1+128*32^(p-1))*(1+(edgeDiameter L e:ℝ))^(2*p) := by
  classical
  have hn (H : Finset Vertex) : 0 ≤ if e∈rimEdges H then holeCost p H else 0 := by
    split_ifs <;> [exact holeCost_nonneg p H;exact le_refl _]
  have h0 := Finset.sum_nonneg fun H (hH : H∈L) => hn H
  refine ⟨by unfold holeWeights;linarith,?_⟩
  let S := L.filter (fun H => e∈rimEdges H)
  let t : ℝ := (1+(edgeDiameter L e:ℝ))^(2*p)
  have ht : 1 ≤ t := Real.one_le_rpow (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith)
  have hs : ∑ H∈L, (if e∈rimEdges H then holeCost p H else 0) = ∑ H∈S, holeCost p H :=
    (Finset.sum_filter _ _).symm
  have hb : ∑ H∈S, holeCost p H ≤ (S.card:ℝ)*(16*32^(p-1)*t) := by
    calc
      _ ≤ ∑ H∈S, 16*32^(p-1)*t := Finset.sum_le_sum fun H hH =>
        holeCost_bound p hp H _ (rim_diameter_le_edge L (Finset.mem_filter.mp hH).1 (Finset.mem_filter.mp hH).2)
      _ = _ := by simp
  have hc : (S.card:ℝ) ≤ 8 := by exact_mod_cast rim_overlap L hL e
  have hscalar : 0 ≤ 16*32^(p-1)*t := by dsimp [t];positivity
  have hb' := hb.trans (mul_le_mul_of_nonneg_right hc hscalar)
  change 1+(∑ H∈L, if e∈rimEdges H then holeCost p H else 0) ≤ _
  rw [hs]
  change _ ≤ (1+128*32^(p-1))*t
  nlinarith

open Classical

lemma power_hole_edge_bound (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) (p : ℝ) (hp : 1 < p) {x y : Vertex} (hxy : grid.Adj x y)
    {H : Finset Vertex} (hH : H∈L) (hx : x∈H) :
    (edgeAbs (extension L u) s(x,y))^p ≤
      (if goodEdge L s(x,y) then (edgeAbs u s(x,y))^p else 0) +
      ∑ K∈L, if s(x,y)∈incidentEdges K then
        (8*(K.card:ℝ))^(p-1)*∑ e∈rimEdges K, (edgeAbs u e)^p else 0 := by
  classical
  have hgood : 0 ≤ if goodEdge L s(x,y) then (edgeAbs u s(x,y))^p else 0 := by
    split_ifs <;> [exact Real.rpow_nonneg (edgeAbs_nonneg _ _) _;rfl]
  have hn (K : Finset Vertex) : 0 ≤ if s(x,y)∈incidentEdges K then
      (8*(K.card:ℝ))^(p-1)*∑ e∈rimEdges K, (edgeAbs u e)^p else 0 := by
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg fun e he => Real.rpow_nonneg (edgeAbs_nonneg _ _) _)
    · rfl
  by_cases hy : y∈H
  · rw [same_hole_edge L hL u hH hx hy,Real.zero_rpow (by linarith : p≠0)]
    exact add_nonneg hgood (Finset.sum_nonneg fun K hK => hn K)
  · have he : s(x,y)∈incidentEdges H := (mem_incidentEdges H _).mpr ⟨hxy,x,hx,by simp⟩
    have hsum := Finset.single_le_sum (s := L) (f := fun K => if s(x,y)∈incidentEdges K then
        (8*(K.card:ℝ))^(p-1)*∑ e∈rimEdges K, (edgeAbs u e)^p else 0)
      (fun K hK => hn K) hH
    rw [ite_eq_left he] at hsum
    exact (crossing_power L hL u p hp.le hH hx hy hxy).trans (hsum.trans (le_add_of_nonneg_left hgood))

lemma edge_power_bound (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) (p : ℝ) (hp : 1 < p) (e : Edge) (he : e∈grid.edgeSet) :
    (edgeAbs (extension L u) e)^p ≤
      (if goodEdge L e then (edgeAbs u e)^p else 0) +
      ∑ H∈L, if e∈incidentEdges H then
        (8*(H.card:ℝ))^(p-1)*∑ f∈rimEdges H, (edgeAbs u f)^p else 0 := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    by_cases hx : goodSite L x
    · by_cases hy : goodSite L y
      · have hg : goodEdge L s(x,y) := ⟨he,by intro z hz;rcases Sym2.mem_iff.mp hz with rfl|rfl <;> assumption⟩
        rw [ite_eq_left hg]
        have hv : edgeAbs (extension L u) s(x,y)=edgeAbs u s(x,y) := by
          simp [extension,fillSite_good L hx,fillSite_good L hy]
        rw [hv]
        apply le_add_of_nonneg_right
        apply Finset.sum_nonneg
        intro H hH
        split_ifs
        · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg fun f hf => Real.rpow_nonneg (edgeAbs_nonneg _ _) _)
        · rfl
      · have hy' : ∃ H∈L, y∈H := by simpa only [goodSite,not_forall,not_not,exists_prop] using hy
        obtain ⟨H,hH,hyH⟩ := hy'
        simpa only [Sym2.eq_swap] using power_hole_edge_bound L hL u p hp (SimpleGraph.Adj.symm he) hH hyH
    · have hx' : ∃ H∈L, x∈H := by simpa only [goodSite,not_forall,not_not,exists_prop] using hx
      obtain ⟨H,hH,hxH⟩ := hx'
      exact power_hole_edge_bound L hL u p hp he hH hxH

lemma sum_incident_bound (H : Finset Vertex) (E : Finset Edge) (b : ℝ) (hb : 0 ≤ b) :
    (∑ e∈E, if e∈incidentEdges H then b else 0) ≤ 4*(H.card:ℝ)*b := by
  classical
  rw [← Finset.sum_filter]
  have hs : E.filter (fun e => e∈incidentEdges H) ⊆ incidentEdges H := by
    intro e he;exact (Finset.mem_filter.mp he).2
  have hc : ((E.filter (fun e => e∈incidentEdges H)).card:ℝ) ≤ 4*(H.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hs).trans (incidentEdges_card H)
  simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right hc hb

lemma extension_sum_bound (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) (p : ℝ) (hp : 1 < p) (E : Finset Edge)
    (hE : ∀ e∈E, e∈grid.edgeSet) :
    (∑ e∈E, (edgeAbs (extension L u) e)^p) ≤
      (∑ e∈E.filter (goodEdge L), (edgeAbs u e)^p) +
      ∑ H∈L, holeCost p H * ∑ e∈rimEdges H, (edgeAbs u e)^p := by
  classical
  calc
    _ ≤ ∑ e∈E, ((if goodEdge L e then (edgeAbs u e)^p else 0) +
        ∑ H∈L, if e∈incidentEdges H then
          (8*(H.card:ℝ))^(p-1)*∑ f∈rimEdges H, (edgeAbs u f)^p else 0) :=
      Finset.sum_le_sum fun e he => edge_power_bound L hL u p hp e (hE e he)
    _ = (∑ e∈E.filter (goodEdge L), (edgeAbs u e)^p) +
        ∑ H∈L, ∑ e∈E, if e∈incidentEdges H then
          (8*(H.card:ℝ))^(p-1)*∑ f∈rimEdges H, (edgeAbs u f)^p else 0 := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter,Finset.sum_comm]
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro H hH
      have hh := sum_incident_bound H E ((8*(H.card:ℝ))^(p-1)*∑ f∈rimEdges H, (edgeAbs u f)^p)
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg fun f hf => Real.rpow_nonneg (edgeAbs_nonneg _ _) _))
      simpa only [holeCost,mul_assoc] using hh

lemma weighted_sum_identity (L : Finset (Finset Vertex)) (u : Vertex → ℝ) (p : ℝ)
    (F : Finset Edge) (hF : ∀ H∈L, rimEdges H ⊆ F) :
    (∑ e∈F, holeWeights L p e*(edgeAbs u e)^p) =
      (∑ e∈F, (edgeAbs u e)^p) +
      ∑ H∈L, holeCost p H * ∑ e∈rimEdges H, (edgeAbs u e)^p := by
  classical
  simp only [holeWeights,add_mul,one_mul,Finset.sum_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro H hH
  rw [Finset.mul_sum]
  calc
    _ = ∑ e∈F, if e∈rimEdges H then holeCost p H*(edgeAbs u e)^p else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    _ = ∑ e∈F.filter (fun e => e∈rimEdges H), holeCost p H*(edgeAbs u e)^p := by rw [Finset.sum_filter]
    _ = _ := by
      congr 1
      ext e
      simp only [Finset.mem_filter]
      exact ⟨And.right,fun he => ⟨hF H hH he,he⟩⟩

theorem hole_extension_energy (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) (p : ℝ) (hp : 1 < p) (E : Finset Edge)
    (hE : ∀ e∈E, e∈grid.edgeSet) :
    ∃ F : Finset Edge, (∀ e∈F, goodEdge L e) ∧
      (∑ e∈E, (edgeAbs (extension L u) e)^p) ≤
        ∑ e∈F, holeWeights L p e * (edgeAbs u e)^p ∧
      ∀ e, 1 ≤ holeWeights L p e ∧
        holeWeights L p e ≤ (1+128*32^(p-1))*(1+(edgeDiameter L e:ℝ))^(2*p) := by
  classical
  let F := E.filter (goodEdge L) ∪ L.biUnion rimEdges
  have hr : ∀ H∈L, rimEdges H ⊆ F := by
    intro H hH e he
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨H,hH,he⟩)
  refine ⟨F,?_,?_,weights_bound L hL p hp.le⟩
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · exact (Finset.mem_filter.mp he).2
    · obtain ⟨H,hH,he⟩ := Finset.mem_biUnion.mp he
      exact rim_edge_good L hL hH he
  · rw [weighted_sum_identity L u p F hr]
    apply (extension_sum_bound L hL u p hp E hE).trans
    apply add_le_add _ (le_refl _)
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun e he hne => Real.rpow_nonneg (edgeAbs_nonneg _ _) _)

end SparseHoles

end

end OAI
