import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialTraining

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation PreparedProjectiveGeometry
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialPreparation_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialPreparation_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialPreparation_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem preparation (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hST : S.card≤T.card)
    (plane : J→Finset (Projectivization K V)) (bs : List J)
    (σ P g : ℝ) (L c : ℝ≥0) (R p h : ℕ)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card) (hcs : (c:ℝ)≤1/100)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hNup : (S.card:ℝ)≤exp (3*σ/2+g))
    (hcell : ∀ i : Fin bs.length,((indexedCell S plane bs i).card:ℝ)/(S.card:ℝ)≤1/25)
    (hsp : (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K))
    (D₀ D₁ : Finset (Projectivization K V))
    (hD₀ : (D₀.card:ℝ)≤S.card*exp (-P/200)) (hD₁ : (D₁.card:ℝ)≤S.card*exp (5*P))
    (hrad : ∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S.card+2),
      ((richRadials (S\(own S plane bs x∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤exp (σ+P/100-2*g))
    (hstrong : ∀ x,x∉D₁ → (richRadials (S\(own S plane bs x∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P)) :
    let B := (Nat.card K:ℝ)^3/S.card
    let E := badHyperplanes S plane bs c
    ∃ Ds Da : Finset (Projectivization K V),Ds⊆Da ∧
      (Ds.card:ℝ)≤S.card*exp (-P/200)+(S.card:ℝ)/10000 ∧
      (Da.card:ℝ)≤2*S.card+S.card*exp (5*P) ∧
      (∑ H∈E,mass S c H)≤20804*(Nat.card K:ℝ)*B ∧
      (∀ x,((own S plane bs x).card:ℝ)/(S.card:ℝ)≤1/25) ∧
      (∀ x,x∉Ds → ((pencil x∩E).card:ℝ)≤50000*B*exp ((L:ℝ)/1000) ∧
        SecondPencil 3 R S (own S plane bs x) x c L (pencil x\E)
          (((own S plane bs x).card:ℝ)/(S.card:ℝ)) B 400000
          (range (Nat.log 2 S.card+2)) DyadicGrid.value) ∧
      (∀ x,x∉Da → HighPencil 3 R p h S (own S plane bs x) x c L (pencil x\E)
          (((own S plane bs x).card:ℝ)/(S.card:ℝ)) B
          (range (Nat.log 2 S.card+2)) DyadicGrid.value) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^3/N
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    dsimp [q]; exact_mod_cast hh
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hsmall : N^2≤2*q^4 := Incidence.sparse_smaller_square (n:=1) hdim S T hST hsp
  obtain ⟨D,hD,hE,hW,hown,hregular⟩ := source_regular_preparation (n:=1) hdim S hS
    plane bs c hc hcs hcell L L.coe_nonneg
  have hDN : (D.card:ℝ)≤N/10000 := by
    apply hD.trans
    have hh : exp (-(L:ℝ)/500)≤1 := exp_le_one_iff.mpr (by nlinarith [L.coe_nonneg])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (show 0≤N/10000 by positivity)
  have hD₀N : (D₀.card:ℝ)≤N := by
    apply hD₀.trans
    have he : exp (-P/200)≤1 := exp_le_one_iff.mpr (by linarith [hbud.large])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hNs.le
  have hDs : ((D₀∪D).card:ℝ)≤N*exp (-P/200)+N/10000 := by
    have hh : ((D₀∪D).card:ℝ)≤D₀.card+D.card := by exact_mod_cast card_union_le D₀ D
    linarith
  have hDa : (((D₀∪D)∪D₁).card:ℝ)≤2*N+N*exp (5*P) := by
    have h1 : ((D₀∪D).card:ℝ)≤D₀.card+D.card := by exact_mod_cast card_union_le D₀ D
    have h2 : (((D₀∪D)∪D₁).card:ℝ)≤(D₀∪D).card+D₁.card := by exact_mod_cast card_union_le (D₀∪D) D₁
    linarith
  have hcards : ((∑ i∈range 3,Nat.card K^i):ℝ)≤4*B^2 :=
    Incidence.sparse_retained_pencil (n:=1) hdim S S hS Subset.rfl T hST hsp
  have hdir : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B := by
    simpa only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,Nat.cast_add,Nat.cast_one]
      using Incidence.scalar_direction_three q N hq2 hNs hsmall
  have hc1 : 1/(S.card:ℝ)≤c := by
    rw [hc]
    exact div_le_div_of_nonneg_right (show 1≤q by linarith) hNs.le
  refine ⟨D₀∪D,(D₀∪D)∪D₁,subset_union_left,hDs,hDa,hW,hown,?_,?_⟩
  · intro x hx
    have hx' := not_or.mp (mt mem_union.mpr hx)
    obtain ⟨he,htyp,hsq⟩ := hregular x hx'.2
    refine ⟨he.le,?_⟩

    have hh := spatial_pencils hdim R p h hbud.p_pos S (own S plane bs x) hS x c L hc1
      (pencil x\badHyperplanes S plane bs c) sdiff_subset _ B 400000
      (400000*B*exp ((L:ℝ)/1000)) (exp (σ+P/100-2*g)) (exp_pos _).le htyp hsq

    have hout := spatial_pencil_budgets hdim S (own S plane bs x) hS x c L hc1
      (pencil x\badHyperplanes S plane bs c) sdiff_subset σ P g R p h hbud hqexp hNup hsmall
      htyp hsq hcards hdir (hrad x hx'.1)
    by_cases hs : x∈D₁
    · clear hout hh
      have hpairs : ∀ i∈range (Nat.log 2 S.card+2),
          ((largePairs (S\(own S plane bs x∪{x})) x c (DyadicGrid.value i)
            (pencil x\badHyperplanes S plane bs c)).card:ℝ)*(DyadicGrid.value i)^200≤
            B^2*exp (((L:ℝ)*R)/50) := by
        intro i hi
        apply (spatial_pair_power hdim S _ x c _ sdiff_subset _ (exp_pos _).le i (hrad x hx'.1 i hi)).trans
        have hp := overlap_scale hNs hNup (by linarith [hbud.sigma])
          (by linarith [hbud.large] : 400≤P)
        simpa only [hqexp,←hbud.identity] using hp
      refine ⟨fun H hH => (htyp H hH).1,fun H hH => (htyp H hH).2.1,
        (fun H hH => (htyp H hH).2.2.trans (by norm_num)),?_,?_,
        (fun i _ => DyadicGrid.value_pos i),?_,hpairs,?_,?_,?_,?_⟩
      · apply hsq.trans
        apply mul_le_mul_of_nonneg_left _ (by dsimp [B]; positivity)
        exact exp_le_exp.mpr (by nlinarith [L.coe_nonneg])
      · nlinarith [sq_nonneg B]
      · intro H hH J hJ hne hp
        exact spatial_overlap_cover S _ hS x c hc1 _ (fun H hH => (htyp H hH).2.1) H J hH hp
      · simpa only [←hbud.identity] using hbud.diag
      · simpa only [←hbud.identity] using hbud.pow
      · simpa only [card_range,←hbud.identity] using hbud.sum
      · simpa only [←hbud.identity] using hbud.two
    · exact (hout (hstrong x hs)).1
  · intro x hx
    have hx' := not_or.mp (mt mem_union.mpr hx)
    have hx'' := not_or.mp (mt mem_union.mpr hx'.1)
    obtain ⟨he,htyp,hsq⟩ := hregular x hx''.2
    exact (spatial_pencil_budgets hdim S (own S plane bs x) hS x c L hc1
      (pencil x\badHyperplanes S plane bs c) sdiff_subset σ P g R p h hbud hqexp hNup hsmall
      htyp hsq hcards hdir (hrad x hx''.1) (hstrong x hx'.2)).2

end
end SharpLogRamsey.SpatialLearning

end

end OAI
