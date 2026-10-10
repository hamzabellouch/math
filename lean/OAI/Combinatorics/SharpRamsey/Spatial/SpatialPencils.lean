import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanePencils
import OAI.Combinatorics.SharpRamsey.Learning.PreparedOverlapBounds
import OAI.Combinatorics.SharpRamsey.Selection.DyadicGrid

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedProjectiveGeometry
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialPencils_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialPencils_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

omit [Finite K] [FiniteDimensional K V] in
lemma overlap_le_outside (S O : Finset (Projectivization K V))
    (x : Projectivization K V) (c : ℝ≥0)
    (H J : Projectivization K (Module.Dual K V)) :
    overlap (S\(O∪{x})) x c H J≤outsideMass S O x c H := by
  apply mul_le_mul_of_nonneg_left _ c.coe_nonneg
  apply Nat.cast_le.mpr
  apply card_le_card
  intro y hy
  obtain ⟨hy,hne,hle⟩ := mem_filter.mp hy
  exact mem_filter.mpr ⟨hy,hne,hle.trans inf_le_left⟩

omit [Finite K] [FiniteDimensional K V] in

lemma spatial_overlap_cover (S O : Finset (Projectivization K V))
    (hS : S.Nonempty) (x : Projectivization K V) (c : ℝ≥0)
    (hc : 1/(S.card:ℝ)≤c)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hu : ∀ H∈A,outsideMass S O x c H≤2)
    (H J : Projectivization K (Module.Dual K V)) (hH : H∈A)
    (hp : 0<overlap (S\(O∪{x})) x c H J) :
    ∃ i∈range (Nat.log 2 S.card+2),
      DyadicGrid.value i≤overlap (S\(O∪{x})) x c H J ∧
      overlap (S\(O∪{x})) x c H J≤2*DyadicGrid.value i := by
  have hu' := (overlap_le_outside S O x c H J).trans (hu H hH)
  unfold overlap at hp hu' ⊢
  have hk : 0<((S\(O∪{x})).filter (fun y => y ≠ x ∧
      y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep)).card := by
    by_contra! hh
    have hz := Nat.eq_zero_of_le_zero hh
    rw [hz,Nat.cast_zero,mul_zero] at hp
    exact lt_irrefl _ hp
  exact DyadicGrid.integer_overlap_cover (card_pos.mpr hS) c hc _ hk hu'

lemma spatial_neighbor_power (hdim : Module.finrank K V=4)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (hu : ∀ H∈A,outsideMass S O x c H≤2)
    (H : Projectivization K (Module.Dual K V)) (hH : H∈A) (i : ℕ) :
    ((largeNeighbors (S\(O∪{x})) x c (DyadicGrid.value i) A H).card:ℝ)*
      (DyadicGrid.value i)^200≤2*((Nat.card K:ℝ)+1) := by
  have ha := DyadicGrid.value_pos i
  have hh := largeNeighbors_bound hdim (S\(O∪{x})) x c (DyadicGrid.value i)
    c.coe_nonneg ha A (fun J hJ => (mem_filter.mp (hA hJ)).2)
    H (mem_filter.mp (hA hH)).2 (hu H hH)
  have hh' := (le_div_iff₀ ha).mp hh
  have hp : (DyadicGrid.value i)^200≤DyadicGrid.value i :=
    pow_le_of_le_one ha.le (DyadicGrid.value_le_one i) (by decide)
  exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans hh'

lemma spatial_pair_power (hdim : Module.finrank K V=4)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (K₀ : ℝ) (hK : 0≤K₀) (i : ℕ)
    (hr : ((richRadials (S\(O∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
      (DyadicGrid.value i)^100≤K₀) :
    ((largePairs (S\(O∪{x})) x c (DyadicGrid.value i) A).card:ℝ)*
      (DyadicGrid.value i)^200≤K₀*((Nat.card K:ℝ)+1)^2 := by
  apply (pairs_of_radial_bound hdim (S\(O∪{x})) x c _ K₀ hr A
    (fun H hH => (mem_filter.mp (hA hH)).2)).trans
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (DyadicGrid.value_pos i).le (DyadicGrid.value_le_one i)

theorem spatial_pencils (hdim : Module.finrank K V=4)
    (R p h : ℕ) (hp : 0<p)
    (S O : Finset (Projectivization K V)) (hS : S.Nonempty)
    (x : Projectivization K V) (c L : ℝ≥0) (hc : 1/(S.card:ℝ)≤c)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (f B C V₀ K₀ : ℝ) (hK : 0≤K₀)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-f)|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤V₀)
    (hsqs : V₀≤C*B*Real.exp ((L:ℝ)/100))
    (hsqa : V₀≤B*Real.exp (((L:ℝ)*R)/100))
    (hcards : ((∑ i∈range 3,Nat.card K^i):ℝ)≤C*B^2)
    (hcarda : ((∑ i∈range 3,Nat.card K^i):ℝ)≤4*B^2)
    (hdir : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B)
    (hrad : ∀ i∈range (Nat.log 2 S.card+2),
      ((richRadials (S\(O∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤K₀)
    (hpair : K₀*((Nat.card K:ℝ)+1)^2≤B^2*Real.exp (((L:ℝ)*R)/50))
    (hneighbor : 2*((Nat.card K:ℝ)+1)≤B*Real.exp (((L:ℝ)*R)/50))
    (hstrong : (richRadials (S\(O∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*((Nat.card K:ℝ)+1)/(1/(100*(p:ℝ)))≤B*Real.exp (-3*((L:ℝ)*R)))
    (hB : 0≤B)
    (hdiag : C*2^R≤Real.exp ((L:ℝ)*R/20))
    (hpow : (2*(L:ℝ)^2)^R≤Real.exp ((L:ℝ)*R/25))
    (hsum : C^2*Real.exp ((L:ℝ)/50)+(Nat.log 2 S.card+2:ℕ)*2^R*
      Real.exp ((L:ℝ)*R/50)≤Real.exp ((L:ℝ)*R/20))
    (htwo : 2≤Real.exp ((L:ℝ)*R/20))
    (hcert : MomentBudgetBridge.certificateOverhead p (Nat.log 2 S.card+2) ((L:ℝ)*R)≤
      Real.exp (2*((L:ℝ)*R)/25))
    (hshift : MomentBudgetBridge.shiftOverhead p (Nat.log 2 S.card+2)≤
      Real.exp (2*((L:ℝ)*R)/25))
    (hpb : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3≤Real.exp (((L:ℝ)*R)/10))
    (hh : 0<h) (hhs : h≤(R/2)/400) (hhe : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2) :
    SecondPencil 3 R S O x c L A f B C (range (Nat.log 2 S.card+2)) DyadicGrid.value ∧
    HighPencil 3 R p h S O x c L A f B (range (Nat.log 2 S.card+2)) DyadicGrid.value := by
  have hu := fun H hH => (htyp H hH).2.1
  have hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
      ∃ i∈range (Nat.log 2 S.card+2),DyadicGrid.value i≤overlap (S\(O∪{x})) x c H J ∧
        overlap (S\(O∪{x})) x c H J≤2*DyadicGrid.value i := by
    intro H hH J _ _ hh
    exact spatial_overlap_cover S O hS x c hc A hu H J hH hh
  have hpair' := fun i hi => (spatial_pair_power hdim S O x c A hA K₀ hK i (hrad i hi)).trans hpair
  constructor
  · refine ⟨(fun H hH => (htyp H hH).1),hu,?_,hsq.trans hsqs,hcards,
      (fun i _ => DyadicGrid.value_pos i),hcover,hpair',hdiag,hpow,?_,htwo⟩
    · intro H hH
      exact (htyp H hH).2.2.trans (by norm_num)
    · simpa only [card_range] using hsum
  · refine ⟨(fun H hH => (htyp H hH).1),hu,(fun H hH => (htyp H hH).2.2),
      hsq.trans hsqa,hcarda,hdir,(fun i _ => (DyadicGrid.value_pos i).le),hcover,hpair',?_,?_,
      ?_,?_,hpb,hps,hh,hhs,hhe⟩
    · intro H hH i _
      exact (spatial_neighbor_power hdim S O x c A hA hu H hH i).trans hneighbor
    · intro H hH
      rcases hstrong with he|hb
      · rw [neighbors_empty_of_radials hdim (S\(O∪{x})) x c _ he A
          (fun J hJ => (mem_filter.mp (hA hJ)).2) H hH]
        simp only [card_empty,Nat.cast_zero]
        positivity
      · exact (largeNeighbors_bound hdim (S\(O∪{x})) x c _ c.coe_nonneg (by positivity)
          A (fun J hJ => (mem_filter.mp (hA hJ)).2) H (mem_filter.mp (hA hH)).2 (hu H hH)).trans hb
    · simpa only [card_range] using hcert
    · simpa only [card_range] using hshift

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
