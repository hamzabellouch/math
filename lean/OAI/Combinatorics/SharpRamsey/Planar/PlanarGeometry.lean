import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanarBudget

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarGeometry_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarGeometry_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarGeometry_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarGeometry_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem preparation (hdim : Module.finrank K V=3)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hST : S.card≤T.card)
    (σ P : ℝ) (L c : ℝ≥0) (R p h : ℕ) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hcs : (c:ℝ)≤1/100) (hbud : Budget σ P L R p h)
    (hsp : (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    let B := (Nat.card K:ℝ)^2/S.card
    let E := badHyperplanes S (fun _ : Unit => ∅) [] c
    ∃ Ds : Finset (Projectivization K V),
      (Ds.card:ℝ)≤(S.card:ℝ)/10000 ∧
      (∑ H∈E,mass S c H)≤20804*(Nat.card K:ℝ)*B ∧
      (∀ x,((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)≤1/25) ∧
      ∀ x,x∉Ds →
        ((pencil x∩E).card:ℝ)≤50000*B*exp ((L:ℝ)/1000) ∧
        SecondPencil 2 R S (own S (fun _ : Unit => ∅) [] x) x c L (pencil x\E)
          (((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)) B 400000 (∅ : Finset Unit) (fun _ => 0) ∧
        HighPencil 2 R p h S (own S (fun _ : Unit => ∅) [] x) x c L (pencil x\E)
          (((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)) B (∅ : Finset Unit) (fun _ => 0) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^2/N
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := Finite.one_lt_card
    dsimp [q]; exact_mod_cast hh
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  have hsmall : N^2≤2*q^3 := Incidence.sparse_smaller_square (n:=0) hdim S T hST hsp
  obtain ⟨Ds,hDs,hE,hW,hown,hregular⟩ := source_regular_preparation (n:=0) hdim S hS
    (fun _ : Unit => ∅) [] c hc hcs (by intro i; exact Fin.elim0 i) L L.coe_nonneg
  have hDsN : (Ds.card:ℝ)≤N/10000 := by
    apply hDs.trans
    have hh : exp (-(L:ℝ)/500)≤1 := exp_le_one_iff.mpr (by nlinarith [L.coe_nonneg])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (show 0≤N/10000 by positivity)
  have hcards : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B^2 :=
    Incidence.sparse_retained_pencil (n:=0) hdim S S hS Subset.rfl T hST hsp
  have hdir : (1:ℝ)≤4*B := Incidence.scalar_direction_two q N hq2 hNs hsmall
  refine ⟨Ds,hDsN,hW,hown,?_⟩
  intro x hx
  obtain ⟨he,htyp,hsq⟩ := hregular x hx
  refine ⟨he.le,?_⟩
  exact plane_pencil_budgets hdim S _ x c L _ sdiff_subset σ P B R p h
    hbud hB htyp hsq hcards hdir

end
end SharpLogRamsey.PlanarLearning

end

end OAI
