import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.TestRadialWeights

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset SharpLogRamsey.CertificateGeometry
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestActualMoment_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestActualMoment_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

theorem one_direction_rank_card (m : ℕ) (hdim : Module.finrank K V ≤ m+2)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (A.filter (fun H => W∈lines x H)).card ≤ ∑ i∈range m,Nat.card K^i := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W.1
  have hw := W.2.1
  have hm : Module.finrank K W.1.dualAnnihilator ≤ m := by omega
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // W.1≤LinearMap.ker H.rep} := by
      rw [←Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : {H // H∈A.filter (fun H => W∈lines x H)} =>
        (⟨H.1,(mem_lines _ _ _).mp (mem_filter.mp H.2).2⟩ :
          {H : Projectivization K (Module.Dual K V) // W.1≤LinearMap.ker H.rep}))
      intro H J he
      apply Subtype.ext
      exact congrArg (fun z => z.1) he
    _ = ∑ i∈range (Module.finrank K W.1.dualAnnihilator),Nat.card K^i := card_through _
    _ ≤ _ := sum_le_sum_of_subset (range_mono hm)

theorem pencil_rank_card (m : ℕ) (hdim : Module.finrank K V ≤ m+1)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) :
    A.card ≤ ∑ i∈range m,Nat.card K^i := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq x.submodule
  have hx := x.finrank_submodule
  have hm : Module.finrank K x.submodule.dualAnnihilator ≤ m := by omega
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // x.submodule≤LinearMap.ker H.rep} := by
      rw [←Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : A =>
        (⟨H.1,hA H H.2⟩ : {H : Projectivization K (Module.Dual K V) // x.submodule≤LinearMap.ker H.rep}))
      intro H J he
      apply Subtype.ext
      exact congrArg (fun z => z.1) he
    _ = ∑ i∈range (Module.finrank K x.submodule.dualAnnihilator),Nat.card K^i := card_through _
    _ ≤ _ := sum_le_sum_of_subset (range_mono hm)

end
end SharpLogRamsey.PreparedProjectiveGeometry
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore
open SharpRamseyFive.WeightedPrograms (DistinctPairs)
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestActualMoment_3 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestActualMoment_4 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

lemma family_one_direction_rank (m : ℕ) (hdim : Module.finrank K V ≤ m+2)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (univ.filter (fun H : A => W∈lines x H)).card ≤ ∑ i∈range m,Nat.card K^i := by
  have hh := one_direction_rank_card (K:=K) (V:=V) m hdim A x W
  refine Nat.le_trans ?_ hh
  apply Finset.card_le_card_of_injOn (fun H : A => H.val)
  · intro H hH
    exact mem_filter.mpr ⟨H.2,(mem_filter.mp hH).2⟩
  · intro H hH J hJ he
    exact Subtype.ext he

theorem actual_projective_high_moment
    (j : ℕ) (hj : 2 ≤ j) (hj3 : j ≤ 3) (hdim : Module.finrank K V ≤ j+1)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B : ℝ) (hf : f ≤ 1/25) {p : ℕ} (hp : 0<p) (R : ℕ)
    (own : A → Fin R → Bool)
    (hL : 10000 ≤ (L:ℝ))
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 13/100)
    (hB : Real.exp (3*((L:ℝ)*R)) ≤ B)
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ 4*B^2)
    (hdir : ((∑ i∈range (j-1),Nat.card K^i):ℝ) ≤ 4*B)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap S x c H J →
      ∃ i∈T,a i ≤ overlap S x c H J ∧ overlap S x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs S x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hrow : ∀ H∈A,∀ i∈T,((largeNeighbors S x c (a i) A H).card:ℝ)*a i^200 ≤ B*Real.exp (((L:ℝ)*R)/50))
    (hstrong : ∀ H∈A,((largeNeighbors S x c (1/(100*(p:ℝ))) A H).card:ℝ) ≤ B*Real.exp (-3*((L:ℝ)*R)))
    (hsq : (∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ B*Real.exp (((L:ℝ)*R)/100))
    (hpoly : SharpLogRamsey.MomentBudgetBridge.certificateOverhead p T.card ((L:ℝ)*R) ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hshift : SharpLogRamsey.MomentBudgetBridge.shiftOverhead p T.card ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3 ≤ Real.exp (((L:ℝ)*R)/10))
    (h : ℕ) (hh : 0<h) (hR : 400 ≤ R) (hsize : h ≤ (R/2)/400)
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2) :
    (∫ ω,(∑ H : A,scoreTerm (lines x H) (Real.exp (-(L:ℝ)*(1-f))) (own H)
      (fun r d => ω (r,d)))^p ∂batchMeasure (fun i : Fin R × RadialLine x => L*radialWeight S x c i.2))
      ≤ B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hm H (hH : H∈A) := radialWeight_mass S x c H (hA H hH)
  have hi H (hH : H∈A) J (hJ : J∈A) := radialWeight_intersection S x c H J (hA H hH) (hA J hJ)
  apply SharpLogRamsey.HighMoment.prepared_pencil_high_moment
    (radialWeight S x c) (fun H : A => lines x H) hp R own L (1-f) B
    hL (by linarith) _ _ _ hB _ (∑ i∈range (j-1),Nat.card K^i) (by exact_mod_cast hdir) _ _
    T a ha _ _ _ _ _ hpoly hshift hp2 hps h hh hR hsize herr
  · intro H
    rw [hm H H.2]
    exact hlow H H.2
  · intro H
    rw [hm H H.2]
    exact hupp H H.2
  · intro H
    rw [hm H H.2]
    exact (hdelta H H.2).trans (by norm_num)
  · rw [Fintype.card_coe]
    exact (Nat.cast_le.mpr (pencil_rank_card j hdim A x hA)).trans (by exact_mod_cast hcard)
  · intro W
    exact family_one_direction_rank (j-1) (by omega) A x W
  · intro D E hne
    exact family_two_directions (by omega) A x D E hne
  · intro z hz
    have he : SharpRamseyFive.WeightedPrograms.strength (fun H : A => lines x H)
        (radialWeight S x c) z=overlap S x c z.1 z.2 := hi z.1 z.1.2 z.2 z.2.1.2
    rw [he] at hz ⊢
    exact hcover z.1 z.1.2 z.2 z.2.1.2 (fun he => z.2.2 (Subtype.ext he.symm)) hz
  · intro i hiT
    have hc := family_pair_card A S x c (a i) hA
    change ((univ.filter (fun z : DistinctPairs A =>
      a i ≤ mass (radialWeight S x c) (lines x z.1∩lines x z.2))).card:ℝ)*a i^200 ≤ _
    rw [hc]
    exact hcount i hiT
  · intro H i hiT
    rw [family_neighbor_card A S x c (a i) hA H]
    exact hrow H H.2 i hiT
  · intro H
    rw [family_neighbor_card A S x c (1/(100*(p:ℝ))) hA H]
    exact hstrong H H.2
  · calc
      _ = ∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2 := by
        rw [←Finset.sum_coe_sort A (fun H => ((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2)]
        apply sum_congr rfl
        intro H _
        rw [hm H H.2]
      _ ≤ _ := hsq

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
