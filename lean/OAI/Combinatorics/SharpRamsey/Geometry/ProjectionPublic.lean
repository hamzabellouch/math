import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.QuotientBounds
import OAI.Combinatorics.SharpRamsey.Geometry.EightIntersections

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real Incidence CapComposition
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedProjectionPublic_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedProjectionPublic_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedProjectionPublic_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

omit [Finite K] [FiniteDimensional K V] in
lemma lift_contraction_numeric (A : Finset (Projectivization K V))
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule)))
    (m Q : ℝ) (hm : 0 ≤ m) (hQ : 0 < Q) (hW : (W.card:ℝ) ≤ m)
    (hcol : (orderedCollisions A z:ℝ) ≤ 100*(A.card:ℝ)^2/Q) :
    ((liftCap A z W).card:ℝ) ≤ m+sqrt (100*m/Q)*A.card := by
  apply (liftCap_contraction A z W).trans
  apply add_le_add hW
  have hh : (W.card:ℝ)*orderedCollisions A z ≤ m*(100*(A.card:ℝ)^2/Q) :=
    mul_le_mul hW hcol (by positivity) hm
  apply (sqrt_le_sqrt hh).trans_eq
  rw [show m*(100*(A.card:ℝ)^2/Q)=(100*m/Q)*(A.card:ℝ)^2 by ring,
    sqrt_mul (by positivity),sqrt_sq (by positivity : (0:ℝ) ≤ A.card)]

def liftedLibrary (U : Finset (Projectivization K V))
    (F : ∀ z : Projectivization K V, Finset (Finset (Projectivization K (V ⧸ z.submodule)))) :
    Finset (Finset (Projectivization K V)) :=
  univ.biUnion (fun z => (F z).image (liftCap U z))

lemma liftedLibrary_card (U : Finset (Projectivization K V))
    (F : ∀ z : Projectivization K V, Finset (Finset (Projectivization K (V ⧸ z.submodule))))
    (M : ℕ) (hM : ∀ z,(F z).card ≤ M) :
    (liftedLibrary U F).card ≤ Fintype.card (Projectivization K V)*M := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ z : Projectivization K V,M :=
      sum_le_sum (fun z hz => card_image_le.trans (hM z))
    _ = _ := by simp

theorem eight_projection_library {n : ℕ} (hdim : Module.finrank K V=n+3)
    (U S : Finset (Projectivization K V)) (hSU : S ⊆ U)
    (UT T : Finset (Projectivization K (Module.Dual K V))) (hTU : T ⊆ UT)
    (τ m : ℝ) (hτ : 0 < τ) (hm : 0 ≤ m)
    (hS : 100 ≤ S.card)
    (hsmall : (S.card:ℝ) ≤ (Nat.card K:ℝ)^(n+1)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ) ≤ T.card)
    (hsparse : (incidenceCount S T:ℝ) ≤ τ*S.card*T.card/Nat.card K)
    (F : ∀ z : Projectivization K V, Finset (Finset (Projectivization K (V ⧸ z.submodule))))
    (M : ℕ) (hM : ∀ z,(F z).card ≤ M)
    (hsize : ∀ z W,W ∈ F z → (W.card:ℝ) ≤ m)
    (hcover : ∀ z,
      (9/10:ℝ)*S.card ≤ (projected S z).card →
      (T.card:ℝ)/(3*Nat.card K) ≤ (quotientCut T z).card →
      ((quotientCut T z).card:ℝ) ≤ 2*T.card/Nat.card K →
      ((quotientCut UT z).card:ℝ) ≤ 100*UT.card/Nat.card K →
      (S.card:ℝ)*T.card/(4*Nat.card K) ≤ (projected S z).card*(quotientCut T z).card →
      (incidenceCount (projected S z) (quotientCut T z):ℝ) ≤
        400*τ*(projected S z).card*(quotientCut T z).card/Nat.card K →
      ∃ W ∈ F z,(99/100:ℝ)*(projected S z).card ≤ (projected S z∩W).card)
    (hhalf : sqrt (100*m/(Nat.card K:ℝ)^(n+1)) ≤ 1/2)
    (hpow : (Nat.card K:ℝ)*(sqrt (100*m/(Nat.card K:ℝ)^(n+1)))^7 ≤ 1) :
    ∃ A ∈ powers (liftedLibrary U F) U 8,A ⊆ U ∧
      (A.card:ℝ) ≤ 3*m ∧ (S.card:ℝ)/2 ≤ (S∩A).card ∧
      (powers (liftedLibrary U F) U 8).card ≤
        (Fintype.card (Projectivization K V)*M)^8 := by
  let q : ℝ := Nat.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have h1 : ∀ D ∈ liftedLibrary U F,(D.card:ℝ) ≤ q*m := by
    intro D hD
    obtain ⟨z,_,hz⟩ := mem_biUnion.mp hD
    obtain ⟨W,hW,rfl⟩ := mem_image.mp hz
    have hh : ((liftCap U z W).card:ℝ) ≤ q*W.card := by
      dsimp [q]
      exact_mod_cast liftCap_initial U z W
    exact hh.trans (mul_le_mul_of_nonneg_left (hsize z W hW) hq.le)
  have hstep : ∀ A,A ⊆ U → A.Nonempty → ∃ D ∈ liftedLibrary U F,D ⊆ U ∧
      ((S\D).card:ℝ) ≤ (3/100:ℝ)*S.card ∧
      ((A∩D).card:ℝ) ≤ m+sqrt (100*m/q^(n+1))*A.card := by
    intro A hAU hA
    obtain ⟨z,hSn,hTlo,hThi,hU,hmul,hsp,hcS,hcA⟩ :=
      quotient_data hdim S A T UT hA hTU τ hτ hS hsmall hlarge hsparse
    obtain ⟨W,hW,hcap⟩ := hcover z hSn hTlo hThi hU hmul hsp
    refine ⟨liftCap U z W,mem_biUnion.mpr ⟨z,mem_univ _,mem_image.mpr ⟨W,hW,rfl⟩⟩,
      liftCap_subset U z W,?_,?_⟩
    · have hc : ((projected S z\W).card:ℝ) ≤ (1/100:ℝ)*(projected S z).card := by
        have he : ((projected S z\W).card:ℝ)+(projected S z∩W).card=(projected S z).card := by
          exact_mod_cast card_sdiff_add_card_inter (projected S z) W
        linarith
      have hcol : (orderedCollisions S z:ℝ)+1 ≤ (2/100:ℝ)*S.card := by
        have hs : (100:ℝ) ≤ S.card := by exact_mod_cast hS
        linarith
      simpa only [show (1/100:ℝ)+2/100=3/100 by norm_num] using
        original_support_loss_real S U hSU z W (1/100) (2/100) (by norm_num) hc hcol
    · rw [inter_liftCap A U hAU]
      exact lift_contraction_numeric A z W m (q^(n+1)) hm (pow_pos hq _) (hsize z W hW) hcA.le
  obtain ⟨A,hA,hAU,hsizeA,hcapA⟩ := eight_intersections U S
    (card_pos.mp (by omega)) hSU (liftedLibrary U F) m q (sqrt (100*m/q^(n+1))) hm hq.le
    (sqrt_nonneg _) hhalf hpow h1 hstep
  refine ⟨A,hA,hAU,hsizeA,hcapA,?_⟩
  exact (powers_card _ _ _).trans (Nat.pow_le_pow_left (liftedLibrary_card U F M hM) 8)

end
end SharpLogRamsey.Projection

end

end OAI
