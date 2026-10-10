import OAI.Combinatorics.SquareDifference.TensorPair

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma positiveLaw_density_nonneg {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F) (z : Ω) :
    0≤lawDensity L z := hL _ (fun x => by split_ifs <;> norm_num)

lemma positiveLaw_bound_on_support {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (F : Ω → ℝ) (C : ℝ) (hF : ∀z,lawDensity L z≠0 → |F z|≤C) :
    |L F|≤C*L (fun _ => 1) := by
  rw [linearFunctional_density L F,linearFunctional_density L (fun _ => 1)]
  calc
    _ ≤ ∑z,|lawDensity L z*F z| := abs_sum_le_sum_abs _ _
    _ ≤ ∑z,lawDensity L z*C := by
      apply sum_le_sum
      intro z _
      by_cases hz : lawDensity L z=0
      · simp only [hz,zero_mul,abs_zero,le_refl]
      · rw [abs_mul,abs_of_nonneg (positiveLaw_density_nonneg L hL z)]
        exact mul_le_mul_of_nonneg_left (hF z hz) (positiveLaw_density_nonneg L hL z)
    _ = _ := by simp only [mul_one,mul_sum,lawDensity]; apply sum_congr rfl; intros; ring

lemma positiveLaw_density_pair_support {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (T : Ω → A) (P : A → Prop) [DecidablePred P]
    (hP : L (fun x => if P (T x) then 0 else 1)=0)
    (z : Ω) (hz : lawDensity L z≠0) : P (T z) := by
  by_contra hn
  have hle : lawDensity L z≤L (fun x => if P (T x) then 0 else 1) := by
    apply positiveLaw_mono L hL
    intro x
    by_cases hx : x=z
    · subst x; simp only [ite_true,hn,ite_false,le_refl]
    · simp only [hx,ite_false]; split_ifs <;> norm_num
  rw [hP] at hle
  exact hz (le_antisymm hle (positiveLaw_density_nonneg L hL z))

section Localized

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
  (hL : ∀j F,(∀z,0≤F z) → 0≤L j F) (hm : ∀j,L j (fun _ => 1)=1)

include hL hm in
lemma tensorLaw_localized_pair (B : Finset J) (W : (V → ∀j,X j) → ℝ)
    (F G : (∀j,X j) → ℝ) (u v : V) (C E : ℝ) (hC : 0≤C) (_ : 0≤E)
    (hW : ∀(z x : V → ∀j,X j),W (fun v j => if j∈B then z v j else x v j)=W z)
    (hWC : ∀z,|W z|≤C)
    (hpair : ∀z,lawDensity (tensorLaw L) z≠0 →
      |tensorLaw L (fun x => F (fun j => if j∈B then z u j else x u j)*
        G (fun j => if j∈B then z v j else x v j))|≤E) :
    |tensorLaw L (fun z => W z*F (z u)*G (z v))|≤C*E := by
  rw [←tensorLaw_freeze L L B hm (fun _ _ => rfl)]
  have hh (z : V → ∀j,X j) :
      tensorLaw L (fun x => W (fun v j => if j∈B then z v j else x v j)*
        F (fun j => if j∈B then z u j else x u j)*G (fun j => if j∈B then z v j else x v j))=
      W z*tensorLaw L (fun x => F (fun j => if j∈B then z u j else x u j)*
        G (fun j => if j∈B then z v j else x v j)) := by
    simp_rw [hW,mul_assoc]
    exact (tensorLaw L).map_smul (W z) _
  simp_rw [hh]
  have hpos := tensorLaw_nonneg L hL
  have hmass : tensorLaw L (fun _ => 1)=1 := by
    simpa only [prod_const_one,hm] using tensorLaw_fubini L (fun _ _ => (1:ℝ))
  have hb := positiveLaw_bound_on_support (tensorLaw L) hpos
    (fun z => W z*tensorLaw L (fun x => F (fun j => if j∈B then z u j else x u j)*
      G (fun j => if j∈B then z v j else x v j))) (C*E) (by
        intro z hz
        rw [abs_mul]
        exact mul_le_mul (hWC z) (hpair z hz) (abs_nonneg _) hC)
  simpa only [hmass,mul_one] using hb

end Localized

end SquareDifference

end

end OAI
