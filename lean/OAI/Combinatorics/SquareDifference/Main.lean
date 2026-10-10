import OAI.Combinatorics.SquareDifference.UniformInduction

namespace OAI

section

open Finset

namespace SquareDifference

lemma density_root_bound (d N : ℕ) (hd : 0<d) (hN : 0<N) (δ D a : ℝ)
    (hδ : 0≤δ) (hD : 0≤D) (hh : δ^d≤D*(N:ℝ)^(-a)) :
    δ≤D^((d:ℝ)⁻¹)*(N:ℝ)^(-(a*(d:ℝ)⁻¹)) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he := Real.rpow_le_rpow (pow_nonneg hδ _) hh (inv_nonneg.mpr hd0.le)
  rw [←Real.rpow_natCast_mul hδ,mul_inv_cancel₀ hd0.ne',Real.rpow_one] at he
  rw [Real.mul_rpow hD (Real.rpow_nonneg hn.le _),←Real.rpow_mul hn.le] at he
  simpa only [neg_mul] using he

lemma nat_power_saving :
    ∃c C : ℝ,0<c ∧ ∀N : ℕ,1≤N → ∀A : Finset ℕ,A⊆range N → NatSquareFree A →
      (A.card:ℝ)≤C*(N:ℝ)^(1-c) := by
  obtain ⟨P,hP,hpt⟩ := exists_exceptional_threshold
  obtain ⟨a,D,ha,hD,hdec⟩ := uniform_functional_decay (smallPrimes P) (smallPrimes_injective P)
    (actualSmallModulus_ge_two P (by omega))
  let d := Fintype.card TupleVertex
  have hd : 0<d := Fintype.card_pos
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  let c := a*(d:ℝ)⁻¹
  let C := D^((d:ℝ)⁻¹)
  refine ⟨c,C,mul_pos ha (inv_pos.mpr hd0),?_⟩
  intro N hN A hA hf
  let p := largePrimes P N
  have hp := actualPrime_hyp P hP hpt N
  have hh := hdec N hN p hp A hA hf
  have hmass (j : LargePrime P N) : max tupleMassThreshold tupleReflectionThreshold≤(p j:ℝ) :=
    max_le ((le_max_left _ _).trans (hp.mass j)) (hp.reflection j)
  have hl := setFunctional_density p hmass N (powerCutoff N sourceBeta)
    (powerCutoff_pos N (by omega) sourceBeta (by norm_num [sourceBeta])) A hA
  have hb := density_root_bound d N hd (by omega) ((A.card:ℝ)/(N:ℝ)) D a
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith) (hl.trans hh)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hb' := mul_le_mul_of_nonneg_right hb hn.le
  rw [div_mul_cancel₀ _ hn.ne'] at hb'
  apply hb'.trans_eq
  change C*(N:ℝ)^(-c)*(N:ℝ)=C*(N:ℝ)^(1-c)
  have hr : (N:ℝ)^(-c)*(N:ℝ)=(N:ℝ)^(1-c) := by
    calc
      _ = (N:ℝ)^(-c)*(N:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hn]; congr 1; ring
  rw [mul_assoc,hr]

def natTranslate (A : Finset ℤ) : Finset ℕ := A.image (fun z => (z-1).toNat)

lemma natTranslate_sub (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) : natTranslate A⊆range N := by
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  have hz' := mem_Icc.mp (hA hz)
  rw [mem_range]
  omega

lemma natTranslate_card (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) : (natTranslate A).card=A.card := by
  apply card_image_iff.mpr
  intro z hz w hw he
  change (z-1).toNat=(w-1).toNat at he
  have hz' := (mem_Icc.mp (hA hz)).1
  have hw' := (mem_Icc.mp (hA hw)).1
  omega

lemma natTranslate_free (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) (hf : IsSquareDifferenceFree A) :
    NatSquareFree (natTranslate A) := by
  intro a ha b hb m hm he
  obtain ⟨z,hz,rfl⟩ := mem_image.mp ha
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
  apply hf w hw z hz m hm
  have hz' := (mem_Icc.mp (hA hz)).1
  have hw' := (mem_Icc.mp (hA hw)).1
  have he' := congrArg (fun n : ℕ => (n:ℤ)) he
  push_cast at he'
  omega

theorem power_saving :
    ∃ c C : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ,
      A ⊆ Finset.Icc 1 (N : ℤ) → IsSquareDifferenceFree A →
        (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c) := by
  obtain ⟨c,C,hc,h⟩ := nat_power_saving
  refine ⟨c,C,hc,?_⟩
  intro N hN A hA hf
  have hh := h N hN (natTranslate A) (natTranslate_sub N A hA) (natTranslate_free N A hA hf)
  rwa [natTranslate_card N A hA] at hh

end SquareDifference

end

end OAI
