import Mathlib
import OAI.Analysis.FreeWords.MixedScaling
import OAI.Analysis.FreeWords.MixedToPatching
import OAI.Analysis.FreeWords.PatchingSmall

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

theorem finite_scalar_free_approximation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (K : Finset ℤ) (F : Finset (List (ℤ × ConcreteAlgebra M)))
    (hFne : ∀ w∈F, w≠[])
    (hcenter : ∀ w∈F, ∀ z∈w, z.1≠0 ∧ τ.map z.2=0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ u : unitary (ConcreteAlgebra M),
      (∀ k∈K, k≠0 → ‖τ.map ((u^k).val)‖<ε) ∧
      (∀ w∈F, ‖τ.map ((w.map (fun z => ((u^z.1).val)*z.2)).prod)‖<ε) := by
  classical
  let S : Finset (ConcreteAlgebra M) := F.biUnion (fun w => w.toFinset.image Prod.snd)
  have hS (w) (hw : w∈F) (z) (hz : z∈w) : z.2∈S := by
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_image.mpr ⟨z,List.mem_toFinset.mpr hz,rfl⟩⟩
  have hScenter : ∀ x∈S, τ.map x=0 := by
    intro x hx
    obtain ⟨w,hw,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (hcenter w hw z (List.mem_toFinset.mp hz)).2
  let R : ℝ := 1+∑ x∈S, ‖x‖
  have hR1 : 1≤R := by
    dsimp only [R]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hR : 0<R := zero_lt_one.trans_le hR1
  have hSbound : ∀ x∈S, ‖x‖≤R := by
    intro x hx
    have hi := Finset.single_le_sum (fun z _ => norm_nonneg z) hx
    dsimp only [R]
    linarith
  let c : ℂ := (R:ℂ)⁻¹
  let X : Set (ConcreteAlgebra M) := (fun x => c • x) '' (S : Set (ConcreteAlgebra M))
  have hXfin : X.Finite := S.finite_toSet.image _
  have hXnorm : ∀ x∈X, ‖x‖≤1 := by
    rintro x ⟨y,hy,rfl⟩
    rw [norm_smul,show ‖c‖=R⁻¹ by simp [c,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]]
    exact (mul_le_mul_of_nonneg_left (hSbound y hy) (inv_nonneg.mpr hR.le)).trans_eq (inv_mul_cancel₀ hR.ne')
  have hXcenter : ∀ x∈X, τ.map x=0 := by
    rintro x ⟨y,hy,rfl⟩
    simp only [map_smul,hScenter y hy,smul_zero]
  let L : Finset ℤ := insert 1 (insert (-1) ((K ∪ F.biUnion (fun w => w.toFinset.image Prod.fst)).erase 0))
  have hLzero : ∀ k∈(L:Set ℤ), k≠0 := by
    intro k hk
    simp only [L,Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hk
    rcases hk with rfl | rfl | ⟨hk,_⟩
    · norm_num
    · norm_num
    · exact hk
  have hL1 : (1:ℤ)∈(L:Set ℤ) := Finset.mem_insert_self _ _
  have hLm1 : (-1:ℤ)∈(L:Set ℤ) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hLK : ∀ k∈K, k≠0 → k∈(L:Set ℤ) := by
    intro k hk hk0
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hk0,Finset.mem_union_left _ hk⟩))
  have hLF : ∀ w∈F, ∀ z∈w, z.1∈(L:Set ℤ) := by
    intro w hw z hz
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨(hcenter w hw z hz).1,Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_image.mpr ⟨z,List.mem_toFinset.mpr hz,rfl⟩⟩)⟩))
  let N : ℕ := 1+∑ w∈F, w.length
  have hN1 : 1≤N := Nat.le_add_right _ _
  have hNF : ∀ w∈F, w.length≤N := by
    intro w hw
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw).trans (Nat.le_add_left _ _)
  let ξ := ε/R^N
  have hξ : 0<ξ := div_pos hε (pow_pos hR _)
  obtain ⟨u,hu⟩ := unitary_admissible_small τ hF hD hXfin L.finite_toSet
    hXnorm hXcenter hLzero hL1 hLm1 (N := N) ξ hξ
  have hξle : ξ≤ε := div_le_self hε.le (one_le_pow₀ hR1)
  refine ⟨u,?_,?_⟩
  · intro k hk hk0
    let A : PatchingWord (ConcreteAlgebra M) := ⟨1,k,[],1⟩
    have hA : PatchingWord.Admissible X (L:Set ℤ) N A :=
      ⟨Set.mem_insert _ _,hLK k hk hk0,Set.mem_insert _ _,by simp [A],hN1⟩
    have hh := hu A hA
    simpa only [A,PatchingWord.value,PatchingWord.tailValue_nil,one_mul,mul_one] using hh.trans_le hξle
  · intro w hw
    have hn := hNF w hw
    have hcword : ∀ z∈scaledMixed c w, z.1∈(L:Set ℤ) ∧ z.2∈X := by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
      exact ⟨hLF w hw y hy,⟨y.2,hS w hw y hy,rfl⟩⟩
    have hscaled : ‖τ.map (mixedValue (fun k => (u^k).val) (scaledMixed c w))‖<ξ := by
      cases w with
      | nil => exact (hFne [] hw rfl).elim
      | cons z s =>
        have hhead := hcword (z.1,c • z.2) List.mem_cons_self
        have htail : ∀ y∈scaledMixed c s, y.1∈(L:Set ℤ) ∧ y.2∈X :=
          fun y hy => hcword y (List.mem_cons_of_mem _ hy)
        have hlen : (scaledMixed c s).length+1≤N := by
          simpa only [scaledMixed,List.length_map,List.length_cons] using hn
        have hA := PatchingWord.ofMixedHead_admissible z.1 (c • z.2) (scaledMixed c s)
          hhead.1 hhead.2 htail hlen
        have hh := hu _ hA
        simpa only [PatchingWord.ofMixedHead_value,mixedValue,scaledMixed,List.map_cons,List.prod_cons] using hh
    have hpow : R^w.length≤R^N := pow_le_pow_right₀ hR1 hn
    have hbound : R^w.length*ξ≤ε := by
      calc
        _ ≤ R^N*ξ := mul_le_mul_of_nonneg_right hpow hξ.le
        _ = ε := by dsimp only [ξ]; field_simp
    rw [show (w.map (fun z => ((u^z.1).val)*z.2)).prod=mixedValue (fun k => (u^k).val) w from rfl]
    rw [norm_trace_scaled τ _ R hR w]
    exact (mul_lt_mul_of_pos_left hscaled (pow_pos hR _)).trans_le hbound

end

end KKLocalPatching
end

end OAI
