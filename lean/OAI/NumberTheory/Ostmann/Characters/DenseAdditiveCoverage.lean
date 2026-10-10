import OAI.NumberTheory.Ostmann.Characters.DenseGroupCoverage

namespace OAI

noncomputable section
open scoped BigOperators Pointwise
namespace Ostmann.Characters
section Additive
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_ordered_sum_cover (A : Finset G) (h0 : 0∈A)
    (hgen : AddSubgroup.closure (A : Set G) = ⊤) (N : ℕ)
    (hN : (Fintype.card G : ℚ) < (3/2:ℚ)^N*A.card) :
    ∃ r≤2^N, ∀ x:G, ∃ f : Fin r → G, (∀ i, f i∈A) ∧ ∑ i, f i=x := by
  let B : Finset (Multiplicative G) := A.image Multiplicative.ofAdd
  have h1 : (1 : Multiplicative G)∈B := Finset.mem_image.mpr ⟨0,h0,rfl⟩
  have hBcard : B.card=A.card := Finset.card_image_of_injective _ Multiplicative.ofAdd.injective
  have hBgen : Subgroup.closure (B : Set (Multiplicative G))=⊤ := by
    have he : (B : Set (Multiplicative G)) = Multiplicative.toAdd ⁻¹' (A:Set G) := by
      ext x
      simp [B]
    rw [he, ← AddSubgroup.toSubgroup_closure, hgen]
    rfl
  have hsize : (Fintype.card (Multiplicative G):ℚ) < (3/2:ℚ)^N*B.card := by
    simpa only [Fintype.card_multiplicative, hBcard] using hN
  obtain ⟨n,hn,hcover⟩ := exists_doubled_eq_univ B h1 hBgen N hsize
  rw [doubled_eq_pow] at hcover
  refine ⟨2^n, pow_le_pow_right' (by decide : 1≤(2:ℕ)) hn, ?_⟩
  intro x
  have hx : Multiplicative.ofAdd x ∈ B^(2^n) := by rw [hcover]; exact Finset.mem_univ _
  obtain ⟨f,hf⟩ := Finset.mem_pow.mp hx
  refine ⟨fun i => (f i).val.toAdd, ?_, ?_⟩
  · intro i
    have hi := (f i).property
    rcases Finset.mem_image.mp hi with ⟨y,hy,he⟩
    have hyx : (f i).val.toAdd=y := congrArg Multiplicative.toAdd he.symm
    change (f i).val.toAdd ∈ A
    exact hyx.symm ▸ hy
  · have hs := congrArg Multiplicative.toAdd hf
    rw [toAdd_list_sum, List.map_ofFn] at hs
    change (List.ofFn (fun i => (f i).val.toAdd)).sum = x at hs
    rw [List.sum_ofFn] at hs
    exact hs
end Additive

theorem exists_uniform_sum_cover_length (δ : ℚ) (hδ : 0<δ) :
    ∃ R:ℕ, ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
      (A : Finset G), 0∈A → AddSubgroup.closure (A:Set G)=⊤ →
      δ*Fintype.card G≤A.card →
      ∃ r≤R, ∀ x:G, ∃ f : Fin r → G, (∀ i, f i∈A) ∧ ∑ i, f i=x := by
  obtain ⟨N,hN0⟩ := exists_nat_gt (2/δ)
  have hbern := one_add_mul_le_pow (by norm_num : (-2:ℚ)≤1/2) N
  have hN : 1/δ < (3/2:ℚ)^N := by
    norm_num at hbern
    have he : 2/δ = 2*(1/δ) := by ring
    rw [he] at hN0
    linarith
  refine ⟨2^N, ?_⟩
  intro G _ _ _ A h0 hgen hdensity
  apply exists_ordered_sum_cover A h0 hgen N
  have hcard : (0:ℚ)<Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hpow : (0:ℚ)≤(3/2:ℚ)^N := by positivity
  have hg : 1 < (3/2:ℚ)^N*δ := (div_lt_iff₀ hδ).mp hN
  have hm := mul_le_mul_of_nonneg_left hdensity hpow
  nlinarith
end Ostmann.Characters

end

end OAI
