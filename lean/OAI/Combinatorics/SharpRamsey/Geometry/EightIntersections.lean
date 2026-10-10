import Mathlib

namespace OAI

section
namespace SharpLogRamsey.CapComposition
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*}

def powers (L : Finset (Finset α)) (U : Finset α) : ℕ → Finset (Finset α)
  | 0 => {U}
  | k+1 => (powers L U k).biUnion (fun A => L.image (fun D => A∩D))

lemma powers_step (L : Finset (Finset α)) (U A D : Finset α) (k : ℕ)
    (hA : A ∈ powers L U k) (hD : D ∈ L) : A∩D ∈ powers L U (k+1) :=
  mem_biUnion.mpr ⟨A,hA,mem_image.mpr ⟨D,hD,rfl⟩⟩

lemma powers_card (L : Finset (Finset α)) (U : Finset α) (k : ℕ) :
    (powers L U k).card ≤ L.card^k := by
  induction k with
  | zero => simp [powers]
  | succ k ih =>
    calc
      _  ≤  ∑ A ∈ powers L U k,(L.image (fun D => A∩D)).card := card_biUnion_le
      _  ≤  ∑ _A ∈ powers L U k,L.card := sum_le_sum (fun A hA => card_image_le)
      _ = (powers L U k).card*L.card := by simp
      _  ≤  L.card^k*L.card := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

lemma loss_inter (S A D : Finset α) :
    (S\(A∩D)).card ≤ (S\A).card+(S\D).card := by
  have he : S\(A∩D)=(S\A)∪(S\D) := by ext x; simp; tauto
  rw [he]
  exact card_union_le _ _

lemma remains_nonempty (S A : Finset α) (hS : S.Nonempty) (δ : ℝ) (hδ : δ < 1)
    (hloss : ((S\A).card:ℝ) ≤ δ*S.card) : A.Nonempty := by
  by_contra h
  have he : A=∅ := not_nonempty_iff_eq_empty.mp h
  rw [he,sdiff_empty] at hloss
  have hs : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  nlinarith

theorem eight_intersections (U S : Finset α) (hS : S.Nonempty) (hSU : S ⊆ U)
    (L : Finset (Finset α)) (m q ρ : ℝ) (hm : 0 ≤ m) (_hq : 0 ≤ q)
    (hρ : 0 ≤ ρ) (hρhalf : ρ ≤ 1/2) (hρpow : q*ρ^7 ≤ 1)
    (hfirst : ∀ D ∈ L,(D.card:ℝ) ≤ q*m)
    (hstep : ∀ A,A ⊆ U → A.Nonempty → ∃ D ∈ L,D ⊆ U ∧
      ((S\D).card:ℝ) ≤ (3/100:ℝ)*S.card ∧
      ((A∩D).card:ℝ) ≤ m+ρ*A.card) :
    ∃ A ∈ powers L U 8,A ⊆ U ∧ (A.card:ℝ) ≤ 3*m ∧ (S.card:ℝ)/2 ≤ (S∩A).card := by
  have hU : U.Nonempty := hS.mono hSU
  obtain ⟨D,hD,hDU,hloss,_hcont⟩ := hstep U Subset.rfl hU
  have hinit : D ∈ powers L U 1 := by
    have hh := powers_step L U U D 0 (by simp [powers]) hD
    simpa only [inter_eq_right.mpr hDU] using hh
  have hex : ∀ r : ℕ,r ≤ 7 → ∃ A ∈ powers L U (r+1),A ⊆ U ∧
      ((S\A).card:ℝ) ≤ ((r:ℝ)+1)*(3/100:ℝ)*S.card ∧
      (A.card:ℝ) ≤ 2*m+q*m*ρ^r := by
    intro r
    induction r with
    | zero =>
      intro hr
      refine ⟨D,hinit,hDU,by simpa using hloss,?_⟩
      have hh := hfirst D hD
      simpa only [pow_zero,mul_one] using hh.trans (by linarith : q*m ≤ 2*m+q*m)
    | succ r ih =>
      intro hr
      obtain ⟨A,hA,hAU,hl,hsize⟩ := ih (by omega)
      have hAne : A.Nonempty := remains_nonempty S A hS (((r:ℝ)+1)*(3/100:ℝ))
        (by
          have hh : (r:ℝ) ≤ 6 := by exact_mod_cast (by omega : r ≤ 6)
          linarith) hl
      obtain ⟨E,hE,_hEU,hEl,hEc⟩ := hstep A hAU hAne
      refine ⟨A∩E,powers_step L U A E (r+1) hA hE,inter_subset_left.trans hAU,?_,?_⟩
      · have hh : ((S\(A∩E)).card:ℝ) ≤ (S\A).card+(S\E).card := by exact_mod_cast loss_inter S A E
        push_cast
        linarith
      · have hh := mul_le_mul_of_nonneg_left hsize hρ
        rw [pow_succ]
        have hb : 2*m*ρ ≤ m := by nlinarith
        nlinarith
  obtain ⟨A,hA,hAU,hl,hsize⟩ := hex 7 (le_refl _)
  refine ⟨A,hA,hAU,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hρpow hm
    nlinarith
  · have he : ((S\A).card:ℝ)+(S∩A).card=S.card := by exact_mod_cast card_sdiff_add_card_inter S A
    norm_num at hl
    linarith

end
end SharpLogRamsey.CapComposition

end

end OAI
