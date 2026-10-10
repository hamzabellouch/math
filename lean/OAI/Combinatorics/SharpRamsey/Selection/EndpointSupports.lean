import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.LevelLosses
import OAI.Combinatorics.SharpRamsey.Selection.SupportIncidence

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

def Law.swap (p : Law (A × B)) : Law (B × A) where
  mass z := p.mass (z.2,z.1)
  nonneg z := p.nonneg _
  total := by
    rw [Fintype.sum_prod_type, sum_comm, ← Fintype.sum_prod_type]
    exact p.total

@[simp] lemma Law.swap_mass (p : Law (A × B)) (b : B) (a : A) :
    p.swap.mass (b,a) = p.mass (a,b) := rfl

@[simp] lemma Law.swap_fst (p : Law (A × B)) : p.swap.fst = p.snd := rfl

@[simp] lemma Law.swap_snd (p : Law (A × B)) : p.swap.snd = p.fst := rfl

lemma Law.swap_eq_map (p : Law (A × B)) : p.swap = p.map Prod.swap := by
  ext ⟨b,a⟩
  exact (p.map_mass_injective Prod.swap Prod.swap_injective (a,b)).symm

@[simp] lemma entropy_swap (p : Law (A × B)) : entropy p.swap = entropy p := by
  rw [Law.swap_eq_map]
  exact entropy_map_eq_of_injective p Prod.swap Prod.swap_injective

lemma Law.swap_condFst (p : Law (A × B)) (a : A) (ha : p.fst.mass a ≠ 0) :
    p.swap.condFst a = p.condSnd a := by
  ext endpoint
  exact (p.swap.condFst_mass a ha endpoint).trans (p.condSnd_mass a ha endpoint).symm

lemma goodSecond_swap (p : Law (A × B)) {M : ℝ} (hM : 0 < M)
    (L κ ε : ℝ) (a : A) : goodSecond p.swap M L κ ε a ↔ goodFirst p M L κ ε a := by
  unfold goodSecond goodFirst conditionalHeavy
  simp only [Law.swap_snd]
  constructor <;> intro h
  · have ha : p.fst.mass a ≠ 0 := (lt_of_lt_of_le (by positivity) h.1).ne'
    rw [Law.swap_condFst p a ha] at h
    exact h
  · have ha : p.fst.mass a ≠ 0 := (lt_of_lt_of_le (by positivity) h.1).ne'
    rw [Law.swap_condFst p a ha]
    exact h

theorem badFirst_mass (p : Law (A × B)) (S : Finset (A × B))
    (hs : ∀ x, x ∉ S → p.mass x = 0) (D : Finset A)
    (hD : ∀ a, a ∉ D → p.fst.mass a = 0)
    (M L κ ε : ℝ) (hM : 0 < M) (hcard : (D.card:ℝ) ≤ M)
    (hκ : 0 < κ) (hε : 0 < ε) :
    p.fst.event (univ.filter (fun a => ¬goodFirst p M L κ ε a)) ≤
      exp (-κ) + (L - entropy p + S.card * exp (-L)) / (κ * ε) := by
  have hs' : ∀ x, x ∉ S.image Prod.swap → p.swap.mass x = 0 := by
    rintro ⟨b,a⟩ hx
    rw [Law.swap_mass]
    apply hs
    intro h
    exact hx (mem_image.mpr ⟨(a,b),h,rfl⟩)
  have H := badSecond_mass p.swap (S.image Prod.swap) hs' D
    hD M L κ ε hM hcard hκ hε
  have he : (S.image Prod.swap).card = S.card := card_image_of_injective S Prod.swap_injective
  simpa only [Law.swap_snd, goodSecond_swap p hM L κ ε, entropy_swap, he] using H

lemma levelSet_card_le_domain (p : Law A) (S : Finset A)
    (hS : ∀ a, a ∉ S → p.mass a = 0) (b : Levels p) :
    (levelSet p b).card ≤ S.card := by
  apply card_le_card
  intro a ha
  by_contra hnot
  have hp := (mem_filter.mp ha).2.1
  rw [hS a hnot] at hp
  exact lt_irrefl _ hp

structure AuxiliarySupport (p : Law A) (good : Finset A) (M κ : ℝ) where
  law : Law (retainedLevels p good M κ)
  size : ∀ b : retainedLevels p good M κ,
    M * exp (-κ) / 2 ≤ ((levelSet p b ∩ good).card : ℝ) ∧
      ((levelSet p b ∩ good).card : ℝ) ≤ M
  density : ∀ a, (∑ b : retainedLevels p good M κ, law.mass b *
    (if a ∈ levelSet p b ∩ good then 1 / ((levelSet p b ∩ good).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a

lemma auxiliarySupport_exists (p : Law A) (good : Finset A) {M κ : ℝ}
    (hM : 0 < M) (hκ : 0 < κ)
    (hcap : ∀ b, ((levelSet p b).card : ℝ) ≤ M)
    (hbudget : (∑ b, (p.map (levelIndex p)).mass b * levelLoss p M b) / κ +
      2 * exp 1 * p.event (univ \ good) ≤ 1/2) :
    Nonempty (AuxiliarySupport p good M κ) := by
  obtain ⟨ρ,hsize,hρ⟩ := auxiliary_supports p good hM hκ hcap hbudget
  exact ⟨⟨ρ,hsize,hρ⟩⟩

lemma mean_levelLoss_nonneg (p : Law A) (M : ℝ)
    (hcap : ∀ b, ((levelSet p b).card : ℝ) ≤ M) :
    0 ≤ ∑ b, (p.map (levelIndex p)).mass b * levelLoss p M b :=
  sum_nonneg (fun b _ => mul_nonneg ((p.map (levelIndex p)).nonneg b)
    (levelLoss_nonneg p b (hcap b)))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem reciprocal_auxiliary_choices {n : ℕ} (hdim : Module.finrank K V = n+3)
    (p : Law (Projectivization K (Module.Dual K V) × Projectivization K V))
    (S : Finset (Projectivization K (Module.Dual K V) × Projectivization K V))
    (DA : Finset (Projectivization K (Module.Dual K V)))
    (DB : Finset (Projectivization K V))
    (hs : ∀ z, z ∉ S → p.mass z = 0)
    (hf : ∀ z, 0 < p.mass z → z.1.rep z.2.rep = 0)
    (hDA : ∀ a, a ∉ DA → p.fst.mass a = 0)
    (hDB : ∀ b, b ∉ DB → p.snd.mass b = 0)
    (MA MB C L κ ε : ℝ) (hMA : 0 < MA) (hMB : 0 < MB) (hC : 1 ≤ C)
    (hA : (DA.card : ℝ) ≤ MA) (hB : (DB.card : ℝ) ≤ MB)
    (hcap : MA * MB ≤ C * (Nat.card K : ℝ)^(n+3))
    (hκ : 0 < κ) (hε : 0 < ε)
    (hsmall :
      (2 * (log (2*C*(Nat.card K:ℝ)^(n+2)) - entropy p +
        log (entropy p.fst+2) + log (entropy p.snd+2) + 2)) / κ +
      2 * exp 1 * (exp (-κ) + (L - entropy p + S.card * exp (-L)) / (κ*ε)) ≤ 1/2) :
    Nonempty (AuxiliarySupport p.fst (univ.filter (goodFirst p MA L κ ε)) MA κ) ∧
    Nonempty (AuxiliarySupport p.snd (univ.filter (goodSecond p MB L κ ε)) MB κ) := by
  have hLA (b : Levels p.fst) : ((levelSet p.fst b).card : ℝ) ≤ MA :=
    (show ((levelSet p.fst b).card : ℝ) ≤ DA.card by
      exact_mod_cast levelSet_card_le_domain p.fst DA hDA b).trans hA
  have hLB (b : Levels p.snd) : ((levelSet p.snd b).card : ℝ) ≤ MB :=
    (show ((levelSet p.snd b).card : ℝ) ≤ DB.card by
      exact_mod_cast levelSet_card_le_domain p.snd DB hDB b).trans hB
  have hloss := Incidence.reciprocal_level_losses hdim p.swap
    (by rintro ⟨a,b⟩ h; exact hf (b,a) (by exact h))
    hMB hMA hC (by simpa only [mul_comm MA] using hcap)
    hLB hLA
  rw [entropy_swap] at hloss
  change (∑ b, (p.snd.map (levelIndex p.snd)).mass b * levelLoss p.snd MB b) +
    (∑ b, (p.fst.map (levelIndex p.fst)).mass b * levelLoss p.fst MA b) ≤
    2 * (log (2*C*(Nat.card K:ℝ)^(n+2)) - entropy p +
      log (entropy p.snd+2) + log (entropy p.fst+2) + 2) at hloss
  have hna := mean_levelLoss_nonneg p.fst MA hLA
  have hnb := mean_levelLoss_nonneg p.snd MB hLB
  have hbadA := badFirst_mass p S hs DA hDA MA L κ ε hMA hA hκ hε
  have hbadB := badSecond_mass p S hs DB hDB MB L κ ε hMB hB hκ hε
  have heA : univ \ univ.filter (goodFirst p MA L κ ε) =
      univ.filter (fun a => ¬goodFirst p MA L κ ε a) := by ext; simp
  have heB : univ \ univ.filter (goodSecond p MB L κ ε) =
      univ.filter (fun a => ¬goodSecond p MB L κ ε a) := by ext; simp
  constructor
  · apply auxiliarySupport_exists p.fst _ hMA hκ hLA
    rw [heA]
    apply le_trans _ hsmall
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hκ.le
      linarith
    · exact mul_le_mul_of_nonneg_left hbadA (by positivity)
  · apply auxiliarySupport_exists p.snd _ hMB hκ hLB
    rw [heB]
    apply le_trans _ hsmall
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hκ.le
      linarith
    · exact mul_le_mul_of_nonneg_left hbadB (by positivity)

end
end SharpLogRamsey.Selection

end

end OAI
