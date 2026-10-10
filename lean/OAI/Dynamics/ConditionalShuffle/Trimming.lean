import OAI.Dynamics.ConditionalShuffle.Instrument

namespace OAI

noncomputable section
namespace Thorp.Trim
open scoped Classical
variable {I G H : Type*} [fintype_I : Fintype I] [Group G] [fintype_G : Fintype G] [Group H] [Fintype H]

def repair (ψ : (I → H) →* G) (μ : G → ℝ) : G → ℝ :=
  if discarded ψ μ ≤ 1 / 2 then normalized ψ μ else fun _ => (Fintype.card G : ℝ)⁻¹

lemma repair_nonneg (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (g : G) :
    0 ≤ repair ψ μ g := by
  let retained_fintype_I := fintype_I
  unfold repair
  split_ifs with h
  · exact normalized_nonneg ψ μ hμ (by linarith) g
  · positivity

lemma repair_sum (ψ : (I → H) →* G) (μ : G → ℝ) (h1 : ∑ g, μ g = 1) :
    ∑ g, repair ψ μ g = 1 := by
  let retained_fintype_I := fintype_I
  unfold repair
  split_ifs with h
  · exact normalized_sum ψ μ h1 (by linarith)
  · simp

lemma tv_prob_le_one {X : Type*} [Fintype X] (μ ν : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hμ1 : ∑ x, μ x = 1) (hν1 : ∑ x, ν x = 1) : tv μ ν ≤ 1 := by
  unfold tv
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (μ x) 0 (ν x))
  simp only [sub_zero, zero_sub, abs_neg] at h
  simp only [abs_of_nonneg (hμ _), abs_of_nonneg (hν _), Finset.sum_add_distrib,
    hμ1, hν1] at h
  linarith

lemma repair_tv (ψ : (I → H) →* G) (μ : G → ℝ)
    (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1) :
    tv μ (repair ψ μ) ≤ 2 * discarded ψ μ := by
  let retained_fintype_I := fintype_I
  unfold repair
  split_ifs with h
  · rw [normalized_tv ψ μ hμ h1 (by linarith)]
    linarith [discarded_nonneg ψ μ hμ]
  · have hu : ∑ _ : G, (Fintype.card G : ℝ)⁻¹ = 1 := by simp
    exact (tv_prob_le_one μ _ hμ (fun _ => by positivity) h1 hu).trans (by linarith)

lemma repair_coset (ψ : (I → H) →* G) (μ : G → ℝ)
    (hμ : ∀ g, 0 ≤ μ g) (i : I) (g : G) :
    cosetMass ψ (repair ψ μ) i g ≤ 4 * (Fintype.card H : ℝ) / Fintype.card G := by
  let retained_fintype_I := fintype_I
  unfold repair
  split_ifs with h
  · exact normalized_coset ψ μ hμ h i g
  · simp only [cosetMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : 0 ≤ (Fintype.card H : ℝ) / Fintype.card G := by positivity
    simp only [div_eq_mul_inv] at hn ⊢
    linarith

lemma point_le_coset (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (i : I) (g : G) :
    μ g ≤ cosetMass ψ μ i g := by
  let retained_fintype_I := fintype_I
  let retained_fintype_G := fintype_G
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun h => μ (g * ψ (Pi.mulSingle i h)))
    (fun h _ => hμ _) (Finset.mem_univ (1 : H))
  simpa [cosetMass] using h

lemma dirac_discarded [Nonempty I] [DecidableEq G] (ψ : (I → H) →* G) (a : G)
    (hc : 2 * ((Fintype.card H : ℝ) / Fintype.card G) < 1) :
    discarded ψ (fun g => if g = a then 1 else 0) = 1 := by
  let μ : G → ℝ := fun g => if g = a then 1 else 0
  have hμ : ∀ g, 0 ≤ μ g := fun g => by dsimp [μ]; split_ifs <;> norm_num
  have ha : ¬ good ψ μ a := by
    intro h
    have hb := (point_le_coset ψ μ hμ (Classical.arbitrary I) a).trans (h _)
    simp only [μ, ite_eq_left rfl] at hb
    linarith
  change discarded ψ μ = 1
  unfold discarded
  rw [Finset.sum_eq_single a]
  · simp [ha, μ]
  · intro b _ hba
    simp only [μ, ite_eq_right hba]
    split_ifs <;> rfl
  · simp

end Thorp.Trim

namespace Thorp.Trim
open scoped Classical
variable {I H : Type*} [fintype_I : Fintype I] [Nonempty I] [Group H] [Fintype H]
variable {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]

def signDichotomy (μ : Equiv.Perm α → ℝ) : Prop :=
  (∑ g, (μ g : ℂ) * Specht.complexSign g = 0) ∨
    ∃ a, μ = fun g => if g = a then 1 else 0

lemma repair_bias (ψ : (I → H) →* Equiv.Perm α) (μ : Equiv.Perm α → ℝ)
    (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1)
    (hc : 2 * ((Fintype.card H : ℝ) / Fintype.card (Equiv.Perm α)) < 1)
    (hb : signDichotomy μ) :
    ‖∑ g, (repair ψ μ g : ℂ) * Specht.complexSign g‖ ≤ 2 * discarded ψ μ := by
  unfold repair
  split_ifs with h
  · have hz : ∑ g, (μ g : ℂ) * Specht.complexSign g = 0 := by
      rcases hb with hb | ⟨a, rfl⟩
      · exact hb
      · rw [dirac_discarded ψ a hc] at h
        norm_num at h
    exact normalized_bias ψ μ hμ h1 (by linarith) Specht.complexSign
      (fun g => (Specht.complexSign_norm g).le) hz
  · rw [← Finset.mul_sum, Specht.complexSign_sum, mul_zero, norm_zero]
    exact mul_nonneg (by norm_num) (discarded_nonneg ψ μ hμ)

end Thorp.Trim

end

end OAI
