import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedAnnulus
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedTail
import OAI.NumberTheory.CubicMoment.Estimates.CoprimePoissonSeries

namespace OAI

/-! Complete nonzero-frequency Poisson control for bounded squarefree
rows.  The actual infinite tail improves as the outer length grows. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma bounded_poisson_large_cutoff {N : ℝ} (hN : 65536 ≤ N) : 16 ≤ N^(3/4:ℝ) := by
  have he : (65536:ℝ)^(3/4:ℝ) = 4096 := by
    rw [show (65536:ℝ) = 16^4 by norm_num,←Real.rpow_natCast (16:ℝ) 4,
      ←Real.rpow_mul (by norm_num)]
    norm_num
  calc
    (16:ℝ) ≤ 4096 := by norm_num
    _ = (65536:ℝ)^(3/4:ℝ) := he.symm
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) hN (by norm_num)

theorem bounded_poisson_total (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (H : ℕ → Finset Eisenstein) (β : Eisenstein → ℂ) (N M A u : ℝ),
      65536 ≤ N → 0 ≤ M → N^(3/2:ℝ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N/2 ≤ norm a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → (∀ j, H j ⊆ frequencyDyad j) →
      ‖∑' j : ℕ, finitePoissonContribution S (H j) β u V A‖ ≤
        K*A^(2/3:ℝ)*N^(5/3:ℝ)*M^2*(1+Real.log N)^d := by
  obtain ⟨K₁,d,hK₁,hshort⟩ := bounded_poisson_dyadic hpnt hHuxley V hV hV'
  obtain ⟨K₂,hK₂,htail⟩ := bounded_poisson_energy_tail V hV hV'
  refine ⟨K₁+K₂,d,by positivity,?_⟩
  intro S H β N M A u hN hM hAlo hS hβ hH
  have hlarge := bounded_poisson_large_cutoff hN
  have hNp : 0 < N := by linarith
  have hA : 0 < A := (Real.rpow_pos_of_pos hNp _).trans_le hAlo
  have hp : ∀ a ∈ S, primary a ∧ N/2 ≤ norm a ∧ norm a ≤ N :=
    fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩
  obtain ⟨n,hn,hprefix⟩ := smallB_poisson_cutoff hNp hlarge
  let F : ℕ → ℂ := fun j => finitePoissonContribution S (H j) β u V A
  let B : ℝ := A^(2/3:ℝ)*N^(5/3:ℝ)*M^2*(1+Real.log N)^d
  have hs : ‖∑ j ∈ Finset.range n, F j‖ ≤ K₁*B := by
    have hs₀ : ‖∑ j ∈ Finset.range n, F j‖ ≤
        K₁*A^(2/3:ℝ)*N^(5/3:ℝ)*M^2*(1+Real.log N)^d :=
      hshort S H (Finset.range n) β N M u A hN hM hA hS hβ
        (fun j hj => hprefix j (Finset.mem_range.mp hj)) hH
    exact hs₀.trans_eq (by dsimp [B]; ring)
  have ht : Summable (fun j => F (j+n)) ∧
      ‖∑' j : ℕ, F (j+n)‖ ≤ K₂*B := by
    have ht₀ : Summable (fun j => F (j+n)) ∧
        ‖∑' j : ℕ, F (j+n)‖ ≤
          K₂*A^(2/3:ℝ)*N^(5/3:ℝ)*M^2*(1+Real.log N)^d :=
      htail S H β N M A u n d (by linarith) hAlo hn hp hβ hH
    exact ⟨ht₀.1,ht₀.2.trans_eq (by dsimp [B]; ring)⟩
  have htotal : ‖∑' j : ℕ, F j‖ ≤ K₁*B+K₂*B :=
    norm_tsum_prefix_tail (F := F) n ht.1 hs ht.2
  exact htotal.trans_eq (by dsimp [B]; ring)

theorem bounded_coprime_dispersion (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (N M A u : ℝ),
      65536 ≤ N → 0 ≤ M → N^(3/2:ℝ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N/2 ≤ norm a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖coprimeDispersionGram S β u V A‖ ≤
        K*A^(2/3:ℝ)*N^(5/3:ℝ)*M^2*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_poisson_total hpnt hHuxley V hV hV'
  refine ⟨K,d,hK,?_⟩
  intro S β N M A u hN hM hAlo hS hβ
  have hA : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < N) _).trans_le hAlo
  have hp : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1 := by
    intro a ha
    refine ⟨(hS a ha).1,(hS a ha).2.1,?_⟩
    intro he
    have hl := (hS a ha).2.2.1
    rw [he,norm_one_eq] at hl
    linarith
  rw [coprimeDispersionGram_eq_poisson_series S hp β u V hV hV' hA]
  exact hbound S frequencyDyad β N M A u hN hM hAlo hS hβ
    (fun _ => Finset.Subset.refl _)

end CubicFirstMoment

end

end OAI
