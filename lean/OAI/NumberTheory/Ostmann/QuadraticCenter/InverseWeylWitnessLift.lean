import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylWitness

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

def witnessIntegerLift (M : ℕ) (a t h : ℤ) : ℤ :=
  a*t-(round ((a:ℝ)*((h:ℝ)+(t:ℝ)/(M:ℝ)))-a*h)*(M:ℤ)

theorem witnessIntegerLift_abs {M : ℕ} (hM : 0 < M) (a t h : ℤ) :
    |(witnessIntegerLift M a t h:ℝ)| =
      (M:ℝ)*integerDistance ((a:ℝ)*((h:ℝ)+(t:ℝ)/(M:ℝ))) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have he : (witnessIntegerLift M a t h:ℝ) =
      (M:ℝ)*((a:ℝ)*((h:ℝ)+(t:ℝ)/(M:ℝ))-
        (round ((a:ℝ)*((h:ℝ)+(t:ℝ)/(M:ℝ))):ℤ)) := by
    unfold witnessIntegerLift
    push_cast
    field_simp
    ring
  rw [he,abs_mul,abs_of_pos hMr]
  rfl

theorem witnessIntegerLift_congruence (M : ℕ) (a t h tp : ℤ) (p : ℕ)
    (hpM : (p:ℤ) ∣ (M:ℤ)) (hpt : (p:ℤ) ∣ t-tp) :
    (p:ℤ) ∣ witnessIntegerLift M a t h-a*tp := by
  have h₁ := dvd_mul_of_dvd_right hpt a
  have h₂ := dvd_mul_of_dvd_right hpM
    (round ((a:ℝ)*((h:ℝ)+(t:ℝ)/(M:ℝ)))-a*h)
  convert dvd_sub h₁ h₂ using 1
  simp only [witnessIntegerLift]
  ring

theorem exists_witness_integer_lift {M : ℕ} (hM : 0 < M) (a t h : ℤ) {E : ℝ}
    (herr : integerDistance ((a:ℝ)*((h:ℝ)+(t:ℝ)/(M:ℝ))) ≤ E) :
    ∃ n : ℤ, |(n:ℝ)| ≤ (M:ℝ)*E ∧
      ∀ (p : ℕ) (tp : ℤ), (p:ℤ) ∣ (M:ℤ) → (p:ℤ) ∣ t-tp → (p:ℤ) ∣ n-a*tp := by
  refine ⟨witnessIntegerLift M a t h,?_,?_⟩
  · rw [witnessIntegerLift_abs hM]
    exact mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg _)
  · intro p tp hpM hpt
    exact witnessIntegerLift_congruence M a t h tp p hpM hpt

theorem centered_quadratic_witness_lift {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i,NeZero (p i)] [NeZero (∏ i,p i)]
    (hp : ∀ i,(p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i,Finset (ZMod (p i))) (mInv : ZMod (∏ i,p i))
    (s v M : ℕ) (hM : 0 < M) (R : ℝ) (h t : ℤ) :
    let d := ∏ i,p i
    let N := Real.sqrt (R/((s:ℝ)*v/(d:ℕ)))
    let Y := N/d
    ∀ ε B : ℝ, (d:ℝ) ≤ N → 0 < ε → ε ≤ 1 → 1 ≤ B →
      B ≤ Y*(ε/(10*cutoffFourierBound)) →
      1024*(1+Real.log (2*Y)) ≤ (ε/(10*cutoffFourierBound))^2*B →
      Real.sqrt ((2:ℝ)^Fintype.card ι)*ε ≤
        ‖centeredQuadraticSum p hcop S mInv s v 1 R h ((t:ℝ)/(M:ℝ))‖ →
      ∃ (q : ℕ) (n : ℤ),1 ≤ q ∧ (q:ℝ) ≤ 2*B ∧
        |(n:ℝ)| ≤ (M:ℝ)*B/(Y*(ε/(10*cutoffFourierBound)))^2 ∧
        ∀ (ℓ : ℕ) (tp : ℤ), (ℓ:ℤ) ∣ (M:ℤ) → (ℓ:ℤ) ∣ t-tp →
          (ℓ:ℤ) ∣ n-((q*s*v*d:ℕ):ℤ)*tp := by
  intro d N Y ε B hdN hε hε1 hB hBsmall hscale hlarge
  obtain ⟨q,hq,hqB,herr⟩ := centered_quadratic_witness_inverse p hp hcop S mInv s v
    R h ((t:ℝ)/(M:ℝ)) ε B hdN hε hε1 hB hBsmall hscale hlarge
  have hfreq : (((q*s*v*d:ℕ):ℤ):ℝ)*((h:ℝ)+(t:ℝ)/(M:ℝ)) =
      (q:ℝ)*(((h:ℝ)+(t:ℝ)/(M:ℝ))*((s:ℝ)*v*d)) := by push_cast; ring
  have hh := exists_witness_integer_lift hM ((q*s*v*d:ℕ):ℤ) t h
    (E := B/(Y*(ε/(10*cutoffFourierBound)))^2) (by rw [hfreq]; exact herr)
  obtain ⟨n,hn,hcong⟩ := hh
  refine ⟨q,n,hq,hqB,?_,hcong⟩
  simpa only [mul_div_assoc] using hn

end Ostmann.QuadraticCenter

end

end OAI
