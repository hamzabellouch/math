import OAI.NumberTheory.JointDickman.Amplification.LatentRowSquareMass

namespace OAI

/-! # Bounded row and normalized total second moments of the latent graph -/

namespace JointDickman
open Finset Filter Classical
open PublishedInputs
open scoped Topology

private theorem finite_average_square_bound {M : ℕ} {Ω : Type*} [Fintype Ω]
    (hM : 0 < M) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f : Fin M → Ω → ℝ) {D : ℝ}
    (hf : ∀ i, finiteExpectation w (fun x => (f i x)^2) ≤ D) :
    finiteExpectation w (fun x => ((∑ i, f i x)/(M : ℝ))^2) ≤ D := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hpoint (x : Ω) : ((∑ i, f i x)/(M : ℝ))^2 ≤ (∑ i, (f i x)^2)/(M : ℝ) := by
    have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin M)) (fun _ => (1 : ℝ)) (fun i => f i x)
    simp only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hc
    rw [div_pow]
    refine (div_le_div_of_nonneg_right hc (sq_nonneg (M : ℝ))).trans_eq ?_
    field_simp
  calc
    _ ≤ finiteExpectation w (fun x => (∑ i, (f i x)^2)/(M : ℝ)) :=
      finiteExpectation_mono w hw hpoint
    _ = (∑ i, finiteExpectation w (fun x => (f i x)^2))/(M : ℝ) := by
      simp only [div_eq_mul_inv,finiteExpectation_mul_const,finiteExpectation_sum]
    _ ≤ (∑ _i : Fin M, D)/(M : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum (fun i _ => hf i)) hMr.le
    _ = D := by simp [ne_of_gt hMr]

/-- Both conclusions of the manuscript's integrated-row-moments
proposition hold for the actual independent-site kernel. -/
theorem latentPrimeSiteKernel_moments
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ K D : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧ 0 < K ∧ 0 < D ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        T ≤ auxiliaryCutoff B → (T : ℝ) ≤ (B : ℝ)^2 →
        η*(B : ℝ)^(32/100 : ℝ) ≤ H → 0 < M →
        ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        (∀ i : Fin M, siteRowSquareMass (fun _ : Fin M => independentPrimeSetMass B)
          (latentPrimeSiteKernel B L T H M τ C χ) i ≤ K*(B : ℝ)^(-(21/100 : ℝ))) ∧
        (∀ i : Fin M, finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
          (fun x => (siteRowSum (latentPrimeSiteKernel B L T H M τ C χ) i x)^2) ≤ D) ∧
        finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
          (fun x => ((∑ i : Fin M, siteRowSum (latentPrimeSiteKernel B L T H M τ C χ) i x)/(M : ℝ))^2) ≤ D := by
  obtain ⟨τ,K,hτ,hτcap,hτsampling,hK,hrows⟩ := latentPrimeSiteKernel_row_square_mass hFord hM hL hη hcap
  obtain ⟨J,hJ,hmean⟩ := latentPrimeSiteKernel_row_mean hFord hM
  refine ⟨τ,K,J^2+K,hτ,hτcap,hτsampling,hK,by positivity,?_⟩
  filter_upwards [hrows,hmean,eventually_ge_atTop 1] with B hrows hmean hB
  intro T H M C hT hTs hcut hT2 hH hMpos χ hχ
  let p := fun _ : Fin M => independentPrimeSetMass B
  let kernel := latentPrimeSiteKernel B L T H M τ C χ
  have hp : ∀ (i : Fin M) a, 0 ≤ p i a := fun _ => independentPrimeSetMass_nonneg B
  have hpone : ∀ i : Fin M, ∑ a, p i a = 1 := fun _ => independentPrimeSetMass_sum B
  have hdiag : ∀ i a, kernel i i a a = 0 := fun i a => candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _
  have hrow (i : Fin M) : siteRowSquareMass p kernel i ≤ K*(B : ℝ)^(-(21/100 : ℝ)) :=
    hrows T H M C hT hTs hcut hT2 hH χ hχ i
  have hpower : (B : ℝ)^(-(21/100 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ B by exact_mod_cast hB) (show -(21/100 : ℝ) ≤ 0 by norm_num)
  have hsquare (i : Fin M) : finiteExpectation (siteProductMass p)
      (fun x => (siteRowSum kernel i x)^2) ≤ J^2+K := by
    refine (siteRow_sq_le p hp hpone kernel hdiag i J
      (hmean L T H M τ C hT hTs χ hχ i)).trans ?_
    exact add_le_add le_rfl ((hrow i).trans (mul_le_of_le_one_right hK.le hpower))
  exact ⟨hrow,hsquare,finite_average_square_bound hMpos (siteProductMass p)
    (siteProductMass_nonneg p hp) (fun i x => siteRowSum kernel i x) hsquare⟩

end JointDickman

end OAI
