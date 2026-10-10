import OAI.NumberTheory.TotientAsymptotic.UntruncatedCount
import OAI.NumberTheory.TotientAsymptotic.SmoothCutoffTail
import OAI.NumberTheory.TotientAsymptotic.MassUpper

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma full_prime_mass_le_G (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p) ≤ G x (m x) := by
  obtain ⟨C,hC,hprime⟩ := full_prime_mass_bound hbox
  obtain ⟨K,hK,hproj⟩ := uniform_projected_volume_bound hren
  have hcut := ((tendsto_natCast_atTop_atTop.comp P_tendsto).const_mul_atTop lam_pos).eventually
    (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hcut,(fullPrimeFactor_tendsto C hK).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    eventually_ge_atTop 2] with H hc hf hH
  filter_upwards [theta_eventually_mem,B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    inverse_scale_bound,hproj,m_tendsto.eventually (eventually_ge_atTop H)] with x hs hB hscale hp hm
  have hPH := P_lt_self hH
  have hL : 0<L x H := by unfold L; omega
  have hPm : P H≤ m x := by omega
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp (P H) hPm)
  have ha : 0 ≤ (1+bandPrimeError C (9/10) (P H))*Real.exp (simplexBoxTail 4 (P H)) := by
    have hh := bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ)<9/10) (P H)
    positivity
  calc
    _ ≤ (1+bandPrimeError C (9/10) (P H))*Real.exp (simplexBoxTail 4 (P H))*G x (L x H) :=
      hprime hs.1 hc hB hscale hL
    _ ≤ (1+bandPrimeError C (9/10) (P H))*Real.exp (simplexBoxTail 4 (P H))*
        (projectedEnvelope K (P H)*G x (m x)) := mul_le_mul_of_nonneg_left hG ha
    _ = fullPrimeFactor C K H*G x (m x) := by unfold fullPrimeFactor; ring
    _ ≤ _ := mul_le_of_le_one_left (G_pos hB _).le hf.le

lemma cofactorScale_tendsto : Tendsto cofactorScale atTop atTop := by
  apply tendsto_atTop_mono (fun H => ?_) (tendsto_natCast_atTop_atTop.comp P_tendsto)
  have hh : 1 ≤ (rho^(P H))⁻¹ := (one_le_inv₀ (pow_pos rho_pos _)).mpr
    (pow_le_one₀ rho_pos.le rho_lt_one.le)
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hh

lemma terminal_band_lower {x : ℝ} {H : ℕ} (hs : 0 ≤ theta x) (hm : P H ≤ m x) :
    lam*cofactorScale H ≤ bandScale x (L x H) := by
  have he : m x-L x H=P H := by unfold L; omega
  simp only [bandScale,he,cofactorScale]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (alpha_ge_lam hs) (Nat.cast_nonneg (P H)))
      (inv_nonneg.mpr (pow_pos rho_pos (P H)).le)

lemma untruncated_cofactor_smooth {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hL : 0<L x H) (hη : IsUntruncatedRemainder x H η) :
    largestPrimeFactor η.cofactor ≤ remainderPrimeBound x (L x H) := by
  have hp := basic_remainder_prime_bound hη.2.1 (⟨L x H-1,by omega⟩ : Fin (L x H))
  have he : L x H-1+1=L x H := by omega
  rw [he] at hp
  exact hη.2.2.trans (by
    simpa only [primeOnly,remainderPrime,dite_eq_left (show 1≤L x H ∧ L x H≤L x H from ⟨hL,le_rfl⟩)] using hp)

lemma untruncated_weight_product {x : ℝ} {H : ℕ} (S : Finset (RemainderDatum (L x H)))
    (hS : ∀ η ∈ S, IsUntruncatedRemainder x H η) :
    (∑ η ∈ S, (η.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight η.primes) ≤
      (∑ a ∈ S.image RemainderDatum.cofactor, (a.totient : ℝ)⁻¹)*
        ∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p := by
  classical
  let F : RemainderDatum (L x H) → ℕ × (Fin (L x H) → ℕ) := fun η => (η.cofactor,η.primes)
  have hinj : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa only [F,Prod.mk.injEq,RemainderDatum.mk.injEq,and_comm] using h
  have he : (∑ η ∈ S, (η.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight η.primes)=
      ∑ z ∈ S.image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image (fun η _ ξ _ hh => hinj hh)]
  rw [he]
  have hsub : S.image F ⊆ S.image RemainderDatum.cofactor ×ˢ fullPrimeTuples x H := by
    intro z hz
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨η,hη,rfl⟩,untruncated_prime_mem (hS η hη)⟩
  calc
    _ ≤ ∑ z ∈ S.image RemainderDatum.cofactor ×ˢ fullPrimeTuples x H,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul]

end TotientAsymptotic

end

end OAI
