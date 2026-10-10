import OAI.NumberTheory.CubicMoment.Decomposition.StoppedFilteredCore
import OAI.NumberTheory.CubicMoment.Estimates.CoreIndexLogCount

namespace OAI

/-! A pointwise all-frequency estimate for bounded squarefree rows.
The tiny noncube cores and the cube frequencies use the actual finite
coefficient mass; all remaining cores use the proved hybrid sieve. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bounded_primary_character_row (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) {N M : ℝ} (hN : 0 ≤ N)
    (hS : ∀ a ∈ S, primary a ∧ norm a ≤ N) (hβ : ∀ a ∈ S, ‖β a‖ ≤ M)
    (v : Eisenstein) : ‖∑ a ∈ S, β a*cubicSymbol a v‖^2 ≤ 324*N^2*M^2 := by
  have hc := primary_support_card_le S hN hS
  have he : (∑ a ∈ S, ‖β a‖^2) ≤ 18*N*M^2 := by
    calc
      _ ≤ ∑ _a ∈ S, M^2 := Finset.sum_le_sum (fun a ha =>
        pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ a ha) 2)
      _ = (S.card:ℝ)*M^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg M)
  exact (cubic_character_row_sq S (fun a ha => (hS a ha).1) β v).trans
    ((mul_le_mul hc he (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (by positivity)).trans_eq (by ring))

theorem bounded_short_noncube_mass (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N M B : ℝ), 65536 ≤ N → 0 ≤ B →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → 8*B ≤ N^(3/4:ℝ) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ a : Eisenstein, a^3 = v) →
      (∑ v ∈ H, ‖∑ a ∈ S, β a*cubicSymbol a v‖^2) ≤
        K*(1+(largeCoreDyadicIndices 1 B).card)*B^(1/3:ℝ)*N^2*M^2 := by
  obtain ⟨K,hK,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  let c : ℝ := ((1:ℝ)/5832)^(-(1/4:ℝ))
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  refine ⟨104976+18*K*(c+1),by positivity,?_⟩
  intro S H β N M B hN hB hS hβ hsize hH
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  let f := fun v => ‖∑ a ∈ S, β a*cubicSymbol a v‖^2
  let I := largeCoreDyadicIndices 1 B
  have he : (∑ a ∈ S, ‖β a‖^2) ≤ 18*N*M^2 := by
    have hcard := primary_support_card_le S hNp.le
      (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
    calc
      _ ≤ ∑ _a ∈ S, M^2 := Finset.sum_le_sum (fun a ha =>
        pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ a ha) 2)
      _ = (S.card:ℝ)*M^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
  have hsmall : (∑ v ∈ H.filter (fun v => v ∈ lowNoncubeSupport 1 (B^(1/3:ℝ))), f v) ≤
      104976*B^(1/3:ℝ)*N^2*M^2 := by
    have hcard : ((H.filter (fun v => v ∈ lowNoncubeSupport 1 (B^(1/3:ℝ)))).card:ℝ) ≤
        324*B^(1/3:ℝ) := by
      simpa only [mul_one] using
        (Nat.cast_le.mpr (Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2))).trans
          (lowNoncubeSupport_card (by norm_num : (0:ℝ) ≤ 1) (Real.rpow_nonneg hB _))
    calc
      _ ≤ ∑ _v ∈ H.filter (fun v => v ∈ lowNoncubeSupport 1 (B^(1/3:ℝ))),
          324*N^2*M^2 := Finset.sum_le_sum (fun v _ =>
            bounded_primary_character_row S β hNp.le
              (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩) hβ v)
      _ = ((H.filter (fun v => v ∈ lowNoncubeSupport 1 (B^(1/3:ℝ)))).card:ℝ)*
          (324*N^2*M^2) := by simp
      _ ≤ (324*B^(1/3:ℝ))*(324*N^2*M^2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hrow (q : ℕ × ℕ) (hq : q ∈ I) :
      (∑ v ∈ coreDyadicBlock B q.1 q.2, f v) ≤
        (18*K*(c+1))*B^(1/3:ℝ)*N^2*M^2 := by
    have hq' := (Finset.mem_filter.mp hq).2
    have hm := hcore S (coreDyadicBlock B q.1 q.2) β N B 1 q.1 q.2
      hN hB (by norm_num) hS hq'.1.le
      ((mul_le_mul_of_nonneg_left hq'.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
      (Finset.Subset.refl _)
    have hp : N^(1-1/20000:ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
        (by norm_num : (1-1/20000:ℝ) ≤ 1)
    have hb : N*c+N^(1-1/20000:ℝ) ≤ N*(c+1) := by nlinarith
    exact hm.trans ((mul_le_mul
      (mul_le_mul_of_nonneg_left hb (mul_nonneg hK.le (Real.rpow_nonneg hB _))) he
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)).trans_eq (by dsimp [c]; ring))
  have hlarge := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,nsmul_eq_mul] at hlarge
  apply (noncube_frequency_mass_split H hH f (fun _ => sq_nonneg _)).trans
    ((add_le_add hsmall hlarge).trans _)
  have hi : 0 ≤ (I.card:ℝ) := Nat.cast_nonneg _
  have hs := mul_nonneg (show 0 ≤ 104976*(I.card:ℝ)+18*K*(c+1) by positivity)
    (show 0 ≤ B^(1/3:ℝ)*N^2*M^2 by positivity)
  dsimp only [I] at *
  nlinarith

theorem bounded_short_all_frequency_mass (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N M B : ℝ), 65536 ≤ N → 1 ≤ B →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → 8*B ≤ N^(3/4:ℝ) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ v ∈ H, ‖∑ a ∈ S, β a*cubicSymbol a v‖^2) ≤
        K*B^(1/3:ℝ)*N^2*M^2*(1+Real.log B)^2 := by
  obtain ⟨K,hK,hbound⟩ := bounded_short_noncube_mass hHuxley
  obtain ⟨C,hC,hcount⟩ := core_dyadic_index_log_count
  refine ⟨K*(1+C)+5832,by positivity,?_⟩
  intro S H β N M B hN hB hS hβ hsize hH
  have hNp : 0 < N := by linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hl : 1 ≤ 1+Real.log B := by linarith [Real.log_nonneg hB]
  have hI : 1+((largeCoreDyadicIndices 1 B).card:ℝ) ≤ (1+C)*(1+Real.log B)^2 := by
    have hc := hcount 1 B B hB hB (by nlinarith)
    have hp : 1 ≤ (1+Real.log B)^2 := one_le_pow₀ hl
    nlinarith
  let HN := H.filter (fun v => ¬∃ a : Eisenstein, a^3 = v)
  let HC := H.filter (fun v => ∃ a : Eisenstein, a^3 = v)
  have hn := hbound S HN β N M B hN hB0 hS hβ hsize
    (fun v hv => ⟨(hH v (Finset.mem_filter.mp hv).1).1,
      (hH v (Finset.mem_filter.mp hv).1).2,(Finset.mem_filter.mp hv).2⟩)
  have hsub : HC ⊆ nonzeroCubeNormBall B := by
    intro v hv
    exact mem_nonzeroCubeNormBall (hH v (Finset.mem_filter.mp hv).1).1
      (hH v (Finset.mem_filter.mp hv).1).2 (Finset.mem_filter.mp hv).2
  have hcard : (HC.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroCubeNormBall_card hB0)
  have hc : (∑ v ∈ HC, ‖∑ a ∈ S, β a*cubicSymbol a v‖^2) ≤
      5832*B^(1/3:ℝ)*N^2*M^2 := by
    calc
      _ ≤ ∑ _v ∈ HC, 324*N^2*M^2 := Finset.sum_le_sum (fun v _ =>
        bounded_primary_character_row S β hNp.le
          (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩) hβ v)
      _ = (HC.card:ℝ)*(324*N^2*M^2) := by simp
      _ ≤ (18*B^(1/3:ℝ))*(324*N^2*M^2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hn' : (∑ v ∈ HN, ‖∑ a ∈ S, β a*cubicSymbol a v‖^2) ≤
      (K*(1+C))*B^(1/3:ℝ)*N^2*M^2*(1+Real.log B)^2 := by
    apply hn.trans
    calc
      _ = (K*(1+((largeCoreDyadicIndices 1 B).card:ℝ)))*(B^(1/3:ℝ)*N^2*M^2) := by ring
      _ ≤ (K*((1+C)*(1+Real.log B)^2))*(B^(1/3:ℝ)*N^2*M^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI hK.le) (by positivity)
      _ = _ := by ring
  have hc' := mul_le_mul_of_nonneg_left (one_le_pow₀ hl : (1:ℝ) ≤ (1+Real.log B)^2)
    (show 0 ≤ 5832*B^(1/3:ℝ)*N^2*M^2 by positivity)
  have hs := Finset.sum_filter_add_sum_filter_not H (fun v => ∃ a : Eisenstein, a^3 = v)
    (fun v => ‖∑ a ∈ S, β a*cubicSymbol a v‖^2)
  change _ = _ at hs
  rw [←hs]
  exact (add_le_add (hc.trans (by simpa only [mul_one] using hc')) hn').trans_eq (by ring)

end CubicFirstMoment

end

end OAI
