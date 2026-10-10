import OAI.NumberTheory.TwoPoint.Halasz.HalaszCofactorScale

namespace OAI

/-! A large minimum gives the same cofactor saving at every frequency;
no prime-repulsion input is needed in this case. -/
namespace TwoPointCorrelations

open Filter Finset

lemma halasz_large_minimum_cutoff (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), OneBounded F → ∀ v : ℝ,
      (1/10:ℝ)*Real.log (Real.log X) ≤ squaredDistance F (mrtArchimedeanTwist v) X →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
  obtain ⟨K₀,hK₀,hcut⟩ := halasz_distance_cutoff_loss
  have hll := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (25*(K+K₀)))
  filter_upwards [eventually_ge_atTop 2,hll] with n hn2 hlln
  intro X hnX hX F hF v hv
  have hlogn : 0 < Real.log (n:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hlog : Real.log (n:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0<n by omega)) (by exact_mod_cast hnX)
  have hllmono := Real.log_le_log hlogn hlog
  have hc := hcut F hF n X hn2 hnX hX v
  dsimp only [Function.comp_def] at hlln
  linarith

theorem halasz_large_minimum_actual_cofactor :
    ∃ X₀ : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N:ℝ)/a⌋₊:ℝ) →
      n = ⌊(2*N:ℝ)/a⌋₊ → ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ v : ℝ, |v| ≤ X → (1/10:ℝ)*Real.log (Real.log X) ≤
        squaredDistance F (mrtArchimedeanTwist v) X) →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) → ∀ t : ℝ,
      |t|+(Real.log n)^8 ≤ X →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        (Real.log n)^(-1/40:ℝ) := by
  obtain ⟨C,K,X₀,hC,hK,hcofactor⟩ := halasz_exceptional_typical_window
  refine ⟨X₀,?_⟩
  have hlog : Tendsto (fun n:ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [halasz_large_minimum_cutoff K,halasz_cofactor_band_count,
    hlog.eventually (halasz_exceptional_decay C hC.le),
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with n hcut hcount hdec hln
  intro N a ha hbase hn X hnX hX F hF1 hFm hFb hmin P Q J hQ hband A hA t ht
  let R := (Real.log n)^(1/16:ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (by linarith) _
  have hM : 0 ≤ (3/100:ℝ)*Real.log (Real.log n) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hln)
  have hd : ∀ v:ℝ, |v-t| ≤ (Real.log n)^8 → 1/2 ≤ |v-(t+R)| →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
    intro v hv _
    have hvX : |v| ≤ X := by
      have hh := abs_add_le (v-t) t
      rw [sub_add_cancel] at hh
      linarith
    exact hcut X hnX hX F hFb v (hmin v hvX)
  have hb := hcofactor N a ha hbase F hF1 hFm hFb ℕ (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) A
    (fun _ _ _ hp => mrtPrimeBand_prime hp) hA t (t+R)
    ((3/100:ℝ)*Real.log (Real.log n)) hM (by simpa only [← hn] using hd)
  have haway : (Real.log n)^(1/16:ℝ)/2 ≤ |(t+R)-t| := by
    rw [add_sub_cancel_left,abs_of_nonneg hR]
    change R/2 ≤ R
    linarith
  have hsave := hdec ((2:ℝ)^(Icc 1 J).card) ((t+R)-t) (by positivity)
    (hcount X hnX hX Q J hQ hband) haway
  apply hb.trans
  simpa only [← hn,mul_comm C] using hsave

theorem halasz_large_minimum_extra_cofactor :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ v : ℝ, |v| ≤ 2*N → (1/10:ℝ)*Real.log (Real.log (2*N:ℕ)) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ a : ℝ, 1 ≤ a → a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      ∀ t : ℝ, |t| ≤ N →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        2*(Real.log N)^(-1/40:ℝ) := by
  obtain ⟨X₀,hcofactor⟩ := halasz_large_minimum_actual_cofactor
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hcofactor
  filter_upwards [halasz_cofactor_floor_scale X₀ n₀,eventually_ge_atTop 2]
    with N hscale hN
  intro F hF1 hFm hFb hmin P Q J hQ hband A hA a ha haU t ht
  let n := ⌊(2*N:ℝ)/a⌋₊
  obtain ⟨hbase,hnlarge,hnupper,hncube,hloglow,hlogupper,hwidth⟩ := hscale a ha haU
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hLN : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hdec := halasz_cofactor_scale_decay hLN hloglow hlogupper
  have hband' : mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log (2*N:ℕ))) := by
    apply hband.trans
    apply Real.exp_le_exp.mpr
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log hN0
    exact_mod_cast (show N≤2*N by omega)
  have ht' : |t|+Real.log (n:ℝ)^8 ≤ (2*N:ℕ) := by
    push_cast
    linarith
  have hmin' : ∀ v:ℝ, |v| ≤ (2*N:ℕ) →
      (1/10:ℝ)*Real.log (Real.log (2*N:ℕ)) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmin
  have hh := hn₀ n hnlarge N a ha hbase rfl (2*N) hnupper hncube
    F hF1 hFm hFb hmin' P Q J hQ hband' A hA t ht'
  exact hh.trans hdec.2

end TwoPointCorrelations

end OAI
