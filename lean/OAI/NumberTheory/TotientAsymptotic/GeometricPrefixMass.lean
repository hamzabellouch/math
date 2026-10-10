import OAI.NumberTheory.TotientAsymptotic.UnbandedSimplexMass
import OAI.NumberTheory.TotientAsymptotic.GeometricPrimeRegion
import OAI.NumberTheory.TotientAsymptotic.PrimeMassSplit
import OAI.NumberTheory.TotientAsymptotic.ExceptionalPrimeLayer

namespace OAI

/-! A projected reciprocal-mass bound for the constructed geometric family. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma relaxed_geometric_projection {x c : ℝ} {N n : ℕ}
    (hB : 0 ≤ B x) (hn : n ≤ N) {u : Fin N → ℝ}
    (hu : u ∈ relaxedGeometricFamily (m x) N (B x) c) :
    (fun j : Fin n => u (Fin.castLE hn j)) ∈
      enlargedSimplex n (B x) (1+simplexBoxError 0 (m x))
        (fun i => 1+simplexBoxError 0 (m x-(i.val+1))) := by
  have hu0 := hu.1.1
  have hrows (i : Fin N) :
      (∑ j : Fin N,if i<j then a (j.val-i.val)*u j else 0) ≤ u i :=
    (hu.1.2.2.1 i).trans (div_le_self (hu0 i)
      (by linarith only [rowContractionError_nonneg (m x-(i.val+1))]))
  have htop : (∑ i : Fin N,a (i.val+1)*u i) ≤ B x :=
    hu.1.2.2.2.trans (div_le_self hB
      (by linarith only [rowContractionError_nonneg (m x)]))
  refine ⟨fun i => hu0 _,?_,?_⟩
  · intro i
    have hs := sum_restrict_le hn
      (fun j : Fin N => if Fin.castLE hn i<j then a (j.val-i.val)*u j else 0) (by
        intro j
        split_ifs with hij
        · exact mul_nonneg (a_pos (by have := hij; simp only [Fin.lt_def,Fin.val_castLE] at this; omega)).le (hu0 j)
        · rfl)
    have hsmall : (∑ j : Fin n,if i<j then a (j.val-i.val)*u (Fin.castLE hn j) else 0) ≤
        u (Fin.castLE hn i) := by
      have hs' : (∑ j : Fin n,if i<j then a (j.val-i.val)*u (Fin.castLE hn j) else 0) ≤
          ∑ j : Fin N,if Fin.castLE hn i<j then a (j.val-i.val)*u j else 0 := by
        simpa only [Fin.lt_def,Fin.val_castLE] using hs
      exact hs'.trans (hrows _)
    apply hsmall.trans
    have he := simplexBoxError_nonneg (by norm_num : (0:ℝ) ≤ 0) (m x-(i.val+1))
    nlinarith only [he,hu0 (Fin.castLE hn i)]
  · have hs := sum_restrict_le hn (fun j : Fin N => a (j.val+1)*u j)
      (fun j => mul_nonneg (a_pos (by omega)).le (hu0 j))
    have hs' : (∑ j : Fin n,a (j.val+1)*u (Fin.castLE hn j)) ≤
        ∑ j : Fin N,a (j.val+1)*u j := by
      simpa only [Fin.val_castLE] using hs
    apply hs'.trans (htop.trans ?_)
    have he := simplexBoxError_nonneg (by norm_num : (0:ℝ) ≤ 0) (m x)
    nlinarith only [he,hB]

theorem geometric_projected_prime_mass {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N n : ℕ,N+H=m x → ∀ hn : n ≤ N,0 < n →
      ∀ Q : Finset (Fin N → ℕ),
        (∀ p ∈ Q,(∀ i,(p i).Prime) ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) c) →
      (∑ p ∈ Q.image (fun p => primeInitial p n hn),reciprocalShiftWeight p) ≤ C*G x n := by
  classical
  obtain ⟨C,hC,hbound⟩ := unbanded_simplex_prime_mass
  refine ⟨C,hC,?_⟩
  filter_upwards [geometric_dominates_polynomial hc (1/100) 0] with H hH
  filter_upwards [hbound,B_tendsto.eventually (eventually_ge_atTop (0:ℝ))]
    with x hx hB
  intro N n hN hn hn0 Q hQ
  let K := m x-n
  have hnM : n ≤ m x := by omega
  have hK : K < m x := by dsimp [K]; omega
  have he : m x-K=n := by dsimp [K]; omega
  have hh := hx K hK
  rw [he] at hh
  apply hh
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hprime,hgeom⟩ := hQ q hq
  refine ⟨fun i => hprime _,relaxed_geometric_projection hB hn hgeom,?_⟩
  intro i _hi
  have hdist : H ≤ m x-(Fin.castLE hn i).val := by
    have := i.isLt
    simp only [Fin.val_castLE]
    omega
  have hlo := hH _ hdist
  simp only [pow_zero,mul_one] at hlo
  exact hlo.trans (hgeom.2.1 _)

lemma late_prefix_volume_le : ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ K : ℕ,H ≤ K → K ≤ m x → G x (m x-K) ≤ G x (m x) := by
  obtain ⟨D,hD,hbound⟩ := uniform_projected_volume_bound fordRenewalInput
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    ((summable_projectedEnvelope hD).tendsto_atTop_zero.eventually
      (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)))
  filter_upwards [eventually_ge_atTop L] with H hH
  filter_upwards [hbound,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro K hHK hKm
  have hp := (div_le_iff₀ (G_pos hB (m x))).mp (hx K hKm)
  exact hp.trans (mul_le_of_le_one_left (G_pos hB _).le (hL K (hH.trans hHK)).le)

lemma late_prefix_volume_monotone : ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N n : ℕ,N+H ≤ m x → n ≤ N → G x n ≤ G x N := by
  obtain ⟨C,hC,hstep⟩ := uniform_step_bound fordRenewalInput
  have ht : Tendsto (fun H : ℕ => C*rho^H) atTop (nhds 0) :=
    by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul C
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))]
    with H hH
  filter_upwards [hstep,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hB
  intro N n hN hn
  have hg := G_sub_eq_product hB N (N-n) (Nat.sub_le _ _)
  rw [Nat.sub_sub_self hn] at hg
  rw [hg]
  apply mul_le_of_le_one_right (G_pos hB _).le
  apply Finset.prod_le_one₀
  · intro k _
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (g_pos _).le) hB.le
  · intro k hk
    have hkN : k < N := (Finset.mem_range.mp hk).trans_le (Nat.sub_le _ _)
    have hi : m x-(N-k) ≤ m x := Nat.sub_le _ _
    have he : m x-(m x-(N-k))=N-k := by omega
    have hh := hx (m x-(N-k)) hi
    rw [he] at hh
    have hHI : H ≤ m x-(N-k) := by omega
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le hHI) hC.le).trans hH.le)

theorem geometric_initial_mass_le {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N n : ℕ,N+H=m x → ∀ hn : n ≤ N,
      ∀ Q : Finset (Fin N → ℕ),
        (∀ p ∈ Q,(∀ i,(p i).Prime) ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) c) →
      (∑ p ∈ Q.image (fun p => primeInitial p n hn),reciprocalShiftWeight p) ≤ C*G x (m x) := by
  classical
  obtain ⟨C,hC,hbound⟩ := geometric_projected_prime_mass hc
  refine ⟨max C 1,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  filter_upwards [hbound,late_prefix_volume_le] with H hH hV
  filter_upwards [hH,hV,central_volume_one_le,
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hv hG hB
  intro N n hN hn Q hQ
  by_cases hn0 : 0 < n
  · have hm : G x n ≤ G x (m x) := by
      have he : m x-(m x-n)=n := by omega
      simpa only [he] using hv (m x-n) (by omega) (Nat.sub_le _ _)
    exact (hx N n hN hn hn0 Q hQ).trans
      (mul_le_mul (le_max_left _ _) hm (G_pos hB _).le (by positivity))
  · have he : n=0 := by omega
    have hw : ∀ p : Fin n → ℕ,reciprocalShiftWeight p=1 := by
      intro p
      simp [reciprocalShiftWeight,he]
    have hcard : (Q.image (fun p => primeInitial p n hn)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p _ q _
      funext i
      have hi := i.isLt
      omega
    calc
      _ = ((Q.image (fun p => primeInitial p n hn)).card:ℝ) := by simp [hw]
      _ ≤ 1 := by exact_mod_cast hcard
      _ ≤ G x (m x) := hG
      _ ≤ _ := le_mul_of_one_le_left (G_pos hB _).le (le_max_right _ _)

theorem geometric_initial_mass_le_base {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N n : ℕ,N+H=m x → ∀ hn : n ≤ N,
      ∀ Q : Finset (Fin N → ℕ),
        (∀ p ∈ Q,(∀ i,(p i).Prime) ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) c) →
      (∑ p ∈ Q.image (fun p => primeInitial p n hn),reciprocalShiftWeight p) ≤ C*G x N := by
  classical
  obtain ⟨C,hC,hbound⟩ := geometric_projected_prime_mass hc
  refine ⟨max C 1,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  filter_upwards [hbound,late_prefix_volume_monotone] with H hH hV
  filter_upwards [hH,hV,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hv hB
  intro N n hN hn Q hQ
  have hvol := hv N n hN.le hn
  by_cases hn0 : 0 < n
  · exact (hx N n hN hn hn0 Q hQ).trans
      (mul_le_mul (le_max_left _ _) hvol (G_pos hB _).le (by positivity))
  · have he : n=0 := by omega
    have hw : ∀ p : Fin n → ℕ,reciprocalShiftWeight p=1 := by
      intro p
      simp [reciprocalShiftWeight,he]
    have hcard : (Q.image (fun p => primeInitial p n hn)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p _ q _
      funext i
      have hi := i.isLt
      omega
    have hG : (1:ℝ) ≤ G x N := by simpa [he,G] using hvol
    calc
      _ = ((Q.image (fun p => primeInitial p n hn)).card:ℝ) := by simp [hw]
      _ ≤ 1 := by exact_mod_cast hcard
      _ ≤ G x N := hG
      _ ≤ _ := le_mul_of_one_le_left (G_pos hB _).le (le_max_right _ _)

/-- A literal local exceptional-prime restriction, retaining the original
prefix geometry rather than counting each prefix separately. -/
theorem geometric_local_exception_mass {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N n : ℕ,N+H=m x → ∀ hn : n < N,0 < n →
      ∀ (Q : Finset (Fin N → ℕ)) (U V : Finset ℕ),
        (∀ p ∈ Q,(∀ i,(p i).Prime) ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) c) →
        (∀ p ∈ Q,∀ i : Fin (N-n),primeFinal p n i ∈ U) →
        (∀ p ∈ Q,primeFinal p n ⟨0,by omega⟩ ∈ V) →
      (∑ p ∈ Q,reciprocalShiftWeight p) ≤
        C*G x n*(∑ p ∈ V,((p-1:ℕ):ℝ)⁻¹)*
          (∑ p ∈ U,((p-1:ℕ):ℝ)⁻¹)^(N-n-1) := by
  obtain ⟨C,hC,hbound⟩ := geometric_projected_prime_mass hc
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with H hH
  filter_upwards [hH] with x hx
  intro N n hN hn hn0 Q U V hQ hU hV
  have hmass := prime_mass_one_exception hn.le Q ⟨0,by omega⟩ U V hU hV
  have hp := hx N n hN hn.le hn0 Q hQ
  apply hmass.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hp (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact pow_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) _

end TotientAsymptotic

end

end OAI
