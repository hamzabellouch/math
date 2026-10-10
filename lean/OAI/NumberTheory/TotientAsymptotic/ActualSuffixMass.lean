import OAI.NumberTheory.TotientAsymptotic.FirstCollision
import OAI.NumberTheory.TotientAsymptotic.DyadicCollisionMass

namespace OAI

/-! The actual reciprocal mass of distinct colliding suffix pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def suffixDyadicIndex {n : ℕ} (s : PrefixDatum n × PrefixDatum n) : ℕ :=
  Nat.clog 2 (prefixDenominator s.1)

lemma firstCollisionSuffixes_denominator_gt_one {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hL : L x H < m x) (hR : R x H < L x H)
    (hi : 1 ≤ i) (hiR : i ≤ R x H)
    {s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)}
    (hs : s ∈ firstCollisionSuffixes x H t i) : 1 < prefixDenominator s.1 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
  have hl := (firstCollisionPairs_data hPH hq).1
  rw [show (pairSuffix q i).1=tupleSuffix q.1 i from rfl,
    tupleSuffix_denominator_positive hl.1 hL hR hi hiR]
  have hη := (chosenRemainder_spec hl.1.2.2.1).1
  have hp := basic_remainder_prime_ge_three hη (Finset.mem_Icc.mpr ⟨hi,hiR.trans hR.le⟩)
    (hiR.trans_lt (hR.trans hL))
  have hd := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := i))
  have he : 2 ≤ (remainderPrime (chosenRemainder x H q.1.tail) i-1)*
      (suffixPreimage (chosenRemainder x H q.1.tail) i).totient := by
    calc
      2 = 2*1 := by omega
      _ ≤ _ := Nat.mul_le_mul (by omega) hd
  omega

/-- All distinct suffix pairs, with no fixed prefix, have exponentially
small reciprocal mass. Constants and the cutoff are uniform in the phase. -/
theorem actual_suffix_mass (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → L x H < m x → R x H < L x H → ∀ t : ℝ,
    (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹) ≤
      (16/Real.log 2)*((m x-i : ℕ) : ℝ)^4*
        Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨y₀,hy₀,hcount⟩ := actual_suffix_block_count hford hmertens
  have hevent : ∀ᶠ y : ℝ in atTop, y₀ ≤ y := eventually_ge_atTop y₀
  filter_upwards [hcount,first_collision_dyadic_blocks,
    collision_endpoints_eventually hevent,ford_band_polynomial_lower 1,
    eventually_ge_atTop 100,eventually_tail_cut_separated]
    with H hc hblocks hlarge hpoly hH hsep
  filter_upwards [hc,hblocks,hlarge,hpoly,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hx hb hy hxpoly hm
  intro i hi hiR hL hR t
  let S := firstCollisionSuffixes x H t i
  let h : ℝ := (m x-i : ℕ)
  let σ : ℝ := 1/(8*h^4)
  have hhNat : H ≤ m x-i := by unfold R at hiR; omega
  have hh : (100 : ℝ) ≤ h := by
    dsimp [h]
    exact_mod_cast hH.trans hhNat
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hbi : (100 : ℝ) ≤ fordBandScale x i := by
    have hp := hxpoly i (hiR.trans_lt (hR.trans hL)) hhNat
    have hh' : (100 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hhNat
    exact hh'.trans (by simpa only [pow_one] using hp)
  have hPH : P H ≤ H := by omega
  have hsdata (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (hs : s ∈ S) :
      1 ≤ suffixDyadicIndex s ∧
      (2 : ℝ)^(suffixDyadicIndex s)/2 < (prefixDenominator s.1 : ℝ) ∧
      (prefixDenominator s.1 : ℝ) ≤ (2 : ℝ)^(suffixDyadicIndex s) :=
    dyadic_nat_bounds (firstCollisionSuffixes_denominator_gt_one hPH hL hR hi hiR hs)
  have hsband (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (hs : s ∈ S) :
      (87/100 : ℝ)*fordBandScale x i ≤ B ((2 : ℝ)^(suffixDyadicIndex s)) := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    have hd := hsdata _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
    exact (hb i hi hiR hL hR t _ q hq hd.2.1 hd.2.2).2.1
  have hstart (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (hs : s ∈ S) :
      2 ≤ suffixDyadicIndex s ∧ Real.exp (fordBandScale x i/2) ≤
        ((suffixDyadicIndex s-1 : ℕ) : ℝ)*Real.log 2 :=
    dyadic_band_start hbi (hsdata s hs).1 (hsband s hs)
  have hcounts (n : ℕ) : ((S.filter (fun s => suffixDyadicIndex s=n)).card : ℝ) ≤
      1*(2 : ℝ)^n*dyadicSuffixWeight σ n := by
    let Q := (firstCollisionPairs x H t i).filter (fun q => suffixDyadicIndex (pairSuffix q i)=n)
    have himage : S.filter (fun s => suffixDyadicIndex s=n)=Q.image (fun q => pairSuffix q i) := by
      exact Finset.filter_image
    by_cases hne : Q.Nonempty
    · obtain ⟨q,hq⟩ := hne
      obtain ⟨hq,hn⟩ := Finset.mem_filter.mp hq
      have hs : pairSuffix q i ∈ S := Finset.mem_image.mpr ⟨q,hq,rfl⟩
      have hd := hsdata _ hs
      have hblock := hb i hi hiR hL hR t _ q hq hd.2.1 hd.2.2
      have hn1 : 1 ≤ n := by rw [← hn]; exact hd.1
      have hyn : 1 < (2 : ℝ)^n := one_lt_pow₀ (by norm_num) (by omega)
      have hlower : (87/100 : ℝ)*fordBandScale x i ≤ B ((2 : ℝ)^n) := by
        simpa only [hn] using hblock.2.1
      have hupper : B ((2 : ℝ)^n) ≤ 2*fordBandScale x i := by
        have hu : B ((2 : ℝ)^n) ≤ (113/100 : ℝ)*fordBandScale x i := by
          simpa only [hn] using hblock.2.2
        linarith
      have hBy : 0 < B ((2 : ℝ)^n) := by linarith
      have hy₀n : y₀ ≤ (2 : ℝ)^n := hy i hiR _ hyn (by linarith)
      have hQ : ∀ q ∈ Q, GoodCollisionBlock x t H i ((2 : ℝ)^n) q := by
        intro q hq
        obtain ⟨hq,hn⟩ := Finset.mem_filter.mp hq
        have hd := hsdata _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        have hh := hb i hi hiR hL hR t _ q hq hd.2.1 hd.2.2
        simpa only [hn] using hh.1
      have he := hx i hiR hL hR t ((2 : ℝ)^n) hy₀n hBy hlower hupper Q hQ
      rw [himage]
      apply he.trans_eq
      dsimp only [dyadicSuffixWeight,σ,h]
      rw [dyadic_endpoint_log,dyadic_endpoint_B]
      have heq : -Real.log ((n : ℝ)*Real.log 2)/(8*((m x-i : ℕ) : ℝ)^4)=
          -(1/(8*((m x-i : ℕ) : ℝ)^4))*Real.log ((n : ℝ)*Real.log 2) := by ring
      rw [heq]
      ring
    · rw [himage,Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
      unfold dyadicSuffixWeight
      positivity
  have he := finite_dyadic_collision_mass S suffixDyadicIndex
    (fun s => (prefixDenominator s.1 : ℝ)) (C := 1) (B := fordBandScale x i/2)
    (by norm_num) hσ hstart (fun s hs => (hsdata s hs).2.1) hcounts
  apply he.trans_eq
  have heq : -σ*(fordBandScale x i/2) = -fordBandScale x i/(16*h^4) := by
    dsimp [σ]
    ring
  rw [heq]
  dsimp [σ,h]
  field_simp
  ring

end TotientAsymptotic

end

end OAI
