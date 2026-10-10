import OAI.NumberTheory.TotientAsymptotic.PPTRegularWitness
import OAI.NumberTheory.TotientAsymptotic.PPTRelativeHead
import OAI.NumberTheory.TotientAsymptotic.LocalPrimeRoughness
import OAI.NumberTheory.TotientAsymptotic.LocalSuffixRegularCount

namespace OAI

/-! Apply the finite regular comparison count to the actual distinct suffix
values, then integrate their occupied dyadic layers. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem local_suffix_regular_bound {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,LocalSuffixRegularBound x c d L H := by
  classical
  let D := pptLocalDimensionConstant (c/2)
  have hD : 0 < D := ppt_local_dimension_constant_pos _
  obtain ⟨z₀,hz₀⟩ := eventually_atTop.mp
    ((ppt_regular_geometric_count d hd hD 4).and
      ((ppt_geometric_suffix_head d (half_pos hc)).and
        (ppt_local_prime_dimension (half_pos hc))))
  obtain ⟨A,hA,hvalues⟩ := local_bad_suffix_value_bounds hc d hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hA' : 0 < A+Real.log d+2 := by
    have := Real.log_nonneg hd1
    linarith
  obtain ⟨E,_hE,hlayers⟩ := local_residual_layer_bounds (half_pos hc) hA' L
  obtain ⟨H₁,hH₁⟩ := eventually_atTop.mp (hlayers z₀)
  obtain ⟨H₂,hH₂⟩ := eventually_atTop.mp
    (local_residual_mass_of_fourth_power_count (half_pos hc) hA' d L)
  obtain ⟨H₃,hH₃⟩ := eventually_atTop.mp
    (localNormalityScale_tendsto.eventually (eventually_ge_atTop (largestPrimeFactor d:ℝ)))
  filter_upwards [local_bad_suffix_geometric_data hc d L,hvalues L,
    local_geometric_primes_three (half_pos hc),
    eventually_ge_atTop (max H₁ (max H₂ (max H₃ 1)))]
    with H hdata hvalues hthree hlarge
  filter_upwards [hdata,hvalues] with x hdata hvalues
  intro i F
  dsimp only
  intro _hinj hF
  let R := localBadSuffixValues x c d L H i
  let h := m x-i.val
  let Q := localWitnessRegular R F h
  have hlarge' : max H₁ (max H₂ (max H₃ 1)) ≤ h := by
    have := i.isLt
    dsimp only [h]
    omega
  have hh1 : H₁ ≤ h := (le_max_left _ _).trans hlarge'
  have hh2 : H₂ ≤ h := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge')
  have hh3 : H₃ ≤ h := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge'))
  have hhpos : 1 ≤ h := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge'))
  have hQR : Q⊆R := by intro r hr; exact (Finset.mem_sdiff.mp hr).1
  have hval (r) (hr : r∈Q) :
      ∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧ (c/2)*(rho^h)⁻¹ ≤ B p ∧
        ((d*r.totient:ℕ):ℝ) ≤ Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L h)) := by
    obtain ⟨hu,p,hp,hpv,hgeo⟩ := hvalues i r (hQR hr)
    exact ⟨p,hp,hpv,hgeo,hu⟩
  apply hH₂ h hh2 Q hval
  intro k _hk hnonempty
  let T := Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)
  let z : ℝ := (2:ℝ)^k
  obtain ⟨r₀,hr₀⟩ := hnonempty
  obtain ⟨hr₀Q,hr₀k⟩ := Finset.mem_filter.mp hr₀
  obtain ⟨p₀,hp₀,hpv₀,hgeo₀,hu₀⟩ := hval r₀ hr₀Q
  have hend := hH₁ h hh1 p₀ (d*r₀.totient) hp₀ hpv₀ hgeo₀ hu₀
  have hz : max 256 z₀ ≤ z := by
    simpa only [hr₀k,z] using hend.2.2.1
  have hB0 : 0 ≤ B z := by
    simpa only [hr₀k,z] using hend.2.2.2.2.1
  obtain ⟨hcount,hhead,hdim⟩ := hz₀ z ((le_max_right _ _).trans hz)
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num : (1:ℝ) < 256) ((le_max_left _ _).trans hz)
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hTQ : T⊆Q := Finset.filter_subset _ _
  have hTR : T⊆R := hTQ.trans hQR
  have hex (r : ℕ) : ∃ p : Fin (m x-H) → ℕ,r∈T →
      r=∏ j,primeFinal p i.val j ∧
      primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
      StrictAnti p ∧ (∀ j,(p j).Prime) ∧
      (∀ j : Fin (m x-H-i.val),IsNormalPrime (localNormalityScale h) (primeFinal p i.val j)) := by
    by_cases hr : r∈T
    · obtain ⟨p,he,hgeom,ho,hp,hn,_hembed⟩ := hdata i r (hTR hr)
      exact ⟨p,fun _ => ⟨he,hgeom,ho,hp,hn⟩⟩
    · exact ⟨fun _=>1,fun hh => (hr hh).elim⟩
  choose p hp using hex
  let q (r : ℕ) := primeFinal (p r) i.val
  let v (r : ℕ) := primePrefixCoord (p r)
  let ι (_r : ℕ) := primeFinalOrderEmbedding (N:=m x-H) i.val
  have hN : 0 < m x-H-i.val := Nat.sub_pos_of_lt i.isLt
  have hqprime (r) (hr : r∈T) (j) : (q r j).Prime := (hp r hr).2.2.2.1 _
  have hqanti (r) (hr : r∈T) : StrictAnti (q r) := by
    intro j k hjk
    exact (hp r hr).2.2.1 ((primeFinalOrderEmbedding i.val).strictMono hjk)
  have hqthree (r) (hr : r∈T) (j) : 3 ≤ q r j := by
    have hn : m x-H+H=m x := Nat.sub_add_cancel (by have := i.isLt; omega)
    exact hthree (m x) (m x-H) hn (B x) (p r) (hp r hr).2.2.2.1 (hp r hr).2.1 _
  have hrpos (r) (hr : r∈T) : 0 < r := by
    rw [(hp r hr).1]
    exact Finset.prod_pos (fun j _ => (hqprime r hr j).pos)
  have hpredecessor (r) (hr : r∈T) (j) : (q r j-1:ℕ) ≤ z := by
    have hdiv : q r j ∣ r :=
      (Finset.dvd_prod_of_mem (q r) (Finset.mem_univ j)).trans (dvd_of_eq (hp r hr).1.symm)
    have hle := prime_predecessor_le_seed_totient (hrpos r hr) (hqprime r hr j) hdiv hd
    have he := (Finset.mem_filter.mp hr).2
    have hdyad := (dyadic_nat_bounds (show 1 < d*r.totient from by
      obtain ⟨p,hp,hpv,hgeo,hu⟩ := hval r (hTQ hr)
      exact (hH₁ h hh1 p (d*r.totient) hp hpv hgeo hu).1)).2.2
    exact (Nat.cast_le.mpr hle).trans (by simpa only [he,z] using hdyad)
  have hremaining : (h:ℝ) ≤ D*Real.log (B z) := by
    have hgeo := (hp r₀ (show r₀∈T from hr₀)).2.1.2.1 i
    have hq0 : q r₀ ⟨0,hN⟩=p r₀ i := by unfold q primeFinal; congr 1
    exact hdim h (p r₀ i) (by rw [←hq0]; exact hqthree r₀ hr₀ _)
      hgeo (by rw [←hq0]; exact hpredecessor r₀ hr₀ _)
  have hresult := hcount (m x) (m x-H) (m x-H-i.val) h (B x) (c/2)
    (localNormalityScale h) T F q v ι hN (Nat.sub_le _ _) (by dsimp [h]; omega) hremaining
    (by
      apply Real.exp_le_exp.mpr
      apply Real.exp_le_exp.mpr
      have hhr : (1:ℝ) ≤ h := by exact_mod_cast hhpos
      exact one_le_pow₀ hhr)
    (by simp only [localNormalityScale,B,Real.log_exp]; exact le_rfl)
    (hH₃ h hh3)
    (by intro r hr; change m x-(i.val+0) ≤ h; simp only [add_zero]; exact le_rfl)
    (fun r hr => (hp r hr).2.1)
    (by intro r hr j; rfl)
    (fun r hr => (hp r hr).2.2.2.2)
    hqthree hqanti
    (fun r hr => ⟨(hF r (hTR hr)).1,(hF r (hTR hr)).2.1,(hp r hr).1⟩)
    (by intro r hr; exact ⟨(local_regular_witness_properties (hTQ hr)).2.2.1,
      (local_regular_witness_properties (hTQ hr)).2.2.2⟩)
    (fun r hr => (local_regular_witness_properties (hTQ hr)).2.1)
    (by
      intro r hr
      have he : largestPrimeFactor r=q r ⟨0,hN⟩ := by
        exact (congrArg largestPrimeFactor (hp r hr).1).trans
          (ordered_prime_product_largest hN (q r) (hqprime r hr) (hqanti r hr))
      rw [←he]
      exact (hF r (hTR hr)).2.2.2)
    hpredecessor
    (by
      intro r hr
      rw [(hF r (hTR hr)).2.1]
      have he := (Finset.mem_filter.mp hr).2
      have hdyad := (dyadic_nat_bounds (show 1 < d*r.totient from by
        obtain ⟨p,hp,hpv,hgeo,hu⟩ := hval r (hTQ hr)
        exact (hH₁ h hh1 p (d*r.totient) hp hpv hgeo hu).1)).2.2
      simpa only [he,z] using hdyad)
    (by
      intro r hr
      have hn : m x-H ≤ m x := Nat.sub_le _ _
      have hlow : z/2 < ((d*(∏ j,primeFinal (p r) i.val j).totient:ℕ):ℝ) := by
        rw [←(hp r hr).1]
        have he := (Finset.mem_filter.mp hr).2
        obtain ⟨p,hp,hpv,hgeo,hu⟩ := hval r (hTQ hr)
        have hdyr := (dyadic_nat_bounds (hH₁ h hh1 p (d*r.totient) hp hpv hgeo hu).1).2.1
        simpa only [he,z] using hdyr
      have hp3 := hthree (m x) (m x-H) (Nat.sub_add_cancel (by have := i.isLt; omega))
        (B x) (p r) (hp r hr).2.2.2.1 (hp r hr).2.1
      have hq0 : q r ⟨0,hN⟩=p r i := by unfold q primeFinal; congr 1
      rw [hq0]
      exact (hhead (m x) (m x-H) (B x) (p r) hn (hp r hr).2.2.2.1 hp3
        (hp r hr).2.1 i (by rw [←hq0]; exact hpredecessor r hr _) hlow).le)
  have hcoef : z/((d:ℝ)*Real.log z) ≤ z/Real.log z := by
    apply div_le_div_of_nonneg_left (zero_lt_one.trans hz1).le hlogz
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hlogz.le
  exact hresult.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hB0 _))

end TotientAsymptotic

end

end OAI
