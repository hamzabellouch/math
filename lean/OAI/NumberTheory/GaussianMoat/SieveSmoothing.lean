import OAI.NumberTheory.GaussianMoat.SeparatedParameters

namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

lemma allBins_scale_bound {m W : ℕ} (J : ℕ → Finset ℕ)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m))
    {j : ℕ} (hj : j∈allBins W J) :
    (2:ℝ)^j≤Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
  obtain ⟨w,hw,hj⟩ := Finset.mem_biUnion.mp hj
  have hw' := Finset.mem_range.mp hw
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
  rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith only [hb w hw' j hj,hp]

lemma eventually_allBins_weight (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      residueWeight ((allBins W J).biUnion (fun j => (dyadicSieve j).availableFactors))≤
        Real.exp ((2*(100:ℝ)^W)*Real.exp m) := by
  have hp := eventually_poly_le_exp_linear (4*Real.log 4*(3*(W:ℝ)*(100:ℝ)^W))
    (a := (19/20)*(100:ℝ)^W) (by positivity) 1
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hp,ht.eventually (eventually_ge_atTop (2:ℝ))] with m hp hm
  intro J hJ
  have he := fun (j : ℕ) (hj : j∈allBins W J) => allBins_scale_bound J hJ hj
  have hcard := allBins_card_upper J hm hJ
  have hs : (∑ j∈allBins W J, residueWeight (dyadicSieve j).availableFactors)≤
      (4*Real.log 4)*((allBins W J).card:ℝ)*Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
    calc
      _ ≤ ∑ _j∈allBins W J, (4*Real.log 4)*Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (dyadicSieve_available_weight j).trans
          (mul_le_mul_of_nonneg_left (he j hj) (by positivity))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hcard' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (show 0≤4*Real.log 4 by positivity))
    (Real.exp_nonneg (21/20*(100:ℝ)^W*Real.exp m))
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (21/20*(100:ℝ)^W*Real.exp m))
  rw [←Real.exp_add] at hh
  simp only [pow_one] at hh
  have heq : (19/20)*100^W*Real.exp (m:ℝ)+21/20*100^W*Real.exp m=
      (2*(100:ℝ)^W)*Real.exp m := by ring
  rw [heq] at hh
  apply (residueWeight_biUnion_le _ _).trans (hs.trans (hcard'.trans _))
  convert hh using 1; ring

theorem eventually_allBins_smoothing (D : ℝ) (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      (∀ i∈allBins W J, ∀ j∈allBins W J, ∀ a<batchWordLength j,
        2*Real.binEntropy ((a:ℝ)/(windowSmoothing W m+1))+
          ((a:ℝ)/(windowSmoothing W m+1))*((batchWordLength i:ℝ)*Real.log (latticeBall D).card+
            2*residueWeight ((allBins W J).biUnion (fun j => (dyadicSieve j).availableFactors)))≤
          Real.exp (-Real.exp m)) ∧
      ((allBins W J).card:ℝ)*Real.exp (-Real.exp m)≤1 := by
  have hA : 1≤2*(100:ℝ)^W := by have := window_power_one W; linarith only [this]
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_allBins_weight W,
    ht.eventually (eventually_smoothing_guard (H := Real.log (latticeBall D).card) hA),
    ht.eventually (eventually_smoothing_total (3*(W:ℝ)*(100:ℝ)^W)),
    ht.eventually (eventually_ge_atTop (2:ℝ))] with m hweight hsmooth htotal hm
  intro J hJ
  have hL (j : ℕ) (hj : j∈allBins W J) :
      (batchWordLength j:ℝ)≤Real.exp ((2*(100:ℝ)^W)*Real.exp m) := by
    apply (batchWordLength_le_scale j).trans ((allBins_scale_bound J hJ hj).trans _)
    apply Real.exp_le_exp.mpr
    have : 0≤(100:ℝ)^W*Real.exp m := by positivity
    nlinarith only [this]
  constructor
  · intro i hi j hj a ha
    apply hsmooth _ _ _ _ (Nat.cast_nonneg _)
      ((show (a:ℝ)≤batchWordLength j by exact_mod_cast ha.le).trans (hL j hj))
      (Nat.cast_nonneg _) (hL i hi) (hweight J hJ)
    convert (windowSmoothing_bounds W m).1 using 1
    congr 1
    ring
  · exact (mul_le_mul_of_nonneg_right (allBins_card_upper J hm hJ)
      (Real.exp_nonneg _)).trans htotal

end GaussianMoat

end OAI
