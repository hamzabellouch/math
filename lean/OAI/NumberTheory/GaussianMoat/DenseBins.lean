import OAI.NumberTheory.GaussianMoat.ConditionalSampling

namespace OAI

namespace GaussianMoat
open Filter Topology Finset
open scoped BigOperators

namespace PrimeLogMass
open Filter Topology Finset
open ArithmeticFunction.vonMangoldt Complex
open scoped BigOperators

def dyadicBatch (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2^j) (2^(j+1))).filter (fun p => p.Prime ∧ p % 4 = 1)

lemma mem_dyadicBatch (j p : ℕ) : p ∈ dyadicBatch j ↔
    2^j ≤ p ∧ p < 2^(j+1) ∧ p.Prime ∧ p % 4 = 1 := by
  simp only [dyadicBatch,Finset.mem_filter,Finset.mem_Ico]
  tauto

lemma logBin_mem (p : ℕ) (hp : p.Prime) (hm : p % 4 = 1) :
    p ∈ dyadicBatch (Nat.log 2 p) := by
  rw [mem_dyadicBatch]
  exact ⟨Nat.pow_log_le_self 2 hp.ne_zero,
    Nat.lt_pow_succ_log_self (by norm_num) p,hp,hm⟩

lemma prime_log_mass_le_theta (S : Finset ℕ) {U : ℝ} (hU : 0 ≤ U)
    (hp : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ U) :
    (∑ p ∈ S, Real.log p) ≤ Real.log 4*U := by
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x hU)
  rw [Chebyshev.theta_eq_sum_primesLE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hpS
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.le_floor_iff hU).mpr (hp p hpS).2,(hp p hpS).1⟩
  · intro p hpS _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hpS).2.one_le)

noncomputable def dyadicMass (j : ℕ) : ℝ :=
  ∑ p ∈ dyadicBatch j, Real.log p/p

lemma dyadicMass_nonneg (j : ℕ) : 0 ≤ dyadicMass j := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (mem_dyadicBatch _ _ |>.mp hp).2.2.1.one_le))
    (Nat.cast_nonneg _)

lemma dyadicMass_le (j : ℕ) : dyadicMass j ≤ 2*Real.log 4 := by
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hs : dyadicMass j ≤ (∑ p ∈ dyadicBatch j, Real.log p)/(2^j : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have h := (mem_dyadicBatch j p).mp hp
    apply div_le_div_of_nonneg_left
    · exact Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)
    · exact hT
    · exact_mod_cast h.1
  have ht := prime_log_mass_le_theta (dyadicBatch j) (U := (2 : ℝ)^(j+1))
    (by positivity) (by intro p hp; have h := (mem_dyadicBatch j p).mp hp
                        exact ⟨h.2.2.1,by exact_mod_cast h.2.1.le⟩)
  apply hs.trans
  apply (div_le_iff₀ hT).mpr
  rw [pow_succ] at ht
  nlinarith

lemma dyadicMass_le_card (j : ℕ) : dyadicMass j ≤
    (dyadicBatch j).card * Real.log ((2 : ℝ)^(j+1)) / (2 : ℝ)^j := by
  rw [dyadicMass]
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hp (p : ℕ) (hp : p ∈ dyadicBatch j) :
      Real.log p/p ≤ Real.log ((2 : ℝ)^(j+1))/(2 : ℝ)^j := by
    have h := (mem_dyadicBatch j p).mp hp
    apply le_trans (div_le_div_of_nonneg_left
      (Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)) hT (by exact_mod_cast h.1))
    apply div_le_div_of_nonneg_right _ hT.le
    exact Real.log_le_log (by exact_mod_cast h.2.2.1.pos) (by exact_mod_cast h.2.1.le)
  have hs := Finset.sum_le_sum (s := dyadicBatch j) hp
  simpa [Finset.sum_const,nsmul_eq_mul,mul_div_assoc] using hs

theorem many_dense_bins (J : Finset ℕ) {X c A : ℝ} (hc : 0 < c)
    (hA : 0 < A) (hcard : (J.card : ℝ) ≤ A*X)
    (hmass : c*X ≤ ∑ j ∈ J, dyadicMass j) :
    c*X/(4*Real.log 4) ≤
      ((J.filter (fun j => c/(2*A) ≤ dyadicMass j)).card : ℝ) ∧
    ∀ j ∈ J.filter (fun j => c/(2*A) ≤ dyadicMass j),
      c/(2*A)*(2 : ℝ)^j/Real.log ((2 : ℝ)^(j+1)) ≤ (dyadicBatch j).card := by
  classical
  let G := J.filter (fun j => c/(2*A) ≤ dyadicMass j)
  have hlog : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hδ : 0 < c/(2*A) := div_pos hc (by positivity)
  have ht (j : ℕ) (hj : j ∈ J) : dyadicMass j ≤
      (if j ∈ G then 2*Real.log 4 else 0)+c/(2*A) := by
    by_cases hg : j ∈ G
    · simp only [hg,ite_eq_left]
      linarith [dyadicMass_le j]
    · rw [ite_eq_right hg,zero_add]
      exact (not_le.mp (fun h => hg (Finset.mem_filter.mpr ⟨hj,h⟩))).le
  have hs := Finset.sum_le_sum (s := J) ht
  have he : (∑ j ∈ J, if j ∈ G then 2*Real.log 4 else 0) = G.card*(2*Real.log 4) := by
    rw [← Finset.sum_filter]
    have hG : J.filter (fun j => j ∈ G) = G := by
      ext j
      simp only [G,Finset.mem_filter]
      tauto
    rw [hG]
    simp [nsmul_eq_mul]
  rw [Finset.sum_add_distrib,he,Finset.sum_const,nsmul_eq_mul] at hs
  have hsmall : (J.card : ℝ)*(c/(2*A)) ≤ c*X/2 := by
    have h := mul_le_mul_of_nonneg_right hcard hδ.le
    have he : A*X*(c/(2*A))=c*X/2 := by field_simp
    rwa [he] at h
  refine ⟨(div_le_iff₀ (by positivity)).mpr (by dsimp [G] at hs; nlinarith),?_⟩
  intro j hj
  have hg := (Finset.mem_filter.mp hj).2
  have h := dyadicMass_le_card j
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hL : 0 < Real.log ((2 : ℝ)^(j+1)) := Real.log_pos (one_lt_pow₀ (by norm_num) (by omega))
  apply (div_le_iff₀ hL).mpr
  have h' := (le_div_iff₀ hT).mp (hg.trans h)
  exact h'

noncomputable def splitWindow (X : ℝ) : Finset ℕ :=
  (windowIndices X).filter (fun p => p.Prime ∧ p % 4 = 1)

noncomputable def windowBins (X : ℝ) : Finset ℕ :=
  (splitWindow X).image (Nat.log 2)

lemma split_residue_mass (p : ℕ) (hp : p.Prime) :
    residueClass (1 : ZMod 4) p = if p % 4 = 1 then Real.log p else 0 := by
  have he : (p : ZMod 4) = 1 ↔ p % 4 = 1 := by
    rw [show (1 : ZMod 4) = (1 : ℕ) from rfl,ZMod.natCast_eq_natCast_iff]
    rfl
  simp only [residueClass,Set.indicator_apply,Set.mem_ofPred_eq,he,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma window_mass_le_bins (X : ℝ) :
    (∑ p ∈ (windowIndices X).filter Nat.Prime, residueClass (1 : ZMod 4) p/p) ≤
      ∑ j ∈ windowBins X, dyadicMass j := by
  classical
  have hres : (∑ p ∈ (windowIndices X).filter Nat.Prime, residueClass (1 : ZMod 4) p/p) =
      ∑ p ∈ splitWindow X, Real.log p/p := by
    rw [splitWindow,Finset.sum_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · rw [ite_eq_left hp,split_residue_mass p hp]
      by_cases hm : p % 4=1 <;> simp [hp,hm]
    · simp [hp]
  rw [hres,← Finset.sum_fiberwise_of_maps_to
    (s := splitWindow X) (t := windowBins X) (g := Nat.log 2)
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)]
  apply Finset.sum_le_sum
  intro j _
  dsimp [dyadicMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hj⟩
    obtain ⟨_,hpp,hpm⟩ := Finset.mem_filter.mp hp
    rw [← hj]
    exact logBin_mem p hpp hpm
  · intro p hp _
    have hpp := ((mem_dyadicBatch j p).mp hp).2.2.1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg p)

lemma windowBin_bounds {X : ℝ} (hX : 1000 ≤ X) {j : ℕ} (hj : j ∈ windowBins X) :
    X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hpW,hpP,hpM⟩ := Finset.mem_filter.mp hp
  have hw := (mem_windowIndices X p).mp hpW
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
  have hlb := (Real.le_log_iff_exp_le hp0).mpr hw.1
  have hub := (Real.log_le_iff_le_exp hp0).mpr hw.2
  have hbin := (mem_dyadicBatch _ _).mp (logBin_mem p hpP hpM)
  have hlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) (Nat.log 2 p))
    (by exact_mod_cast hbin.1 : (2 : ℝ)^Nat.log 2 p ≤ p)
  have hhigh := Real.log_lt_log hp0
    (by exact_mod_cast hbin.2.1 : (p : ℝ) < (2 : ℝ)^(Nat.log 2 p+1))
  rw [Real.log_pow] at hlow hhigh
  simp only [Nat.cast_add,Nat.cast_one] at hhigh
  constructor
  · nlinarith [Real.log_two_lt_d9]
  · nlinarith

lemma windowBins_card {X : ℝ} (hX : 1000 ≤ X) : (windowBins X).card ≤ 3*X := by
  classical
  have hX0 : 0 ≤ X := by linarith
  have hs : windowBins X ⊆ Finset.range (⌊2*X⌋₊+1) := by
    intro j hj
    have h := (windowBin_bounds hX hj).2
    have hlog := Real.log_two_gt_d9
    have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
    have hjX : (j : ℝ)≤2*X := by nlinarith
    rw [Finset.mem_range,Nat.lt_succ_iff,Nat.le_floor_iff (by positivity : (0 : ℝ)≤2*X)]
    exact hjX
  have hc : (windowBins X).card ≤ ⌊2*X⌋₊+1 :=
    (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hcR : ((windowBins X).card:ℝ) ≤ ⌊2*X⌋₊+1 := by exact_mod_cast hc
  have hf := Nat.floor_le (show (0 : ℝ)≤2*X by positivity)
  nlinarith

theorem eventually_dense_split_bins : ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      c*X ≤ J.card ∧
      ∀ j ∈ J, X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X ∧
        δ*(2 : ℝ)^j/Real.log ((2 : ℝ)^(j+1)) ≤ (dyadicBatch j).card := by
  obtain ⟨c,hc,he⟩ := eventually_prime_window_mass (show IsUnit (1 : ZMod 4) from isUnit_one)
  refine ⟨c/(4*Real.log 4),c/6,div_pos hc (by positivity),div_pos hc (by norm_num),?_⟩
  filter_upwards [he,eventually_ge_atTop (1000 : ℝ)] with X hmass hX
  let J := (windowBins X).filter (fun j => c/6 ≤ dyadicMass j)
  have hh := many_dense_bins (windowBins X) hc (by norm_num : (0 : ℝ)<3)
    (windowBins_card hX) (hmass.trans (window_mass_le_bins X))
  refine ⟨J,?_,?_⟩
  · simpa only [show (2 : ℝ)*3=6 by norm_num,div_mul_eq_mul_div] using hh.1
  · intro j hj
    have hb := windowBin_bounds hX (Finset.mem_filter.mp hj).1
    have hd := hh.2 j (by simpa only [show (2 : ℝ)*3=6 by norm_num] using hj)
    exact ⟨hb.1,hb.2,by simpa only [show (2 : ℝ)*3=6 by norm_num] using hd⟩

end PrimeLogMass
end GaussianMoat

end OAI
