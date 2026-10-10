import Mathlib
import OAI.Probability.BinarySweep.Mixing.ShapeDimension

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

def dimensionInv {n : ℕ} (p : n.Partition) : ℝ :=
  ((Module.finrank ℂ (PartitionHilbert p):ℝ)^8)⁻¹

def dimensionFiber (n k : ℕ) : ℝ := if k=0 then 0 else
  ∑p : {p : n.Partition // flatTail (diagram p)=k},dimensionInv p.val

def dimensionSeries (n : ℕ) : ℝ :=
  ∑p : n.Partition, if flatTail (diagram p)=0 then 0 else dimensionInv p

lemma dimensionInv_nonneg {n : ℕ} (p : n.Partition) : 0≤dimensionInv p := by
  unfold dimensionInv; positivity

lemma dimensionInv_exponential {n k : ℕ} (p : n.Partition) (hp : flatTail (diagram p)=k) :
    dimensionInv p≤(1/16:ℝ)^k := by
  have hD : (0:ℝ)<Module.finrank ℂ (PartitionHilbert p) := by exact_mod_cast partition_dimension_pos p
  have hl := partition_log_lower p hp
  have hh : (16:ℝ)^k≤(Module.finrank ℂ (PartitionHilbert p):ℝ)^8 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow,Real.log_pow]
    have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
      rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
      norm_num
    rw [h16]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hi := (inv_le_inv₀ (by positivity : (0:ℝ)<(Module.finrank ℂ (PartitionHilbert p):ℝ)^8)
    (by positivity : (0:ℝ)<16^k)).mpr hh
  simpa only [dimensionInv,one_div,inv_pow] using hi

lemma dimensionFiber_nonneg (n k : ℕ) : 0≤dimensionFiber n k := by
  unfold dimensionFiber
  split
  · rfl
  · exact Finset.sum_nonneg (fun _ _ => dimensionInv_nonneg _)

lemma dimensionFiber_bound (n k : ℕ) : dimensionFiber n k≤2*(1/8:ℝ)^k := by
  by_cases hk : k=0
  · simp [dimensionFiber,hk]
  rw [dimensionFiber,ite_eq_right hk]
  calc
    _ ≤ (Fintype.card {p : n.Partition // flatTail (diagram p)=k}:ℝ)*(1/16:ℝ)^k := by
      calc
        _ ≤ ∑p : {p : n.Partition // flatTail (diagram p)=k}, (1/16:ℝ)^k :=
          Finset.sum_le_sum (fun p _ => dimensionInv_exponential p.val p.property)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ (2*2^k:ℝ)*(1/16:ℝ)^k := by
      have hh : (Fintype.card {p : n.Partition // flatTail (diagram p)=k}:ℝ)≤2*2^k := by
        exact_mod_cast flatTail_card n k
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by rw [mul_assoc,←mul_pow]; norm_num

lemma dimensionFiber_grows_bound {n k : ℕ} (hk : 0<k) (hn : 2*k<n) :
    dimensionFiber n k≤(2*2^k:ℝ)*(((n-2*k:ℕ):ℝ)⁻¹)^8 := by
  rw [dimensionFiber,ite_eq_right (by omega : k≠0)]
  have hp : (0:ℝ)<(n-2*k:ℕ) := by exact_mod_cast (show 0<n-2*k by omega)
  calc
    _ ≤ (Fintype.card {p : n.Partition // flatTail (diagram p)=k}:ℝ)*(((n-2*k:ℕ):ℝ)⁻¹)^8 := by
      calc
        _ ≤ ∑p : {p : n.Partition // flatTail (diagram p)=k}, (((n-2*k:ℕ):ℝ)⁻¹)^8 := ?_
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      apply Finset.sum_le_sum
      intro p _
      have hd : ((n-2*k:ℕ):ℝ)≤Module.finrank ℂ (PartitionHilbert p.val) := by
        exact_mod_cast partition_dimension_grows p.val p.property hk
      have hi := one_div_le_one_div_of_le hp hd
      simp only [dimensionInv,←inv_pow]
      apply pow_le_pow_left₀ (by positivity)
      simpa only [one_div] using hi
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast flatTail_card n k) (by positivity)

lemma dimensionFiber_tendsto (k : ℕ) :
    Filter.Tendsto (fun n => dimensionFiber n k) Filter.atTop (nhds 0) := by
  by_cases hk : k=0
  · subst k
    simpa only [dimensionFiber,ite_true] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop (nhds 0))
  have ht : Filter.Tendsto (fun n : ℕ => n-2*k) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2 ⟨b+2*k,fun n hn => by omega⟩
  have hr : Filter.Tendsto (fun n : ℕ => ((n-2*k:ℕ):ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  have hlim : Filter.Tendsto (fun n : ℕ => (2*2^k:ℝ)*(((n-2*k:ℕ):ℝ)⁻¹)^8)
      Filter.atTop (nhds 0) := by
    simpa using (hr.inv_tendsto_atTop.pow 8).const_mul (2*2^k:ℝ)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => dimensionFiber_nonneg n k)) _ hlim
  exact Filter.eventually_atTop.2 ⟨2*k+1,fun n hn => dimensionFiber_grows_bound (by omega) (by omega)⟩

lemma dimensionFiber_eq_filter (n k : ℕ) : dimensionFiber n k=
    ∑p ∈ Finset.univ.filter (fun p : n.Partition => flatTail (diagram p)=k),
      if flatTail (diagram p)=0 then 0 else dimensionInv p := by
  unfold dimensionFiber
  split
  · subst k
    symm
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hp
    simp only [hp,ite_true]
  · rename_i hk
    rw [Finset.sum_subtype _ (by simp : ∀p : n.Partition,
      p ∈ Finset.univ.filter (fun p => flatTail (diagram p)=k) ↔ flatTail (diagram p)=k)]
    apply Finset.sum_congr rfl
    intro p _
    rw [ite_eq_right (by rw [p.property]; exact hk)]

lemma dimensionSeries_tsum (n : ℕ) : dimensionSeries n=∑'k,dimensionFiber n k := by
  rw [tsum_eq_sum (s:=Finset.range (n+1))]
  · simp_rw [dimensionFiber_eq_filter]
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro p _
    simp only [Finset.mem_range]
    have ht : flatTail (diagram p)≤n := by unfold flatTail; rw [diagram_card]; omega
    omega
  · intro k hk
    by_cases he : k=0
    · simp [dimensionFiber,he]
    rw [dimensionFiber,ite_eq_right he]
    apply Finset.sum_eq_zero
    intro p _
    have ht : flatTail (diagram p.val)≤n := by unfold flatTail; rw [diagram_card]; omega
    have hp := p.property
    simp only [Finset.mem_range,not_lt] at hk
    omega

theorem dimensionSeries_tendsto : Filter.Tendsto dimensionSeries Filter.atTop (nhds 0) := by
  have hs : Summable (fun k : ℕ => 2*(1/8:ℝ)^k) :=
    Summable.mul_left 2 (summable_geometric_of_norm_lt_one (by norm_num))
  have ht := tendsto_tsum_of_dominated_convergence hs dimensionFiber_tendsto
    (Filter.Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (dimensionFiber_nonneg n k)]
      exact dimensionFiber_bound n k))
  simpa only [←dimensionSeries_tsum,tsum_zero] using ht

end BinaryCoordinateSweeps.Young

end

end OAI
