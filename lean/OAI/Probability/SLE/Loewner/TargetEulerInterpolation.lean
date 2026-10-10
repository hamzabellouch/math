import OAI.Probability.SLE.Loewner.TargetEulerBridge

namespace OAI

/-! The prescribed Euler interpolants are continuous piecewise-affine
paths with the exact right derivative at every nonnegative time. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

lemma mesh_pos (N : ℕ) : 0 < mesh N := zpow_pos (by norm_num) _

lemma mesh_tendsto_zero : Tendsto mesh atTop (𝓝 0) := by
  have he (N : ℕ) : mesh N = ((2:ℝ)⁻¹)^N := by
    simp only [mesh,zpow_neg,zpow_natCast,inv_pow]
  have hm : mesh = fun N : ℕ => ((2:ℝ)⁻¹)^N := funext he
  rw [hm]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹ < 1)

lemma eulerFlow_on_cell (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ)
    (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc ((k:ℝ)*mesh N) (((k:ℝ)+1)*mesh N)) :
    eulerFlow κ b j N z t = eulerSteps κ b j N z k +
      ((t-(k:ℝ)*mesh N : ℝ):ℂ) * cutoffField κ b j ((k:ℝ)*mesh N) (eulerSteps κ b j N z k) := by
  have hh := mesh_pos N
  have ht0 : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg k) hh.le).trans ht.1
  by_cases hu : t=((k:ℝ)+1)*mesh N
  · have hd : t/mesh N=((k+1:ℕ):ℝ) := by rw [hu,mul_div_cancel_right₀ _ hh.ne']; norm_num
    simp only [eulerFlow,hd,Nat.floor_natCast,sub_self,Complex.ofReal_zero,zero_mul,
      sub_zero,add_zero]
    rw [eulerSteps]
    have he : t-(k:ℝ)*mesh N=mesh N := by rw [hu]; ring
    rw [he]
    simp only [Complex.ofReal_one,one_mul]
  · have hlt : t<((k:ℝ)+1)*mesh N := lt_of_le_of_ne ht.2 hu
    have hk : ⌊t/mesh N⌋₊=k := (Nat.floor_eq_iff (div_nonneg ht0 hh.le)).2
      ⟨(le_div_iff₀ hh).2 ht.1,(div_lt_iff₀ hh).2 hlt⟩
    simp only [eulerFlow,hk,eulerSteps]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hh.ne']
    ring

lemma eulerFlow_continuousOn_cell (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) (k : ℕ) :
    ContinuousOn (eulerFlow κ b j N z) (Icc ((k:ℝ)*mesh N) (((k:ℝ)+1)*mesh N)) := by
  have hc : Continuous (fun t : ℝ => eulerSteps κ b j N z k +
      ((t-(k:ℝ)*mesh N : ℝ):ℂ) * cutoffField κ b j ((k:ℝ)*mesh N) (eulerSteps κ b j N z k)) := by
    fun_prop
  exact hc.continuousOn.congr (fun t ht => eulerFlow_on_cell κ b j N z k t ht)

lemma eulerFlow_continuousOn_grid (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) (k : ℕ) :
    ContinuousOn (eulerFlow κ b j N z) (Icc 0 ((k:ℝ)*mesh N)) := by
  induction k with
  | zero => simpa only [Nat.cast_zero,zero_mul,Icc_self] using
      (continuousOn_singleton (eulerFlow κ b j N z) 0)
  | succ k ih =>
    have hnonneg : 0 ≤ (k:ℝ)*mesh N := mul_nonneg (Nat.cast_nonneg _) (mesh_pos N).le
    have hle : (k:ℝ)*mesh N ≤ ((k:ℝ)+1)*mesh N := by nlinarith [mesh_pos N]
    have hu : Icc (0:ℝ) (((k:ℝ)+1)*mesh N) =
        Icc 0 ((k:ℝ)*mesh N) ∪ Icc ((k:ℝ)*mesh N) (((k:ℝ)+1)*mesh N) := by
      ext t
      simp only [mem_Icc,mem_union]
      constructor
      · rintro ⟨ht0,ht1⟩
        rcases le_total t ((k:ℝ)*mesh N) with h|h
        · exact Or.inl ⟨ht0,h⟩
        · exact Or.inr ⟨h,ht1⟩
      · rintro (⟨ht0,ht1⟩|⟨ht0,ht1⟩)
        · exact ⟨ht0,ht1.trans hle⟩
        · exact ⟨hnonneg.trans ht0,ht1⟩
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hu]
    exact ih.union_of_isClosed (eulerFlow_continuousOn_cell κ b j N z k) isClosed_Icc isClosed_Icc

lemma eulerFlow_continuousOn (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) (T : ℝ) :
    ContinuousOn (eulerFlow κ b j N z) (Icc 0 T) := by
  obtain ⟨k,hk⟩ := exists_nat_ge (T/mesh N)
  have hT : T ≤ (k:ℝ)*mesh N := (div_le_iff₀ (mesh_pos N)).1 hk
  exact (eulerFlow_continuousOn_grid κ b j N z k).mono (Icc_subset_Icc le_rfl hT)

lemma eulerFlow_right_deriv (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (eulerFlow κ b j N z)
      (cutoffField κ b j (((⌊t/mesh N⌋₊:ℕ):ℝ)*mesh N)
        (eulerSteps κ b j N z ⌊t/mesh N⌋₊)) (Ici t) t := by
  let k := ⌊t/mesh N⌋₊
  let v := cutoffField κ b j ((k:ℝ)*mesh N) (eulerSteps κ b j N z k)
  have hh := mesh_pos N
  have hk : (k:ℝ)*mesh N ≤ t := (le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg ht hh.le))
  have hnext : t<((k:ℝ)+1)*mesh N := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one (t/mesh N))
  have he : eulerFlow κ b j N z =ᶠ[𝓝[Ici t] t]
      (fun s => eulerSteps κ b j N z k + ((s-(k:ℝ)*mesh N : ℝ):ℂ)*v) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hnext)] with s hs hu
    exact eulerFlow_on_cell κ b j N z k s ⟨hk.trans hs,hu.le⟩
  have hd : HasDerivAt (fun s : ℝ => eulerSteps κ b j N z k + ((s-(k:ℝ)*mesh N : ℝ):ℂ)*v) v t := by
    convert ((((hasDerivAt_id t).sub_const ((k:ℝ)*mesh N)).ofReal_comp).mul_const v).const_add
      (eulerSteps κ b j N z k) using 1 <;> simp
  exact hd.hasDerivWithinAt.congr_of_eventuallyEq he
    (eulerFlow_on_cell κ b j N z k t ⟨hk,hnext.le⟩)

lemma eulerFlow_zero (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) :
    eulerFlow κ b j N z 0=z := by
  simp [eulerFlow,eulerSteps]

lemma eulerSteps_dist_le (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ)
    (L : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L) (k : ℕ) :
    dist (eulerSteps κ b j N z k) z ≤ (k:ℝ)*mesh N*L := by
  induction k with
  | zero => simp [eulerSteps]
  | succ k ih =>
    rw [eulerSteps]
    have hs : dist (eulerSteps κ b j N z k + mesh N *
        cutoffField κ b j ((k:ℝ)*mesh N) (eulerSteps κ b j N z k))
        (eulerSteps κ b j N z k) ≤ mesh N*L := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mesh_pos N)]
      exact mul_le_mul_of_nonneg_left (hL _ _) (mesh_pos N).le
    have ht := (dist_triangle (eulerSteps κ b j N z k + mesh N *
      cutoffField κ b j ((k:ℝ)*mesh N) (eulerSteps κ b j N z k))
      (eulerSteps κ b j N z k) z).trans (add_le_add hs ih)
    exact ht.trans_eq (by push_cast; ring)

lemma eulerFlow_dist_grid_le (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ)
    (L : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L)
    (t : ℝ) (ht : 0 ≤ t) :
    dist (eulerFlow κ b j N z t) (eulerSteps κ b j N z ⌊t/mesh N⌋₊) ≤ L*mesh N := by
  let k := ⌊t/mesh N⌋₊
  have hh := mesh_pos N
  have hk : (k:ℝ)*mesh N ≤ t := (le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg ht hh.le))
  have hnext : t<((k:ℝ)+1)*mesh N := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one (t/mesh N))
  change dist (eulerFlow κ b j N z t) (eulerSteps κ b j N z k) ≤ L*mesh N
  rw [eulerFlow_on_cell κ b j N z k t ⟨hk,hnext.le⟩,dist_eq_norm,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hk)]
  have hlag : t-(k:ℝ)*mesh N ≤ mesh N := by nlinarith
  exact (mul_le_mul_of_nonneg_left (hL _ _) (sub_nonneg.mpr hk)).trans
    (by nlinarith [L.coe_nonneg])

lemma eulerFlow_dist_initial_le (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ)
    (L : ℝ≥0) (hL : ∀ t w, ‖cutoffField κ b j t w‖ ≤ L)
    (t : ℝ) (ht : 0 ≤ t) :
    dist (eulerFlow κ b j N z t) z ≤ L*t := by
  let k := ⌊t/mesh N⌋₊
  have hh := mesh_pos N
  have hk : (k:ℝ)*mesh N ≤ t := (le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg ht hh.le))
  have hnext : t<((k:ℝ)+1)*mesh N := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one (t/mesh N))
  have he := eulerFlow_on_cell κ b j N z k t ⟨hk,hnext.le⟩
  rw [he]
  have hb : dist (eulerSteps κ b j N z k+((t-(k:ℝ)*mesh N : ℝ):ℂ)*
      cutoffField κ b j ((k:ℝ)*mesh N) (eulerSteps κ b j N z k))
      (eulerSteps κ b j N z k) ≤ (t-(k:ℝ)*mesh N)*L := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hk)]
    exact mul_le_mul_of_nonneg_left (hL _ _) (sub_nonneg.mpr hk)
  have htriangle := (dist_triangle (eulerSteps κ b j N z k+((t-(k:ℝ)*mesh N : ℝ):ℂ)*
    cutoffField κ b j ((k:ℝ)*mesh N) (eulerSteps κ b j N z k))
    (eulerSteps κ b j N z k) z).trans
    (add_le_add hb (eulerSteps_dist_le κ b j N z L hL k))
  exact htriangle.trans_eq (by ring)

end SLEExactGauge.Target

end

end OAI
