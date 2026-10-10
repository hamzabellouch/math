import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.CutoffFlow

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.Euler
def interpolate (f : ℝ → ℂ → ℂ) (h : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  let k := ⌊t/h⌋₊
  let w := t/h-(k:ℝ)
  (1-w) • nodes f h z k + w • nodes f h z (k+1)

lemma finite_gronwall {e : ℕ → ℝ} {L h ε : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hε : 0 ≤ ε) (he0 : e 0 ≤ 0) {N : ℕ}
    (hrec : ∀ k < N, e (k+1) ≤ (1+L*h)*e k + ε*h) :
    e N ≤ ε*((N:ℝ)*h)*Real.exp (L*((N:ℝ)*h)) := by
  have hstep : ∀ k ≤ N, e k ≤ ε*((k:ℝ)*h)*Real.exp (L*((k:ℝ)*h)) := by
    intro k hk
    induction k with
    | zero => simpa using he0
    | succ k ih =>
      have hi := ih (by omega)
      have hk' : k < N := by omega
      have he : 1+L*h ≤ Real.exp (L*h) := by
        simpa only [add_comm] using Real.add_one_le_exp (L*h)
      have he1 : 1 ≤ Real.exp (L*(((k+1:ℕ):ℝ)*h)) :=
        Real.one_le_exp (by positivity)
      calc e (k+1)
          ≤ (1+L*h)*(ε*((k:ℝ)*h)*Real.exp (L*((k:ℝ)*h))) + ε*h :=
            (hrec k hk').trans (add_le_add (mul_le_mul_of_nonneg_left hi
              (show 0 ≤ 1+L*h from by positivity)) le_rfl)
        _ ≤ Real.exp (L*h)*(ε*((k:ℝ)*h)*Real.exp (L*((k:ℝ)*h))) +
            (ε*h)*Real.exp (L*(((k+1:ℕ):ℝ)*h)) := by
          exact add_le_add (mul_le_mul_of_nonneg_right he (by positivity))
            (le_mul_of_one_le_right (mul_nonneg hε hh) he1)
        _ = ε*(((k+1:ℕ):ℝ)*h)*Real.exp (L*(((k+1:ℕ):ℝ)*h)) := by
          have hex : Real.exp (L*(((k+1:ℕ):ℝ)*h)) =
              Real.exp (L*h)*Real.exp (L*((k:ℝ)*h)) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring
          rw [hex]
          push_cast
          ring
  exact hstep N le_rfl

lemma nodes_error {f : ℝ → ℂ → ℂ} {g : ℝ → ℂ} {z : ℂ} {L h ε T : ℝ}
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hg0 : g 0 = z)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x y, ‖f t x-f t y‖ ≤ L*‖x-y‖)
    (hres : ∀ k : ℕ, ((k+1:ℕ):ℝ)*h ≤ T →
      ‖g (((k+1:ℕ):ℝ)*h) - g ((k:ℝ)*h) - h • f ((k:ℝ)*h) (g ((k:ℝ)*h))‖ ≤ ε*h)
    (N : ℕ) (hN : (N:ℝ)*h ≤ T) :
    ‖nodes f h z N - g ((N:ℝ)*h)‖ ≤ ε*T*Real.exp (L*T) := by
  have hrec (k : ℕ) (hk : k < N) :
      ‖nodes f h z (k+1)-g (((k+1:ℕ):ℝ)*h)‖ ≤
        (1+L*h)*‖nodes f h z k-g ((k:ℝ)*h)‖ + ε*h := by
    have hkT : ((k+1:ℕ):ℝ)*h ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hh).trans hN
    have hk0 : 0 ≤ (k:ℝ)*h := by positivity
    have hkT' : (k:ℝ)*h ≤ T := (by push_cast; nlinarith : (k:ℝ)*h ≤ ((k+1:ℕ):ℝ)*h).trans hkT
    let r := g (((k+1:ℕ):ℝ)*h)-g ((k:ℝ)*h)-h • f ((k:ℝ)*h) (g ((k:ℝ)*h))
    have he : nodes f h z (k+1)-g (((k+1:ℕ):ℝ)*h) =
        (nodes f h z k-g ((k:ℝ)*h)) +
          h • (f ((k:ℝ)*h) (nodes f h z k)-f ((k:ℝ)*h) (g ((k:ℝ)*h))) - r := by
      simp only [nodes, r, smul_sub]
      abel
    rw [he]
    calc _ ≤ ‖nodes f h z k-g ((k:ℝ)*h)‖ +
          ‖h • (f ((k:ℝ)*h) (nodes f h z k)-f ((k:ℝ)*h) (g ((k:ℝ)*h)))‖ + ‖r‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖nodes f h z k-g ((k:ℝ)*h)‖ +
          h*(L*‖nodes f h z k-g ((k:ℝ)*h)‖) + ε*h := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (hlip _ ⟨hk0,hkT'⟩ _ _) hh)) (hres k hkT)
      _ = _ := by ring
  have hb := finite_gronwall (e := fun k => ‖nodes f h z k-g ((k:ℝ)*h)‖)
    hL hh hε (by simp [nodes, hg0]) hrec
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg _) hh).trans hN
  exact hb.trans (by gcongr)

lemma residual_bound {f : ℝ → ℂ → ℂ} {g : ℝ → ℂ} {T s h ε : ℝ}
    (hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt g (f t (g t)) (Icc 0 T) t)
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hsh : s+h ≤ T)
    (hosc : ∀ t ∈ Icc s (s+h), ‖f t (g t)-f s (g s)‖ ≤ ε) :
    ‖g (s+h)-g s-h • f s (g s)‖ ≤ ε*h := by
  have hsub : Icc s (s+h) ⊆ Icc 0 T := fun t ht => ⟨hs.trans ht.1, ht.2.trans hsh⟩
  have hd (t : ℝ) (ht : t ∈ Icc s (s+h)) :
      HasDerivWithinAt (fun u => g u-u • f s (g s))
        (f t (g t)-f s (g s)) (Icc s (s+h)) t := by
    convert! ((hder t (hsub ht)).mono hsub).sub
      (((hasDerivAt_id t).smul_const (f s (g s))).hasDerivWithinAt) using 1
    simp only [one_smul]
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hosc
    (convex_Icc s (s+h)) (left_mem_Icc.mpr (by linarith))
    (right_mem_Icc.mpr (by linarith))
  have he : (g (s+h)-(s+h) • f s (g s))-(g s-s • f s (g s)) =
      g (s+h)-g s-h • f s (g s) := by rw [add_smul]; abel
  simpa only [he, add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hh] using hb

lemma exists_residual_bound {f : ℝ → ℂ → ℂ} {g : ℝ → ℂ} {T : ℝ}
    (hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt g (f t (g t)) (Icc 0 T) t)
    (hcf : ContinuousOn (fun t => f t (g t)) (Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 ≤ h → h < δ → ∀ s : ℝ, 0 ≤ s → s+h ≤ T →
      ‖g (s+h)-g s-h • f s (g s)‖ ≤ ε*h := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hcf
  obtain ⟨δ,hδ,hb⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ,hδ, fun h hh hhδ s hs hsT => residual_bound hder hs hh hsT ?_⟩
  intro u hu
  apply le_of_lt
  have huT : u ∈ Icc 0 T := ⟨hs.trans hu.1, hu.2.trans hsT⟩
  have hsT' : s ∈ Icc 0 T := ⟨hs, by linarith⟩
  have hd : dist u s < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)]
    linarith [hu.2]
  simpa only [dist_eq_norm] using hb u huT s hsT' hd

lemma norm_interpolate_sub_le {x y z : ℂ} {w E : ℝ}
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hx : ‖x-z‖ ≤ E) (hy : ‖y-z‖ ≤ E) :
    ‖(1-w) • x+w • y-z‖ ≤ E := by
  have he : (1-w) • x+w • y-z = (1-w) • (x-z)+w • (y-z) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [he]
  calc _ ≤ ‖(1-w) • (x-z)‖+‖w • (y-z)‖ := norm_add_le _ _
    _ = (1-w)*‖x-z‖+w*‖y-z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hw1), abs_of_nonneg hw]
    _ ≤ (1-w)*E+w*E := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hw1))
      (mul_le_mul_of_nonneg_left hy hw)
    _ = E := by ring

lemma interpolate_error {f : ℝ → ℂ → ℂ} {g : ℝ → ℂ} {z : ℂ} {L M h ε T t : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hh : 0 < h) (hε : 0 ≤ ε) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hres : ∀ k : ℕ, ((k+1:ℕ):ℝ)*h ≤ T →
      ‖g (((k+1:ℕ):ℝ)*h) - g ((k:ℝ)*h) - h • f ((k:ℝ)*h) (g ((k:ℝ)*h))‖ ≤ ε*h)
    (hpath : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖g u-g v‖ ≤ M*|u-v|)
    (ht : 0 ≤ t) (htT : t+h ≤ T) :
    ‖interpolate f h z t-g t‖ ≤ ε*T*Real.exp (L*T)+M*h := by
  let k := ⌊t/h⌋₊
  have hf0 : (k:ℝ) ≤ t/h := Nat.floor_le (div_nonneg ht hh.le)
  have hf1 : t/h < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk0 : 0 ≤ (k:ℝ)*h := by positivity
  have hkt : (k:ℝ)*h ≤ t := (le_div_iff₀ hh).mp hf0
  have htks : t < ((k+1:ℕ):ℝ)*h := by
    push_cast
    exact (div_lt_iff₀ hh).mp hf1
  have hksT : ((k+1:ℕ):ℝ)*h ≤ T := by push_cast; nlinarith
  have hkT : (k:ℝ)*h ≤ T := hkt.trans (by linarith)
  have hw : 0 ≤ t/h-(k:ℝ) := by linarith
  have hw1 : t/h-(k:ℝ) ≤ 1 := by linarith
  apply norm_interpolate_sub_le hw hw1
  · calc _ ≤ ‖nodes f h z k-g ((k:ℝ)*h)‖+‖g ((k:ℝ)*h)-g t‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε*T*Real.exp (L*T)+M*h := add_le_add
        (nodes_error hL hh.le hε hg0 hlip hres k hkT)
        ((hpath _ ⟨hk0,hkT⟩ _ ⟨ht,by linarith⟩).trans (by
          rw [abs_of_nonpos (sub_nonpos.mpr hkt)]
          apply mul_le_mul_of_nonneg_left _ hM
          push_cast at htks
          linarith))
  · calc _ ≤ ‖nodes f h z (k+1)-g (((k+1:ℕ):ℝ)*h)‖+
          ‖g (((k+1:ℕ):ℝ)*h)-g t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε*T*Real.exp (L*T)+M*h := add_le_add
        (nodes_error hL hh.le hε hg0 hlip hres (k+1) hksT)
        ((hpath _ ⟨by positivity,hksT⟩ _ ⟨ht,by linarith⟩).trans (by
          rw [abs_of_nonneg (by linarith : 0 ≤ ((k+1:ℕ):ℝ)*h-t)]
          apply mul_le_mul_of_nonneg_left _ hM
          push_cast
          linarith))

lemma converge {f : ℝ → ℂ → ℂ} {g : ℝ → ℂ} {z : ℂ} {L M T t : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (f u (g u)) (Icc 0 T) u)
    (hcf : ContinuousOn (fun u => f u (g u)) (Icc 0 T))
    (hbound : ∀ u ∈ Icc 0 T, ‖f u (g u)‖ ≤ M)
    (ht : 0 ≤ t) (htT : t < T)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => interpolate f (h n) z t) atTop (𝓝 (g t)) := by
  have hT : 0 < T := lt_of_le_of_lt ht htT
  have hpath : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖g u-g v‖ ≤ M*|u-v| := by
    intro u hu v hv
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 T) hv hu
  rw [Metric.tendsto_nhds]
  intro ε hε
  let E := T*Real.exp (L*T)
  have hE : 0 < E := mul_pos hT (Real.exp_pos _)
  let η := ε/(2*E)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hres⟩ := exists_residual_bound hder hcf hη
  have hev1 : ∀ᶠ n in atTop, h n < δ := (tendsto_order.1 hh0).2 δ hδ
  have hev2 : ∀ᶠ n in atTop, h n < T-t :=
    (tendsto_order.1 hh0).2 (T-t) (sub_pos.mpr htT)
  have hev3 : ∀ᶠ n in atTop, h n < ε/(2*(M+1)) :=
    (tendsto_order.1 hh0).2 _ (div_pos hε (by positivity))
  filter_upwards [hev1,hev2,hev3] with n hnδ hnT hnε
  rw [dist_eq_norm]
  have hb := interpolate_error hL hM (hh n) hη.le hg0 hlip
    (fun k hk => by
      have hc : ((k+1:ℕ):ℝ)*h n = (k:ℝ)*h n+h n := by push_cast; ring
      rw [hc] at hk ⊢
      exact hres (h n) (hh n).le hnδ ((k:ℝ)*h n) (mul_nonneg (Nat.cast_nonneg _) (hh n).le) hk)
    hpath ht (by linarith : t+h n ≤ T)
  apply lt_of_le_of_lt hb
  have hηE : η*T*Real.exp (L*T) = ε/2 := by
    dsimp [η, E]
    field_simp
  have hsmall : M*h n < ε/2 := by
    have hhε := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hnε
    nlinarith [hh n]
  rw [hηE]
  linarith

lemma converge_uniformOn {f : ℝ → ℂ → ℂ} {g : ℝ → ℂ} {z : ℂ} {L M T U : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (f u (g u)) (Icc 0 T) u)
    (hcf : ContinuousOn (fun u => f u (g u)) (Icc 0 T))
    (hbound : ∀ u ∈ Icc 0 T, ‖f u (g u)‖ ≤ M)
    (hU : 0 ≤ U) (hUT : U < T)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => interpolate f (h n) z) g atTop (Icc 0 U) := by
  have hT : 0 < T := lt_of_le_of_lt hU hUT
  have hpath : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖g u-g v‖ ≤ M*|u-v| := by
    intro u hu v hv
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 T) hv hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let E := T*Real.exp (L*T)
  have hE : 0 < E := mul_pos hT (Real.exp_pos _)
  let η := ε/(2*E)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hres⟩ := exists_residual_bound hder hcf hη
  have hev1 : ∀ᶠ n in atTop, h n < δ := (tendsto_order.1 hh0).2 δ hδ
  have hev2 : ∀ᶠ n in atTop, h n < T-U :=
    (tendsto_order.1 hh0).2 (T-U) (sub_pos.mpr hUT)
  have hev3 : ∀ᶠ n in atTop, h n < ε/(2*(M+1)) :=
    (tendsto_order.1 hh0).2 _ (div_pos hε (by positivity))
  filter_upwards [hev1,hev2,hev3] with n hnδ hnT hnε
  intro t ht
  rw [dist_comm, dist_eq_norm]
  have hb := interpolate_error hL hM (hh n) hη.le hg0 hlip
    (fun k hk => by
      have hc : ((k+1:ℕ):ℝ)*h n = (k:ℝ)*h n+h n := by push_cast; ring
      rw [hc] at hk ⊢
      exact hres (h n) (hh n).le hnδ ((k:ℝ)*h n)
        (mul_nonneg (Nat.cast_nonneg _) (hh n).le) hk)
    hpath ht.1 (by linarith [ht.2] : t+h n ≤ T)
  apply lt_of_le_of_lt hb
  have hηE : η*T*Real.exp (L*T) = ε/2 := by
    dsimp [η, E]
    field_simp
  have hsmall : M*h n < ε/2 := by
    have hhε := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hnε
    nlinarith [hh n]
  rw [hηE]
  linarith

end SLEExactGauge.Euler

namespace SLEExactGauge.LiteralTrace

lemma continuous_driverValue (b : Driver) : Continuous (driverValue b) :=
  (map_continuous b).comp continuous_real_toNNReal

lemma mesh_pos (n : ℕ) : 0 < mesh n := zpow_pos (by norm_num) _

lemma mesh_tendsto_zero : Tendsto mesh atTop (𝓝 0) := by
  have he : mesh = fun n : ℕ => ((2:ℝ)⁻¹)^n := by
    funext n
    simp only [mesh, zpow_neg, zpow_natCast, inv_pow]
  rw [he]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma cutoffField_eq (κ : ℝ) (b : Driver) (j : ℕ) :
    cutoffField κ b j = Cutoff.field (a κ) ((j:ℝ)^(-(2:ℤ))) (driverValue b) := by
  funext t z
  have hp : ((j:ℝ)^(-(2:ℤ)))^2 = (j:ℝ)^(-(4:ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  simp only [cutoffField, Cutoff.field, Cutoff.inverse, Cutoff.denominator, hp, mul_div_assoc]

lemma eulerSteps_eq_nodes (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) :
    eulerSteps κ b j N z = Euler.nodes (cutoffField κ b j) (mesh N) z := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih => simp only [eulerSteps, Euler.nodes, ih, Complex.real_smul]

lemma eulerFlow_eq_interpolate (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) :
    eulerFlow κ b j N z = Euler.interpolate (cutoffField κ b j) (mesh N) z := by
  funext t
  simp only [eulerFlow, Euler.interpolate, eulerSteps_eq_nodes, Complex.real_smul]

 

theorem cutoffFlow_solution (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun N => eulerFlow κ b j N z) (cutoffFlow κ b j z) atTop (Icc 0 T) ∧
    cutoffFlow κ b j z 0 = z ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (cutoffFlow κ b j z)
      (cutoffField κ b j t (cutoffFlow κ b j z t)) (Icc 0 T) t := by
  let q : ℝ := (j:ℝ)^(-(2:ℤ))
  have hq : 0 < q := zpow_pos (by exact_mod_cast hj) _
  obtain ⟨g,hg0,hg⟩ := Cutoff.exists_solution_on_compact hq (a κ) (continuous_driverValue b) z
    (show 0 ≤ T+1 by linarith)
  have hg' : ∀ t ∈ Icc 0 (T+1),
      HasDerivWithinAt g (cutoffField κ b j t (g t)) (Icc 0 (T+1)) t := by
    simpa only [cutoffField_eq] using hg
  have hgc : ContinuousOn g (Icc 0 (T+1)) := fun t ht => (hg' t ht).continuousWithinAt
  have hfc : ContinuousOn (fun t => cutoffField κ b j t (g t)) (Icc 0 (T+1)) := by
    simp only [cutoffField_eq, Cutoff.field]
    exact continuousOn_const.mul ((Cutoff.lipschitz_inverse hq).continuous.comp_continuousOn
      (hgc.sub ((Complex.continuous_ofReal.comp (continuous_driverValue b)).continuousOn)))
  have hconv : TendstoUniformlyOn (fun N => eulerFlow κ b j N z) g atTop (Icc 0 T) := by
    simp only [eulerFlow_eq_interpolate]
    apply Euler.converge_uniformOn (L := |a κ| * 3/q^2) (M := |a κ|/q)
      (by positivity) (by positivity) hg0 _ hg' hfc _ hT (by linarith)
      mesh_pos mesh_tendsto_zero
    · intro t ht x y
      rw [cutoffField_eq]
      exact Cutoff.field_sub_le hq _ _ _ _ _
    · intro t ht
      rw [cutoffField_eq]
      exact Cutoff.norm_field_le hq _ _ _ _
  have heq : ∀ t ∈ Icc 0 T, cutoffFlow κ b j z t = g t := by
    intro t ht
    exact (hconv.tendsto_at ht).limUnder_eq
  refine ⟨?_, (heq 0 ⟨le_rfl,hT⟩).trans hg0, ?_⟩
  · exact hconv.congr_right (fun t ht => (heq t ht).symm)
  · intro t ht
    rw [heq t ht]
    exact ((hg' t ⟨ht.1,by linarith [ht.2]⟩).mono
      (show Icc 0 T ⊆ Icc 0 (T+1) from fun u hu => ⟨hu.1,by linarith [hu.2]⟩)).congr heq (heq t ht)

end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace

 
def PositiveSolution (κ : ℝ) (b : Driver) (z : ℂ) (T : ℝ) (f : ℝ → ℂ) : Prop :=
  0 ≤ T ∧ ContinuousOn f (Icc 0 T) ∧ f 0 = z ∧
  (∀ t ∈ Icc 0 T, 0 < (f t).im) ∧
  ∀ t ∈ Icc 0 T, HasDerivWithinAt f ((a κ : ℂ)/(f t-driverValue b t)) (Icc 0 T) t

lemma cutoffField_of_height (κ : ℝ) (b : Driver) {j : ℕ} (hj : 1 ≤ j)
    {t : ℝ} {z : ℂ} (hz : (j:ℝ)⁻¹ ≤ z.im) :
    cutoffField κ b j t z = (a κ : ℂ)/(z-driverValue b t) := by
  have hjpos : (0:ℝ) < j := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hjone : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hi : (j:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hjpos).mpr hjone
  have hin : 0 ≤ (j:ℝ)⁻¹ := (inv_pos.mpr hjpos).le
  have hn : (j:ℝ)⁻¹ ≤ ‖z-driverValue b t‖ :=
    hz.trans (by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using Complex.im_le_norm (z-driverValue b t))
  have hsq : (j:ℝ)⁻¹^2 ≤ (j:ℝ)⁻¹ := by nlinarith
  have hpow : (j:ℝ)^(-(4:ℤ)) ≤ ‖z-driverValue b t‖^2 := by
    norm_num only [zpow_neg,zpow_ofNat]
    rw [← inv_pow]
    calc
      (j:ℝ)⁻¹^4 = ((j:ℝ)⁻¹^2)^2 := by ring
      _ ≤ ((j:ℝ)⁻¹)^2 := pow_le_pow_left₀ (sq_nonneg _) hsq 2
      _ ≤ ‖z-driverValue b t‖^2 := pow_le_pow_left₀ hin hn 2
  unfold cutoffField
  simp only [max_eq_left hpow,div_eq_mul_inv]
  rw [Complex.inv_def (z-driverValue b t)]
  simp only [Complex.normSq_eq_norm_sq,Complex.ofReal_inv,starRingEnd_apply,mul_assoc]

lemma cutoffFlow_continuous (κ : ℝ) (b : Driver) {j : ℕ} (hj : 1 ≤ j) (z : ℂ)
    {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (cutoffFlow κ b j z) (Icc 0 T) :=
  fun t ht => ((cutoffFlow_solution κ b j hj z hT).2.2 t ht).continuousWithinAt

lemma cutoff_solution_unique (κ : ℝ) (b : Driver) {j : ℕ} (hj : 1 ≤ j)
    {z : ℂ} {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℂ}
    (hc : ContinuousOn f (Icc 0 T)) (h0 : f 0 = z)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (cutoffField κ b j t (f t)) (Icc 0 T) t) :
    EqOn (cutoffFlow κ b j z) f (Icc 0 T) := by
  let q : ℝ := (j:ℝ)^(-(2:ℤ))
  have hq : 0 < q := zpow_pos (by exact_mod_cast (Nat.zero_lt_of_lt hj)) _
  let K : ℝ≥0 := ⟨|a κ| * 3/q^2,by positivity⟩
  apply ODE_solution_unique (v := cutoffField κ b j) (K := K)
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [dist_eq_norm,cutoffField_eq]
    exact Cutoff.field_sub_le hq _ _ _ _ _
  · exact cutoffFlow_continuous κ b hj z hT
  · intro t ht
    exact ((cutoffFlow_solution κ b j hj z hT).2.2 t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  · exact hc
  · intro t ht
    exact (hd t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  · rw [(cutoffFlow_solution κ b j hj z hT).2.1,h0]

lemma PositiveSolution.cutoff_eq {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) {j : ℕ} (hj : 1 ≤ j)
    (hgap : ∀ t ∈ Icc 0 T, (j:ℝ)⁻¹ ≤ (f t).im) :
    EqOn (cutoffFlow κ b j z) f (Icc 0 T) := by
  apply cutoff_solution_unique κ b hj hf.1 hf.2.1 hf.2.2.1
  intro t ht
  rw [cutoffField_of_height κ b hj (hgap t ht)]
  exact hf.2.2.2.2 t ht

lemma PositiveSolution.exists_cutoff {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) :
    ∃ j : ℕ, 1 ≤ j ∧ ∀ t ∈ Icc 0 T, (j:ℝ)⁻¹ < (f t).im := by
  obtain ⟨t0,ht0,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0,le_rfl,hf.1⟩
    (Complex.continuous_im.comp_continuousOn hf.2.1)
  have hy := hf.2.2.2.1 t0 ht0
  have ht : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨j,hj,hj'⟩ := ((eventually_ge_atTop 1).and (ht.eventually (eventually_lt_nhds hy))).exists
  exact ⟨j,hj,fun t ht => hj'.trans_le (hmin ht)⟩

lemma PositiveSolution.unique {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f g : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) (hg : PositiveSolution κ b z T g) : EqOn f g (Icc 0 T) := by
  obtain ⟨j,hj,hjf⟩ := hf.exists_cutoff
  obtain ⟨k,hk,hkg⟩ := hg.exists_cutoff
  let n := max j k
  have hn : 1 ≤ n := hj.trans (le_max_left _ _)
  have hinj : (n:ℝ)⁻¹ ≤ (j:ℝ)⁻¹ := inv_anti₀ (by exact_mod_cast (Nat.zero_lt_of_lt hj)) (by exact_mod_cast le_max_left j k)
  have hink : (n:ℝ)⁻¹ ≤ (k:ℝ)⁻¹ := inv_anti₀ (by exact_mod_cast (Nat.zero_lt_of_lt hk)) (by exact_mod_cast le_max_right j k)
  have he := hf.cutoff_eq hn (fun t ht => hinj.trans (hjf t ht).le)
  have hg' := hg.cutoff_eq hn (fun t ht => hink.trans (hkg t ht).le)
  exact fun t ht => (he ht).symm.trans (hg' ht)

end SLEExactGauge.LiteralTrace
end
end
end
end

end OAI
