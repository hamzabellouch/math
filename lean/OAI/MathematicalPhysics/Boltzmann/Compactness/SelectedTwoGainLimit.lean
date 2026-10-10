import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.MainCoreScaleWindow
import OAI.MathematicalPhysics.Boltzmann.Branching.RetainedAxialDecay
import OAI.MathematicalPhysics.Boltzmann.Branching.TwoCoreLimit

namespace OAI

section

/-! # Removing the large-scale remainder from the selected pair integral -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel discardedFreeKernel

theorem selected_pair_le_retained {r s₀ η K α γ d₀ q M a t₁ t₂ : ℝ} {N : ℕ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hM : 0 < M) (ht₂ : a ≤ t₂) (htt : t₂ ≤ t₁) (x v : Velocity) :
    (∫⁻ w, selectedFreeKernel r s₀ η K α γ d₀ q N ((t₂,x-(t₁-t₂) • w),w) univ
      ∂selectedFreeKernel r s₀ η K α γ d₀ q N ((t₁,x),v)) ≤
    (∫⁻ w, retainedFreeKernel r s₀ η K α γ d₀ q M N ((t₂,x-(t₁-t₂) • w),w) univ
      ∂selectedFreeKernel r s₀ η K α γ d₀ q N ((t₁,x),v))+
      ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/M)*
        ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a) := by
  let κ := selectedFreeKernel r s₀ η K α γ d₀ q N ((t₁,x),v)
  let D := ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/M)
  have hb (w : Velocity) :
      selectedFreeKernel r s₀ η K α γ d₀ q N ((t₂,x-(t₁-t₂) • w),w) univ ≤
        retainedFreeKernel r s₀ η K α γ d₀ q M N ((t₂,x-(t₁-t₂) • w),w) univ+D := by
    rw [selectedFreeKernel_decomposition r s₀ η K α γ d₀ q M N]
    change _+_ ≤ _+D
    exact add_le_add le_rfl (discardedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ
      hd₀ hdmax hq₁ hq₂ hM N ((t₂,x-(t₁-t₂) • w),w) (ha.le.trans ht₂))
  have hm : κ univ ≤ ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a) := by
    apply (selectedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N
      ((t₁,x),v) (ha.trans_le (ht₂.trans htt))).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
      (JetCoreSheet.growthConstant_nonneg hK α γ q) ha (ht₂.trans htt))
  calc
    _ ≤ ∫⁻ w, retainedFreeKernel r s₀ η K α γ d₀ q M N
        ((t₂,x-(t₁-t₂) • w),w) univ+D ∂κ := lintegral_mono hb
    _ = (∫⁻ w, retainedFreeKernel r s₀ η K α γ d₀ q M N
        ((t₂,x-(t₁-t₂) • w),w) univ ∂κ)+D*κ univ := by
      rw [lintegral_add_right _ measurable_const,lintegral_const]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl hm)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Vanishing of two actual selected gains at an axial endpoint -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel

theorem selected_pair_axial_tendsto {K α γ q a s₀ η d₀ V T : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V)
    (r t₁ t₂ : ℕ → ℝ) (N : ℕ → ℕ) (x v : ℕ → Velocity)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht₂ : ∀ n, a ≤ t₂ n) (htt : ∀ n, t₂ n ≤ t₁ n) (ht₁ : ∀ n, t₁ n ≤ T)
    (hv : ∀ n, ‖v n‖ ≤ V)
    (htrans : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ w,
      selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n)
        ((t₂ n,x n-(t₁ n-t₂ n) • w),w) univ
      ∂selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) ((t₁ n,x n),v n)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hε.ne'
  have he' : (0 : ℝ) < e := he
  let S := JetCoreSheet.growthConstant K α γ q
  let C := S/a
  have hS : 0 ≤ S := JetCoreSheet.growthConstant_nonneg hK α γ q
  have hC : 0 ≤ C := div_nonneg hS ha.le
  let M := (S*C+1)/(e : ℝ)
  have hM : 0 < M := div_pos (by positivity) he'
  have herror : ENNReal.ofReal (S/M)*ENNReal.ofReal C ≤ (e : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hS hM.le),← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hm : S*C ≤ (e : ℝ)*M := by
      calc
        _ ≤ S*C+1 := by linarith
        _ = (e : ℝ)*M := by dsimp [M]; field_simp
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hm)
  have hret := selected_retained_pair_tendsto hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax
    hd₀ hdmax hV r t₁ t₂ N x v hr hrlim ht₂ htt ht₁ hv htrans (M := M)
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hret) e (ENNReal.coe_pos.mpr he)] with n hn
  calc
    _ ≤ (∫⁻ w, retainedFreeKernel (r n) s₀ η K α γ d₀ q M (N n)
        ((t₂ n,x n-(t₁ n-t₂ n) • w),w) univ
      ∂selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) ((t₁ n,x n),v n))+
        ENNReal.ofReal (S/M)*ENNReal.ofReal C :=
      selected_pair_le_retained (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
        ha hM (ht₂ n) (htt n) (x n) (v n)
    _ ≤ (e : ℝ≥0∞)+e := add_le_add hn herror
    _ = (e : ℝ≥0∞)*2 := by ring
    _ ≤ ε := heε.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform selected-pair convergence and the two collision times -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel

def selectedPairMass (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) (t₁ t₂ : ℝ) (x v : Velocity) : ℝ≥0∞ :=
  ∫⁻ w, selectedFreeKernel r s₀ η K α γ d₀ q N ((t₂,x-(t₁-t₂) • w),w) univ
    ∂selectedFreeKernel r s₀ η K α γ d₀ q N ((t₁,x),v)

variable {K α γ q a s₀ η d₀ V T : ℝ}
  (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
  (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
  (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V)
  (r b : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
  (hblim : Tendsto b atTop (𝓝 0))

include hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax hd₀ hdmax hV hr hrlim hblim in
theorem selected_pair_uniform {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (N : ℕ) (t₁ t₂ : ℝ) (x v : Velocity),
      a ≤ t₂ → t₂ ≤ t₁ → t₁ ≤ T → ‖v‖ ≤ V → ‖transverse v‖ ≤ b n →
      selectedPairMass (r n) s₀ η K α γ d₀ q N t₁ t₂ x v ≤ ε := by
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hε.ne'
  have he' : (0 : ℝ) < e := he
  let S := JetCoreSheet.growthConstant K α γ q
  let C := S/a
  have hS : 0 ≤ S := JetCoreSheet.growthConstant_nonneg hK α γ q
  have hC : 0 ≤ C := div_nonneg hS ha.le
  let M := (S*C+1)/(e : ℝ)
  have hM : 0 < M := div_pos (by positivity) he'
  have herror : ENNReal.ofReal (S/M)*ENNReal.ofReal C ≤ (e : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hS hM.le),← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hm : S*C ≤ (e : ℝ)*M := by
      calc
        _ ≤ S*C+1 := by linarith
        _ = (e : ℝ)*M := by dsimp [M]; field_simp
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hm)
  let e₀ := (e : ℝ)/(3*C+1)
  have he₀ : 0 < e₀ := div_pos he' (by positivity)
  obtain ⟨L,d,ρ,hL,hd,hρ,hsmall⟩ := selected_retained_pair_small
    hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax hd₀ hdmax hV he₀ (M := M)
  have hD := GeometricMesh.retained_thermal_width_tendsto d₀ M hrlim
  have hflight : Tendsto (fun n => r n*T*L) atTop (𝓝 0) := by
    simpa using (hrlim.mul_const T).mul_const L
  filter_upwards [hD.eventually (gt_mem_nhds hd),
    hflight.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)),
    hblim.eventually (gt_mem_nhds hρ)] with n hnD hnF hnb
  intro N t₁ t₂ x v ht₂ htt ht₁ hv htrans
  have hret := hsmall (N := N) (hr n) hnD.le hnF ht₂ htt ht₁ x v hv (htrans.trans hnb.le)
  have hret' : (∫⁻ w, retainedFreeKernel (r n) s₀ η K α γ d₀ q M N
      ((t₂,x-(t₁-t₂) • w),w) univ
    ∂selectedFreeKernel (r n) s₀ η K α γ d₀ q N ((t₁,x),v)) ≤ (e : ℝ≥0∞) := by
    apply hret.trans
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (3*C+1)*e₀ := mul_le_mul_of_nonneg_right (by change 3*C ≤ 3*C+1; linarith) he₀.le
      _ = e := by dsimp [e₀]; field_simp
  calc
    _ ≤ (∫⁻ w, retainedFreeKernel (r n) s₀ η K α γ d₀ q M N
      ((t₂,x-(t₁-t₂) • w),w) univ
      ∂selectedFreeKernel (r n) s₀ η K α γ d₀ q N ((t₁,x),v))+
        ENNReal.ofReal (S/M)*ENNReal.ofReal C :=
      selected_pair_le_retained (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
        ha hM ht₂ htt x v
    _ ≤ (e : ℝ≥0∞)+e := add_le_add hret' herror
    _ = (e : ℝ≥0∞)*2 := by ring
    _ ≤ ε := heε.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Transverse spatial escape removes every bounded retained scale -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem retained_zero_of_transverse_far {r s₀ η K α γ d₀ q M : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (N : ℕ) (z : Published.KineticPhase)
    (hx : ∀ k : Lattice, Real.exp η*M ≤ ‖transverse (z.1.2-r⁻¹ • latticeVector k)‖) :
    retainedFreeKernel r s₀ η K α γ d₀ q M N z = 0 := by
  rcases retainedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax z with hz | ⟨i,hi,hM,_⟩
  · exact hz
  · have h := (mainCoreRegion_scale_radius hs₀ hη hr hi).2
    have hle := mul_le_mul_of_nonneg_left hM (Real.exp_pos η).le
    exact False.elim ((h.trans_le hle).not_ge (hx i.lattice))

theorem selected_transverse_escape_small {K α γ q a T V s₀ η d₀ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 ≤ a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (N : ℕ → ℕ) (z : ℕ → Published.KineticPhase)
    (ht : ∀ n, (z n).1.1 ∈ Icc a T) (hv : ∀ n, ‖(z n).2‖ ≤ V)
    (hx : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ k : Lattice,
      R ≤ ‖transverse ((z n).1.2-(r n)⁻¹ • latticeVector k)‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc a (z n).1.1,
      selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s) univ ≤ ENNReal.ofReal ε := by
  let G := JetCoreSheet.growthConstant K α γ q
  let M := (G+1)/ε
  have hG : 0 ≤ G := JetCoreSheet.growthConstant_nonneg hK α γ q
  have hM : 0 < M := div_pos (by linarith) hε
  have hGM : G/M ≤ ε := by
    apply (div_le_iff₀ hM).mpr
    have he : ε*M = G+1 := by dsimp [M]; field_simp
    linarith
  have hT : 0 ≤ T := ha.trans (ht 0).1 |>.trans (ht 0).2
  filter_upwards [hx (Real.exp η*M+T*V)] with n hn
  intro s hs
  have hsT : s ∈ Icc 0 T := ⟨ha.trans hs.1,hs.2.trans (ht n).2⟩
  have hfar (k : Lattice) : Real.exp η*M ≤
      ‖transverse ((flight (z n) s).1.2-(r n)⁻¹ • latticeVector k)‖ := by
    have hlen : 0 ≤ (z n).1.1-s := sub_nonneg.mpr hs.2
    have hlenT : (z n).1.1-s ≤ T := by linarith [hsT.1,(ht n).2]
    have hv' := (LargeOutput.transverse_norm_le (z n).2).trans (hv n)
    have he : transverse ((z n).1.2-(r n)⁻¹ • latticeVector k) =
        transverse ((flight (z n) s).1.2-(r n)⁻¹ • latticeVector k)+
          ((z n).1.1-s) • transverse (z n).2 := by
      apply (WithLp.ext_iff 2).mpr
      funext i
      change (z n).1.2 i.castSucc-(r n)⁻¹*(k i.castSucc:ℝ) =
        ((z n).1.2 i.castSucc-((z n).1.1-s)*(z n).2 i.castSucc-
          (r n)⁻¹*(k i.castSucc:ℝ))+((z n).1.1-s)*(z n).2 i.castSucc
      ring
    have htri := norm_add_le
      (transverse ((flight (z n) s).1.2-(r n)⁻¹ • latticeVector k))
      (((z n).1.1-s) • transverse (z n).2)
    rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hlen] at htri
    have hp := mul_le_mul hlenT hv' (norm_nonneg _) hT
    linarith [hn k]
  have hzero := retained_zero_of_transverse_far (K := K) (α := α) (γ := γ) (d₀ := d₀)
    (q := q) (M := M) (hr n) hs₀ hsmax hη hηmax (N n)
    (flight (z n) s) hfar
  rw [selectedFreeKernel_decomposition (r n) s₀ η K α γ d₀ q M (N n)]
  change (retainedFreeKernel (r n) s₀ η K α γ d₀ q M (N n) (flight (z n) s)+
    discardedFreeKernel (r n) s₀ η K α γ d₀ q M (N n) (flight (z n) s)) univ ≤ _
  rw [hzero,zero_add]
  exact (discardedFreeKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax
    hq₁ hq₂ hM (N n) (flight (z n) s) hsT.1).trans (ENNReal.ofReal_le_ofReal hGM)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual selected two-gain iterate vanishes at axial endpoints -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel

theorem selected_two_gain_axial_tendsto {K α γ q a s₀ η d₀ V T : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V)
    (r t : ℕ → ℝ) (N : ℕ → ℕ) (x v : ℕ → Velocity)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ≤ T) (hv : ∀ n, ‖v n‖ ≤ V)
    (htrans : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => PositiveIteration.iterate a
      (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n)) (fun _ => 1) 2 ((t n,x n),v n))
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hVol : (volume (Ioc a T))^2 ≠ ∞ := ENNReal.pow_ne_top measure_Ioc_lt_top.ne
  obtain ⟨δ,hδ,hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hVol hε.ne'
  have hpair := selected_pair_uniform hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax hd₀ hdmax hV
    r (fun n => ‖transverse (v n)‖) hr hrlim htrans (T := T) (ε := δ) (ENNReal.coe_pos.mpr hδ)
  filter_upwards [hpair] with n hn
  rw [PositiveIteration.iterate_two_eq_pairMass]
  have hi : ∀ t₁ ∈ Ioc a (t n), ∀ t₂ ∈ Ioc a t₁,
      PositiveIteration.pairMass (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n))
        (PositiveIteration.flight ((t n,x n),v n) t₁) t₂ ≤ δ := by
    intro t₁ ht₁ t₂ ht₂
    exact hn (N n) t₁ t₂ (x n-(t n-t₁) • v n) (v n) ht₂.1.le ht₂.2
      (ht₁.2.trans (ht n)) (hv n) le_rfl
  apply (GainPullback.two_time_integral_le hi).trans
  calc
    (δ : ℝ≥0∞)*(volume (Ioc a (t n)))^2 ≤ δ*(volume (Ioc a T))^2 := by
      have hm : volume (Ioc a (t n)) ≤ volume (Ioc a T) :=
        measure_mono (Ioc_subset_Ioc_right (ht n))
      simpa only [pow_two] using mul_le_mul' (show (δ : ℝ≥0∞) ≤ δ from le_rfl)
        (mul_le_mul' hm hm)
    _ ≤ ε := hδε.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
