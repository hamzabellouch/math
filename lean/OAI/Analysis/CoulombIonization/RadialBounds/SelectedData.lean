import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SelectionBudget
import OAI.Analysis.CoulombIonization.ThomasFermi.AnnularTFAndCap

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphRawLaw physicalObservationLaw jointMasterPosterior

theorem exists_actual_selected_data_constants :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧
      ∀ {ι : Type*} {f : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N : ι → ℕ),
        (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s f (𝓝 0) →
        Tendsto (fun i => (Z i:ℝ)*(s i)^3) f atTop →
        (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
        ∀ l : ℝ, 1 ≤ l → ∀ᶠ i in f,
          Nonempty (SelectedQuantumData (Z i) (N i) (s i) l (selectedTailThreshold (s i)) B C selectedTailRadius) := by
  classical
  let c : ℝ := 1/2000000
  have hc : 0 < c := by norm_num [c]
  have hcL : c < (10*(100000:ℝ))⁻¹ := by norm_num [c]
  have hc1 : c ≤ 1/2 := by norm_num [c]
  obtain ⟨ε,B,C,M,D,hε,hε1,hB,hM,hD,hbar⟩ := actual_outward_barrier_given_state_eventually hc hcL
  refine ⟨B,max C 0,hB,le_max_right _ _,?_⟩
  intro ι f Z s N hZ hs hs0 hscale hN l hl
  have hlp : 0 < l := zero_lt_one.trans_le hl
  let r : ι → ℝ := fun i => ε*(Z i:ℝ)^(-1/3:ℝ)
  let J : ι → ℕ := fun i => selectedDyadicIndex (r i) (s i/l)
  let K : ι → ℕ := fun i => J i+1
  have hZp (i) : 0 < (Z i:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hZ i))
  have hr (i) : 0 < r i := mul_pos hε (Real.rpow_pos_of_pos (hZp i) _)
  let p₀ (i) : Fin (K i+1) → ℝ := fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*r i)
  have hp₀ (i) (j : Fin (K i+1)) : 0 < p₀ i j :=
    tinyProbabilityFloor_pos (by positivity) (mul_pos (pow_pos (by norm_num) _) (hr i))
  have hstate (i) : ∃ F : fermionGraph (N i),
      OwnProbabilityTailTiltState (Z i) ((s i)^(-4:ℝ)) (r i) (K i) (p₀ i) 1 F ∧
      (s i ≤ 1 → actualScreenRadius*s i ≤ 1 →
        (∫ x, rawExteriorCount (2*(actualScreenRadius*s i)) x ∂graphRawLaw F) ≤ actualScreenConstant/s i) := by
    by_cases hh : s i ≤ 1 ∧ actualScreenRadius*s i ≤ 1
    · obtain ⟨F,hF,hFt⟩ := exists_own_state_exterior_number (Nat.cast_nonneg (Z i)) (hs i) hh.1 hh.2 (hr i)
        (by simpa only [price_scale_inverse (hs i)] using hN i) (K i) (p₀ i) (hp₀ i)
      exact ⟨F,by simpa only [price_scale_inverse (hs i)] using hF,fun _ _ => hFt⟩
    · obtain ⟨F,hF⟩ := exists_actual_own_probability_tail_tilt_state (Nat.cast_nonneg (Z i)) (hr i)
        (hN i) (K i) (p₀ i) (hp₀ i) zero_lt_one
      exact ⟨F,hF,fun hs1 hRs => (hh ⟨hs1,hRs⟩).elim⟩
  choose F hF hFt using hstate
  have hbar' := hbar Z s N K hZ hs hs0 hscale hN F hF
  have hQB : 1 ≤ 2*l^2 := by nlinarith [sq_nonneg (l-1)]
  have htol : 0 < l⁻¹^8 := pow_pos (inv_pos.mpr hlp) _
  obtain ⟨A,hA,hgood⟩ := exists_actual_annular_TF_cap_constant hQB hc hcL htol
  have hgood' := hgood (r₀ := r) (s := s) (Z := fun i => (Z i:ℝ))
    (lam := fun i => (s i)^(-4:ℝ)) (N := N) (K := K) (F := F)
    zero_le_one hs0 (Eventually.of_forall hr)
    (Eventually.of_forall (fun i => ⟨Nat.cast_nonneg (Z i),Real.rpow_pos_of_pos (hs i) _,hF i⟩))
  have hrt := fixed_target_nuclear_radius_eventually hZp hs hscale hε hlp
  have hbud := selection_budget_eventually hs hs0 D A hA.le
  have hsmall := hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hRs : ∀ᶠ i in f, actualScreenRadius*s i < 1 := by
    have hh : Tendsto (fun i => actualScreenRadius*s i) f (𝓝 0) := by
      simpa only [mul_zero] using hs0.const_mul actualScreenRadius
    exact hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hbar',hgood',hrt,hbud,hsmall,hRs] with i hbi hgi hri hbudi hsi hRsi
  have hrad := selectedDyadicIndex_radius (hr i) (hs i) hl hri
  let j : Fin (K i) := ⟨J i,Nat.lt_succ_self _⟩
  obtain ⟨a,p,hbp⟩ := hbi (J i) (Nat.le_succ _) hrad.2.1
  obtain ⟨G,hG,hprob,hcomp⟩ := hgi j hrad.2.1
  have hGm : MeasurableSet G := (observationInformation_le _ _) _ hG
  have hrs : r i ≤ s i := hri.trans (div_le_self (hs i).le hl)
  apply selected_data_of_events (hs i) hsi.le (hr i) hrs hc hc1 hl
    (selectedTailThreshold_pos (hs i)) (F i) (hF i).1 (J i)
    hrad.1 hrad.2.2.1 hrad.2.2.2.1 hrad.2.2.2.2 (hFt i hsi.le hRsi.le)
    (hbp.mono_cap (le_max_left C 0)) hGm
  · intro q hq y hyl hyh
    simpa only [price_scale_inverse (hs i)] using hcomp q hq y hyl hyh
  · exact lt_of_le_of_lt (add_le_add le_rfl hprob) (hbudi _ hrad.1.le hrad.2.1)

end
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis

lemma uniform_bound_of_eventual {α : Type*} {f : ℕ → α → ℝ} {K : Set α}
    (hf : ∀ n, ∃ M ≥ 0, ∀ x ∈ K, f n x ≤ M)
    (he : ∃ M ≥ 0, ∀ᶠ n in atTop, ∀ x ∈ K, f n x ≤ M) :
    ∃ M ≥ 0, ∀ n x, x ∈ K → f n x ≤ M := by
  classical
  choose b hb hfb using hf
  obtain ⟨M,hM,he⟩ := he
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp he
  refine ⟨M+∑ n ∈ Finset.range n₀, b n,add_nonneg hM (Finset.sum_nonneg (fun n _ => hb n)),?_⟩
  intro n x hx
  by_cases hn : n₀ ≤ n
  · exact (hn₀ n hn x hx).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => hb n)))
  · have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range n₀) => hb i)
      (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact (hfb n x hx).trans (hh.trans (le_add_of_nonneg_left hM))

lemma SelectedQuantumData.scaled_bounded {Z s l τ B C R : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hs : 0 < s) :
    ∃ M ≥ 0, ∀ x, tfDilation s d.density x ≤ M := by
  obtain ⟨M,hM,hMb⟩ := d.bounded_density
  exact ⟨s^6*M,mul_nonneg (pow_nonneg hs.le 6) hM,
    fun x => mul_le_mul_of_nonneg_left (hMb _) (pow_nonneg hs.le 6)⟩

lemma SelectedQuantumData.scaled_TF_bound {Z s l τ B C R a : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hl : 1 ≤ l) (ha : 0 < a)
    {x : TFSpace} (hxa : a ≤ ‖x‖) (hxl : d.radius/s ≤ ‖x‖) (hxh : ‖x‖ ≤ l) :
    tfDilation s d.density x ≤
      tfDensityCoefficient*(actualInverseCap/a^4)^(3/2:ℝ)+1/a^6 := by
  have hC : 0 ≤ actualInverseCap := by
    have := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  have hcap := d.cap x hxl hxh
  have hdiv : actualInverseCap/‖x‖^4 ≤ actualInverseCap/a^4 := by gcongr
  have hmax : max (nuclearField (s^3*Z) x-tfPotential (tfDilation s d.density) x-1) 0 ≤ actualInverseCap/a^4 :=
    max_le (by linarith) (by positivity)
  have hpow : l⁻¹^8 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (zero_lt_one.trans_le hl).le)
    ((inv_le_one₀ (zero_lt_one.trans_le hl)).mpr hl)
  have herr : l⁻¹^8/‖x‖^6 ≤ 1/a^6 := by gcongr
  have hreact : tfDensityCoefficient*(max (nuclearField (s^3*Z) x-
      tfPotential (tfDilation s d.density) x-1) 0)^(3/2:ℝ) ≤
      tfDensityCoefficient*(actualInverseCap/a^4)^(3/2:ℝ) := by
    apply mul_le_mul_of_nonneg_left _ tfDensityCoefficient_pos.le
    exact Real.rpow_le_rpow (le_max_right _ _) hmax (by norm_num)
  have ht := (abs_le.mp (d.TF x hxl hxh)).2
  linarith

lemma selected_data_local_bounds {Z s l τ : ℕ → ℝ} {N : ℕ → ℕ} {B C R : ℝ}
    (d : ∀ n, SelectedQuantumData (Z n) (N n) (s n) (l n) (τ n) B C R)
    (hZ : ∀ n, 0 ≤ Z n) (hs : ∀ n, 0 < s n) (hl : ∀ n, 1 ≤ l n)
    (hl0 : Tendsto l atTop atTop) :
    (∀ K : Set TFSpace, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M ≥ 0, ∀ n x, x ∈ K → nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M) ∧
    (∀ K : Set TFSpace, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M ≥ 0, ∀ n x, x ∈ K → tfDilation (s n) (d n).density x ≤ M) := by
  have hC : 0 ≤ actualInverseCap := by
    have := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  have local_bounds (K : Set TFSpace) (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
      (∃ M ≥ 0, ∀ n x, x ∈ K → nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M) ∧
      (∃ M ≥ 0, ∀ n x, x ∈ K → tfDilation (s n) (d n).density x ≤ M) := by
    obtain ⟨a,b,ha,hb,hann⟩ := compact_away_zero_annulus hK hK0
    have hinv : Tendsto (fun n => (l n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hl0
    have he : ∀ᶠ n in atTop, ∀ x ∈ K, (d n).radius/s n ≤ ‖x‖ ∧ ‖x‖ ≤ l n := by
      filter_upwards [hinv.eventually (gt_mem_nhds ha),hl0.eventually_ge_atTop b] with n hna hnb x hx
      exact ⟨((d n).radius_upper.trans hna.le).trans (hann hx).1,(hann hx).2.trans hnb⟩
    have hf (n) : ∃ M ≥ 0, ∀ x ∈ K, nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M := by
      refine ⟨((s n)^3*Z n)/a,div_nonneg (mul_nonneg (pow_nonneg (hs n).le 3) (hZ n)) ha.le,?_⟩
      intro x hx
      have hp : 0 ≤ tfPotential (tfDilation (s n) (d n).density) x :=
        tfPotential_nonneg (Eventually.of_forall (tfDilation_nonneg (d n).nonneg_density)) x
      have hn : ((s n)^3*Z n)/‖x‖ ≤ ((s n)^3*Z n)/a := by
        apply div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (hs n).le 3) (hZ n)) ha (hann hx).1
      unfold nuclearField
      linarith
    have hfe : ∃ M ≥ 0, ∀ᶠ n in atTop, ∀ x ∈ K, nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M := by
      refine ⟨1+actualInverseCap/a^4,by positivity,?_⟩
      filter_upwards [he] with n hn x hx
      have hh := (d n).cap x (hn x hx).1 (hn x hx).2
      have hd : actualInverseCap/‖x‖^4 ≤ actualInverseCap/a^4 := by
        gcongr
        exact (hann hx).1
      linarith
    have hρf (n) : ∃ M ≥ 0, ∀ x ∈ K, tfDilation (s n) (d n).density x ≤ M := by
      obtain ⟨M,hM,hMb⟩ := (d n).scaled_bounded (hs n)
      exact ⟨M,hM,fun x _ => hMb x⟩
    have hρe : ∃ M ≥ 0, ∀ᶠ n in atTop, ∀ x ∈ K, tfDilation (s n) (d n).density x ≤ M := by
      refine ⟨tfDensityCoefficient*(actualInverseCap/a^4)^(3/2:ℝ)+1/a^6,by
        have := tfDensityCoefficient_pos
        positivity,?_⟩
      filter_upwards [he] with n hn x hx
      exact (d n).scaled_TF_bound (hl n) ha (hann hx).1 (hn x hx).1 (hn x hx).2
    exact ⟨uniform_bound_of_eventual hf hfe,uniform_bound_of_eventual hρf hρe⟩
  exact ⟨fun K hK hK0 => (local_bounds K hK hK0).1,fun K hK hK0 => (local_bounds K hK hK0).2⟩

end CoulombBarrier

end

end OAI
