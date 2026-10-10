import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ConductivityMetricRealizationComplete
import OAI.Geometry.SmoothYau.Smoothness.CompactMetricInverseJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma scalar_composition_jet_bound_on {O : Set E} {U : Set ℝ}
    (hO : IsOpen O) (hU : IsOpen U) {x : E} (hx : x ∈ O)
    {f : E → ℝ} {g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f O)
    (hg : ContDiffOn ℝ ∞ g U) (hfx : f x ∈ U) (h : ℕ) {C D : ℝ}
    (hgJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hfJ : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ h (g ∘ f) x‖ ≤ (h.factorial:ℝ)*C*D^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hx hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hU hfx hg
  have hfxe := hfe.self_of_nhds
  have he : g ∘ f =ᶠ[𝓝 x] g' ∘ f' := by
    have hc := hge.comp_tendsto (hf.continuousOn.continuousAt (hO.mem_nhds hx))
    filter_upwards [hc,hfe] with y hy hy'
    change g (f y)=g' (f' y)
    change g (f y)=g' (f y) at hy
    rw [hy,hy']
  rw [(he.iteratedFDeriv ℝ h).self_of_nhds]
  apply norm_iteratedFDeriv_comp_le hg' hf'
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  · intro j hj
    rw [←hfxe,←(hge.iteratedFDeriv ℝ j).self_of_nhds]
    exact hgJ j hj
  · intro j hj hjh
    rw [←(hfe.iteratedFDeriv ℝ j).self_of_nhds]
    exact hfJ j hj hjh

theorem sqrt_near_one_jet_bound (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (O : Set E), IsOpen O → ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f O → (∀ y ∈ O, 0 < f y) →
      ∀ (x : E), x ∈ O → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y-1) x‖ ≤ ε) →
      (1/4 ≤ f x ∧ f x ≤ 9/4) →
      ‖iteratedFDeriv ℝ h (fun y => Real.sqrt (f y)-1) x‖ ≤ C*ε := by
  let H : ℝ → ℝ := fun z => 1/(Real.sqrt z+1)
  have hH : ContDiffOn ℝ ∞ H (Ioi 0) := by
    intro z hz
    exact (contDiffAt_const.div
      ((Real.contDiffAt_sqrt (ne_of_gt hz)).add contDiffAt_const)
      (ne_of_gt (by have := Real.sqrt_nonneg z; linarith))).contDiffWithinAt
  obtain ⟨B,hB,hBJ⟩ := compact_raw_jet_bound isOpen_Ioi
    (isCompact_Icc : IsCompact (Icc (1/4:ℝ) (9/4)))
    (show Icc (1/4:ℝ) (9/4) ⊆ Ioi 0 by intro z hz; change 0 < z; have := hz.1; linarith)
    hH h
  let A := (h.factorial:ℝ)*B*2^h
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A*2^h,by positivity,?_⟩
  intro O hO f hf hfp x hx ε hε hε1 hfJ hfx
  have hfJ' (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ h) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ (2:ℝ)^j := by
    have hfj := hfJ j hjh
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    change ‖iteratedFDeriv ℝ j (f - fun _ => (1:ℝ)) x‖ ≤ ε at hfj
    rw [iteratedFDeriv_sub_apply ((hf.contDiffAt (hO.mem_nhds hx)).of_le hle)
      contDiffAt_const,iteratedFDeriv_const_of_ne (by omega) (1:ℝ),Pi.zero_apply,sub_zero] at hfj
    exact hfj.trans (hε1.trans (one_le_pow₀ (by norm_num)))
  have hHJ (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j (fun y => H (f y)) x‖ ≤ A := by
    have hh := scalar_composition_jet_bound_on hO isOpen_Ioi hx hf hH (hfp x hx) j
      (fun k hk => hBJ k (hk.trans hj) (f x) hfx)
      (fun k hk hkj => hfJ' k hk (hkj.trans hj))
    calc
      _ ≤ (j.factorial:ℝ)*B*2^j := hh
      _ ≤ A := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hB)
          exact_mod_cast Nat.factorial_le hj
        · exact pow_le_pow_right₀ (by norm_num) hj
        · positivity
        · positivity
  have hHf : ContDiffOn ℝ ∞ (fun y => H (f y)) O :=
    hH.comp hf hfp
  have hh := geometric_product_jet_bound_on hO hx (hf.sub contDiffOn_const) hHf h
    hε hA.le (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
    (fun j hj => by simpa using hfJ j hj) (fun j hj => by simpa using hHJ j hj)
  have he : (fun y => Real.sqrt (f y)-1) =ᶠ[𝓝 x]
      (fun y => (f y-1)*H (f y)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    dsimp [H]
    have hs := Real.sq_sqrt (hfp y hy).le
    have hd : Real.sqrt (f y)+1 ≠ 0 := ne_of_gt (by have := Real.sqrt_nonneg (f y); linarith)
    field_simp
    nlinarith
  rw [(he.iteratedFDeriv ℝ h).self_of_nhds]
  convert hh using 1
  ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma near_one_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {d q : E → ℝ} (hd : ContDiffOn ℝ ∞ d O) (hq : ContDiffOn ℝ ∞ q O)
    (h : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d y-1) x‖ ≤ ε)
    (hqJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q y-1) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ h (fun y => d y*q y-1) x‖ ≤ (2^h+2)*ε := by
  have hle : (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h))
  have hd' := (hd.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)
  have hq' := (hq.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)
  have hp := geometric_product_jet_bound_on hO hx (hd.sub (contDiffOn_const (c:=(1:ℝ))))
    (hq.sub (contDiffOn_const (c:=(1:ℝ)))) h hε hε (show (0:ℝ) ≤ 1 by norm_num)
    (show (0:ℝ) ≤ 1 by norm_num) (by simpa using hdJ) (by simpa using hqJ)
  have he : (fun y => d y*q y-1) =
      (fun y => (d y-1)*(q y-1)+(d y-1)+(q y-1)) := by funext y; ring
  rw [he,fun_iteratedFDeriv_add_apply ((hd'.mul hq').add hd' |>.of_le hle) (hq'.of_le hle),
    fun_iteratedFDeriv_add_apply ((hd'.mul hq').of_le hle) (hd'.of_le hle)]
  have hb := norm_add_le
    (iteratedFDeriv ℝ h (fun y => (d y-1)*(q y-1)) x + iteratedFDeriv ℝ h (fun y => d y-1) x)
    (iteratedFDeriv ℝ h (fun y => q y-1) x)
  have hb' := norm_add_le (iteratedFDeriv ℝ h (fun y => (d y-1)*(q y-1)) x)
    (iteratedFDeriv ℝ h (fun y => d y-1) x)
  have hsq : ε*ε ≤ ε := by nlinarith
  have hp' : ‖iteratedFDeriv ℝ h (fun y => (d y-1)*(q y-1)) x‖ ≤ ε*2^h :=
    hp.trans (by norm_num only [one_add_one_eq_two]; exact mul_le_mul_of_nonneg_right hsq (by positivity))
  have := hdJ h le_rfl
  have := hqJ h le_rfl
  linarith

theorem conductivity_response_jet_bound (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (O : Set E), IsOpen O → ∀ (d q : E → ℝ),
      ContDiffOn ℝ ∞ d O → ContDiffOn ℝ ∞ q O →
      (∀ y ∈ O, 0 < d y) → (∀ y ∈ O, 0 < q y) →
      ∀ (x : E), x ∈ O → ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d y-1) x‖ ≤ ε) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q y-1) x‖ ≤ ε) →
      ‖iteratedFDeriv ℝ h (fun y => Real.sqrt (d y*q y)-1) x‖ ≤ C*ε ∧
      ‖iteratedFDeriv ℝ h (fun y => d y/q y-1) x‖ ≤ C*ε := by
  let F : ℝ := 2^h+2
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨A,hA,hAJ⟩ := sqrt_near_one_jet_bound (E:=E) h
  let B := 2*(h.factorial:ℝ)^2/(1/2)*(1+max 1 (1/(1/2)))^h
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨min (1/2) (1/F),max (A*F) B,lt_min (by norm_num) (by positivity),
    (mul_pos hA hF).trans_le (le_max_left _ _),?_⟩
  intro O hO d q hd hq hdp hqp x hx ε hε hεδ hdJ hqJ
  have hεhalf : ε ≤ 1/2 := hεδ.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := by linarith
  have hFe : F*ε ≤ 1 := by
    have hh := hεδ.trans (min_le_right _ _)
    have hh' := (le_div_iff₀ hF).mp hh
    nlinarith
  have hd0 := hdJ 0 (Nat.zero_le h)
  have hq0 := hqJ 0 (Nat.zero_le h)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hd0 hq0
  obtain ⟨hdl,hdu⟩ := abs_le.mp hd0
  obtain ⟨hql,hqu⟩ := abs_le.mp hq0
  have hdlo : 1/2 ≤ d x := by linarith
  have hqlo : 1/2 ≤ q x := by linarith
  have hdhi : d x ≤ 3/2 := by linarith
  have hqhi : q x ≤ 3/2 := by linarith
  constructor
  · have hpJ (j : ℕ) (hj : j ≤ h) :
        ‖iteratedFDeriv ℝ j (fun y => d y*q y-1) x‖ ≤ F*ε := by
      have hp := near_one_product_jet_bound_on hO hx hd hq j hε hε1
        (fun k hk => hdJ k (hk.trans hj)) (fun k hk => hqJ k (hk.trans hj))
      apply hp.trans
      apply mul_le_mul_of_nonneg_right _ hε
      dsimp [F]
      exact add_le_add (show (2:ℝ)^j ≤ 2^h from pow_le_pow_right₀ (by norm_num) hj) le_rfl
    have hb := hAJ O hO (fun y => d y*q y) (hd.mul hq)
      (fun y hy => mul_pos (hdp y hy) (hqp y hy)) x hx (F*ε) (by positivity) hFe hpJ
      ⟨by nlinarith [mul_le_mul hdlo hqlo (by norm_num : (0:ℝ) ≤ 1/2) (hdp x hx).le],
       by nlinarith [mul_le_mul hdhi hqhi (hqp x hx).le (by norm_num : (0:ℝ) ≤ 3/2)]⟩
    exact hb.trans (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hε)
  · have hnumJ (j : ℕ) (hj : j ≤ h) :
        ‖iteratedFDeriv ℝ j (fun y => d y-q y) x‖ ≤ 2*ε := by
      have ht : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
      have he : (fun y => d y-q y)=(fun y => (d y-1)-(q y-1)) := by funext y; ring
      rw [he,fun_iteratedFDeriv_sub_apply
        (((hd.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)).of_le ht)
        (((hq.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)).of_le ht)]
      exact (norm_sub_le _ _).trans (by linarith [hdJ j hj,hqJ j hj])
    have hqJ' (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ h) :
        ‖iteratedFDeriv ℝ j q x‖ ≤ 1 := by
      have hh := hqJ j hjh
      have ht : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
      change ‖iteratedFDeriv ℝ j (q - fun _ => (1:ℝ)) x‖ ≤ ε at hh
      rw [iteratedFDeriv_sub_apply ((hq.contDiffAt (hO.mem_nhds hx)).of_le ht)
        contDiffAt_const,iteratedFDeriv_const_of_ne (by omega) (1:ℝ),Pi.zero_apply,sub_zero] at hh
      exact hh.trans hε1
    have hb := weighted_quotient_jet_bound_on hO hx (hd.sub hq) hq h (δ:=1/2) (W:=1)
      (M:=1) (N:=2*ε) (R:=1) (S:=1) (by norm_num) zero_lt_one (by positivity)
      (by norm_num) (by norm_num) (by simpa using hqlo)
      (by simpa using hnumJ) (by simpa using hqJ')
    have he : (fun y => d y/q y-1) =ᶠ[𝓝 x] (fun y => (d y-q y)/q y) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      field_simp [(hqp y hy).ne']
    rw [(he.iteratedFDeriv ℝ h).self_of_nhds]
    apply hb.trans
    change 2*ε*(h.factorial:ℝ)^2/(1/2)*(1+max 1 (1/(1/2))*1)^h ≤ _
    calc
      _ = B*ε := by dsimp [B]; ring
      _ ≤ max (A*F) B*ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem conductivity_response_all_jets (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (O : Set E), IsOpen O → ∀ (d q : E → ℝ),
      ContDiffOn ℝ ∞ d O → ContDiffOn ℝ ∞ q O →
      (∀ y ∈ O, 0 < d y) → (∀ y ∈ O, 0 < q y) →
      ∀ (x : E), x ∈ O → ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d y-1) x‖ ≤ ε) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q y-1) x‖ ≤ ε) →
      ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => Real.sqrt (d y*q y)-1) x‖ ≤ C*ε ∧
      ‖iteratedFDeriv ℝ j (fun y => d y/q y-1) x‖ ≤ C*ε := by
  induction h with
  | zero =>
    obtain ⟨δ,C,hδ,hC,hb⟩ := conductivity_response_jet_bound (E:=E) 0
    refine ⟨δ,C,hδ,hC,?_⟩
    intro O hO d q hd hq hdp hqp x hx ε hε hδε hdJ hqJ j hj
    have he : j=0 := by omega
    subst j
    exact hb O hO d q hd hq hdp hqp x hx ε hε hδε hdJ hqJ
  | succ h ih =>
    obtain ⟨δ,C,hδ,hC,hprev⟩ := ih
    obtain ⟨δ',C',hδ',hC',hnew⟩ := conductivity_response_jet_bound (E:=E) (h+1)
    refine ⟨min δ δ',max C C',lt_min hδ hδ',hC.trans_le (le_max_left _ _),?_⟩
    intro O hO d q hd hq hdp hqp x hx ε hε hδε hdJ hqJ j hj
    by_cases hjh : j ≤ h
    · obtain ⟨ha,hc⟩ := hprev O hO d q hd hq hdp hqp x hx ε hε
        (hδε.trans (min_le_left _ _)) (fun k hk => hdJ k (by omega))
        (fun k hk => hqJ k (by omega)) j hjh
      exact ⟨ha.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε),
        hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε)⟩
    · have he : j=h+1 := by omega
      subst j
      obtain ⟨ha,hc⟩ := hnew O hO d q hd hq hdp hqp x hx ε hε
        (hδε.trans (min_le_right _ _)) hdJ hqJ
      exact ⟨ha.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε),
        hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)⟩

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma conductivity_tensor_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    (a c G : E → ℝ) (Gi P : ι → E → ℝ)
    (ha : ContDiffOn ℝ ∞ a O) (hc : ContDiffOn ℝ ∞ c O)
    (hG : ContDiffOn ℝ ∞ G O) (hGi : ∀ i, ContDiffOn ℝ ∞ (Gi i) O)
    (hP : ∀ i, ContDiffOn ℝ ∞ (P i) O)
    (h : ℕ) {ε A C n : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) (hC : 0 ≤ C) (hn : 1 ≤ n)
    (haJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j a x‖ ≤ ε)
    (hcJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j c x‖ ≤ ε)
    (hGJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j G x‖ ≤ A)
    (hGiJ : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (Gi i) x‖ ≤ A)
    (hPJ : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (P i) x‖ ≤ C*n^j) :
    ‖iteratedFDeriv ℝ h (fun y => a y*G y+(c y-a y)*∑ i, Gi i y*P i y) x‖ ≤
      A*(2^h+2*(Fintype.card ι:ℝ)*C*4^h)*ε*n^h := by
  have hn0 := zero_le_one.trans hn
  let Q := fun y => ∑ i, Gi i y*P i y
  have hQ : ContDiffOn ℝ ∞ Q O := ContDiffOn.sum (fun i _ => (hGi i).mul (hP i))
  have hQJ (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j Q x‖ ≤ ((Fintype.card ι:ℝ)*A*C*2^h)*n^j := by
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    have hi (i : ι) : ‖iteratedFDeriv ℝ j (fun y => Gi i y*P i y) x‖ ≤ A*C*2^h*n^j := by
      have hb := geometric_product_jet_bound_on hO hx (hGi i) (hP i) j hA hC
        (show (0:ℝ) ≤ 1 by norm_num) hn0
        (fun k hk => by simpa using hGiJ i k (hk.trans hj))
        (fun k hk => hPJ i k (hk.trans hj))
      calc
        _ ≤ A*C*(1+n)^j := hb
        _ ≤ A*C*(2*n)^j := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (show (0:ℝ) ≤ 1+n by positivity) (show (1:ℝ)+n ≤ 2*n by linarith) j) (mul_nonneg hA hC)
        _ = A*C*2^j*n^j := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj)
            (mul_nonneg hA hC)) (pow_nonneg hn0 _)
    dsimp only [Q]
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (((hGi i).mul (hP i)).contDiffAt (hO.mem_nhds hx)).of_le hle)]
    calc
      _ ≤ ∑ i : ι, ‖iteratedFDeriv ℝ j (fun y => Gi i y*P i y) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, A*C*2^h*n^j := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hcaJ (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j (fun y => c y-a y) x‖ ≤ 2*ε := by
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    rw [fun_iteratedFDeriv_sub_apply ((hc.contDiffAt (hO.mem_nhds hx)).of_le hle)
      ((ha.contDiffAt (hO.mem_nhds hx)).of_le hle)]
    exact (norm_sub_le _ _).trans (by linarith [hcJ j hj,haJ j hj])
  have hfirst := geometric_product_jet_bound_on hO hx ha hG h hε hA
    (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
    (by simpa using haJ) (by simpa using hGJ)
  have hsecond := geometric_product_jet_bound_on hO hx (hc.sub ha) hQ h
    (show 0 ≤ 2*ε by positivity) (show 0 ≤ (Fintype.card ι:ℝ)*A*C*2^h by positivity)
    (show (0:ℝ) ≤ 1 by norm_num) hn0 (by simpa using hcaJ) hQJ
  have hpow : (1+n)^h ≤ 2^h*n^h := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (show (0:ℝ) ≤ 1+n by positivity) (show (1:ℝ)+n ≤ 2*n by linarith) h
  have hp : (1:ℝ) ≤ n^h := one_le_pow₀ hn
  have hf' : ‖iteratedFDeriv ℝ h (fun y => a y*G y) x‖ ≤ ε*A*2^h*n^h :=
    hfirst.trans (by norm_num only [one_add_one_eq_two]; exact le_mul_of_one_le_right (by positivity) hp)
  have hs' : ‖iteratedFDeriv ℝ h (fun y => (c y-a y)*Q y) x‖ ≤
      2*ε*((Fintype.card ι:ℝ)*A*C*2^h)*(2^h*n^h) := hsecond.trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hle : (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h))
  change ‖iteratedFDeriv ℝ h (fun y => a y*G y+(c y-a y)*Q y) x‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply (((ha.mul hG).contDiffAt (hO.mem_nhds hx)).of_le hle)
    ((((hc.sub ha).mul hQ).contDiffAt (hO.mem_nhds hx)).of_le hle)]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ε*A*2^h*n^h+2*ε*((Fintype.card ι:ℝ)*A*C*2^h)*(2^h*n^h) := add_le_add hf' hs'
    _ = _ := by rw [show (4:ℝ)^h=2^h*2^h by rw [←mul_pow]; norm_num]; ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem conductivity_metric_realization_jets (hn : Module.finrank ℝ E=3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (h : ℕ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ (d q : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q →
      (∀ x, 0 < d x) → (∀ x, 0 < q x) →
      tsupport (fun x => d x-q x^3) ⊆ {x | coordinateGradientPair g u u x ≠ 0} →
      ∃ ĝ : SmoothMetric E M,
        (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
        (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) ∧
        ∀ (p : M) (O : Set E), IsOpen O → O ⊆ (chartAt E p).target →
        (∀ y ∈ O, coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0) →
        ∀ (x : E), x ∈ O → ∀ ε A C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ A → 0 ≤ C → 1 ≤ n →
        (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d ((chartAt E p).symm y)-1) x‖ ≤ ε) →
        (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q ((chartAt E p).symm y)-1) x‖ ≤ ε) →
        (∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (fun y => metricCoefficients g p y i j) x‖ ≤ A) →
        (∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g u p i j) x‖ ≤ C*n^k) →
        ∀ i j : CoordIndex E,
        ‖iteratedFDeriv ℝ h (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) x‖ ≤
          L*A*(2^h+2*(Fintype.card (CoordIndex E):ℝ)*C*4^h)*ε*n^h := by
  obtain ⟨δ,L,hδ,hL,hR⟩ := conductivity_response_all_jets (E:=E) h
  refine ⟨δ,L,hδ,hL,?_⟩
  intro d q hd hq hd0 hq0 hsupp
  obtain ⟨ĝ,hΔ,hout,hformula⟩ := conductivity_metric_realization_projection hn g u hu d q hd hq hd0 hq0 hsupp
  refine ⟨ĝ,hΔ,hout,?_⟩
  intro p O hO hOT hF x hx ε A C n hε hεδ hA hC hn1 hdJ hqJ hGJ hPJ i j
  let d' := d ∘ (chartAt E p).symm
  let q' := q ∘ (chartAt E p).symm
  have hd' : ContDiffOn ℝ ∞ d' O := fun y hy => (contDiffAt_inChart hd p (hOT hy)).contDiffWithinAt
  have hq' : ContDiffOn ℝ ∞ q' O := fun y hy => (contDiffAt_inChart hq p (hOT hy)).contDiffWithinAt
  let a := fun y => Real.sqrt (d' y*q' y)-1
  let c := fun y => d' y/q' y-1
  have ha : ContDiffOn ℝ ∞ a O := by
    intro y hy
    exact (((Real.contDiffAt_sqrt (mul_pos (hd0 _) (hq0 _)).ne').comp y
      ((hd'.contDiffAt (hO.mem_nhds hy)).mul (hq'.contDiffAt (hO.mem_nhds hy)))).sub
        contDiffAt_const).contDiffWithinAt
  have hc : ContDiffOn ℝ ∞ c O := (hd'.div hq' (fun y _ => (hq0 _).ne')).sub contDiffOn_const
  have hresponse := hR O hO d' q' hd' hq' (fun y _ => hd0 _) (fun y _ => hq0 _) x hx ε hε hεδ hdJ hqJ
  have hbound := conductivity_tensor_jet_bound_on hO hx a c
    (fun y => metricCoefficients g p y i j)
    (fun k y => metricCoefficients g p y i k) (fun k => chartGradientProjection g u p k j)
    ha hc ((contDiffOn_metricCoefficient g p i j).mono hOT)
    (fun k => (contDiffOn_metricCoefficient g p i k).mono hOT)
    (fun k => chartGradientProjection_smooth_on g hu p hO hOT hF k j) h
    (mul_nonneg hL.le hε) hA hC hn1 (fun k hk => (hresponse k hk).1)
    (fun k hk => (hresponse k hk).2) (hGJ i j) (fun k => hGJ i k) (fun k => hPJ k j)
  have he : (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) =ᶠ[𝓝 x]
      (fun y => a y*metricCoefficients g p y i j+(c y-a y)*∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [hformula p y (hOT hy) (hF y hy) i j]
    dsimp [a,c,d',q']
    ring
  rw [(he.iteratedFDeriv ℝ h).self_of_nhds]
  convert hbound using 1
  ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem conductivity_metric_realization_uniform_all_jets (hn : Module.finrank ℝ E=3) (h : ℕ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ (g : SmoothMetric E M) (u : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u → ∀ (d q : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q →
      (∀ x, 0 < d x) → (∀ x, 0 < q x) →
      tsupport (fun x => d x-q x^3) ⊆ {x | coordinateGradientPair g u u x ≠ 0} →
      ∃ ĝ : SmoothMetric E M,
        (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
        (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) ∧
        ∀ (p : M) (x : E), x ∈ (chartAt E p).target → ∀ ε A C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ A → 0 ≤ C → 1 ≤ n →
        (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d ((chartAt E p).symm y)-1) x‖ ≤ ε) →
        (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q ((chartAt E p).symm y)-1) x‖ ≤ ε) →
        (∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (fun y => metricCoefficients g p y i j) x‖ ≤ A) →
        (((chartAt E p).symm x) ∈ tsupport (fun z => d z-q z^3) →
        ∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g u p i j) x‖ ≤ C*n^k) →
        ∀ r ≤ h, ∀ i j : CoordIndex E,
        ‖iteratedFDeriv ℝ r (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) x‖ ≤
          L*A*(2^r+2*(Fintype.card (CoordIndex E):ℝ)*C*4^r)*ε*n^r := by
  obtain ⟨δ,L,hδ,hL,hR⟩ := conductivity_response_all_jets (E:=E) h
  refine ⟨δ,L,hδ,hL,?_⟩
  intro g u hu d q hd hq hd0 hq0 hsupp
  obtain ⟨ĝ,hΔ,hout,hcompat,hformula⟩ := conductivity_metric_realization_complete hn g u hu d q hd hq hd0 hq0 hsupp
  refine ⟨ĝ,hΔ,hout,?_⟩
  intro p x hx ε A C n hε hεδ hA hC hn1 hdJ hqJ hGJ hPJ r hr i j
  let d' := d ∘ (chartAt E p).symm
  let q' := q ∘ (chartAt E p).symm
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hd' : ContDiffOn ℝ ∞ d' O := fun y hy => (contDiffAt_inChart hd p hy).contDiffWithinAt
  have hq' : ContDiffOn ℝ ∞ q' O := fun y hy => (contDiffAt_inChart hq p hy).contDiffWithinAt
  let a := fun y => Real.sqrt (d' y*q' y)-1
  let c := fun y => d' y/q' y-1
  have ha : ContDiffOn ℝ ∞ a O := by
    intro y hy
    exact (((Real.contDiffAt_sqrt (mul_pos (hd0 _) (hq0 _)).ne').comp y
      ((hd'.contDiffAt (hO.mem_nhds hy)).mul (hq'.contDiffAt (hO.mem_nhds hy)))).sub
        contDiffAt_const).contDiffWithinAt
  have hc : ContDiffOn ℝ ∞ c O := (hd'.div hq' (fun y _ => (hq0 _).ne')).sub contDiffOn_const
  have hresponse := hR O hO d' q' hd' hq' (fun y _ => hd0 _) (fun y _ => hq0 _) x hx ε hε hεδ hdJ hqJ
  by_cases hs : (chartAt E p).symm x ∈ tsupport (fun z => d z-q z^3)
  · have hne := hsupp hs
    have hFn := (contDiffAt_inChart (contMDiff_coordinateGradientPair hu hu g) p hx).continuousAt.eventually_ne hne
    obtain ⟨V,hVO,hV,hxV⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds hx) hFn)
    have hVT : V ⊆ (chartAt E p).target := fun y hy => (hVO hy).1
    have hVF : ∀ y ∈ V, coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0 := fun y hy => (hVO hy).2
    have hbound := conductivity_tensor_jet_bound_on hV hxV a c
      (fun y => metricCoefficients g p y i j)
      (fun k y => metricCoefficients g p y i k) (fun k => chartGradientProjection g u p k j)
      (ha.mono hVT) (hc.mono hVT) ((contDiffOn_metricCoefficient g p i j).mono hVT)
      (fun k => (contDiffOn_metricCoefficient g p i k).mono hVT)
      (fun k => chartGradientProjection_smooth_on g hu p hV hVT hVF k j) r
      (mul_nonneg hL.le hε) hA hC hn1 (fun k hk => (hresponse k (hk.trans hr)).1)
      (fun k hk => (hresponse k (hk.trans hr)).2) (fun k hk => hGJ i j k (hk.trans hr)) (fun l k hk => hGJ i l k (hk.trans hr)) (fun l k hk => hPJ hs l j k (hk.trans hr))
    have he : (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) =ᶠ[𝓝 x]
        (fun y => a y*metricCoefficients g p y i j+(c y-a y)*∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y) := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      rw [hformula p y (hVT hy) (hVF y hy) i j]
      dsimp [a,c,d',q']
      ring
    rw [(he.iteratedFDeriv ℝ r).self_of_nhds]
    convert hbound using 1
    ring
  · have he0 := ((chartAt E p).continuousAt_symm hx).tendsto.eventually
      (notMem_tsupport_iff_eventuallyEq.mp hs)
    have he : (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) =ᶠ[𝓝 x]
        (fun y => a y*metricCoefficients g p y i j) := by
      filter_upwards [he0] with y hy
      have hdy : d ((chartAt E p).symm y)=q ((chartAt E p).symm y)^3 := sub_eq_zero.mp hy
      have hm := hcompat ((chartAt E p).symm y) hdy (coordinateVector p y i) (coordinateVector p y j)
      change metricCoefficients ĝ p y i j=q ((chartAt E p).symm y)^2*metricCoefficients g p y i j at hm
      rw [hm]
      dsimp [a,d',q']
      rw [hdy,show q ((chartAt E p).symm y)^3*q ((chartAt E p).symm y)=
          (q ((chartAt E p).symm y)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
      ring
    have hb := geometric_product_jet_bound_on hO hx ha (contDiffOn_metricCoefficient g p i j) r
      (mul_nonneg hL.le hε) hA (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
      (by simpa using (fun k hk => (hresponse k (hk.trans hr)).1)) (by simpa using (fun k hk => hGJ i j k (hk.trans hr)))
    rw [(he.iteratedFDeriv ℝ r).self_of_nhds]
    apply hb.trans
    norm_num only [one_add_one_eq_two]
    calc
      L*ε*A*2^r = L*A*2^r*ε := by ring
      _ ≤ L*A*(2^r+2*(Fintype.card (CoordIndex E):ℝ)*C*4^r)*ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by positivity)) (mul_nonneg hL.le hA)) hε
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn1)

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma compact_metric_all_jets (g : SmoothMetric E M) (t : CoordinateTest E M) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x ∈ t.compactSet, ∀ i j : CoordIndex E, ∀ k ≤ h,
      ‖iteratedFDeriv ℝ k (fun y => metricCoefficients g t.center y i j) x‖ ≤ A := by
  classical
  have hb (i j : CoordIndex E) := compact_raw_jet_bound (chartAt E t.center).open_target
    t.isCompact t.inTarget (contDiffOn_metricCoefficient g t.center i j) h
  choose B hB using hb
  let A := 1+∑ i : CoordIndex E, ∑ j : CoordIndex E, B i j
  have hB0 (i j : CoordIndex E) : 0 ≤ B i j := zero_le_one.trans (hB i j).1
  refine ⟨A,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)))
  · intro x hx i j k hk
    calc
      _ ≤ B i j := (hB i j).2 k hk x hx
      _ ≤ ∑ j : CoordIndex E, B i j := Finset.single_le_sum (fun l _ => hB0 i l) (Finset.mem_univ _)
      _ ≤ ∑ i : CoordIndex E, ∑ j : CoordIndex E, B i j := Finset.single_le_sum
        (fun l _ => Finset.sum_nonneg (fun j _ => hB0 l j)) (Finset.mem_univ _)
      _ ≤ A := by dsimp [A]; linarith

theorem conductivity_metric_in_smooth_neighborhood (hn : Module.finrank ℝ E=3)
    (g : SmoothMetric E M) (N : Set (SmoothMetric E M)) (hN : IsSmoothNeighborhood g N) :
    ∃ tests : List (CoordinateTest E M), ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧
    ∀ (u d q : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q → (∀ x, 0 < d x) → (∀ x, 0 < q x) →
      tsupport (fun x => d x-q x^3) ⊆ {x | coordinateGradientPair g u u x ≠ 0} →
      ∀ ε C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ C → 1 ≤ n → ε*(1+C)*n^h < δ →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => d ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => q ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet,
        ((chartAt E t.center).symm x) ∈ tsupport (fun z => d z-q z^3) →
        ∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g u t.center i j) x‖ ≤ C*n^k) →
      ∃ ĝ ∈ N,
        (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
        (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) := by
  classical
  obtain ⟨tests,τ,hτ,hN⟩ := hN
  let h := tests.toFinset.sup (fun t => t.order)
  obtain ⟨δ,L,hδ,hL,hR⟩ := conductivity_metric_realization_uniform_all_jets (M:=M) hn h
  choose B hB using fun t : CoordinateTest E M => compact_metric_all_jets g t h
  let A := 1+∑ t ∈ tests.toFinset, B t
  have hB0 (t : CoordinateTest E M) : 0 ≤ B t := zero_le_one.trans (hB t).1
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (fun t _ => hB0 t))
  have hBA (t : CoordinateTest E M) (ht : t ∈ tests) : B t ≤ A := by
    have hb := Finset.single_le_sum (fun t (_ : t ∈ tests.toFinset) => hB0 t)
      (List.mem_toFinset.mpr ht)
    dsimp [A]
    linarith
  let K := L*A*(2^h+2*(Fintype.card (CoordIndex E):ℝ)*4^h)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨tests,h,min δ (τ/K),lt_min hδ (div_pos hτ hK),?_⟩
  intro u d q hu hd hq hd0 hq0 hsupp ε C n hε hεδ hC hn1 hsmall hdJ hqJ hPJ
  obtain ⟨ĝ,hΔ,hout,hjets⟩ := hR g u hu d q hd hq hd0 hq0 hsupp
  refine ⟨ĝ,hN ĝ ?_,hΔ,hout⟩
  intro t ht x hx
  have hr : t.order ≤ h := Finset.le_sup (f:=fun t : CoordinateTest E M => t.order)
    (List.mem_toFinset.mpr ht)
  have hb := hjets t.center x (t.inTarget hx) ε A C n hε (hεδ.trans (min_le_left _ _))
    (zero_le_one.trans hA) hC hn1 (hdJ t ht x hx) (hqJ t ht x hx)
    (fun i j k hk => ((hB t).2 x hx i j k hk).trans (hBA t ht))
    (hPJ t ht x hx) t.order hr t.row t.column
  have hpow2 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr
  have hpow4 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hr
  have hcoeff : (2:ℝ)^t.order+2*(Fintype.card (CoordIndex E):ℝ)*C*4^t.order ≤
      ((2:ℝ)^h+2*(Fintype.card (CoordIndex E):ℝ)*4^h)*(1+C) := by
    have hm := mul_le_mul_of_nonneg_left hpow4
      (show 0 ≤ 2*(Fintype.card (CoordIndex E):ℝ)*C by positivity)
    have hpos : 0 ≤ (2:ℝ)^h*C+2*(Fintype.card (CoordIndex E):ℝ)*4^h := by positivity
    nlinarith
  have hbound : L*A*(2^t.order+2*(Fintype.card (CoordIndex E):ℝ)*C*4^t.order)*ε*n^t.order ≤
      K*(ε*(1+C)*n^h) := by
    calc
      _ ≤ L*A*(((2:ℝ)^h+2*(Fintype.card (CoordIndex E):ℝ)*4^h)*(1+C))*ε*n^h := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff (by positivity)) hε
        · exact pow_le_pow_right₀ hn1 hr
        · positivity
        · positivity
      _ = _ := by dsimp [K]; ring
  exact (hb.trans hbound).trans_lt ((mul_lt_mul_of_pos_left
    (hsmall.trans_le (min_le_right _ _)) hK).trans_eq (mul_div_cancel₀ τ hK.ne'))


end YauCounterexamples
end

end OAI
