import OAI.Analysis.NumericalRange.Model

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
section

def poissonExtension (f : ℂ → ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun t => poissonKernel 0 w t * f t) 0 1

lemma continuousOn_unit_poisson {w : ℂ} (hw : ‖w‖ < 1) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 1) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply Complex.continuous_re.comp_continuousOn
  simpa using continuousOn_herglotzRieszKernel_sphere
    (c := 0) (R := 1) (by simpa using ne_of_lt hw)

lemma unit_poisson_nonneg {w t : ℂ} (hw : ‖w‖ < 1) (ht : t ∈ sphere 0 1) :
    0 ≤ poissonKernel 0 w t := by
  have ht' : ‖t‖ = 1 := by simpa using ht
  simp only [poissonKernel_def, sub_zero, ht']
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg w]

lemma unit_poisson_normalized {w : ℂ} (hw : ‖w‖ < 1) :
    Real.circleAverage (poissonKernel 0 w) 0 1 = 1 := by
  have h := (differentiable_const (c := (1 : ℂ))).diffContOnCl
    (s := ball (0 : ℂ) 1) |>.circleAverage_poissonKernel_smul (by simpa using hw)
  have hi : CircleIntegrable (poissonKernel 0 w) 0 1 :=
    (continuousOn_unit_poisson hw).circleIntegrable (by norm_num)
  have he := Complex.ofRealCLM.circleAverage_comp_comm hi
  apply Complex.ofReal_injective
  change Complex.ofReal (Real.circleAverage (poissonKernel 0 w) 0 1) = (1 : ℂ)
  change Complex.ofRealCLM (Real.circleAverage (poissonKernel 0 w) 0 1) = (1 : ℂ)
  rw [← he]
  change Real.circleAverage (fun t => poissonKernel 0 w t • (1 : ℂ)) 0 1 = 1 at h
  simpa [Function.comp_def, Complex.real_smul] using h

lemma poissonExtension_error_bound {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) {p w : ℂ} {δ ε M : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hw : ‖w‖ < 1) (hwp : dist w p < δ/2)
    (hbound : ∀ t ∈ sphere 0 1, |f t-f p| ≤ M)
    (hsmall : ∀ t ∈ sphere 0 1, dist t p < δ → |f t-f p| ≤ ε) :
    |poissonExtension f w - f p| ≤ ε + (M/(δ/2)^2)*(1-‖w‖^2) := by
  let P := poissonKernel 0 w
  have hPc : ContinuousOn P (sphere 0 1) := continuousOn_unit_poisson hw
  have hfc : ContinuousOn (fun t => f t-f p) (sphere 0 1) := hf.sub continuousOn_const
  have hPmean : Real.circleAverage P 0 1 = 1 := unit_poisson_normalized hw
  have herr : poissonExtension f w-f p =
      Real.circleAverage (fun t => P t*(f t-f p)) 0 1 := by
    simp only [mul_sub]
    rw [Real.circleAverage_fun_sub]
    · simp only [mul_comm _ (f p)]
      have hh : Real.circleAverage (fun t => f p * P t) 0 1 = f p := by
        change Real.circleAverage (fun t => f p • P t) 0 1 = f p
        rw [Real.circleAverage_fun_smul, hPmean]; simp
      rw [hh]
      rfl
    · exact (hPc.mul hf).circleIntegrable (by norm_num)
    · exact (hPc.mul continuousOn_const).circleIntegrable (by norm_num)
  have hpoint : ∀ t ∈ sphere 0 1,
      |P t*(f t-f p)| ≤ ε*P t+(M/(δ/2)^2)*(1-‖w‖^2) := by
    intro t ht
    have hn : 0 ≤ P t := unit_poisson_nonneg hw ht
    rw [abs_mul, abs_of_nonneg hn]
    have hnum : 0 ≤ 1-‖w‖^2 := by nlinarith [norm_nonneg w]
    have htail : 0 ≤ (M/(δ/2)^2)*(1-‖w‖^2) := by positivity
    by_cases htp : dist t p < δ
    · calc P t*|f t-f p| ≤ P t*ε := mul_le_mul_of_nonneg_left (hsmall t ht htp) hn
           _ ≤ ε*P t+(M/(δ/2)^2)*(1-‖w‖^2) := by nlinarith
    · have hdist : δ/2 ≤ ‖t-w‖ := by
        have htr := dist_triangle t w p
        have htw : δ/2 ≤ dist t w := by
          simp only [not_lt] at htp
          linarith
        simpa [dist_eq_norm] using htw
      have hden : (δ/2)^2 ≤ ‖t-w‖^2 := by nlinarith [norm_nonneg (t-w)]
      have hp : P t ≤ (1-‖w‖^2)/(δ/2)^2 := by
        have ht' : ‖t‖ = 1 := by simpa using ht
        dsimp [P]
        simp only [poissonKernel_def, sub_zero, ht', one_pow]
        exact div_le_div_of_nonneg_left hnum (by positivity) hden
      calc
        P t*|f t-f p| ≤ P t*M := mul_le_mul_of_nonneg_left (hbound t ht) hn
        _ ≤ ((1-‖w‖^2)/(δ/2)^2)*M := mul_le_mul_of_nonneg_right hp hM
        _ = (M/(δ/2)^2)*(1-‖w‖^2) := by ring
        _ ≤ ε*P t+(M/(δ/2)^2)*(1-‖w‖^2) := by nlinarith [mul_nonneg hε hn]
  rw [herr]
  calc
    |Real.circleAverage (fun t => P t*(f t-f p)) 0 1| ≤
        Real.circleAverage (fun t => |P t*(f t-f p)|) 0 1 :=
      Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun t => ε*P t+(M/(δ/2)^2)*(1-‖w‖^2)) 0 1 := by
      apply Real.circleAverage_mono
      · exact ((hPc.mul hfc).abs).circleIntegrable (by norm_num)
      · exact ((continuousOn_const.mul hPc).add continuousOn_const).circleIntegrable (by norm_num)
      · simpa using hpoint
    _ = ε+(M/(δ/2)^2)*(1-‖w‖^2) := by
      rw [Real.circleAverage_fun_add]
      · change Real.circleAverage (fun t => ε • P t) 0 1 + _ = _
        rw [Real.circleAverage_fun_smul, hPmean, Real.circleAverage_const]
        simp
      · exact (continuousOn_const.mul hPc).circleIntegrable (by norm_num)
      · exact continuousOn_const.circleIntegrable (by norm_num)

theorem poissonExtension_tendsto_boundary {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) {p : ℂ} (hp : p ∈ sphere 0 1) :
    Tendsto (poissonExtension f) (𝓝[ball 0 1] p) (𝓝 (f p)) := by
  obtain ⟨M,hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
    (hf.sub (continuousOn_const (c := f p)))
  have hM0 : 0 ≤ M := by simpa using hM p hp
  have hpn : ‖p‖ = 1 := by simpa using hp
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hsmall⟩ := Metric.continuousWithinAt_iff.mp (hf p hp) (ε/2) (by positivity)
  let K := M/(δ/2)^2
  have hc : ContinuousAt (fun w : ℂ => K*(1-‖w‖^2)) p := by fun_prop
  obtain ⟨η,hη,hηdef⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  refine ⟨min (δ/2) η, lt_min (by positivity) hη, ?_⟩
  intro w hw hwp
  have hwpδ : dist w p < δ/2 := lt_of_lt_of_le hwp (min_le_left _ _)
  have hwpη : dist w p < η := lt_of_lt_of_le hwp (min_le_right _ _)
  have htail : K*(1-‖w‖^2) < ε/2 := by
    have hh := hηdef hwpη
    simp only [hpn, one_pow, sub_self, mul_zero, dist_zero_right] at hh
    exact (le_abs_self _).trans_lt hh
  have hh := poissonExtension_error_bound hf (ε := ε/2) (M := M) hδ (by positivity) hM0
    (by simpa using hw) hwpδ
    (fun t ht => by simpa [Real.norm_eq_abs] using hM t ht)
    (fun t ht htp => by simpa [Real.dist_eq] using (hsmall ht htp).le)
  rw [Real.dist_eq]
  apply hh.trans_lt
  dsimp [K] at htail
  linarith

theorem harmonicOnNhd_poissonExtension {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    InnerProductSpace.HarmonicOnNhd (poissonExtension f) (ball 0 1) := by
  let H : ℂ → ℂ := fun w => Real.circleAverage
    (fun t => herglotzRieszKernel 0 w t • (f t : ℂ)) 0 1
  have ha : AnalyticOnNhd ℂ H (ball 0 1) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul
      ((Complex.continuous_ofReal.comp_continuousOn hf).circleIntegrable (by norm_num))).mono
      (by intro z hz; simpa using ne_of_lt (show ‖z‖ < 1 by simpa using hz))
  intro w hw
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₁ := fun z => (H z).re) ?_).mp
    ((ha w hw).harmonicAt_re)
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz
  have hh := re_circleAverage_herglotzRieszKernel_smul
    (hf.circleIntegrable (by norm_num))
    (by simpa using ne_of_lt (show ‖z‖ < 1 by simpa using hz))
  simpa [H, poissonExtension, poissonKernel_eq_re_herglotzRieszKernel, Pi.smul_apply,
    smul_eq_mul, Pi.mul_def, Function.comp_def] using hh

def diskDirichlet (f : ℂ → ℝ) (w : ℂ) : ℝ :=
  if ‖w‖ < 1 then poissonExtension f w else f w

lemma diskDirichlet_eq_boundary {f : ℂ → ℝ} {p : ℂ} (hp : p ∈ sphere 0 1) :
    diskDirichlet f p = f p := by
  have h : ‖p‖ = 1 := by simpa using hp
  simp [diskDirichlet,h]

theorem harmonicOnNhd_diskDirichlet {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    InnerProductSpace.HarmonicOnNhd (diskDirichlet f) (ball 0 1) := by
  intro w hw
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₁ := poissonExtension f) ?_).mp
    (harmonicOnNhd_poissonExtension hf w hw)
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz
  simp only [diskDirichlet, ite_eq_left (show ‖z‖ < 1 by simpa using hz)]

theorem continuousOn_diskDirichlet {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    ContinuousOn (diskDirichlet f) (closedBall 0 1) := by
  intro p hp
  by_cases hpi : ‖p‖ < 1
  · have h := (harmonicOnNhd_diskDirichlet hf p (by simpa using hpi)).1.continuousAt
    exact h.continuousWithinAt
  · have hpn : ‖p‖ = 1 := by
      have h : ‖p‖ ≤ 1 := by simpa using hp
      exact le_antisymm h (not_lt.mp hpi)
    have hps : p ∈ sphere 0 1 := by simpa using hpn
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hδdef⟩ := Metric.tendsto_nhdsWithin_nhds.mp
      (poissonExtension_tendsto_boundary hf hps) ε hε
    obtain ⟨η,hη,hηdef⟩ := Metric.continuousWithinAt_iff.mp (hf p hps) ε hε
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro w hw hwp
    rw [diskDirichlet_eq_boundary hps]
    by_cases hwi : ‖w‖ < 1
    · rw [diskDirichlet, ite_eq_left hwi]
      exact hδdef (by simpa using hwi) (lt_of_lt_of_le hwp (min_le_left _ _))
    · rw [diskDirichlet, ite_eq_right hwi]
      apply hηdef _ (lt_of_lt_of_le hwp (min_le_right _ _))
      have hwn : ‖w‖ ≤ 1 := by simpa using hw
      simpa using le_antisymm hwn (not_lt.mp hwi)

end

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
section

lemma harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {p : ℂ}
    (hu : HarmonicAt u p) (hm : IsLocalMax u p) :
    ∀ᶠ z in 𝓝 p, u z = u p := by
  obtain ⟨r,hr,hrs⟩ := Metric.eventually_nhds_iff.mp hu.eventually
  have hur : HarmonicOnNhd u (ball p r) := fun z hz => hrs (by simpa [dist_comm] using hz)
  obtain ⟨H,hHa,hHu⟩ := hur.exists_analyticOnNhd_ball_re_eq
  have hp : p ∈ ball p r := mem_ball_self hr
  have hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (fun z => Complex.exp (H z)) z := by
    filter_upwards [isOpen_ball.mem_nhds hp] with z hz
    exact Complex.differentiable_exp.differentiableAt.comp z (hHa z hz).differentiableAt
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (H z)) p := by
    filter_upwards [hm, isOpen_ball.mem_nhds hp] with z hz hzr
    simp only [Function.comp_def, Complex.norm_exp, hHu hzr, hHu hp]
    exact Real.exp_le_exp.mpr hz
  filter_upwards [Complex.norm_eventually_eq_of_isLocalMax hdiff hmax,
    isOpen_ball.mem_nhds hp] with z hz hzr
  simp only [Complex.norm_exp] at hz
  exact (hHu hzr).symm.trans ((Real.exp_injective hz).trans (hHu hp))

lemma harmonic_eqOn_of_isPreconnected_of_isMaxOn {u : ℂ → ℝ} {U : Set ℂ} {p : ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hu : HarmonicOnNhd u U)
    (hp : p ∈ U) (hm : IsMaxOn u U p) : EqOn u (fun _ => u p) U := by
  let V := U ∩ {z | IsMaxOn u U z}
  have hV : ∀ z ∈ V, u z = u p := fun z hz => le_antisymm (hm hz.1) (hz.2 hp)
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hh := harmonic_eventually_eq_of_isLocalMax (hu z hz.1)
      (hz.2.isLocalMax (hUo.mem_nhds hz.1))
    filter_upwards [hUo.mem_nhds hz.1, hh] with w hw huw
    exact ⟨hw, fun t ht => (hz.2 ht).trans_eq huw.symm⟩
  let W := U ∩ {z | u z ≠ u p}
  have hWo : IsOpen W := hu.continuousOn.isOpen_inter_preimage hUo isOpen_ne
  have hdis : Disjoint V W := disjoint_left.mpr fun z hv hw => hw.2 (hV z hv)
  have hcover : U ⊆ V ∪ W := by
    intro z hz
    by_cases he : u z = u p
    · exact Or.inl ⟨hz, fun t ht => (hm ht).trans_eq he.symm⟩
    · exact Or.inr ⟨hz,he⟩
  have hsub : U ⊆ V := hUc.subset_left_of_subset_union hVo hWo hdis hcover ⟨p,hp,hp,hm⟩
  exact fun z hz => hV z (hsub hz)

theorem harmonic_exists_mem_frontier_isMaxOn {u : ℂ → ℝ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hu : HarmonicOnNhd u U) (huc : ContinuousOn u (closure U)) :
    ∃ p ∈ frontier U, IsMaxOn u (closure U) p := by
  have hc : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨w,hw,hm⟩ := hc.exists_isMaxOn hUne.closure huc
  rw [closure_eq_interior_union_frontier, mem_union] at hw
  rcases hw with hw | hw
  · have hne : interior U ≠ univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
    obtain ⟨z,hz,hzw⟩ := exists_mem_frontier_infDist_compl_eq_dist hw hne
    have hd : 0 < dist w z := by
      apply dist_pos.mpr
      intro he
      subst z
      exact Set.disjoint_left.mp (disjoint_interior_frontier (s := U)) hw (frontier_interior_subset hz)
    have hball : ball w (dist w z) ⊆ U := by
      rw [← hzw]
      exact ball_infDist_compl_subset.trans interior_subset
    have hconst := harmonic_eqOn_of_isPreconnected_of_isMaxOn
      (convex_ball w (dist w z)).isPreconnected isOpen_ball (hu.mono hball)
      (mem_ball_self hd) (hm.on_subset (hball.trans subset_closure))
    have hcl : EqOn u (fun _ => u w) (closure (ball w (dist w z))) :=
      hconst.of_subset_closure (huc.mono (closure_mono hball)) continuousOn_const subset_closure Subset.rfl
    have hze : u z = u w := hcl (by rw [closure_ball _ hd.ne']; simp [dist_comm])
    exact ⟨z,frontier_interior_subset hz, fun t ht => (hm ht).trans_eq hze.symm⟩
  · exact ⟨w,hw,hm⟩

theorem harmonic_le_of_frontier_le {u : ℂ → ℝ} {U : Set ℂ} {C : ℝ}
    (hUb : Bornology.IsBounded U) (hu : HarmonicOnNhd u U)
    (huc : ContinuousOn u (closure U)) (hbd : ∀ z ∈ frontier U, u z ≤ C)
    {z : ℂ} (hz : z ∈ closure U) : u z ≤ C := by
  have hUne : U.Nonempty := by
    by_contra hn
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hz
  obtain ⟨p,hp,hm⟩ := harmonic_exists_mem_frontier_isMaxOn hUb hUne hu huc
  exact (hm hz).trans (hbd p hp)

theorem harmonic_eqOn_closure_of_eqOn_frontier {u v : ℂ → ℝ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (hu : HarmonicOnNhd u U) (hv : HarmonicOnNhd v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hbd : EqOn u v (frontier U)) : EqOn u v (closure U) := by
  intro z hz
  apply le_antisymm
  · have hh := harmonic_le_of_frontier_le hUb (hu.sub hv) (huc.sub hvc)
      (C := 0) (fun t ht => by simp [hbd ht]) hz
    exact sub_nonpos.mp hh
  · have hh := harmonic_le_of_frontier_le hUb (hv.sub hu) (hvc.sub huc)
      (C := 0) (fun t ht => by simp [hbd ht]) hz
    exact sub_nonpos.mp hh

end

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

lemma circleAverage_conj {g : ℂ → ℝ} :
    Real.circleAverage (fun z => g (conj z)) 0 1 = Real.circleAverage g 0 1 := by
  rw [← Real.circleAverage_zero_one_congr_inv (f := g)]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hn : ‖z‖ = 1 := by simpa using hz
  simp only [Complex.inv_eq_conj hn]

lemma unit_poisson_conj (w t : ℂ) :
    poissonKernel 0 (conj w) (conj t) = poissonKernel 0 w t := by
  simp only [poissonKernel_def, sub_zero, ← map_sub, Complex.norm_conj]

lemma poissonExtension_odd {f : ℂ → ℝ}
    (hodd : ∀ z ∈ sphere (0 : ℂ) 1, f (conj z) = -f z) (w : ℂ) :
    poissonExtension f (conj w) = -poissonExtension f w := by
  unfold poissonExtension
  rw [← circleAverage_conj (g := fun t => poissonKernel 0 (conj w) t * f t)]
  calc
    _ = Real.circleAverage (fun t => -(poissonKernel 0 w t * f t)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro t ht
      change poissonKernel 0 (conj w) (conj t) * f (conj t) = -(poissonKernel 0 w t * f t)
      rw [unit_poisson_conj, hodd t (by simpa using ht)]
      ring
    _ = _ := by simp [Real.circleAverage, intervalIntegral.integral_neg]

lemma diskDirichlet_zero_real {f : ℂ → ℝ}
    (hodd : ∀ z ∈ sphere (0 : ℂ) 1, f (conj z) = -f z)
    {z : ℂ} (hz : ‖z‖ < 1) (hzi : z.im = 0) : diskDirichlet f z = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
  have hh := poissonExtension_odd hodd z
  rw [hc] at hh
  simp only [diskDirichlet, ite_eq_left hz]
  linarith

def upperDisk : Set ℂ := ball 0 1 ∩ {z | 0 < z.im}
def upperClosedDisk : Set ℂ := closedBall 0 1 ∩ {z | 0 ≤ z.im}

lemma upperDisk_isOpen : IsOpen upperDisk :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

lemma closure_upperDisk_subset : closure upperDisk ⊆ upperClosedDisk := by
  apply closure_minimal
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, le_of_lt (show 0 < z.im from hz.2)⟩
  · exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

lemma upper_frontier_or {z : ℂ} (hz : z ∈ frontier upperDisk) : ‖z‖ = 1 ∨ z.im = 0 := by
  have hc := closure_upperDisk_subset hz.1
  have hn : ‖z‖ ≤ 1 := by simpa using hc.1
  by_cases he : ‖z‖ = 1
  · exact Or.inl he
  · right
    by_contra hi
    have hi' : 0 < z.im := lt_of_le_of_ne hc.2 (Ne.symm hi)
    apply hz.2
    rw [upperDisk_isOpen.interior_eq]
    exact ⟨by simpa using lt_of_le_of_ne hn he, hi'⟩

def oddBoundary (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then u z else -u (conj z)

lemma oddBoundary_odd {u : ℂ → ℝ}
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : oddBoundary u (conj z) = -oddBoundary u z := by
  have hn : ‖z‖ = 1 := by simpa using hz
  by_cases hzi : z.im = 0
  · have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
    have hu := hzero z ⟨by simp [hn], by simp [hzi]⟩ hzi
    simp [oddBoundary,hc,hzi,hu]
  · by_cases hpos : 0 ≤ z.im
    · have hpos' : 0 < z.im := lt_of_le_of_ne hpos (Ne.symm hzi)
      have hh : ¬0 ≤ (conj z).im := by simp only [Complex.conj_im]; linarith
      simp only [oddBoundary, ite_eq_left hpos, ite_eq_right hh, Complex.conj_conj]
    · have hh : 0 ≤ (conj z).im := by simp only [Complex.conj_im]; linarith
      simp only [oddBoundary, ite_eq_right hpos, ite_eq_left hh, neg_neg]

lemma continuousOn_oddBoundary {u : ℂ → ℝ}
    (hu : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0) :
    ContinuousOn (oddBoundary u) (sphere 0 1) := by
  have hup : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hdown : closure {z : ℂ | ¬0 ≤ z.im} ⊆ {z | z.im ≤ 0} := by
    apply closure_minimal
    · intro z hz
      exact (lt_of_not_ge hz).le
    · exact isClosed_le Complex.continuous_im continuous_const
  have hfront : ∀ z ∈ frontier {z : ℂ | 0 ≤ z.im}, z.im = 0 := by
    intro z hz
    have hp : 0 ≤ z.im := by simpa [hup.closure_eq] using hz.1
    have hm : z.im ≤ 0 := by
      have hh : z ∈ closure {z : ℂ | ¬0 ≤ z.im} := by
        change z ∈ closure ({z : ℂ | 0 ≤ z.im}ᶜ)
        rw [closure_compl]
        exact hz.2
      exact hdown hh
    exact le_antisymm hm hp
  apply ContinuousOn.if
  · intro z hz
    have hzi := hfront z hz.2
    have hn : ‖z‖ = 1 := by simpa using hz.1
    have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
    rw [hc, hzero z ⟨by simp [hn], by simp [hzi]⟩ hzi, neg_zero]
  · apply hu.mono
    intro z hz
    exact ⟨sphere_subset_closedBall hz.1, by simpa [hup.closure_eq] using hz.2⟩
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    exact ⟨by simpa using (sphere_subset_closedBall hz.1), by
      simp only [mem_ofPred_eq, Complex.conj_im, neg_nonneg]; exact hdown hz.2⟩

theorem harmonic_reflection_upperDisk {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u upperDisk) (huc : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0) :
    ∃ v : ℂ → ℝ, HarmonicOnNhd v (ball 0 1) ∧
      ContinuousOn v (closedBall 0 1) ∧ EqOn v u (closure upperDisk) ∧
      (∀ z ∈ ball (0 : ℂ) 1, z.im = 0 → v z = 0) := by
  let f := oddBoundary u
  have hf : ContinuousOn f (sphere 0 1) := continuousOn_oddBoundary huc hzero
  have hodd : ∀ z ∈ sphere (0 : ℂ) 1, f (conj z) = -f z :=
    fun _ hz => oddBoundary_odd hzero hz
  refine ⟨diskDirichlet f, harmonicOnNhd_diskDirichlet hf, continuousOn_diskDirichlet hf, ?_, ?_⟩
  · apply harmonic_eqOn_closure_of_eqOn_frontier
      (isBounded_ball.subset inter_subset_left)
      ((harmonicOnNhd_diskDirichlet hf).mono inter_subset_left) hu
      ((continuousOn_diskDirichlet hf).mono (closure_upperDisk_subset.trans inter_subset_left))
      (huc.mono closure_upperDisk_subset)
    intro z hz
    have hc := closure_upperDisk_subset hz.1
    rcases upper_frontier_or hz with hn | hi
    · rw [diskDirichlet_eq_boundary (by simpa using hn)]
      exact ite_eq_left hc.2
    · have hn : ‖z‖ ≤ 1 := by simpa using hc.1
      by_cases he : ‖z‖ = 1
      · rw [diskDirichlet_eq_boundary (by simpa using he)]
        exact ite_eq_left hc.2
      · rw [diskDirichlet_zero_real hodd (lt_of_le_of_ne hn he) hi, hzero z hc hi]
  · intro z hz hi
    exact diskDirichlet_zero_real hodd (by simpa using hz) hi


end CompleteCrouzeix

end

end OAI
