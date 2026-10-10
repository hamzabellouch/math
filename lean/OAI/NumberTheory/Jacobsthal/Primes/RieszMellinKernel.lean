import OAI.NumberTheory.Jacobsthal.Estimates.LocalZeroMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

lemma modulusHeight_diskPoint_le (q : ℕ) [NeZero q] (t : ℝ) {rho : ℂ}
    (hr : ‖rho‖ ≤ 19/20) :
    modulusHeight q (dirichletDiskPoint t rho).im ≤ 2*modulusHeight q t := by
  have hri : |rho.im| ≤ 19/20 := (Complex.abs_im_le_norm rho).trans hr
  have hi : (dirichletDiskPoint t rho).im = t+(5/2:ℝ)*rho.im := by
    simp [dirichletDiskPoint,dirichletCenter]
  have hdis : |(dirichletDiskPoint t rho).im| ≤ |t|+3 := by
    rw [hi]
    have h := abs_add_le t ((5/2:ℝ)*rho.im)
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 5/2)] at h
    linarith
  have ht := abs_nonneg t
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have hl2 : Real.log 2 ≤ Real.log (|t|+6) := Real.log_le_log (by norm_num) (by linarith)
  have hl : Real.log (|(dirichletDiskPoint t rho).im|+6) ≤ Real.log (2*(|t|+6)) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : |t|+6 ≠ 0)] at hl
  unfold modulusHeight
  linarith

theorem exists_uniform_zero_separation :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), chi ≠ 1 → ∀ sigma t : ℝ,
      1-a/(modulusHeight q t)^2 ≤ sigma →
      DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I) ≠ 0 ∧
      ∀ rho : ℂ, ‖rho‖ ≤ 19/20 →
        DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0 →
        a/(modulusHeight q t)^2 ≤ ‖((2/5*(sigma-3):ℝ):ℂ)-rho‖ := by
  obtain ⟨c,hc,hregion⟩ := exists_nonprincipal_zero_free_region
  let a : ℝ := min (c/16) (1/100)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have hac : a ≤ c/16 := min_le_left _ _
  have ha100 : a ≤ 1/100 := min_le_right _ _
  refine ⟨a,ha,ha100,?_⟩
  intro q _ chi hchi sigma t hs
  have hH := modulusHeight_ge_one q t
  have hHp : 0 < modulusHeight q t := by linarith
  have hHsq : 0 < (modulusHeight q t)^2 := by positivity
  constructor
  · apply hregion q chi hchi ((sigma:ℂ)+(t:ℂ)*Complex.I)
    simp only [show ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma by simp,
      show ((sigma:ℂ)+(t:ℂ)*Complex.I).im = t by simp]
    have hdiv := div_le_div_of_nonneg_right (show a ≤ c by linarith) hHsq.le
    linarith
  · intro rho hr hz
    have hZ := modulusHeight_ge_one q (dirichletDiskPoint t rho).im
    have hZp : 0 < modulusHeight q (dirichletDiskPoint t rho).im := by linarith
    have hheight := modulusHeight_diskPoint_le q t hr
    have hpow : (modulusHeight q (dirichletDiskPoint t rho).im)^2 ≤
        4*(modulusHeight q t)^2 := by nlinarith
    have hdrop : c/(4*(modulusHeight q t)^2) ≤
        c/(modulusHeight q (dirichletDiskPoint t rho).im)^2 :=
      div_le_div_of_nonneg_left hc.le (by positivity) hpow
    have hzeroRe : (dirichletDiskPoint t rho).re <
        1-c/(modulusHeight q (dirichletDiskPoint t rho).im)^2 := by
      by_contra! h
      exact hregion q chi hchi (dirichletDiskPoint t rho) h hz
    have ha4 : 4*(a/(modulusHeight q t)^2) ≤ c/(4*(modulusHeight q t)^2) := by
      have h := div_le_div_of_nonneg_right (show 4*a ≤ c/4 by linarith) hHsq.le
      convert h using 1 <;> ring
    have hdiff : (5/2:ℝ)*((((2/5*(sigma-3):ℝ):ℂ)).re-rho.re) =
        sigma-(dirichletDiskPoint t rho).re := by
      rw [Complex.ofReal_re,dirichletDiskPoint_re]
      ring
    have har : 0 ≤ a/(modulusHeight q t)^2 := div_nonneg ha.le hHsq.le
    have hsep : a/(modulusHeight q t)^2 ≤ (((2/5*(sigma-3):ℝ):ℂ)).re-rho.re := by
      nlinarith only [hs,hzeroRe,hdrop,ha4,hdiff,har]
    have hn := Complex.re_le_norm (((2/5*(sigma-3):ℝ):ℂ)-rho)
    simp only [Complex.sub_re] at hn
    exact hsep.trans hn

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem exists_uniform_nonprincipal_strip_bound :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ sigma t : ℝ, 1-a/(modulusHeight q t)^2 ≤ sigma → sigma ≤ 2 →
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
          C*(modulusHeight q t)^3 := by
  classical
  obtain ⟨a,ha,ha100,hsep⟩ := exists_uniform_zero_separation
  obtain ⟨C0,hC0,hlocal⟩ := uniform_local_zero_estimates
  refine ⟨a,ha,ha100,C0+C0/a,by positivity,?_⟩
  intro q _ chi hchi sigma t hs hs2
  obtain ⟨hne,hseparate⟩ := hsep q chi hchi sigma t hs
  refine ⟨hne,?_⟩
  obtain ⟨S,hS,hmass,hbound⟩ := hlocal q chi hchi t
  let H : ℝ := modulusHeight q t
  have hH : 1 ≤ H := modulusHeight_ge_one q t
  have hHp : 0 < H := by linarith
  have hHsq : 1 ≤ H^2 := by nlinarith
  have hH2 : 0 < H^2 := by positivity
  have hr : 0 < a/H^2 := by positivity
  have hfrac : a/H^2 ≤ a := by
    apply (div_le_iff₀ hH2).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hHsq ha.le
  let w : ℂ := ((2/5*(sigma-3):ℝ):ℂ)
  have hw : ‖w‖ ≤ 17/20 := by
    change ‖((2/5*(sigma-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    change 1-a/H^2 ≤ sigma at hs
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hwne : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact hne
  let D : ℂ := deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
    DirichletCharacter.LFunction chi (dirichletDiskPoint t w)
  let Z : ℂ := ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat/(w-rho)
  have hterm (rho : ℂ) (hrho : rho ∈ S) :
      ‖((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℂ)/(w-rho)‖ ≤
        ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ)/(a/H^2) := by
    rw [norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hr
    exact hseparate rho ((hS rho).mp hrho).1 ((hS rho).mp hrho).2
  have hZ : ‖Z‖ ≤ (C0/a)*H^3 := by
    calc
      _ ≤ ∑ rho ∈ S, ‖((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℂ)/(w-rho)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ)/(a/H^2) :=
        Finset.sum_le_sum hterm
      _ = (∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ))/(a/H^2) := by
        simp only [Finset.sum_div]
      _ ≤ (C0*H)/(a/H^2) := div_le_div_of_nonneg_right hmass hr.le
      _ = _ := by field_simp
  have hb := hbound w hw hwne
  change ‖(5/2:ℂ)*D-Z‖ ≤ C0*H at hb
  have ht := norm_add_le ((5/2:ℂ)*D-Z) Z
  rw [sub_add_cancel] at ht
  have hscale : ‖(5/2:ℂ)*D‖ = (5/2:ℝ)*‖D‖ := by rw [norm_mul]; norm_num
  rw [hscale] at ht
  have hh2 : H ≤ H^2 := by nlinarith
  have hh3 := mul_le_mul_of_nonneg_left hh2 hHp.le
  have hcube : H ≤ H^3 := by nlinarith only [hh2,hh3]
  have hsmall := mul_le_mul_of_nonneg_left hcube hC0.le
  rw [show (sigma:ℂ)+(t:ℂ)*Complex.I = dirichletDiskPoint t w from (dirichletDiskPoint_ofReal sigma t).symm]
  change ‖D‖ ≤ (C0+C0/a)*H^3
  nlinarith only [ht,hb,hZ,hsmall,norm_nonneg D]

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def rieszWeight (x : ℝ) : ℝ := max (1-x) 0
noncomputable def rieszProfile (x : ℝ) : ℂ :=
  (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) x -
    (Ioc (0:ℝ) 1).indicator (fun t => (t:ℂ)) x
noncomputable def rieszKernel (s : ℂ) : ℂ := 1/(s*(s+1))

lemma rieszProfile_eq_weight {x : ℝ} (hx : 0 < x) : rieszProfile x = (rieszWeight x:ℂ) := by
  by_cases hx1 : x ≤ 1
  · have hm : x ∈ Ioc (0:ℝ) 1 := ⟨hx,hx1⟩
    simp [rieszProfile,hm,rieszWeight,max_eq_left (sub_nonneg.mpr hx1)]
  · have hm : x ∉ Ioc (0:ℝ) 1 := fun h => hx1 h.2
    have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    simp [rieszProfile,hm,rieszWeight,max_eq_right (sub_nonpos.mpr hx1')]

lemma continuous_rieszWeight : Continuous rieszWeight := by unfold rieszWeight; fun_prop

lemma continuousAt_rieszProfile {x : ℝ} (hx : 0 < x) : ContinuousAt rieszProfile x := by
  have he : rieszProfile =ᶠ[𝓝 x] (fun t => (rieszWeight t:ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact rieszProfile_eq_weight hy
  exact (continuousAt_congr he).mpr (Complex.continuous_ofReal.comp continuous_rieszWeight).continuousAt

theorem hasMellin_rieszProfile {s : ℂ} (hs : 0 < s.re) :
    HasMellin rieszProfile s (rieszKernel s) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1:ℂ) (s := s) (by simp only [Complex.one_re]; linarith)
  have h1' : HasMellin ((Ioc (0:ℝ) 1).indicator (fun t => (t:ℂ))) s (1/(s+1)) := by
    simpa only [Complex.cpow_one] using h1
  have h := hasMellin_sub h0.1 h1'.1
  rw [h0.2,h1'.2] at h
  change HasMellin rieszProfile s (1/s-1/(s+1)) at h
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  have hs1 : s+1 ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have he : 1/s-1/(s+1) = rieszKernel s := by
    unfold rieszKernel
    field_simp
    ring
  rwa [he] at h

lemma rieszWeight_nonneg (x : ℝ) : 0 ≤ rieszWeight x := le_max_right _ _
lemma rieszWeight_le_one {x : ℝ} (hx : 0 ≤ x) : rieszWeight x ≤ 1 := by
  unfold rieszWeight
  exact max_le (by linarith) zero_le_one
lemma rieszWeight_eq_zero {x : ℝ} (hx : 1 ≤ x) : rieszWeight x = 0 :=
  max_eq_right (sub_nonpos.mpr hx)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
