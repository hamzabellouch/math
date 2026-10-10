import OAI.Probability.SLE.Geometry.ClosedArcCrossing
import OAI.Probability.SLE.Loewner.UnivalentArcRayCrossing

namespace OAI

/-! A small inverse semicircle, closed outside the image domain, traps
its radial interior. All intersections and transversality are explicit. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma path_ofLine_hasStrictDerivAt {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1))
    {a b : ℂ} (h0 : f 0=a) (h1 : f 1=b) {t : ℝ} (ht : t∈Ioo 0 1)
    {α : ℂ} (hd : HasStrictDerivAt f α t) :
    HasStrictDerivAt (Path.ofLine hf h0 h1).extend α t := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [(show Ioo (0:ℝ) 1∈𝓝 t from Ioo_mem_nhds ht.1 ht.2)] with u hu
  exact (Path.extend_apply (Path.ofLine hf h0 h1) (Ioo_subset_Icc_self hu)).symm

lemma polar_point_injective (x r s α θ : ℝ) (hr : 0<r) (hs : 0<s)
    (hα : α∈Ioo 0 Real.pi) (hθ : θ∈Ioo 0 Real.pi)
    (he : (x:ℂ)+(r:ℂ)*Complex.exp ((α:ℂ)*Complex.I)=
      (x:ℂ)+(s:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) : r=s ∧ α=θ := by
  have he' := add_left_cancel he
  have hrs : r=s := by
    have hn := congrArg norm he'
    simpa [norm_mul,Complex.norm_exp,Complex.mul_re,abs_of_pos hr,abs_of_pos hs] using hn
  subst s
  have hexp : Complex.exp ((α:ℂ)*Complex.I)=Complex.exp ((θ:ℂ)*Complex.I) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') he'
  have ha : (α:ℂ)*Complex.I∈{z : ℂ | 0<z.im ∧ z.im<Real.pi} := by simpa using hα
  have ht : (θ:ℂ)*Complex.I∈{z : ℂ | 0<z.im ∧ z.im<Real.pi} := by simpa using hθ
  have hi := congrArg Complex.im (exp_injective_strip ha ht hexp)
  exact ⟨rfl,by simpa using hi⟩

lemma polar_arc_traps_radial_point {F : ℂ → ℂ} {D : Set ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hi : InjOn F upperHalfPlane)
    (hmap : MapsTo F upperHalfPlane D)
    (x r ρ R θ : ℝ) (hρ : 0<ρ) (hρr : ρ<r) (hrR : r<R)
    (hθ : θ∈Ioo 0 Real.pi)
    (c : ℝ → ℂ) (hc : Continuous c)
    (he : ∀ a∈Ioo 0 Real.pi, c a=F ((x:ℂ)+(r:ℂ)*Complex.exp ((a:ℂ)*Complex.I)))
    (hc0 : c 0∉D) (hcπ : c Real.pi∉D)
    (q : Path (c Real.pi) (c 0)) (hq : ∀ u, q u∉D)
    (w : ℂ) (ε : ℝ) (hε : 0<ε)
    (hcball : ∀ a∈Icc 0 Real.pi, c a∈ball w ε)
    (hqball : ∀ u, q u∈ball w ε)
    (hR : F ((x:ℂ)+(R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))∉ball w ε) :
    F ((x:ℂ)+(ρ:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))∈ball w ε := by
  by_contra hρout
  have hr : 0<r := hρ.trans hρr
  have hρR : 0<R-ρ := sub_pos.mpr (hρr.trans hrR)
  let A (u : ℝ) := c (Real.pi*u)
  let B (u : ℝ) := F ((x:ℂ)+((ρ+(R-ρ)*u:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
  have hlin (u : ℝ) (hu : u∈Icc 0 1) : 0<ρ+(R-ρ)*u :=
    add_pos_of_pos_of_nonneg hρ (mul_nonneg hρR.le hu.1)
  have hB : ContinuousOn B (Icc 0 1) := by
    apply hF.continuousOn.comp (by fun_prop)
    intro u hu
    exact univalent_polar_point_mem x _ θ (hlin u hu) hθ
  let a : Path (c 0) (c Real.pi) := Path.ofLine (f := A) (hf := (hc.comp (show Continuous (fun u : ℝ => Real.pi*u) by fun_prop)).continuousOn)
    (by simp [A]) (by simp [A])
  let p : Path (B 0) (B 1) := Path.ofLine hB rfl rfl
  let s : unitInterval := ⟨(r-ρ)/(R-ρ), by
    constructor
    · exact (div_pos (sub_pos.mpr hρr) hρR).le
    · exact (div_le_one hρR).mpr (by linarith)⟩
  let t : unitInterval := ⟨θ/Real.pi, by
    constructor
    · exact (div_pos hθ.1 Real.pi_pos).le
    · exact (div_le_one Real.pi_pos).mpr hθ.2.le⟩
  have hs : 0<(s:ℝ) ∧ (s:ℝ)<1 :=
    ⟨div_pos (sub_pos.mpr hρr) hρR,(div_lt_one hρR).mpr (by linarith)⟩
  have ht : 0<(t:ℝ) ∧ (t:ℝ)<1 :=
    ⟨div_pos hθ.1 Real.pi_pos,(div_lt_one Real.pi_pos).mpr hθ.2⟩
  have hst : ρ+(R-ρ)*(s:ℝ)=r := by dsimp [s]; field_simp; ring
  have htt : Real.pi*(t:ℝ)=θ := by dsimp [t]; field_simp
  have hpin (u : unitInterval) : p u∈D :=
    hmap (univalent_polar_point_mem x _ θ (hlin u u.property) hθ)
  have hp0 : B 0∉ball w ε := by simpa [B] using hρout
  have hp1 : B 1∉ball w ε := by simpa [B] using hR
  have hcross : a t=p s := by
    change c (Real.pi*(t:ℝ))=B s
    rw [htt,he θ hθ]
    simp only [B,hst]
  have huniq (u v : unitInterval) (hev : a v=p u) : u=s ∧ v=t := by
    have hv0 : (v:ℝ)≠0 := by
      intro hv
      apply hc0
      have : a v=c 0 := by change c (Real.pi*(v:ℝ))=c 0; rw [hv,mul_zero]
      rw [←this,hev]
      exact hpin u
    have hv1 : (v:ℝ)≠1 := by
      intro hv
      apply hcπ
      have : a v=c Real.pi := by change c (Real.pi*(v:ℝ))=c Real.pi; rw [hv,mul_one]
      rw [←this,hev]
      exact hpin u
    have hv : Real.pi*(v:ℝ)∈Ioo 0 Real.pi :=
      ⟨mul_pos Real.pi_pos (lt_of_le_of_ne v.property.1 hv0.symm),
       by nlinarith [lt_of_le_of_ne v.property.2 hv1,Real.pi_pos]⟩
    change c (Real.pi*(v:ℝ))=B u at hev
    rw [he _ hv] at hev
    have hpre := hi (univalent_polar_point_mem x r _ hr hv)
      (univalent_polar_point_mem x _ θ (hlin u u.property) hθ) hev
    obtain ⟨hrad,hang⟩ := polar_point_injective x r _ _ θ hr (hlin u u.property) hv hθ hpre
    constructor
    · apply Subtype.ext
      dsimp [s]
      apply (eq_div_iff hρR.ne').mpr
      nlinarith [hrad]
    · apply Subtype.ext
      dsimp [t]
      exact (eq_div_iff Real.pi_ne_zero).mpr (by linarith [hang])
  let z := (x:ℂ)+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  let V := deriv F z*Complex.exp ((θ:ℂ)*Complex.I)
  have hV : V≠0 := mul_ne_zero
    (univalent_deriv_ne_zero isOpen_upperHalfPlane hF hi (univalent_polar_point_mem x r θ hr hθ))
    (Complex.exp_ne_zero _)
  have haD : HasStrictDerivAt a.extend ((Real.pi*r:ℝ) • (Complex.I*V)) t := by
    apply path_ofLine_hasStrictDerivAt _ _ _ ht
    have hd := (holomorphic_polar_arc_strict hF x r θ hr hθ).scomp_of_eq (t:ℝ)
      (show HasStrictDerivAt (fun u : ℝ => Real.pi*u) Real.pi t by
        simpa using (hasStrictDerivAt_id (t:ℝ)).const_mul Real.pi) htt.symm
    have heq : (fun u : ℝ => F ((x:ℂ)+(r:ℂ)*Complex.exp (((Real.pi*u:ℝ):ℂ)*Complex.I)))
        =ᶠ[𝓝 (t:ℝ)] A := by
      filter_upwards [(isOpen_Ioo.mem_nhds (show (t:ℝ)∈Ioo 0 1 from ht))] with u hu
      exact (he _ ⟨mul_pos Real.pi_pos hu.1,by nlinarith [hu.2,Real.pi_pos]⟩).symm
    have hd' := hd.congr_of_eventuallyEq heq
    convert hd' using 1
    dsimp [V,z]
    simp only [Complex.ofReal_mul]
    ring
  have hpD : HasStrictDerivAt p.extend ((R-ρ) • V) s := by
    apply path_ofLine_hasStrictDerivAt hB rfl rfl hs
    have hd := (holomorphic_polar_ray_strict hF x r θ hr hθ).scomp_of_eq (s:ℝ)
      (show HasStrictDerivAt (fun u : ℝ => ρ+(R-ρ)*u) (R-ρ) s by
        simpa using ((hasStrictDerivAt_id (s:ℝ)).const_mul (R-ρ)).const_add ρ) hst.symm
    exact hd
  apply small_closed_arc_no_transverse_crossing a q p hpin hq w ε hε
    (fun u => hcball _ ⟨mul_nonneg Real.pi_pos.le u.property.1,by nlinarith [u.property.2,Real.pi_pos]⟩)
    hqball hp0 hp1 s t hs ht hcross huniq _ _ haD hpD
  intro u v huv
  apply transverse_radial_angular (Real.pi*r) (R-ρ) V
    (mul_pos Real.pi_pos hr).ne' hρR.ne' hV u v
  simpa only [Complex.real_smul,Complex.ofReal_mul,mul_assoc] using huv

end SLEExactGauge

end

end OAI
