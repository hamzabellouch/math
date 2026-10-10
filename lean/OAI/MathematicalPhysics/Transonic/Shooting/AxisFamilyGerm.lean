import OAI.MathematicalPhysics.Transonic.Shooting.AxisFamilyDisk

namespace OAI

section
noncomputable section

namespace SepticProfile.AxisFamily
open Set Filter Metric Fuchsian SourceFamily
open scoped Topology

structure UniformGerm where
  radius : ℝ
  radius_pos : 0<radius
  G : Parameter → ℂ → ℂ
  jointContinuous : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) radius) => G p.1 p.2)
  analytic : ∀ a, AnalyticOnNhd ℂ (G a) (ball 0 radius)
  value : ∀ a, G a 0=((kap a:ℂ)+3)/4
  real : ∀ a (x:ℝ), (G a x).im=0
  equation : ∀ a z, z ∈ ball (0:ℂ) radius →
    NormalizedAxis.A (sig a:ℂ) z (G a z)*(G a z+2*z*deriv (G a) z) =
      (1-(3/5:ℂ)*z*(G a z)^2)*((kap a:ℂ)*(1-z*(G a z)^2)+3*(1-G a z))

theorem exists_uniform_germ : Nonempty UniformGerm := by
  obtain ⟨r,hr,f,hfc,hfr,hf0,hode⟩ := exists_continuous_remainder_disk
  have hr0 : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  let F : Parameter → ℂ → ℂ := fun a z => extend (f a:DiskMap) (z/(r:ℂ))
  have hmem {z:ℂ} (hz:z ∈ ball (0:ℂ) r) : z/(r:ℂ) ∈ ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_lt_one hr).mpr hz
  have hmemc {z:ℂ} (hz:z ∈ closedBall (0:ℂ) r) : z/(r:ℂ) ∈ closedBall (0:ℂ) 1 := by
    rw [mem_closedBall_zero_iff] at hz ⊢
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_le_one hr).mpr hz
  have hFa (a:Parameter) {z:ℂ} (hz:z ∈ ball (0:ℂ) r) : AnalyticAt ℂ (F a) z := by
    have han := (f a).property.analyticAt (isOpen_ball.mem_nhds (hmem hz))
    exact han.comp (f:=fun z:ℂ=>z/(r:ℂ)) (x:=z) (analyticAt_id.div_const (c:=(r:ℂ)))
  have hF0 (a:Parameter) : F a 0=0 := by simpa only [F,zero_div] using hf0 a
  have hFreal (a:Parameter) (x:ℝ) : (F a (x:ℂ)).im=0 := by
    dsimp [F]
    unfold extend
    split
    · apply hfr a
      simp
    · rfl
  have hFcont : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) r) => F p.1 p.2) := by
    have hm : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) r) =>
        (⟨(p.2:ℂ)/(r:ℂ),hmemc p.2.property⟩:Disk)) := by fun_prop
    have he : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) r) =>
        (f p.1:DiskMap) ⟨(p.2:ℂ)/(r:ℂ),hmemc p.2.property⟩) :=
      continuous_eval.comp (((continuous_subtype_val.comp hfc).comp continuous_fst).prodMk hm)
    convert he using 1
    funext p
    exact extend_coe (f p.1:DiskMap) (⟨(p.2:ℂ)/(r:ℂ),hmemc p.2.property⟩:Disk)
  have hFe (a:Parameter) {z:ℂ} (hz:z ∈ ball (0:ℂ) r) :
      denominator a (z,F a z) ≠ 0 ∧
      z*deriv (F a) z+(2:ℂ)*F a z=z*H a (z,F a z) := by
    have hd := hode a (z/(r:ℂ)) (hmem hz)
    have hzdiv : (r:ℂ)*(z/(r:ℂ))=z := by field_simp
    rw [hzdiv] at hd
    refine ⟨hd.1,?_⟩
    have he : deriv (F a) z=deriv (extend (f a:DiskMap)) (z/(r:ℂ))/(r:ℂ) := by
      simpa only [F,Function.comp_def,id_eq,one_div,div_eq_mul_inv,one_mul] using
        (((differentiableAt_extend (f a) (hmem hz)).hasDerivAt).comp z
          ((hasDerivAt_id z).div_const (r:ℂ))).deriv
    change z*deriv (F a) z+(2:ℂ)*extend (f a:DiskMap) (z/(r:ℂ))=_
    rw [he]
    convert hd.2 using 1 ; ring
  let G : Parameter → ℂ → ℂ := fun a z => ((kap a:ℂ)+3)/4+F a z
  have hdg (a:Parameter) {z:ℂ} (hz:z ∈ ball (0:ℂ) r) : deriv (G a) z=deriv (F a) z :=
    ((hFa a hz).differentiableAt.hasDerivAt.const_add (((kap a:ℂ)+3)/4)).deriv
  refine ⟨⟨r,hr,G,?_,?_,?_,?_,?_⟩⟩
  · apply Continuous.add _ hFcont
    exact ((((Complex.continuous_ofReal.comp kap.continuous).comp continuous_fst).add continuous_const).div_const 4)
  · intro a z hz
    exact analyticAt_const.add (hFa a hz)
  · intro a
    simp only [G,hF0,add_zero]
  · intro a x
    simp only [G,Complex.add_im,hFreal,add_zero]
    simp
  · intro a z hz
    let b : ℂ := ((kap a:ℂ)+3)/4
    have hi := NormalizedAxis.axis_identity (sig a:ℂ) (kap a:ℂ) (3/5:ℂ) b z
      (G a z) (deriv (G a) z) (by dsimp [b];ring)
    have hgminus : G a z-b=F a z := by dsimp [G,b];ring
    rw [hgminus,hdg a hz] at hi
    have hfe := (hFe a hz).2
    rw [hfe] at hi
    have hc : 2*NormalizedAxis.A (sig a:ℂ) z (G a z)*(z*H a (z,F a z))-
        z*(NormalizedAxis.R (sig a:ℂ) (kap a:ℂ) (3/5:ℂ) z (G a z)+
          4*NormalizedAxis.A1 (sig a:ℂ) z (G a z)*F a z)=0 := by
      change denominator a (z,F a z)*(z*(numerator a (z,F a z)/denominator a (z,F a z)))-
        z*numerator a (z,F a z)=0
      apply sub_eq_zero.mpr
      calc
        _ = z*((numerator a (z,F a z)/denominator a (z,F a z))*denominator a (z,F a z)) := by ac_rfl
        _ = _ := by rw [div_mul_cancel₀ _ (hFe a hz).1]
    rw [hc] at hi
    rw [hdg a hz]
    exact sub_eq_zero.mp hi

end SepticProfile.AxisFamily

end
end

end OAI
