import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.AffineRetardedBound

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_physical_kernel_affine (P H : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) H, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec,
      ‖(1-dot n (velocity v)) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C*(1+‖E‖+‖B‖)/r^2 := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_physical_kernel_affine P H
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv E B
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv E B
  rw [normalisedElectricKernel_eq hr.1.ne',smul_comm (1-dot n (velocity v)),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma uniform_retarded_density_affine (A P H : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U : ℝ), U≤H →
      (∀ t∈Icc 0 U, ∀ z, |s.f (t,z)|≤A) →
      (∀ t∈Icc 0 U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ t∈Icc 0 U, ∀ (x z : Vec), 0<‖z‖ → ‖z‖≤t →
        ‖retardedElectricDensity s t x (x+z)‖≤
          C*(1+‖s.E (t-‖z‖,x+z)‖+‖s.B (t-‖z‖,x+z)‖)/‖z‖^2 ∧
        ‖retardedMagneticDensity s t x (x+z)‖≤
          C*(1+‖s.E (t-‖z‖,x+z)‖+‖s.B (t-‖z‖,x+z)‖)/‖z‖^2 := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_kernel_affine P H
  refine ⟨A*K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro s U hUH hf hs t ht x z hz hzt
  have htime : t-‖z‖∈Icc 0 U := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hxy : x≠x+z := by
    intro he
    have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa using he.symm)
    exact (norm_pos_iff.mp hz) hh
  have he : ‖retardedElectricDensity s t x (x+z)‖≤
      (A*K*volume.real (closedBall (0:Vec) P))*(1+‖s.E (t-‖z‖,x+z)‖+‖s.B (t-‖z‖,x+z)‖)/‖z‖^2 := by
    unfold retardedElectricDensity
    rw [coneRadius_add]
    exact (physical_integral_bound hA
      (fun u hu => hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hUH)⟩ _ (coneDirection_norm hxy) u hu _ _)
      (fun u => hf _ htime _) (fun u hu => hs _ htime _ u hu)).trans_eq (by ring)
  refine ⟨he,?_⟩
  exact (norm_cross_le _ _).trans (by simpa only [coneDirection_norm hxy,one_mul] using he)

lemma kernel_volterra_norm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Vec → W} {t C : ℝ} (ht : 0≤t) (_ : 0≤C)
    (hF : IntegrableOn F (ball (0:Vec) t)) {g : ℝ → ℝ} (hg : Continuous g)
    (hb : ∀ z, 0<‖z‖ → ‖z‖≤t → ‖F z‖≤C*g (t-‖z‖)/‖z‖^2) :
    ‖∫ z in ball (0:Vec) t, F z‖≤(4*Real.pi)*C*(∫ u in Icc (0:ℝ) t, g u) := by
  rw [integral_ball_polar_flip hF]
  have hr : IntegrableOn (fun r => C*g (t-r)) (Ioo (0:ℝ) t) :=
    ((continuous_const.mul (hg.comp (continuous_const.sub continuous_id))).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hin (a : Sphere) : ‖∫ r in Ioo (0:ℝ) t, r^2 • F (-(r • a.1))‖ ≤
      C*(∫ u in Icc (0:ℝ) t, g u) := by
    have hh := norm_integral_le_of_norm_le hr (f:=fun r => r^2 • F (-(r • a.1))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have he : ‖-(r • a.1)‖=r := by
        rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,sphere_norm,mul_one]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      have hh := hb (-(r • a.1)) (by simpa only [he] using hr.1) (by simpa only [he] using hr.2.le)
      rw [he] at hh
      exact (mul_le_mul_of_nonneg_left hh (sq_nonneg r)).trans_eq (by field_simp [ne_of_gt hr.1]))
    apply hh.trans_eq
    rw [←integral_Icc_eq_integral_Ioo,integral_const_mul,integral_Icc_sub g ht]
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (Filter.Eventually.of_forall hin)
  simpa only [sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh

lemma SmoothClassicalPrefix.physical_vectors {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (hHt : t<H) (x : Vec) :
    (s.E (t,x)=electricBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z)) ∧
    (s.B (t,x)=magneticBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) ∧
    IntegrableOn (fun z => retardedElectricDensity s t x (x+z)) (ball (0:Vec) t) ∧
    IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) t) := by
  let τ := (t+H)/2
  have htτ : t<τ := by dsimp [τ]; linarith
  have hτH : τ<H := by dsimp [τ]; linarith
  have hτ0 : 0≤τ := ht.le.trans htτ.le
  let a := cutoffPrefix τ H s
  have ha := hs.cutoff_classical_before hτ0 hτH
  have ham := hs.cutoff_smooth hτH
  have hE := classical_electric_physical_vector_before ha ham ht htτ x
  have hB := classical_magnetic_physical_vector_before ha ham ht htτ x
  have hED : electricBoundaryField a t x=electricBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_electricConeBoundary_datum_before ha ht x i
  have hBD : magneticBoundaryField a t x=magneticBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_magneticConeBoundary_datum_before ha ht x i
  have heq (z : Vec) : retardedElectricDensity a t x (x+z)=retardedElectricDensity s t x (x+z) := by
    have hh := cutoffPrefix_eq hτH ((sub_le_self t (norm_nonneg (x-(x+z)))).trans htτ.le) s
    unfold retardedElectricDensity
    simp only [coneRadius,hh.1,hh.2.1,hh.2.2,a]
  have hbq (z : Vec) : retardedMagneticDensity a t x (x+z)=retardedMagneticDensity s t x (x+z) := by
    simp only [retardedMagneticDensity,heq]
  have hie := integrableOn_retardedElectricDensity_le ha.1 ha.2.1 ha.2.2.1
    ha.2.2.2.2.2.2.1 ht.le le_rfl x
  have hib := integrableOn_retardedMagneticDensity_le ha.1 ha.2.1 ha.2.2.1
    ha.2.2.2.2.2.2.1 ht.le le_rfl x
  change s.E (t,x)=_ ∧ s.B (t,x)=_ ∧ _
  rw [(cutoffPrefix_eq hτH htτ.le s).2.1 x] at hE
  rw [(cutoffPrefix_eq hτH htτ.le s).2.2 x] at hB
  change s.E (t,x)=electricBoundaryField a t x+(4*Real.pi)⁻¹ •
    (∫ z in ball (0:Vec) t,retardedElectricDensity a t x (x+z)) at hE
  change s.B (t,x)=magneticBoundaryField a t x+(4*Real.pi)⁻¹ •
    (∫ z in ball (0:Vec) t,retardedMagneticDensity a t x (x+z)) at hB
  simp_rw [hED,heq] at hE
  simp_rw [hBD,hbq] at hB
  change IntegrableOn (fun z => retardedElectricDensity a t x (x+z)) _ at hie
  change IntegrableOn (fun z => retardedMagneticDensity a t x (x+z)) _ at hib
  simp_rw [heq] at hie
  simp_rw [hbq] at hib
  exact ⟨hE,hB,hie,hib⟩

end RVM
end

end OAI
