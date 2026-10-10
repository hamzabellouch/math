import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.BoundaryJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma continuous_datumMagneticMoment (i : Fin 3) :
    Continuous (fun p : Vec × Vec => p.1 (curlA i)*velocity p.2 (curlB i)-
      p.1 (curlB i)*velocity p.2 (curlA i)) := by
  have hp (j : Fin 3) : Continuous (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous
  exact ((hp _).comp continuous_fst |>.mul ((hp _).comp ((contDiff_velocity (k:=1)).continuous.comp continuous_snd))).sub
    ((hp _).comp continuous_fst |>.mul ((hp _).comp ((contDiff_velocity (k:=1)).continuous.comp continuous_snd)))

lemma datumWeightedSphere_magneticMoment {d : Datum} (hd : Admissible d) (t : ℝ) (x : Vec) (i : Fin 3) :
    datumWeightedSphere d.f₀ (fun p => p.1 (curlA i)*velocity p.2 (curlB i)-
      p.1 (curlB i)*velocity p.2 (curlA i)) (t,x)=
      (4*Real.pi)⁻¹*(∫ a : Sphere,
        t*a.1 (curlA i)*current d.f₀ (x+t • a.1) (curlB i)-
        t*a.1 (curlB i)*current d.f₀ (x+t • a.1) (curlA i) ∂sphereMeasure) := by
  unfold datumWeightedSphere
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  have hi (j : Fin 3) : Integrable (fun v => d.f₀ (x+t • a.1,v)*velocity v j) := by
    exact datum_velocity_integrable hd.1.continuous hd.2.1
      (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp
        ((contDiff_velocity (k:=1)).continuous.comp continuous_snd)).continuousOn)
      (x+t • a.1) a.1 (sphere_norm a)
  simp_rw [mul_sub,show ∀ j k : Fin 3, ∀ v : Vec, d.f₀ (x+t • a.1,v)*(a.1 j*velocity v k)=
    a.1 j*(d.f₀ (x+t • a.1,v)*velocity v k) by intros; ring]
  rw [integral_sub ((hi _).const_mul _) ((hi _).const_mul _),integral_const_mul,integral_const_mul,
    datum_current_eq_integral hd,datum_current_eq_integral hd]
  ring

lemma magneticConeBoundary_datum_jets {d : Datum} (hd : Admissible d) (k : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1,
      ContDiff ℝ ∞ (fun x => magneticConeBoundary (datumBoundarySolution d) t x i 0) ∧
      ∀ x, ‖iteratedFDeriv ℝ k (fun y => magneticConeBoundary (datumBoundarySolution d) t y i 0) x‖≤C := by
  have hp (j : Fin 3) : ContDiff ℝ ∞ (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).contDiff
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_jets hd.2.2.2.1 hd.2.2.2.2.1 k i
  obtain ⟨hFs,B,hB,hflux⟩ := datumWeightedSphere_smooth_bound hd.1 hd.2.1
    (continuousOn_fluxWeight (continuousOn_datumMagneticFluxKernel i)) k
  obtain ⟨hRs,D,hD,hmoment⟩ := datumWeightedSphere_smooth_bound hd.1 hd.2.1
    ((continuous_datumMagneticMoment i).continuousOn) k
  let a := freeWave (fun y => d.B₀ y i) (fun y => -curl d.E₀ y i)
  let b := datumWeightedSphere d.f₀ (fun p => dot p.1 (datumMagneticFluxKernel i (-p.1,p.2)))
  let c := datumWeightedSphere d.f₀ (fun p => p.1 (curlA i)*velocity p.2 (curlB i)-
    p.1 (curlB i)*velocity p.2 (curlA i))
  have has : ContDiff ℝ ∞ a := contDiff_freeWave ((hp i).comp hd.2.2.2.2.1.1)
    (((hp i).comp (contDiff_curl hd.2.2.2.1.1)).neg)
  refine ⟨A+B+D,by positivity,?_⟩
  intro t ht
  have heq : (fun x => magneticConeBoundary (datumBoundarySolution d) t x i 0)=
      (fun x => a (t,x)-b (t,x)+c (t,x)) := by
    funext x
    simp only [magneticConeBoundary,sub_zero]
    simp_rw [datum_initial_magnetic_flux_normalised d i ht.1]
    rw [←datumWeightedSphere_flux hd.1.continuous hd.2.1 (continuousOn_datumMagneticFluxKernel i)]
    simp only [datumBoundarySolution]
    rw [←datumWeightedSphere_magneticMoment hd]
  rw [heq]
  have ha := has.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hb := hFs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hc := hRs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  refine ⟨(ha.sub hb).add hc,?_⟩
  intro x
  exact (norm_iteratedFDeriv_add_le (ha.sub hb) hc k x).trans (add_le_add
    ((norm_iteratedFDeriv_sub_le ha hb k x).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x).2
      (hflux t ⟨ht.1.le,ht.2⟩ x))) (hmoment t ⟨ht.1.le,ht.2⟩ x))

lemma norm_iteratedFDeriv_vec_le {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {F : U → Vec} (hF : ContDiff ℝ ∞ F) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (h : ∀ i : Fin 3, ∀ x, ‖iteratedFDeriv ℝ n (fun y => F y i) x‖≤C) (x : U) :
    ‖iteratedFDeriv ℝ n F x‖≤3*C := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hb (i : Fin 3) : |(iteratedFDeriv ℝ n F x v) i|≤C*(∏ j, ‖v j‖) := by
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).iteratedFDeriv_comp_left (x:=x)
      hF.contDiffAt (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞)
    have ha := ((iteratedFDeriv ℝ n (fun y => F y i) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h i x) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
    change ‖iteratedFDeriv ℝ n ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i) ∘ F) x v‖≤_ at ha
    rw [he] at ha
    exact ha
  exact (norm_le_three_of_coordinate_bound (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _))) hb).trans_eq (by ring)

lemma datum_boundary_global_jets {d : Datum} (hd : Admissible d) (k : ℕ) :
    ∃ C : ℝ, 0≤C ∧
      (∀ x, ‖iteratedFDeriv ℝ k d.E₀ x‖≤C ∧ ‖iteratedFDeriv ℝ k d.B₀ x‖≤C) ∧
      ∀ t∈Ioc (0:ℝ) 1,
        (ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) ∧
          ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t)) ∧
        ∀ x, ‖iteratedFDeriv ℝ k (electricBoundaryField (datumBoundarySolution d) t) x‖≤C ∧
          ‖iteratedFDeriv ℝ k (magneticBoundaryField (datumBoundarySolution d) t) x‖≤C := by
  choose CE hCE he using electricConeBoundary_datum_jets hd k
  choose CB hCB hb using magneticConeBoundary_datum_jets hd k
  obtain ⟨D,hD⟩ := hd.2.2.2.1.2 k
  obtain ⟨L,hL⟩ := hd.2.2.2.2.1.2 k
  let C := max D 0+max L 0+∑ i, (CE i+CB i)
  have hC : 0≤C := add_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))
    (Finset.sum_nonneg (fun i _ => add_nonneg (hCE i) (hCB i)))
  have hEC (i) : CE i≤C := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [C]; linarith [le_max_right D 0,le_max_right L 0,hCB i]
  have hBC (i) : CB i≤C := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [C]; linarith [le_max_right D 0,le_max_right L 0,hCE i]
  refine ⟨3*C,by positivity,?_,?_⟩
  · intro x
    have hS : 0≤∑ i, (CE i+CB i) := Finset.sum_nonneg (fun i _ => add_nonneg (hCE i) (hCB i))
    constructor
    · exact (hD x).trans (by dsimp [C]; linarith [le_max_left D 0,le_max_right L 0])
    · exact (hL x).trans (by dsimp [C]; linarith [le_max_left L 0,le_max_right D 0])
  · intro t ht
    have hes : ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) :=
      contDiff_euclidean.mpr (fun i => (he i t ht).1)
    have hbs : ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t) :=
      contDiff_euclidean.mpr (fun i => (hb i t ht).1)
    refine ⟨⟨hes,hbs⟩,fun x => ⟨?_,?_⟩⟩
    · exact norm_iteratedFDeriv_vec_le hes k hC (fun i y => ((he i t ht).2 y).trans (hEC i)) x
    · exact norm_iteratedFDeriv_vec_le hbs k hC (fun i y => ((hb i t ht).2 y).trans (hBC i)) x

end RVM
end

end OAI
