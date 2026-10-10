import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.BranchIntegral

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coordinate_fderiv_apply {F : Vec → Vec} (hF : Differentiable ℝ F)
    (x v : Vec) (i : Fin 3) : fderiv ℝ (fun y => F y i) x v = (fderiv ℝ F x v) i := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L v)
    (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hF x).hasFDerivAt).fderiv)

lemma BoundedSmooth.coordinate_bounds {F : Vec → Vec} (hF : BoundedSmooth F) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : Vec, ‖F x‖≤C ∧
      (∀ i v, |fderiv ℝ (fun y => F y i) x v|≤C*‖v‖) ∧ ∀ i, |curl F x i|≤C := by
  obtain ⟨A,hA⟩ := hF.2 0
  obtain ⟨D,hD⟩ := hF.2 1
  have hD' : ∀ x, ‖fderiv ℝ F x‖≤ max D 0 := by
    intro x
    have hh : ‖fderiv ℝ F x‖≤D := by simpa only [norm_iteratedFDeriv_one] using hD x
    exact hh.trans (le_max_left _ _)
  have hfd (x v : Vec) (i : Fin 3) : |fderiv ℝ (fun y => F y i) x v|≤ max D 0*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.1.differentiable (by simp))]
    exact (norm_coordinate_le _ i).trans (((fderiv ℝ F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg v)))
  refine ⟨max A 0+2*max D 0,by positivity,?_⟩
  intro x
  refine ⟨?_,?_,?_⟩
  · have hh : ‖F x‖≤A := by simpa only [norm_iteratedFDeriv_zero] using hA x
    linarith [le_max_left A 0,le_max_right D 0]
  · intro i v
    exact (hfd x v i).trans (mul_le_mul_of_nonneg_right (by
      linarith [le_max_right A 0,le_max_right D 0]) (norm_nonneg v))
  · intro i
    have he : curl F x i=spatialPartial (fun y => F y (curlB i)) x (curlA i)-
        spatialPartial (fun y => F y (curlA i)) x (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    rw [he]
    have ha := hfd x (basis (curlA i)) (curlB i)
    have hb := hfd x (basis (curlB i)) (curlA i)
    simp only [show ∀ j : Fin 3, ‖basis j‖=1 by intro j; simp [basis,PiLp.norm_single],mul_one] at ha hb
    exact (abs_sub _ _).trans ((add_le_add ha hb).trans (by linarith [le_max_right A 0]))

lemma freeWave_bound_global {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    {C : ℝ} (hC : 0≤C) (hg0 : ∀ x, |g x|≤C)
    (hgd : ∀ x n : Vec, ‖n‖=1 → |fderiv ℝ g x n|≤C)
    (hh0 : ∀ x, |h x|≤C) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Vec) :
    |freeWave g h (t,x)|≤3*C := by
  have h₁ := abs_sphere_integral_le (fun n : Sphere => hg0 (x+t • n.1))
  have h₂ := abs_sphere_integral_le (fun n : Sphere => hgd (x+t • n.1) n.1
    (mem_sphere_zero_iff_norm.mp n.2))
  have h₃ := abs_sphere_integral_le (fun n : Sphere => hh0 (x+t • n.1))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  rw [freeWave_sphere hg]
  calc
    _ ≤ (4*Real.pi)⁻¹*(C*(4*Real.pi)+t*(C*(4*Real.pi)))+
        (4*Real.pi)⁻¹*(t*(C*(4*Real.pi))) := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_of_nonneg hp,abs_mul,abs_of_nonneg hp]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hp
        exact (abs_add_le _ _).trans (add_le_add h₁ (by
          rw [abs_mul,abs_of_nonneg ht.1]
          exact mul_le_mul_of_nonneg_left h₂ ht.1))
      · apply mul_le_mul_of_nonneg_left _ hp
        rw [abs_mul,abs_of_nonneg ht.1]
        exact mul_le_mul_of_nonneg_left h₃ ht.1
    _ = C+2*t*C := by field_simp; ring
    _ ≤ 3*C := by nlinarith [ht.2]

lemma BoundedSmooth.freeWave_coordinate_bound {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x : Vec,
      |freeWave (fun y => E y i) (fun y => curl B y i) (t,x)|≤C ∧
      |freeWave (fun y => B y i) (fun y => -curl E y i) (t,x)|≤C := by
  obtain ⟨A,hA,hAb⟩ := hE.coordinate_bounds
  obtain ⟨D,hD,hDb⟩ := hB.coordinate_bounds
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  refine ⟨3*(A+D),by positivity,?_⟩
  intro t ht x
  constructor
  · apply freeWave_bound_global (hproj.comp hE.1) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hAb y).1.trans (le_add_of_nonneg_right hD))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => E u i) y n|≤A := by simpa only [hn,mul_one] using (hAb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_right hD)
    · intro y
      exact (hDb y).2.2 i |>.trans (le_add_of_nonneg_left hA)
  · apply freeWave_bound_global (hproj.comp hB.1) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hDb y).1.trans (le_add_of_nonneg_left hA))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => B u i) y n|≤D := by simpa only [hn,mul_one] using (hDb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_left hA)
    · intro y
      rw [abs_neg]
      exact (hAb y).2.2 i |>.trans (le_add_of_nonneg_right hD)

lemma electricConeBoundary_datum_bound_global {d : Datum} (hd : Admissible d)
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |electricConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumElectricFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_bound hd.2.2.2.1 hd.2.2.2.2.1 i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro t ht x
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_cone_flux i hflux ht.1 x n)
  have hrho : |∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure|≤
      (t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    have hn : |n.1 i|≤1 := by
      exact (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        (hmom (x+t • n.1)).1 (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = t*D := by ring
  have hj : |waveK (fun y => current d.f₀ y i) (t,x)|≤t*D :=
    waveK_bound_of_bounded (fun y => (norm_coordinate_le (current d.f₀ y) i).trans (hmom y).2) ht.1.le x
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure)|≤t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hrho hp
      _ = t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).1
  simp only [electricConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)) hj)).trans (by
      nlinarith [ht.2])

lemma magneticConeBoundary_datum_bound_global {d : Datum} (hd : Admissible d)
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |magneticConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumMagneticFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_bound hd.2.2.2.1 hd.2.2.2.2.1 i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro t ht x
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_magnetic_cone_flux i hflux ht.1 x n)
  have hem (n : Sphere) (j k : Fin 3) :
      |t*n.1 j*current d.f₀ (x+t • n.1) k|≤t*D := by
    have hn : |n.1 j|≤1 :=
      (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    have hj : |current d.f₀ (x+t • n.1) k|≤D :=
      (norm_coordinate_le _ k).trans (hmom _).2
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        hj (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = _ := by ring
  have hj : |∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure|≤
      (2*t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    exact (abs_sub _ _).trans ((add_le_add (hem n _ _) (hem n _ _)).trans (by ring_nf; rfl))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure)|≤2*t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((2*t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hj hp
      _ = 2*t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).2
  simp only [magneticConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)).trans (by
      nlinarith [ht.2])

lemma datum_boundary_global_bound {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ (∀ x, ‖d.E₀ x‖≤C ∧ ‖d.B₀ x‖≤C) ∧
      ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
        ‖electricBoundaryField (datumBoundarySolution d) t x‖≤C ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤C := by
  choose CE hCE hEe using fun i : Fin 3 => electricConeBoundary_datum_bound_global hd i
  choose CB hCB hBb using fun i : Fin 3 => magneticConeBoundary_datum_bound_global hd i
  obtain ⟨E₀,hE₀⟩ := hd.2.2.2.1.2 0
  obtain ⟨B₀,hB₀⟩ := hd.2.2.2.2.1.2 0
  let S := (∑ i : Fin 3, CE i)+(∑ i : Fin 3, CB i)
  have hS : 0≤S := add_nonneg (Finset.sum_nonneg (fun i _ => hCE i))
    (Finset.sum_nonneg (fun i _ => hCB i))
  let C := 3*S+max E₀ 0+max B₀ 0
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_,?_⟩
  · intro x
    constructor
    · have hh : ‖d.E₀ x‖≤E₀ := by simpa only [norm_iteratedFDeriv_zero] using hE₀ x
      dsimp [C]
      linarith [le_max_left E₀ 0,le_max_right B₀ 0]
    · have hh : ‖d.B₀ x‖≤B₀ := by simpa only [norm_iteratedFDeriv_zero] using hB₀ x
      dsimp [C]
      linarith [le_max_left B₀ 0,le_max_right E₀ 0]
  · intro t ht x
    have hEe' : ‖electricBoundaryField (datumBoundarySolution d) t x‖≤3*S := by
      apply norm_le_three_of_coordinate_bound hS
      intro i
      exact (hEe i t ht x).trans (by
        have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hCE j) (Finset.mem_univ i)
        have hh' : 0≤∑ j : Fin 3, CB j := Finset.sum_nonneg (fun j _ => hCB j)
        dsimp [S]
        linarith)
    have hBb' : ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤3*S := by
      apply norm_le_three_of_coordinate_bound hS
      intro i
      exact (hBb i t ht x).trans (by
        have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hCB j) (Finset.mem_univ i)
        have hh' : 0≤∑ j : Fin 3, CE j := Finset.sum_nonneg (fun j _ => hCE j)
        dsimp [S]
        linarith)
    have hh : 3*S≤C := by dsimp [C]; linarith [le_max_right E₀ 0,le_max_right B₀ 0]
    exact ⟨hEe'.trans hh,hBb'.trans hh⟩

lemma smooth_compact_lipschitz {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y, ‖f y-f x‖≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := (hf.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hc.fderiv ℝ)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x y
  exact (convex_univ : Convex ℝ (univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by norm_num) z)
    (fun z _ => (hD z).trans (le_max_left _ _)) (mem_univ x) (mem_univ y)

lemma BoundedSmooth.iterated_lipschitz {F : Vec → Vec} (hF : BoundedSmooth F) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y,
      ‖iteratedFDeriv ℝ n F y-iteratedFDeriv ℝ n F x‖≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := hF.2 (n+1)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x y
  exact (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ContDiff.differentiable_iteratedFDeriv (n:=∞) (m:=n) (by exact_mod_cast ENat.natCast_lt_top n) hF.1 z)
    (fun z _ => by
      rw [norm_fderiv_iteratedFDeriv]
      exact (hD z).trans (le_max_left _ _))
    (mem_univ x) (mem_univ y)

lemma BoundedSmooth.spatial_lipschitz {F : Vec → Vec} (hF : BoundedSmooth F) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y : Vec, ‖F y-F x‖≤C*‖y-x‖ ∧
      (∀ i v, |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤C*‖y-x‖*‖v‖) ∧
      ∀ i, |curl F y i-curl F x i|≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := hF.2 1
  let A := max D 0
  have hA : 0≤A := le_max_right _ _
  have hval (x y : Vec) : ‖F y-F x‖≤A*‖y-x‖ := by
    apply (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hF.1.differentiable (by simp) z) _ (mem_univ x) (mem_univ y)
    intro z _
    have hh : ‖fderiv ℝ F z‖≤D := by simpa only [norm_iteratedFDeriv_one] using hD z
    exact hh.trans (le_max_left _ _)
  obtain ⟨B,hB,hb⟩ := hF.iterated_lipschitz 1
  have hder (x y v : Vec) : ‖fderiv ℝ F y v-fderiv ℝ F x v‖≤B*‖y-x‖*‖v‖ := by
    have hh := (iteratedFDeriv ℝ 1 F y-iteratedFDeriv ℝ 1 F x).le_opNorm (fun _ => v)
    simp only [sub_apply,iteratedFDeriv_one_apply,Fin.prod_univ_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hb x y) (norm_nonneg v))
  have hder' (x y v : Vec) (i : Fin 3) :
      |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤B*‖y-x‖*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.1.differentiable (by simp)),coordinate_fderiv_apply (hF.1.differentiable (by simp))]
    exact (norm_coordinate_le (fderiv ℝ F y v-fderiv ℝ F x v) i).trans (hder x y v)
  refine ⟨A+2*B,by positivity,?_⟩
  intro x y
  refine ⟨(hval x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)),?_,?_⟩
  · intro i v
    exact (hder' x y v i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)) (norm_nonneg _))
  · intro i
    have he (z : Vec) : curl F z i=spatialPartial (fun u => F u (curlB i)) z (curlA i)-
        spatialPartial (fun u => F u (curlA i)) z (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    rw [he y,he x,show ∀ a b c d : ℝ, (a-b)-(c-d)=(a-c)-(b-d) by intros; ring]
    have ha := hder' x y (basis (curlA i)) (curlB i)
    have hb' := hder' x y (basis (curlB i)) (curlA i)
    simp only [show ∀ j : Fin 3, ‖basis j‖=1 by intro j; simp [basis,PiLp.norm_single],mul_one] at ha hb'
    exact (abs_sub _ _).trans ((add_le_add ha hb').trans (by nlinarith [norm_nonneg (y-x)]))

lemma uniform_datum_velocity_integral_lipschitz {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y n : Vec, ‖n‖=1 →
      ‖(∫ v : Vec, f (y,v) • H (n,v))-(∫ v : Vec, f (x,v) • H (n,v))‖≤C*‖y-x‖ := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  obtain ⟨A,hA,hfLip⟩ := smooth_compact_lipschitz hf hc
  obtain ⟨B,hB⟩ := ((isCompact_sphere (0:Vec) 1).prod hK).exists_bound_of_continuousOn
    (hH.mono (by intro p hp; exact ⟨hp.1,mem_univ _⟩))
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨A*D*(volume K).toReal,by positivity,?_⟩
  intro x y n hn
  have hn' : n∈sphere (0:Vec) 1 := mem_sphere_zero_iff_norm.mpr hn
  have hint (z : Vec) : Integrable (fun v => f (z,v) • H (n,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).smul
        (hH.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hn',mem_univ v⟩))
    · exact HasCompactSupport.intro hK (fun v hv => by rw [hz z v hv,zero_smul])
  rw [← integral_sub (hint y) (hint x)]
  have he : (∫ v in K, f (y,v) • H (n,v)-f (x,v) • H (n,v))=
      ∫ v, f (y,v) • H (n,v)-f (x,v) • H (n,v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    simp only [hz _ v hv,zero_smul,sub_self]
  rw [← he]
  have hb : ∀ v∈K, ‖f (y,v) • H (n,v)-f (x,v) • H (n,v)‖≤ A*‖y-x‖*D := by
    intro v hv
    rw [← sub_smul,norm_smul]
    apply mul_le_mul _ ((hB (n,v) ⟨hn',hv⟩).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_eq_left (norm_nonneg _)] using
      hfLip (x,v) (y,v)
  exact (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb).trans_eq (by simp only [Measure.real]; ring)

lemma abs_sphere_integral_sub_le {F G : Sphere → ℝ} {C : ℝ}
    (hF : Continuous F) (hG : Continuous G) (h : ∀ n, |F n-G n|≤C) :
    |(∫ n, F n ∂sphereMeasure)-(∫ n, G n ∂sphereMeasure)|≤C*(4*Real.pi) := by
  rw [← integral_sub (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact abs_sphere_integral_le h

lemma waveK_lipschitz {g : Vec → ℝ} (hg : Continuous g) {C : ℝ}
    (h : ∀ x y, |g y-g x|≤C*‖y-x‖) {t : ℝ} (ht : 0≤t) (x y : Vec) :
    |waveK g (t,y)-waveK g (t,x)|≤t*C*‖y-x‖ := by
  have hc (x : Vec) : Continuous (fun n : Sphere => g (x+t • n.1)) :=
    hg.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have hh := abs_sphere_integral_sub_le (hc y) (hc x) (C:=C*‖y-x‖) (by
    intro n
    simpa only [add_sub_add_right_eq_sub] using h (x+t • n.1) (y+t • n.1))
  simp only [waveK,← mul_sub]
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹),abs_mul,abs_of_nonneg ht]
  calc
    _ ≤ (4*Real.pi)⁻¹*(t*(C*‖y-x‖*(4*Real.pi))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh ht) (by positivity)
    _ = t*C*‖y-x‖ := by field_simp

lemma freeWave_lipschitz {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : Continuous h)
    {C : ℝ} (hC : 0≤C)
    (hg0 : ∀ x y, |g y-g x|≤C*‖y-x‖)
    (hgd : ∀ x y n : Vec, ‖n‖=1 → |fderiv ℝ g y n-fderiv ℝ g x n|≤C*‖y-x‖)
    (hh0 : ∀ x y, |h y-h x|≤C*‖y-x‖)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x y : Vec) :
    |freeWave g h (t,y)-freeWave g h (t,x)|≤3*C*‖y-x‖ := by
  have hc (z : Vec) : Continuous (fun n : Sphere => g (z+t • n.1)) :=
    hg.continuous.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have hd (z : Vec) : Continuous (fun n : Sphere => fderiv ℝ g (z+t • n.1) n.1) :=
    ((hg.continuous_fderiv (by simp)).comp
      (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))).clm_apply continuous_subtype_val
  have hh' (z : Vec) : Continuous (fun n : Sphere => h (z+t • n.1)) :=
    hh.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have A := abs_sphere_integral_sub_le (hc y) (hc x) (by intro n; simpa only [add_sub_add_right_eq_sub] using hg0 (x+t • n.1) (y+t • n.1))
  have B := abs_sphere_integral_sub_le (hd y) (hd x) (by intro n; simpa only [add_sub_add_right_eq_sub] using hgd (x+t • n.1) (y+t • n.1) n.1 (mem_sphere_zero_iff_norm.mp n.2))
  have D := abs_sphere_integral_sub_le (hh' y) (hh' x) (by intro n; simpa only [add_sub_add_right_eq_sub] using hh0 (x+t • n.1) (y+t • n.1))
  rw [freeWave_sphere hg,freeWave_sphere hg]
  have he : ∀ a b c d e f : ℝ, (4*Real.pi)⁻¹*(a+t*b)+(4*Real.pi)⁻¹*(t*c)-
      ((4*Real.pi)⁻¹*(d+t*e)+(4*Real.pi)⁻¹*(t*f))=
      (4*Real.pi)⁻¹*((a-d)+t*(b-e)+t*(c-f)) := by intros; ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  calc
    _ ≤ (4*Real.pi)⁻¹*(C*‖y-x‖*(4*Real.pi)+t*(C*‖y-x‖*(4*Real.pi))+t*(C*‖y-x‖*(4*Real.pi))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (abs_add_le _ _).trans
      apply add_le_add
      · apply (abs_add_le _ _).trans
        apply add_le_add A
        simpa only [abs_mul,abs_of_nonneg ht.1] using mul_le_mul_of_nonneg_left B ht.1
      · simpa only [abs_mul,abs_of_nonneg ht.1] using mul_le_mul_of_nonneg_left D ht.1
    _ = (1+2*t)*C*‖y-x‖ := by field_simp; ring
    _ ≤ 3*C*‖y-x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) hC

lemma datum_moment_lipschitz {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y, |rho d.f₀ y-rho d.f₀ x|≤C*‖y-x‖ ∧
      ‖current d.f₀ y-current d.f₀ x‖≤C*‖y-x‖ := by
  obtain ⟨A,hA,ha⟩ := uniform_datum_velocity_integral_lipschitz
    (hd.1.of_le (by simp)) hd.2.1 (H:=fun _ => (1:ℝ)) continuousOn_const
  obtain ⟨B,hB,hb⟩ := uniform_datum_velocity_integral_lipschitz
    (hd.1.of_le (by simp)) hd.2.1
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn)
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro x y
  constructor
  · have hh := ha x y (basis 0) (by simp [basis,PiLp.norm_single])
    simp only [smul_eq_mul,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (norm_nonneg _))
  · exact (hb x y (basis 0) (by simp [basis,PiLp.norm_single])).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))

lemma BoundedSmooth.freeWave_coordinate_lipschitz {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |freeWave (fun z => E z i) (fun z => curl B z i) (t,y)-
        freeWave (fun z => E z i) (fun z => curl B z i) (t,x)|≤C*‖y-x‖ ∧
      |freeWave (fun z => B z i) (fun z => -curl E z i) (t,y)-
        freeWave (fun z => B z i) (fun z => -curl E z i) (t,x)|≤C*‖y-x‖ := by
  obtain ⟨A,hA,hAb⟩ := hE.spatial_lipschitz
  obtain ⟨D,hD,hDb⟩ := hB.spatial_lipschitz
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  refine ⟨3*(A+D),by positivity,?_⟩
  intro t ht x y
  constructor
  · apply freeWave_lipschitz (hproj.comp hE.1)
      (hproj.continuous.comp (contDiff_curl hB.1).continuous) (add_nonneg hA hD) _ _ _ ht
    · intro z z'
      exact (norm_coordinate_le (E z'-E z) i).trans ((hAb z z').1.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _)))
    · intro z z' n hn
      have hh : |fderiv ℝ (fun u => E u i) z' n-fderiv ℝ (fun u => E u i) z n|≤A*‖z'-z‖ := by
        simpa only [hn,mul_one] using (hAb z z').2.1 i n
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _))
    · intro z z'
      exact ((hDb z z').2.2 i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))
  · apply freeWave_lipschitz (hproj.comp hB.1)
      ((hproj.continuous.comp (contDiff_curl hE.1).continuous).neg) (add_nonneg hA hD) _ _ _ ht
    · intro z z'
      exact (norm_coordinate_le (B z'-B z) i).trans ((hDb z z').1.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _)))
    · intro z z' n hn
      have hh : |fderiv ℝ (fun u => B u i) z' n-fderiv ℝ (fun u => B u i) z n|≤D*‖z'-z‖ := by
        simpa only [hn,mul_one] using (hDb z z').2.1 i n
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))
    · intro z z'
      simpa only [Function.comp_apply,Pi.neg_apply,neg_sub_neg,abs_sub_comm] using
        ((hAb z z').2.2 i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _))

lemma datum_sphere_flux_lipschitz {f : Phase → ℝ} {H : Vec × Vec → Vec}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |(4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, f (y+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)-
        (4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, f (x+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)|≤C*‖y-x‖ := by
  obtain ⟨C,hC,hb⟩ := uniform_datum_velocity_integral_lipschitz hf hc hH
  refine ⟨C,hC,?_⟩
  intro t ht x y
  have hn (n : Sphere) : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have hc' (z : Vec) : Continuous (fun n : Sphere =>
      t*dot n.1 (∫ v, f (z+t • n.1,v) • H (-n.1,v))) := by
    have hI : Continuous (fun n : Sphere => ∫ v, f (z+t • n.1,v) • H (-n.1,v)) := by
      apply (continuousOn_datum_velocity_integral hf.continuous hc hH).comp_continuous
        ((continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)).prodMk continuous_subtype_val.neg)
      intro n
      exact ⟨mem_univ _,by simpa only [mem_sphere_zero_iff_norm,Pi.neg_apply,norm_neg] using hn n⟩
    exact continuous_const.mul ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_subtype_val.prodMk hI))
  have hh := abs_sphere_integral_sub_le (hc' y) (hc' x) (C:=C*‖y-x‖) (by
    intro n
    rw [← mul_sub,← dot_sub_right,abs_mul,abs_of_nonneg ht.1]
    have hbd : ‖(∫ v, f (y+t • n.1,v) • H (-n.1,v))-
        (∫ v, f (x+t • n.1,v) • H (-n.1,v))‖≤C*‖y-x‖ := by
      simpa only [add_sub_add_right_eq_sub] using hb (x+t • n.1) (y+t • n.1) (-n.1) (by simpa only [norm_neg] using hn n)
    exact (mul_le_mul_of_nonneg_left ((abs_dot_le _ _).trans
      (by simpa only [hn n,one_mul] using hbd)) ht.1).trans
        (mul_le_of_le_one_left (by positivity) ht.2))
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)

lemma weighted_sphere_mean_lipschitz {g : Vec → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : 0≤C) (h : ∀ x y, |g y-g x|≤C*‖y-x‖)
    {w : Sphere → ℝ} (hw : Continuous w) (hwb : ∀ n, |w n|≤1)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x y : Vec) :
    |(4*Real.pi)⁻¹*(∫ n : Sphere, t*w n*g (y+t • n.1) ∂sphereMeasure)-
      (4*Real.pi)⁻¹*(∫ n : Sphere, t*w n*g (x+t • n.1) ∂sphereMeasure)|≤C*‖y-x‖ := by
  have hc (z : Vec) : Continuous (fun n : Sphere => t*w n*g (z+t • n.1)) :=
    (continuous_const.mul hw).mul (hg.comp (continuous_const.add
      ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
  have hh := abs_sphere_integral_sub_le (hc y) (hc x) (C:=C*‖y-x‖) (by
    intro n
    rw [← mul_sub,abs_mul,abs_mul,abs_of_nonneg ht.1]
    have hh' : |g (y+t • n.1)-g (x+t • n.1)|≤C*‖y-x‖ := by
      simpa only [add_sub_add_right_eq_sub] using h (x+t • n.1) (y+t • n.1)
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hwb n) ht.1) hh' (abs_nonneg _) (by simpa only [mul_one] using ht.1)).trans
      (by simpa only [mul_one] using mul_le_of_le_one_left (by positivity : 0≤C*‖y-x‖) ht.2))
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)

lemma datum_initial_electric_flux_normalised (d : Datum) (i : Fin 3)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    t^2*dot n.1 (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))=
      t*dot n.1 (∫ v, d.f₀ (x+t • n.1,v) • datumElectricFluxKernel i (-n.1,v)) := by
  have hn : ‖t • n.1‖=t := by simp only [norm_smul,Real.norm_of_nonneg ht.le,mem_sphere_zero_iff_norm.mp n.2,mul_one]
  rw [datumElectricFlux_eq,coneRadius_add,coneDirection_add,hn,inv_smul_smul₀ ht.ne',dot_smul_right]
  field_simp

lemma datum_initial_magnetic_flux_normalised (d : Datum) (i : Fin 3)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    t^2*dot n.1 (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))=
      t*dot n.1 (∫ v, d.f₀ (x+t • n.1,v) • datumMagneticFluxKernel i (-n.1,v)) := by
  have hn : ‖t • n.1‖=t := by simp only [norm_smul,Real.norm_of_nonneg ht.le,mem_sphere_zero_iff_norm.mp n.2,mul_one]
  rw [datumMagneticFlux_eq,coneRadius_add,coneDirection_add,hn,inv_smul_smul₀ ht.ne',dot_smul_right]
  field_simp

lemma electricConeBoundary_datum_lipschitz {d : Datum} (hd : Admissible d) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |electricConeBoundary (datumBoundarySolution d) t y i 0-
        electricConeBoundary (datumBoundarySolution d) t x i 0|≤C*‖y-x‖ := by
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_lipschitz hd.2.2.2.1 hd.2.2.2.2.1 i
  obtain ⟨B,hB,hflux⟩ := datum_sphere_flux_lipschitz (hd.1.of_le (by simp)) hd.2.1
    (continuousOn_datumElectricFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := datum_moment_lipschitz hd
  have hm : Continuous (rho d.f₀) ∧ Continuous (current d.f₀) := by
    constructor
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm,Real.norm_eq_abs] using (hmom y x).1)).continuous
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj : Continuous (fun v : Vec => v i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro t ht x y
  have hrho := weighted_sphere_mean_lipschitz hm.1 hD (fun x y => (hmom x y).1)
    (hproj.comp continuous_subtype_val) (fun n => (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2))
    ⟨ht.1.le,ht.2⟩ x y
  have hj := waveK_lipschitz (hproj.comp hm.2)
    (fun x y => (norm_coordinate_le (current d.f₀ y-current d.f₀ x) i).trans (hmom x y).2) ht.1.le x y
  have he : t*D*‖y-x‖≤D*‖y-x‖ := by
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hD ht.2) (norm_nonneg _)
  simp only [electricConeBoundary,sub_zero]
  simp_rw [datum_initial_electric_flux_normalised d i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c e a' b' c' e' : ℝ) : (a-b-c-e)-(a'-b'-c'-e')=(a-a')-(b-b')-(c-c')-(e-e') := by ring
  rw [halg]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).1
      (hflux t ⟨ht.1.le,ht.2⟩ x y))) hrho)) (hj.trans he))).trans_eq (by ring)

lemma magneticConeBoundary_datum_lipschitz {d : Datum} (hd : Admissible d) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |magneticConeBoundary (datumBoundarySolution d) t y i 0-
        magneticConeBoundary (datumBoundarySolution d) t x i 0|≤C*‖y-x‖ := by
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_lipschitz hd.2.2.2.1 hd.2.2.2.2.1 i
  obtain ⟨B,hB,hflux⟩ := datum_sphere_flux_lipschitz (hd.1.of_le (by simp)) hd.2.1
    (continuousOn_datumMagneticFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := datum_moment_lipschitz hd
  have hjc : Continuous (current d.f₀) := (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
    simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj (j : Fin 3) : Continuous (fun v : Vec => v j) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro t ht x y
  let F : Vec → Sphere → ℝ := fun z n => t*n.1 (curlA i)*current d.f₀ (z+t • n.1) (curlB i)-
    t*n.1 (curlB i)*current d.f₀ (z+t • n.1) (curlA i)
  have hfc (z : Vec) : Continuous (F z) := by
    have hg (j k : Fin 3) : Continuous (fun n : Sphere => t*n.1 j*current d.f₀ (z+t • n.1) k) :=
      (continuous_const.mul ((hproj j).comp continuous_subtype_val)).mul
        (((hproj k).comp hjc).comp (continuous_const.add
          ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
    exact (hg _ _).sub (hg _ _)
  have hh := abs_sphere_integral_sub_le (hfc y) (hfc x) (C:=2*D*‖y-x‖) (by
    intro n
    have hterm (j k : Fin 3) : |t*n.1 j*current d.f₀ (y+t • n.1) k-
        t*n.1 j*current d.f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
      rw [← mul_sub,abs_mul,abs_mul,abs_of_pos ht.1]
      have hn : |n.1 j|≤1 := (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
      have hj : |current d.f₀ (y+t • n.1) k-current d.f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
        simpa only [PiLp.sub_apply,add_sub_add_right_eq_sub] using
          (norm_coordinate_le (current d.f₀ (y+t • n.1)-current d.f₀ (x+t • n.1)) k).trans
            (hmom (x+t • n.1) (y+t • n.1)).2
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le) hj (abs_nonneg _) (by simpa using ht.1.le)).trans
        (by simpa only [mul_one] using mul_le_of_le_one_left (by positivity : 0≤D*‖y-x‖) ht.2)
    dsimp [F]
    rw [show ∀ a b c e : ℝ, (a-b)-(c-e)=(a-c)-(b-e) by intros; ring]
    exact ((abs_sub _ _).trans (add_le_add (hterm _ _) (hterm _ _))).trans_eq (by ring))
  have hj : |(4*Real.pi)⁻¹*(∫ n, F y n ∂sphereMeasure)-
      (4*Real.pi)⁻¹*(∫ n, F x n ∂sphereMeasure)|≤2*D*‖y-x‖ := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)
  simp only [magneticConeBoundary,sub_zero]
  simp_rw [datum_initial_magnetic_flux_normalised d i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c a' b' c' : ℝ) : (a-b+c)-(a'-b'+c')=(a-a')-(b-b')+(c-c') := by ring
  rw [halg]
  exact ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).2 (hflux t ⟨ht.1.le,ht.2⟩ x y))) hj)).trans_eq (by ring)

lemma datum_boundary_global_lipschitz {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ (∀ x y, ‖d.E₀ y-d.E₀ x‖≤C*‖y-x‖ ∧ ‖d.B₀ y-d.B₀ x‖≤C*‖y-x‖) ∧
      ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
        ‖electricBoundaryField (datumBoundarySolution d) t y-electricBoundaryField (datumBoundarySolution d) t x‖≤C*‖y-x‖ ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t y-magneticBoundaryField (datumBoundarySolution d) t x‖≤C*‖y-x‖ := by
  obtain ⟨E,hE,hEb⟩ := hd.2.2.2.1.spatial_lipschitz
  obtain ⟨B,hB,hBb⟩ := hd.2.2.2.2.1.spatial_lipschitz
  choose CE hCE he using electricConeBoundary_datum_lipschitz hd
  choose CB hCB hb using magneticConeBoundary_datum_lipschitz hd
  let S := E+B+∑ i : Fin 3, (CE i+CB i)
  have hS : 0≤S := by dsimp [S]; exact add_nonneg (add_nonneg hE hB) (Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i))
  have hEC (i : Fin 3) : CE i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCB i]
  have hBC (i : Fin 3) : CB i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCE i]
  refine ⟨3*S,by positivity,?_,?_⟩
  · intro x y
    have hh : 0≤∑ i : Fin 3, (CE i+CB i) := Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i)
    constructor
    · exact ((hEb x y).1).trans (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith) (norm_nonneg _))
    · exact ((hBb x y).1).trans (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith) (norm_nonneg _))
  · intro t ht x y
    constructor
    · have hh := norm_le_three_of_coordinate_bound (mul_nonneg hS (norm_nonneg (y-x)))
        (v:=electricBoundaryField (datumBoundarySolution d) t y-electricBoundaryField (datumBoundarySolution d) t x)
        (fun i => (he i t ht x y).trans (mul_le_mul_of_nonneg_right (hEC i) (norm_nonneg _)))
      exact hh.trans_eq (by ring)
    · have hh := norm_le_three_of_coordinate_bound (mul_nonneg hS (norm_nonneg (y-x)))
        (v:=magneticBoundaryField (datumBoundarySolution d) t y-magneticBoundaryField (datumBoundarySolution d) t x)
        (fun i => (hb i t ht x y).trans (mul_le_mul_of_nonneg_right (hBC i) (norm_nonneg _)))
      exact hh.trans_eq (by ring)

end RVM
end

end OAI
