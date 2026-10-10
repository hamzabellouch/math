import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardBoundary
import OAI.Analysis.VlasovMaxwell.Retarded.UniformDatumKernel

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coordinate_bounds_of_low_jets {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    {C : ℝ} (hC : 0≤C) (hjets : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k F x‖≤C) :
    ∀ x : Vec, ‖F x‖≤3*C ∧
      (∀ i v, |fderiv ℝ (fun y => F y i) x v|≤(3*C)*‖v‖) ∧ ∀ i, |curl F x i|≤3*C := by
  have hA := hjets 0 (by norm_num)
  have hD := hjets 1 (by norm_num)
  have hD' : ∀ x, ‖fderiv ℝ F x‖≤ C := by
    intro x
    have hh : ‖fderiv ℝ F x‖≤C := by simpa only [norm_iteratedFDeriv_one] using hD x
    exact hh.trans le_rfl
  have hfd (x v : Vec) (i : Fin 3) : |fderiv ℝ (fun y => F y i) x v|≤ C*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.differentiable (by simp))]
    exact (norm_coordinate_le _ i).trans (((fderiv ℝ F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg v)))
  intro x
  refine ⟨?_,?_,?_⟩
  · have hh : ‖F x‖≤C := by simpa only [norm_iteratedFDeriv_zero] using hA x
    linarith [hC]
  · intro i v
    exact (hfd x v i).trans (mul_le_mul_of_nonneg_right (by
      linarith [hC]) (norm_nonneg v))
  · intro i
    have he : curl F x i=spatialPartial (fun y => F y (curlB i)) x (curlA i)-
        spatialPartial (fun y => F y (curlA i)) x (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    rw [he]
    have ha := hfd x (basis (curlA i)) (curlB i)
    have hb := hfd x (basis (curlB i)) (curlA i)
    simp only [show ∀ j : Fin 3, ‖basis j‖=1 by intro j; simp [basis,PiLp.norm_single],mul_one] at ha hb
    exact (abs_sub _ _).trans ((add_le_add ha hb).trans (by linarith [hC]))

lemma iterated_lipschitz_of_bound {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) {C : ℝ} (hb : ∀ x, ‖iteratedFDeriv ℝ (n+1) F x‖≤C) (x y : Vec) :
    ‖iteratedFDeriv ℝ n F y-iteratedFDeriv ℝ n F x‖≤C*‖y-x‖ := by
  exact (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ContDiff.differentiable_iteratedFDeriv (n:=∞) (m:=n) (by exact_mod_cast ENat.natCast_lt_top n) hF z)
    (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hb z) (mem_univ x) (mem_univ y)

lemma spatial_lipschitz_of_low_jets {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    {C : ℝ} (hC : 0≤C) (hjets : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k F x‖≤C) :
    ∀ x y : Vec, ‖F y-F x‖≤(3*C)*‖y-x‖ ∧
      (∀ i v, |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤(3*C)*‖y-x‖*‖v‖) ∧
      ∀ i, |curl F y i-curl F x i|≤(3*C)*‖y-x‖ := by
  have hD := hjets 1 (by norm_num)
  let A := C
  have hA : 0≤A := hC
  have hval (x y : Vec) : ‖F y-F x‖≤A*‖y-x‖ := by
    apply (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hF.differentiable (by simp) z) _ (mem_univ x) (mem_univ y)
    intro z _
    have hh : ‖fderiv ℝ F z‖≤C := by simpa only [norm_iteratedFDeriv_one] using hD z
    exact hh.trans le_rfl
  let B := C
  have hB : 0≤B := hC
  have hb := iterated_lipschitz_of_bound hF 1 (hjets 2 le_rfl)
  have hder (x y v : Vec) : ‖fderiv ℝ F y v-fderiv ℝ F x v‖≤B*‖y-x‖*‖v‖ := by
    have hh := (iteratedFDeriv ℝ 1 F y-iteratedFDeriv ℝ 1 F x).le_opNorm (fun _ => v)
    simp only [sub_apply,iteratedFDeriv_one_apply,Fin.prod_univ_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hb x y) (norm_nonneg v))
  have hder' (x y v : Vec) (i : Fin 3) :
      |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤B*‖y-x‖*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.differentiable (by simp)),coordinate_fderiv_apply (hF.differentiable (by simp))]
    exact (norm_coordinate_le (fderiv ℝ F y v-fderiv ℝ F x v) i).trans (hder x y v)
  suffices hh : ∀ x y : Vec, ‖F y-F x‖≤(A+2*B)*‖y-x‖ ∧
    (∀ i v, |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤(A+2*B)*‖y-x‖*‖v‖) ∧
    ∀ i, |curl F y i-curl F x i|≤(A+2*B)*‖y-x‖ by
    convert hh using 1
    dsimp [A,B]
    ring_nf
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

lemma freeWave_coordinate_bound_of_low_jets {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    {C : ℝ} (hC : 0≤C)
    (hEj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k E x‖≤C)
    (hBj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k B x‖≤C) (i : Fin 3) :
    ∀ t∈Icc (0:ℝ) 1, ∀ x : Vec,
      |freeWave (fun y => E y i) (fun y => curl B y i) (t,x)|≤18*C ∧
      |freeWave (fun y => B y i) (fun y => -curl E y i) (t,x)|≤18*C := by
  let A := 3*C
  let D := 3*C
  have hA : 0≤A := by positivity
  have hD : 0≤D := by positivity
  have hAb := coordinate_bounds_of_low_jets hE hC hEj
  have hDb := coordinate_bounds_of_low_jets hB hC hBj
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  have he : 18*C=3*(A+D) := by dsimp [A,D]; ring
  rw [he]
  intro t ht x
  constructor
  · apply freeWave_bound_global (hproj.comp hE) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hAb y).1.trans (le_add_of_nonneg_right hD))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => E u i) y n|≤A := by simpa only [hn,mul_one] using (hAb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_right hD)
    · intro y
      exact (hDb y).2.2 i |>.trans (le_add_of_nonneg_left hA)
  · apply freeWave_bound_global (hproj.comp hB) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hDb y).1.trans (le_add_of_nonneg_left hA))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => B u i) y n|≤D := by simpa only [hn,mul_one] using (hDb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_left hA)
    · intro y
      rw [abs_neg]
      exact (hAb y).2.2 i |>.trans (le_add_of_nonneg_right hD)

lemma freeWave_coordinate_lipschitz_of_low_jets {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    {C : ℝ} (hC : 0≤C)
    (hEj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k E x‖≤C)
    (hBj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k B x‖≤C) (i : Fin 3) :
    ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |freeWave (fun z => E z i) (fun z => curl B z i) (t,y)-
        freeWave (fun z => E z i) (fun z => curl B z i) (t,x)|≤18*C*‖y-x‖ ∧
      |freeWave (fun z => B z i) (fun z => -curl E z i) (t,y)-
        freeWave (fun z => B z i) (fun z => -curl E z i) (t,x)|≤18*C*‖y-x‖ := by
  let A := 3*C
  let D := 3*C
  have hA : 0≤A := by positivity
  have hD : 0≤D := by positivity
  have hAb := spatial_lipschitz_of_low_jets hE hC hEj
  have hDb := spatial_lipschitz_of_low_jets hB hC hBj
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  have he : 18*C=3*(A+D) := by dsimp [A,D]; ring
  rw [he]
  intro t ht x y
  constructor
  · apply freeWave_lipschitz (hproj.comp hE)
      (hproj.continuous.comp (contDiff_curl hB).continuous) (add_nonneg hA hD) _ _ _ ht
    · intro z z'
      exact (norm_coordinate_le (E z'-E z) i).trans ((hAb z z').1.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _)))
    · intro z z' n hn
      have hh : |fderiv ℝ (fun u => E u i) z' n-fderiv ℝ (fun u => E u i) z n|≤A*‖z'-z‖ := by
        simpa only [hn,mul_one] using (hAb z z').2.1 i n
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _))
    · intro z z'
      exact ((hDb z z').2.2 i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))
  · apply freeWave_lipschitz (hproj.comp hB)
      ((hproj.continuous.comp (contDiff_curl hE).continuous).neg) (add_nonneg hA hD) _ _ _ ht
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

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {ι : Type*} {d : ι → Datum}
variable (hd : ∀ j, Admissible (d j))
variable {A P L J : ℝ} (hA : 0≤A) (hL : 0≤L) (hJ : 0≤J)
variable (hf : ∀ j z, |(d j).f₀ z|≤A)
variable (hp : ∀ j x v, P<‖v‖ → (d j).f₀ (x,v)=0)
variable (hl : ∀ j x y v, |(d j).f₀ (y,v)-(d j).f₀ (x,v)|≤L*‖y-x‖)
variable (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
variable (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J)

include hA hf hp in
lemma family_datum_moment_bounds :
    ∃ C : ℝ, 0≤C ∧ ∀ j x, |rho (d j).f₀ x|≤C ∧ ‖current (d j).f₀ x‖≤C := by
  obtain ⟨B,hB,hb⟩ := uniform_velocity_integral_bound_from_caps (H:=fun _ => (1:ℝ)) continuousOn_const A P hA
  obtain ⟨C,hC,hc⟩ := uniform_velocity_integral_bound_from_caps
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn) A P hA
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro j x
  constructor
  · have hh := hb (d j).f₀ (hf j) (hp j) x (basis 0) (by simp [basis,PiLp.norm_single])
    simp only [smul_eq_mul,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (le_add_of_nonneg_right hC)
  · exact (hc (d j).f₀ (hf j) (hp j) x (basis 0) (by simp [basis,PiLp.norm_single])).trans (le_add_of_nonneg_left hB)

include hd hL hp hl in
lemma family_datum_moment_lipschitz :
    ∃ C : ℝ, 0≤C ∧ ∀ j x y, |rho (d j).f₀ y-rho (d j).f₀ x|≤C*‖y-x‖ ∧
      ‖current (d j).f₀ y-current (d j).f₀ x‖≤C*‖y-x‖ := by
  obtain ⟨B,hB,hb⟩ := uniform_velocity_integral_lipschitz_from_caps (H:=fun _ => (1:ℝ)) continuousOn_const L P hL
  obtain ⟨C,hC,hc⟩ := uniform_velocity_integral_lipschitz_from_caps
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn) L P hL
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro j x y
  constructor
  · have hh := hb (d j).f₀ (hd j).1.continuous (hl j) (hp j) x y (basis 0) (by simp [basis,PiLp.norm_single])
    simp only [smul_eq_mul,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (norm_nonneg _))
  · exact (hc (d j).f₀ (hd j).1.continuous (hl j) (hp j) x y (basis 0) (by simp [basis,PiLp.norm_single])).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (norm_nonneg _))

include hA hf hp in
lemma family_datumElectricFlux_bound (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j (t : ℝ) (x y : Vec), x≠y →
      ‖retardedElectricFlux (datumBoundarySolution (d j)) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_velocity_integral_bound_from_caps (continuousOn_datumElectricFluxKernel i) A P hA
  refine ⟨C,hC,?_⟩
  intro j t x y hxy
  rw [datumElectricFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound (d j).f₀ (hf j) (hp j) y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

include hA hf hp in
lemma family_datumMagneticFlux_bound (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j (t : ℝ) (x y : Vec), x≠y →
      ‖retardedMagneticFlux (datumBoundarySolution (d j)) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_velocity_integral_bound_from_caps (continuousOn_datumMagneticFluxKernel i) A P hA
  refine ⟨C,hC,?_⟩
  intro j t x y hxy
  rw [datumMagneticFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound (d j).f₀ (hf j) (hp j) y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

include hd hL hp hl in
lemma family_datum_sphere_flux_lipschitz {H : Vec × Vec → Vec}
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |(4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, (d j).f₀ (y+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)-
        (4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, (d j).f₀ (x+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)|≤C*‖y-x‖ := by
  obtain ⟨C,hC,hb⟩ := uniform_velocity_integral_lipschitz_from_caps hH L P hL
  refine ⟨C,hC,?_⟩
  intro q t ht x y
  have hhf := (hd q).1.continuous
  have hhc := (hd q).2.1
  have hb := hb (d q).f₀ hhf (hl q) (hp q)
  have hn (n : Sphere) : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have hc' (z : Vec) : Continuous (fun n : Sphere =>
      t*dot n.1 (∫ v, (d q).f₀ (z+t • n.1,v) • H (-n.1,v))) := by
    have hI : Continuous (fun n : Sphere => ∫ v, (d q).f₀ (z+t • n.1,v) • H (-n.1,v)) := by
      apply (continuousOn_datum_velocity_integral hhf hhc hH).comp_continuous
        ((continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)).prodMk continuous_subtype_val.neg)
      intro n
      exact ⟨mem_univ _,by simpa only [mem_sphere_zero_iff_norm,Pi.neg_apply,norm_neg] using hn n⟩
    exact continuous_const.mul ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_subtype_val.prodMk hI))
  have hh := abs_sphere_integral_sub_le (hc' y) (hc' x) (C:=C*‖y-x‖) (by
    intro n
    rw [← mul_sub,← dot_sub_right,abs_mul,abs_of_nonneg ht.1]
    have hbd : ‖(∫ v, (d q).f₀ (y+t • n.1,v) • H (-n.1,v))-
        (∫ v, (d q).f₀ (x+t • n.1,v) • H (-n.1,v))‖≤C*‖y-x‖ := by
      simpa only [add_sub_add_right_eq_sub] using hb (x+t • n.1) (y+t • n.1) (-n.1) (by simpa only [norm_neg] using hn n)
    exact (mul_le_mul_of_nonneg_left ((abs_dot_le _ _).trans
      (by simpa only [hn n,one_mul] using hbd)) ht.1).trans
        (mul_le_of_le_one_left (by positivity) ht.2))
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)

include hd hA hJ hf hp hEj hBj in
lemma family_electricConeBoundary_datum_bound_global
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |electricConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := family_datumElectricFlux_bound hA hf hp i
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_bounds hA hf hp
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_bound_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro q t ht x
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_cone_flux i hflux ht.1 x n)
  have hrho : |∫ n : Sphere, t*n.1 i*rho (d q).f₀ (x+t • n.1) ∂sphereMeasure|≤
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
  have hj : |waveK (fun y => current (d q).f₀ y i) (t,x)|≤t*D :=
    waveK_bound_of_bounded (fun y => (norm_coordinate_le (current (d q).f₀ y) i).trans (hmom y).2) ht.1.le x
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t*n.1 i*rho (d q).f₀ (x+t • n.1) ∂sphereMeasure)|≤t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hrho hp
      _ = t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).1
  simp only [electricConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)) hj)).trans (by
      nlinarith [ht.2])

include hd hL hJ hp hl hEj hBj in
lemma family_electricConeBoundary_datum_lipschitz (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |electricConeBoundary (datumBoundarySolution (d j)) t y i 0-
        electricConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C*‖y-x‖ := by
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_lipschitz_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  obtain ⟨B,hB,hflux⟩ := family_datum_sphere_flux_lipschitz hd hL hp hl
    (continuousOn_datumElectricFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_lipschitz hd hL hp hl
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro q t ht x y
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hm : Continuous (rho (d q).f₀) ∧ Continuous (current (d q).f₀) := by
    constructor
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm,Real.norm_eq_abs] using (hmom y x).1)).continuous
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj : Continuous (fun v : Vec => v i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous

  have hrho := weighted_sphere_mean_lipschitz hm.1 hD (fun x y => (hmom x y).1)
    (hproj.comp continuous_subtype_val) (fun n => (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2))
    ⟨ht.1.le,ht.2⟩ x y
  have hj := waveK_lipschitz (hproj.comp hm.2)
    (fun x y => (norm_coordinate_le (current (d q).f₀ y-current (d q).f₀ x) i).trans (hmom x y).2) ht.1.le x y
  have he : t*D*‖y-x‖≤D*‖y-x‖ := by
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hD ht.2) (norm_nonneg _)
  simp only [electricConeBoundary,sub_zero]
  simp_rw [datum_initial_electric_flux_normalised (d q) i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c e a' b' c' e' : ℝ) : (a-b-c-e)-(a'-b'-c'-e')=(a-a')-(b-b')-(c-c')-(e-e') := by ring
  rw [halg]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).1
      (hflux t ⟨ht.1.le,ht.2⟩ x y))) hrho)) (hj.trans he))).trans_eq (by ring)

include hd hA hJ hf hp hEj hBj in
lemma family_magneticConeBoundary_datum_bound_global
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |magneticConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := family_datumMagneticFlux_bound hA hf hp i
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_bounds hA hf hp
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_bound_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro q t ht x
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_magnetic_cone_flux i hflux ht.1 x n)
  have hem (n : Sphere) (j k : Fin 3) :
      |t*n.1 j*current (d q).f₀ (x+t • n.1) k|≤t*D := by
    have hn : |n.1 j|≤1 :=
      (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    have hj : |current (d q).f₀ (x+t • n.1) k|≤D :=
      (norm_coordinate_le _ k).trans (hmom _).2
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        hj (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = _ := by ring
  have hj : |∫ n : Sphere,
      t*n.1 (curlA i)*current (d q).f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current (d q).f₀ (x+t • n.1) (curlA i) ∂sphereMeasure|≤
      (2*t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    exact (abs_sub _ _).trans ((add_le_add (hem n _ _) (hem n _ _)).trans (by ring_nf; rfl))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere,
      t*n.1 (curlA i)*current (d q).f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current (d q).f₀ (x+t • n.1) (curlA i) ∂sphereMeasure)|≤2*t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((2*t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hj hp
      _ = 2*t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).2
  simp only [magneticConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)).trans (by
      nlinarith [ht.2])

include hd hL hJ hp hl hEj hBj in
lemma family_magneticConeBoundary_datum_lipschitz (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |magneticConeBoundary (datumBoundarySolution (d j)) t y i 0-
        magneticConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C*‖y-x‖ := by
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_lipschitz_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  obtain ⟨B,hB,hflux⟩ := family_datum_sphere_flux_lipschitz hd hL hp hl
    (continuousOn_datumMagneticFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_lipschitz hd hL hp hl
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro q t ht x y
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hjc : Continuous (current (d q).f₀) := (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
    simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj (j : Fin 3) : Continuous (fun v : Vec => v j) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous

  let F : Vec → Sphere → ℝ := fun z n => t*n.1 (curlA i)*current (d q).f₀ (z+t • n.1) (curlB i)-
    t*n.1 (curlB i)*current (d q).f₀ (z+t • n.1) (curlA i)
  have hfc (z : Vec) : Continuous (F z) := by
    have hg (j k : Fin 3) : Continuous (fun n : Sphere => t*n.1 j*current (d q).f₀ (z+t • n.1) k) :=
      (continuous_const.mul ((hproj j).comp continuous_subtype_val)).mul
        (((hproj k).comp hjc).comp (continuous_const.add
          ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
    exact (hg _ _).sub (hg _ _)
  have hh := abs_sphere_integral_sub_le (hfc y) (hfc x) (C:=2*D*‖y-x‖) (by
    intro n
    have hterm (j k : Fin 3) : |t*n.1 j*current (d q).f₀ (y+t • n.1) k-
        t*n.1 j*current (d q).f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
      rw [← mul_sub,abs_mul,abs_mul,abs_of_pos ht.1]
      have hn : |n.1 j|≤1 := (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
      have hj : |current (d q).f₀ (y+t • n.1) k-current (d q).f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
        simpa only [PiLp.sub_apply,add_sub_add_right_eq_sub] using
          (norm_coordinate_le (current (d q).f₀ (y+t • n.1)-current (d q).f₀ (x+t • n.1)) k).trans
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
  simp_rw [datum_initial_magnetic_flux_normalised (d q) i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c a' b' c' : ℝ) : (a-b+c)-(a'-b'+c')=(a-a')-(b-b')+(c-c') := by ring
  rw [halg]
  exact ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).2 (hflux t ⟨ht.1.le,ht.2⟩ x y))) hj)).trans_eq (by ring)

end RVM

end

end OAI
