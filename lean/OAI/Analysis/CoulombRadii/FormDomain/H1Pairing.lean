import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PotentialAddRsmul
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorFormBottom
import OAI.Analysis.CoulombRadii.FormDomain.CoreKinetic
import OAI.Analysis.CoulombRadii.FormDomain.H1VectorL2

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma real_inner_norm_algebra (z w:ℂ) :
    2*inner ℝ z w=‖z+w‖^2-‖z‖^2-‖w‖^2 := by
  nlinarith [norm_add_sq_real z w]
lemma weighted_inner_integrable {X:Type*} [MeasurableSpace X] {μ:Measure X}
    {f g:X → ℂ} {V:X → ℝ}
    (hf:Integrable (fun x => V x*‖f x‖^2) μ)
    (hg:Integrable (fun x => V x*‖g x‖^2) μ)
    (ha:Integrable (fun x => V x*‖f x+g x‖^2) μ) :
    Integrable (fun x => V x*inner ℝ (f x) (g x)) μ := by
  convert ((ha.sub hf).sub hg).div_const 2 using 1
  ext x
  dsimp only [Pi.sub_apply]
  nlinarith [congrArg (fun t:ℝ => V x*t) (real_inner_norm_algebra (f x) (g x))]
lemma integral_weighted_inner {X:Type*} [MeasurableSpace X] {μ:Measure X}
    {f g:X → ℂ} {V:X → ℝ}
    (hf:Integrable (fun x => V x*‖f x‖^2) μ)
    (hg:Integrable (fun x => V x*‖g x‖^2) μ)
    (ha:Integrable (fun x => V x*‖f x+g x‖^2) μ) :
    2*(∫ x,V x*inner ℝ (f x) (g x) ∂μ)=
      (∫ x,V x*‖f x+g x‖^2 ∂μ)-(∫ x,V x*‖f x‖^2 ∂μ)-(∫ x,V x*‖g x‖^2 ∂μ) := by
  rw [←integral_const_mul]
  calc
    _ = ∫ x,(V x*‖f x+g x‖^2-V x*‖f x‖^2)-V x*‖g x‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      nlinarith [congrArg (fun t:ℝ => V x*t) (real_inner_norm_algebra (f x) (g x))]
    _ = _ := by
      have H:=integral_sub (ha.sub hf) hg
      simp only [Pi.sub_apply] at H
      rw [H,integral_sub ha hf]

def massPair {n:ℕ} (u v:H1Vector n) : ℝ := ∑ s,∫ x,inner ℝ (u.value s x) (v.value s x)
def kineticPair {n:ℕ} (u v:H1Vector n) : ℝ := (1/2:ℝ)*∑ s,∑ a,∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x)
def nuclearPair {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) : ℝ :=
  ∑ s,∫ x,(∑ i,attraction S (position x i))*inner ℝ (u.value s x) (v.value s x)
def repulsionPair {n:ℕ} (u v:H1Vector n) : ℝ :=
  ∑ s,∫ x,pairPotential x*inner ℝ (u.value s x) (v.value s x)
def formPair {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) : ℝ := kineticPair u v-nuclearPair S u v+repulsionPair u v
lemma massPair_polarization {n:ℕ} (u v:H1Vector n) :
    2*massPair u v=mass (u.add v)-mass u-mass v := by
  unfold massPair mass
  rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [one_mul,H1Vector.add] using integral_weighted_inner (V:=fun _ => 1)
    (by simpa using (u.value_L2 s).integrable_norm_pow (by norm_num))
    (by simpa using (v.value_L2 s).integrable_norm_pow (by norm_num))
    (by simpa only [one_mul,H1Vector.add] using ((u.add v).value_L2 s).integrable_norm_pow (by norm_num))
lemma kineticPair_polarization {n:ℕ} (u v:H1Vector n) :
    2*kineticPair u v=kinetic (u.add v)-kinetic u-kinetic v := by
  have h(s:Spins n)(a:Fin n × Fin 3) :
      2*(∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x))=
      (∫ x,‖(u.add v).gradient s a x‖^2)-(∫ x,‖u.gradient s a x‖^2)-(∫ x,‖v.gradient s a x‖^2) := by
    simpa only [one_mul,H1Vector.add] using integral_weighted_inner (V:=fun _ => 1)
      (by simpa using (u.partial_L2 s a).integrable_norm_pow (by norm_num))
      (by simpa using (v.partial_L2 s a).integrable_norm_pow (by norm_num))
      (by simpa only [one_mul,H1Vector.add] using ((u.add v).partial_L2 s a).integrable_norm_pow (by norm_num))
  have H:=congrArg (fun f:Spins n → (Fin n × Fin 3) → ℝ => ∑ s,∑ a,f s a) (funext fun s => funext fun a => h s a)
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum] at H
  unfold kinetic kineticPair
  linarith
lemma nuclearPair_polarization {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) :
    2*nuclearPair S u v=nuclearEnergy S (u.add v)-nuclearEnergy S u-nuclearEnergy S v := by
  unfold nuclearPair nuclearEnergy
  rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact integral_weighted_inner (u.nuclear_integrable S s) (v.nuclear_integrable S s) ((u.add v).nuclear_integrable S s)
lemma repulsionPair_polarization {n:ℕ} (u v:H1Vector n) :
    2*repulsionPair u v=pairEnergy (u.add v)-pairEnergy u-pairEnergy v := by
  unfold repulsionPair pairEnergy
  rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact integral_weighted_inner (u.pair_integrable s) (v.pair_integrable s) ((u.add v).pair_integrable s)
lemma formPair_polarization {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) :
    2*formPair S u v=form S (u.add v)-form S u-form S v := by
  unfold formPair form
  linarith [kineticPair_polarization u v,nuclearPair_polarization S u v,repulsionPair_polarization u v]
lemma formPair_kinetic_integrable {n:ℕ} (u v:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) :
    Integrable (fun x => inner ℝ (u.gradient s a x) (v.gradient s a x)) :=
  memlp_real_inner_integrable (u.partial_L2 s a) (v.partial_L2 s a)
lemma formPair_nuclear_integrable {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (s:Spins n) :
    Integrable (fun x => (∑ i,attraction S (position x i))*inner ℝ (u.value s x) (v.value s x)) :=
  weighted_inner_integrable (u.nuclear_integrable S s) (v.nuclear_integrable S s) ((u.add v).nuclear_integrable S s)
lemma formPair_repulsion_integrable {n:ℕ} (u v:H1Vector n) (s:Spins n) :
    Integrable (fun x => pairPotential x*inner ℝ (u.value s x) (v.value s x)) :=
  weighted_inner_integrable (u.pair_integrable s) (v.pair_integrable s) ((u.add v).pair_integrable s)

lemma form_ge_sector_bottom {M n:ℕ} (S:Nuclei M) (u:H1Vector n)
    (ha:Antisymmetric u) (E:ℝ) (hE:(E:EReal) ≤ sectorFormBottom S n) :
    E*mass u ≤ form S u := by
  rw [←form_normalized_weight S u]
  by_cases hz:mass u=0
  · simp [hz]
  · have hp:0 < mass u:=lt_of_le_of_ne (mass_nonneg u) (Ne.symm hz)
    have H:E≤form S u.normalized:=EReal.coe_le_coe_iff.mp (hE.trans (sInf_le
      ⟨u.normalized,ha.normalized,mass_normalized u hp,rfl⟩))
    simpa [mul_comm] using mul_le_mul_of_nonneg_left H hp.le

lemma sector_minimizer_weak_eigen (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ}
    (u:H1Vector n) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n)
    (v:H1Vector n) (hv:Antisymmetric v) :
    formPair (atom Z hZ) u v=form (atom Z hZ) u*massPair u v := by
  let E:=form (atom Z hZ) u
  let A:=form (atom Z hZ) (u.add v)-form (atom Z hZ) u-form (atom Z hZ) v-
    E*(mass (u.add v)-mass u-mass v)
  let B:=form (atom Z hZ) v-E*mass v
  have hpoly:∀ᶠ t:ℝ in 𝓝 0,0 ≤ A*t+B*t^2 := by
    apply Eventually.of_forall
    intro t
    have H:=form_ge_sector_bottom (atom Z hZ) (u.add (v.rsmul t)) (ha.add (hv.rsmul t)) E hmin.le
    rw [mass_add_rsmul,form_add_rsmul,hm] at H
    dsimp [E] at H
    dsimp [A,B,E]
    rw [hm]
    nlinarith only [H]
  have H:=linear_term_zero_of_eventually_quadratic_nonneg A B hpoly
  dsimp [A,E] at H
  rw [←formPair_polarization,←massPair_polarization] at H
  linarith
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma integrable_real_bounded_mul {X:Type*} [TopologicalSpace X] [MeasureSpace X]
    [BorelSpace X] {f F:X → ℝ} (hf:Integrable f) (hF:Continuous F)
    (B:ℝ) (hB:∀ x,|F x|≤B) : Integrable (fun x => F x*f x) :=
  hf.bdd_mul hF.aestronglyMeasurable (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

lemma reciprocal_kinetic_nonneg {n:ℕ} (u:H1Vector n) (s:Spins n)
    (I:Finset (Fin n × Fin 3)) (U w:Configuration n → ℝ)
    (hU:ContDiff ℝ ∞ U) (hw:ContDiff ℝ ∞ w)
    (BU DU Dw Bw DDU:ℝ)
    (hBU:∀ x,|U x|≤BU) (hDU:∀ a x,|fderiv ℝ U x (EuclideanSpace.single a 1)|≤DU)
    (hBw:∀ x,|w x|≤Bw) (hDw:∀ a x,|fderiv ℝ w x (EuclideanSpace.single a 1)|≤Dw)
    (hDDU:∀ a b x,|fderiv ℝ (fun y => fderiv ℝ U y (EuclideanSpace.single a 1)) x (EuclideanSpace.single b 1)|≤DDU)
    (hpos:∀ x,0≤U x) (hinv:∀ x,U x*w x=1)
    (hlap:∀ x,(∑ a∈I,fderiv ℝ (fun y => fderiv ℝ U y (EuclideanSpace.single a 1)) x (EuclideanSpace.single a 1))≤0) :
    let v:=u.smoothMul w hw Bw Dw hBw hDw
    0≤∑ a∈I,∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x) := by
  dsimp only
  let v:=u.smoothMul w hw Bw Dw hBw hDw
  let z:=v.smoothMul U hU BU DU hBU hDU
  have he:∀ t,u.value t=ᵐ[volume]z.value t := by
    intro t
    exact Eventually.of_forall fun x => by
      change u.value t x=(U x:ℂ)*((w x:ℂ)*u.value t x)
      rw [←mul_assoc,←Complex.ofReal_mul,hinv x]
      simp
  let dU:=fun a (x:Configuration n) => fderiv ℝ U x (EuclideanSpace.single a 1)
  let ddU:=fun a (x:Configuration n) => fderiv ℝ (dU a) x (EuclideanSpace.single a 1)
  have hd(a:Fin n × Fin 3):ContDiff ℝ ∞ (dU a):=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hi(a:Fin n × Fin 3):Integrable (fun x => U x*‖v.gradient s a x‖^2) :=
    integrable_real_bounded_mul ((v.partial_L2 s a).integrable_norm_pow (by norm_num)) hU.continuous BU hBU
  have hj(a:Fin n × Fin 3):Integrable (fun x => dU a x*inner ℝ (v.value s x) (v.gradient s a x)) :=
    integrable_real_bounded_mul (memlp_real_inner_integrable (v.value_L2 s) (v.partial_L2 s a))
      (hd a).continuous DU (hDU a)
  have hk(a:Fin n × Fin 3):Integrable (fun x => ddU a x*‖v.value s x‖^2) :=
    integrable_real_bounded_mul ((v.value_L2 s).integrable_norm_pow (by norm_num))
      (((hd a).continuous_fderiv (by simp)).clm_apply continuous_const) DDU (hDDU a a)
  have hblock(a:Fin n × Fin 3):
      (∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x))=
      (∫ x,U x*‖v.gradient s a x‖^2)-(1/2:ℝ)*(∫ x,ddU a x*‖v.value s x‖^2) := by
    have H:=h1_multiplier_ibp v s a (dU a) (hd a) DU DDU (hDU a) (hDDU a)
    have H':(∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x))=
        (∫ x,U x*‖v.gradient s a x‖^2)+(∫ x,dU a x*inner ℝ (v.value s x) (v.gradient s a x)) := by
      rw [←integral_add (hi a) (hj a)]
      apply integral_congr_ae
      filter_upwards [u.gradient_congr_ae z he s a] with x hx
      rw [hx]
      change inner ℝ ((dU a x:ℂ)*v.value s x+(U x:ℂ)*v.gradient s a x) (v.gradient s a x)=_
      simp only [inner_add_left,←Complex.real_smul,real_inner_smul_left,real_inner_self_eq_norm_sq]
      ring
    dsimp [ddU] at *
    linarith
  change 0≤∑ a∈I,∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x)
  simp_rw [hblock]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  have hh:0≤∑ a∈I,∫ x,U x*‖v.gradient s a x‖^2 :=
    Finset.sum_nonneg fun a _ => integral_nonneg fun x => mul_nonneg (hpos x) (sq_nonneg _)
  have hneg:(∑ a∈I,∫ x,ddU a x*‖v.value s x‖^2)≤0 := by
    rw [←integral_finsetSum _ (fun a _ => hk a)]
    apply integral_nonpos
    intro x
    dsimp only [Pi.zero_apply]
    rw [←Finset.sum_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (hlap x) (sq_nonneg _)
  linarith
end Coulomb
end

end

end OAI
