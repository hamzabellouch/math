import Mathlib
import OAI.Analysis.CoulombRadii.SpectralTheory.BindingCut
import OAI.Analysis.CoulombRadii.FormDomain.H1EnergyLimit

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma binding_cost_tendsto (n Z:ℕ) :
    Tendsto (fun j:ℕ => 3*(n:ℝ)*(radialCutCoefficient/((j:ℝ)+1))^2+(n:ℝ)*((Z:ℝ)/((j:ℝ)+1))) atTop (𝓝 0) := by
  have h:=tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  simpa only [mul_zero,zero_pow (by decide : 2≠0),zero_add,mul_one_div] using
    ((h.const_mul radialCutCoefficient).pow 2 |>.const_mul (3*(n:ℝ))).add ((h.const_mul (Z:ℝ)).const_mul (n:ℝ))

lemma strictly_bound_sequence_tight (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
    (u:ℕ → H1Vector n) (ha:∀ k,Antisymmetric (u k)) (hm:∀ k,mass (u k)=1)
    (E P:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n)
    (hP:(P:EReal) ≤ sectorFormBottom (atom Z hZ) (n-1)) (hgap:E<P)
    (hlim:Tendsto (fun k => form (atom Z hZ) (u k)) atTop (𝓝 E)) :
    ∀ ε:ℝ,0<ε → ∃ A:Set (Configuration n),∃ hA:MeasurableSet A,volume A≠(⊤:ℝ≥0∞) ∧
      ∀ᶠ k in atTop,∀ s,‖cutL2 Aᶜ hA.compl ((u k).valueL2 s)‖≤ε := by
  intro ε hε
  have hh:0<(P-E)*ε^2/2 := by positivity
  obtain ⟨j,hj⟩:=((binding_cost_tendsto n Z).eventually (gt_mem_nhds hh)).exists
  let r:ℝ:=(j:ℝ)+1
  have hr:0<r := by dsimp [r]; positivity
  refine ⟨configurationBox n r,configurationBox_measurable n r,configurationBox_finite n hr,?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds (show E<E+(P-E)*ε^2/2 by linarith))] with k hk s
  have H:=binding_loss_bound Z hZ hn (u k) (ha k) hr E P hE hP
  rw [hm k,mul_one,mul_one] at H
  have hc:=binding_loss_controls_cut (u k) hr s
  have hdiff:mass (u k)-mass (bindingLocalized (u k) hr (fun _ => 1)) ≤ ε^2 := by
    rw [hm k]
    dsimp [r] at H
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) hε.le).mp (hc.trans hdiff)

lemma atom_strict_binding_attained (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
    (hstrict:sectorFormBottom (atom Z hZ) n < sectorFormBottom (atom Z hZ) (n-1)) :
    ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
      (form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n := by
  let E:ℝ:=(sectorFormBottom (atom Z hZ) n).toReal
  let P:ℝ:=(sectorFormBottom (atom Z hZ) (n-1)).toReal
  have hE:(E:EReal)=sectorFormBottom (atom Z hZ) n:=atom_sectorFormBottom_real Z hZ n
  have hP:(P:EReal)=sectorFormBottom (atom Z hZ) (n-1):=atom_sectorFormBottom_real Z hZ (n-1)
  have hgap:E<P := EReal.coe_lt_coe_iff.mp (by rwa [hE,hP])
  obtain ⟨u,ha,hm,hk,hlim⟩:=atom_minimizing_sequence Z hZ n E hE
  obtain ⟨v,hvm,hvk,φ,hφ,hv,hw⟩:=h1_bounded_tight_compact u _ hm hk
    (strictly_bound_sequence_tight Z hZ hn u ha hm E P hE.le hP.le hgap hlim)
  have hva:Antisymmetric v := antisymmetric_strong_limit (fun k => u (φ k)) v (fun k => ha (φ k)) hv
  have hupper:=form_strong_weak_limit_le (atom Z hZ) (fun k => u (φ k)) v hv hw _ (fun k => hk (φ k)) E (hlim.comp hφ.tendsto_atTop)
  have hlower:=atom_normalized_form_ge_bottom Z hZ v hva hvm E hE.le
  refine ⟨v,hva,hvm,?_⟩
  rw [le_antisymm hupper hlower,hE]
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace NeutralAtom
lemma integral_first_weighted_tensor {n:ℕ} (f:Position → ℝ) (ψ:Configuration n → ℂ) (W:Position → ℝ):
    (∫ x:Configuration (n+1),W (x 0)*‖f (x 0) • ψ (fun i => x i.succ)‖^2)=
    (∫ y:Position,W y*(f y)^2)*(∫ x:Configuration n,‖ψ x‖^2) := by
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding
    (fun z:Position × Configuration n => (W z.1*(f z.1)^2)*‖ψ z.2‖^2)
  rw [←integral_prod_mul (μ:=volume) (ν:=volume) (fun y:Position => W y*(f y)^2)
    (fun x:Configuration n => ‖ψ x‖^2)]
  change _ = ∫ z:Position × Configuration n,(W z.1*(f z.1)^2)*‖ψ z.2‖^2
  rw [←he]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [configurationSplit_apply,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    ring
lemma weighted_normSquared_insert_first {n:ℕ} (f:Position → ℝ) (ψ:Wavefunction n) (W:Position → ℝ):
    (∑ s:Spins (n+1),∫ x,W (x 0)*‖insertWavefunction f ψ s x‖^2)=
    (∫ y:Position,W y*(f y)^2)*normSquared ψ := by
  rw [←Equiv.sum_comp (Fin.consEquiv (fun _:Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  have h10:(1:Fin 2)≠0:=by decide
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,insertWavefunction,Fin.cons_zero,
    Fin.cons_succ,h10,↓reduceIte,norm_zero,zero_pow (by decide : 2≠0),mul_zero,
    integral_zero,Finset.sum_const_zero,add_zero,integral_first_weighted_tensor,Finset.mul_sum,normSquared]
lemma distantPacket_outer_zero {t:ℝ} (ht:0<t) {y:Position} (hy:6*t≤‖y‖):distantPacket t y=0 := by
  have hnorm:6≤‖t⁻¹ • y‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
    exact (le_inv_mul_iff₀ ht).mpr (by linarith)
  have hdist:2≤‖t⁻¹ • y-distantCenter‖ := by
    have H:=norm_sub_norm_le (t⁻¹ • y) distantCenter
    rw [distantCenter_norm] at H
    linarith
  have H:=bindingBump.zero_of_le_dist (by simpa [bindingBump] using hdist)
  simp [distantPacket,H]
lemma distantPacket_attraction {t:ℝ} (ht:0<t):
    (6*t)⁻¹≤∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2 := by
  have hi:Integrable (fun y:Position => ‖y‖⁻¹*(distantPacket t y)^2) := by
    exact locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport
      ((distantPacket_smooth t).continuous.pow 2) (by
        simp only [sq]
        change HasCompactSupport ((distantPacket t)*(distantPacket t))
        exact (distantPacket_compact ht).mul_left)
  have hi':Integrable (fun y:Position => (6*t)⁻¹*(distantPacket t y)^2):=
    ((distantPacket_memLp ht).integrable_sq).const_mul _
  have H:=integral_mono hi' hi (fun y => by
    by_cases hz:distantPacket t y=0
    · simp [hz]
    · have hy:‖y‖<6*t:=lt_of_not_ge (fun h => hz (distantPacket_outer_zero ht h))
      have hy0:0<‖y‖:=lt_of_le_of_lt (by positivity : (0:ℝ)≤2*t)
        (lt_of_not_ge (fun h => hz (distantPacket_zero ht h)))
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hy0 hy.le) (sq_nonneg _))
  rwa [integral_const_mul,distantPacket_normalized ht,mul_one] at H
lemma onePacket_domain {t:ℝ} (ht:0<t):
    FormDomain (insertWavefunction (distantPacket t) vacuumWavefunction)
      (insertGradient (distantPacket t) vacuumWavefunction vacuumGradient) := by
  refine ⟨?_,FormRegular.insert_separated vacuum_formDomain.2 ht ht (R:=0) ?_
    (distantPacket_smooth t) (distantPacket_memLp ht) (fun a => distantPacket_derivative_memLp ht _) ?_⟩
  · intro p s
    have hp:p=1:=by
      apply Equiv.ext
      intro i
      apply Fin.ext
      change (p i).val=i.val
      have H1:(p i).val<1:=(p i).isLt
      have H2:i.val<1:=i.isLt
      omega
    subst p
    simp
  · intro s x hx
    have H:x=0:=Subsingleton.elim _ _
    simp [H] at hx
  · intro y hy
    exact distantPacket_zero ht (by linarith)
lemma onePacket_energy (Z:ℕ) {t:ℝ} (ht:0<t):
    energy Z (insertWavefunction (distantPacket t) vacuumWavefunction)
      (insertGradient (distantPacket t) vacuumWavefunction vacuumGradient)=
    (1/2:ℝ)*t⁻¹^2*(distantMass⁻¹*oneParticleGradientNorm bindingBump)-
      (Z:ℝ)*(∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2) := by
  rw [energy_decompose,gradientNormSquared_insert,vacuum_normalized,distantPacket_gradientNorm ht]
  have hp:potentialForm Z (insertWavefunction (distantPacket t) vacuumWavefunction)=
      -(Z:ℝ)*(∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2) := by
    unfold potentialForm
    have hV:∀ x:Configuration 1,coulombPotential Z x= -(Z:ℝ)*‖x 0‖⁻¹ := by
      intro x
      simp [coulombPotential,Finset.filter_singleton]
    simp_rw [hV,neg_mul,mul_assoc,integral_neg,integral_const_mul]
    rw [Finset.sum_neg_distrib,←Finset.mul_sum]
    have hw:=weighted_normSquared_insert_first (distantPacket t) vacuumWavefunction (fun y:Position => ‖y‖⁻¹)
    rw [hw,vacuum_normalized,mul_one]
  rw [hp]
  simp only [gradientNormSquared,Finset.univ_eq_empty,Finset.sum_empty,mul_zero,zero_add,mul_one]
  ring
lemma sectorEnergy_one_neg (Z:ℕ) (hZ:1≤Z):sectorEnergy Z 1<0 := by
  let C:=distantMass⁻¹*oneParticleGradientNorm bindingBump
  let t:ℝ:=3*|C|+1
  have ht:0<t:=by dsimp [t]; positivity
  have hnorm:normSquared (insertWavefunction (distantPacket t) vacuumWavefunction)=1:=by
    rw [normSquared_insert,distantPacket_normalized ht,vacuum_normalized,mul_one]
  have H:=sectorEnergy_le_trial (Z:=Z) (onePacket_domain ht) hnorm
  apply lt_of_le_of_lt H
  rw [onePacket_energy Z ht]
  apply EReal.coe_lt_coe_iff.mpr
  have hZ':(1:ℝ)≤Z:=by exact_mod_cast hZ
  have ha:=distantPacket_attraction ht
  have hb:(6*t)⁻¹≤(Z:ℝ)*(∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2):=
    ha.trans (le_mul_of_one_le_left (le_trans (by positivity) ha) hZ')
  have hsmall:(1/2:ℝ)*t⁻¹^2*C<(6*t)⁻¹ := by
    have hc:C≤|C|:=le_abs_self C
    have ht3:3*C<t:=by dsimp [t]; linarith
    apply (mul_lt_mul_iff_left₀ (show 0<6*t^2 by positivity)).mp
    field_simp
    nlinarith
  change (1/2:ℝ)*t⁻¹^2*C-(Z:ℝ)*_ < 0
  linarith
end NeutralAtom
end

end

end OAI
