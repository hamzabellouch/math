import Mathlib
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorBottomBridge
import OAI.Analysis.CoulombRadii.Propagation.PropagationExpectedDeficit

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma rpow_three_fifths_absorption {A : ℝ} (hA : 0≤A) :
    ∃ C : ℝ,0<C ∧ ∀ {x : ℝ},0≤x → x≤A*x^(3/5:ℝ)+4 → x≤C := by
  let B := (2*(A+1))^(5/2:ℝ)
  have hbase : 0<2*(A+1) := by linarith
  have hB : 0<B := Real.rpow_pos_of_pos hbase _
  have hb : B^(-2/5:ℝ)=(2*(A+1))⁻¹ := by
    rw [←Real.rpow_mul hbase.le]
    norm_num only [show (5/2:ℝ)*(-2/5)= -1 by norm_num,Real.rpow_neg_one]
  have hab : A*B^(-2/5:ℝ)≤1/2 := by
    rw [hb,←div_eq_mul_inv]
    apply (div_le_iff₀ hbase).mpr
    linarith
  refine ⟨2*(A*B^(3/5:ℝ)+4),by positivity,?_⟩
  intro x hx H
  have hl := mul_le_mul_of_nonneg_left (rpow_three_fifths_linear hx hB) hA
  have hab' := mul_le_mul_of_nonneg_right hab hx
  nlinarith only [H,hl,hab']

lemma atomic_kinetic_scaling {z t A : ℝ} (hz : 0<z) (ht : 0≤t)
    (H : t≤z*A*t^(3/5:ℝ)*(z^(-1/3:ℝ))^(1/5:ℝ)+4*z^(7/3:ℝ)) :
    t/z^(7/3:ℝ)≤ A*(t/z^(7/3:ℝ))^(3/5:ℝ)+4 := by
  have hzq : 0<z^(7/3:ℝ) := Real.rpow_pos_of_pos hz _
  have he : z*A*t^(3/5:ℝ)*(z^(-1/3:ℝ))^(1/5:ℝ)=
      (A*(t/z^(7/3:ℝ))^(3/5:ℝ))*z^(7/3:ℝ) := by
    rw [Real.div_rpow ht hzq.le,←Real.rpow_mul hz.le,←Real.rpow_mul hz.le]
    norm_num only [show (7/3:ℝ)*(3/5)=7/5 by norm_num,
      show (-1/3:ℝ)*(1/5)= -1/15 by norm_num]
    have hp : z^(7/3:ℝ)/z^(7/5:ℝ)=z*z^(-1/15:ℝ) := by
      rw [←Real.rpow_sub hz]
      conv_rhs => lhs; rw [←Real.rpow_one z]
      rw [←Real.rpow_add hz]
      norm_num
    calc
      _=A*t^(3/5:ℝ)*(z*z^(-1/15:ℝ)) := by ring_nf
      _=A*t^(3/5:ℝ)*(z^(7/3:ℝ)/z^(7/5:ℝ)) := by rw [hp]
      _=_ := by ring
  apply (div_le_iff₀ hzq).mpr
  rw [add_mul]
  simpa only [he] using H
end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma atomic_far_scale {z n : ℝ} (hz : 0<z) (hn : n≤3*z) :
    z*n/z^(-1/3:ℝ)≤3*z^(7/3:ℝ) := by
  have h : z*n/z^(-1/3:ℝ)≤ z*(3*z)/z^(-1/3:ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hz.le) (by positivity)
  apply h.trans_eq
  have he : z^(2:ℝ)/z^(-1/3:ℝ)=z^(7/3:ℝ) := by rw [←Real.rpow_sub hz]; norm_num
  rw [Real.rpow_two] at he
  calc
    _=3*(z^2/z^(-1/3:ℝ)) := by ring
    _=_ := by rw [he]

theorem atomic_global_kinetic_density : ∃ C : ℝ,0<C ∧
    ∀ {N : ℕ} (Z : ℕ) (hZ : 1≤Z) (u : H1Vector (N+1)), Antisymmetric u → mass u=1 →
    (N+1:ℝ)≤3*(Z:ℝ) → form (atom Z hZ) u≤(Z:ℝ)^(7/3:ℝ) →
    kinetic u≤C*(Z:ℝ)^(7/3:ℝ) ∧
    (∫ x,(NeutralAtom.density (NeutralAtom.fromH1Wave u) x)^(5/3:ℝ))≤C*(Z:ℝ)^(7/3:ℝ) := by
  obtain ⟨C,hC,HC⟩ := rpow_three_fifths_absorption fermionicNearConstant_nonneg
  let L := 32768/(3*Real.pi^2)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨(1+L)*C,by positivity,?_⟩
  intro N Z hZ u hu hm hn hf
  have hz : 0<(Z:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hZ)
  have HR : 0<(Z:ℝ)^(-1/3:ℝ) := Real.rpow_pos_of_pos hz _
  have H := atomic_kinetic_le_near Z hZ u hu hm HR hf
  have Hf := atomic_far_scale hz hn
  have H' : kinetic u≤(Z:ℝ)*fermionicNearConstant*kinetic u^(3/5:ℝ)*
      ((Z:ℝ)^(-1/3:ℝ))^(1/5:ℝ)+4*(Z:ℝ)^(7/3:ℝ) := by
    have hn' : ((N+1:ℕ):ℝ)=(N+1:ℝ) := by push_cast; rfl
    rw [hn'] at H
    linarith only [H,Hf]
  have HS := HC (div_nonneg (kinetic_nonneg u) (by positivity))
    (atomic_kinetic_scaling hz (kinetic_nonneg u) H')
  have HT : kinetic u≤C*(Z:ℝ)^(7/3:ℝ) := (div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp HS
  have HQ := (NeutralAtom.physical_density_power_bound u hu hm.le).2.trans
    (mul_le_mul_of_nonneg_left HT hL.le)
  constructor
  · nlinarith only [HT,mul_nonneg hL.le (mul_nonneg hC.le (Real.rpow_nonneg hz.le (7/3:ℝ)))]
  · change _≤ L*(C*(Z:ℝ)^(7/3:ℝ)) at HQ
    nlinarith only [HQ,mul_nonneg hC.le (Real.rpow_nonneg hz.le (7/3:ℝ))]

lemma atom_unrestricted_bottom_nonpos (Z : ℕ) (hZ : 1≤Z) :
    unrestrictedFormBottom (atom Z hZ)≤0 := by
  apply (iInf_le (fun n => sectorFormBottom (atom Z hZ) n) 0).trans
  rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ]
  exact NeutralAtom.sectorEnergy_nonpos Z 0
end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace Coulomb

lemma coreCoulombPotential_eq_form {n : ℕ} (u : H1Vector n) (y : Space) :
    coreCoulombPotential u y=potentialForm (fun x => ∑ i,coulombKernel (y-position x i)) u := by
  unfold coreCoulombPotential potentialForm
  apply Finset.sum_congr rfl
  intro σ _
  rw [show (fun x => (∑ i,coulombKernel (y-position x i))*‖u.value σ x‖^2)=
    fun x => ∑ i,coulombKernel (y-position x i)*‖u.value σ x‖^2 by funext x; rw [Finset.sum_mul]]
  rw [integral_finsetSum _ (fun i _ => by
    simpa only [coulombKernel,norm_sub_rev] using
      (u.nuclear_coulomb_integrable_bound σ i y (by norm_num : (0:ℝ)<1)).1)]
  simp only [coulombKernel,norm_sub_rev]

lemma coreCoulombPotential_le_near_far {n : ℕ} (u : H1Vector n) (y : Space)
    {R : ℝ} (hR : 0<R) :
    coreCoulombPotential u y≤potentialForm (nearPotential y R) u+((n:ℝ)/R)*mass u := by
  rw [coreCoulombPotential_eq_form]
  apply potentialForm_le_add_const u
  · intro σ
    simpa only [Finset.sum_mul] using integrable_finsetSum Finset.univ (fun i _ => by
      simpa only [coulombKernel,norm_sub_rev] using
        (u.nuclear_coulomb_integrable_bound σ i y (by norm_num : (0:ℝ)<1)).1)
  · exact nearPotential_integrable u y R
  · apply Eventually.of_forall
    intro x
    have H (i : Fin n) : coulombKernel (y-position x i)≤nearWeight y R (position x i)+1/R := by
      by_cases hx : position x i∈Metric.ball y R
      · rw [nearWeight,Set.indicator_of_mem hx]
        exact le_add_of_nonneg_right (by positivity)
      · have hd : R≤‖y-position x i‖ := by
          simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev,not_lt] using hx
        rw [nearWeight,Set.indicator_of_notMem hx,zero_add]
        simpa only [coulombKernel,one_div] using one_div_le_one_div_of_le hR hd
    have Hsum := Finset.sum_le_sum (fun (i : Fin n) (_ : i∈Finset.univ) => H i)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,nearPotential,mul_one,div_eq_mul_inv,one_mul] using Hsum

lemma global_potential_scale {z C : ℝ} (hz : 0<z) (hC : 0≤C) :
    (C*z^(7/3:ℝ))^(3/5:ℝ)*(z^(-1/3:ℝ))^(1/5:ℝ)=C^(3/5:ℝ)*z^(4/3:ℝ) := by
  rw [Real.mul_rpow hC (by positivity),←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,mul_assoc,
    ←Real.rpow_add hz]
  norm_num

theorem atomic_global_potential : ∃ C : ℝ,0<C ∧
    ∀ {N : ℕ} (Z : ℕ) (hZ : 1≤Z) (u : H1Vector (N+1)),Antisymmetric u → mass u=1 →
    (N+1:ℝ)≤3*(Z:ℝ) → form (atom Z hZ) u≤(Z:ℝ)^(7/3:ℝ) →
    ∀ y : Space, coreCoulombPotential u y≤C*(Z:ℝ)^(4/3:ℝ) := by
  obtain ⟨A,hA,HA⟩ := atomic_global_kinetic_density
  refine ⟨fermionicNearConstant*A^(3/5:ℝ)+3,by have := fermionicNearConstant_nonneg; positivity,?_⟩
  intro N Z hZ u hu hm hn hf y
  have hz : 0<(Z:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hZ)
  have HR : 0<(Z:ℝ)^(-1/3:ℝ) := Real.rpow_pos_of_pos hz _
  have H := coreCoulombPotential_le_near_far u y HR
  have Hl := nearPotential_normalized u hu hm.le y HR.le
  have HT := (HA Z hZ u hu hm hn hf).1
  have Hpow := Real.rpow_le_rpow (kinetic_nonneg u) HT (by norm_num : (0:ℝ)≤3/5)
  have Hl' := Hl.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hpow fermionicNearConstant_nonneg) (by positivity))
  have He : fermionicNearConstant*(A*(Z:ℝ)^(7/3:ℝ))^(3/5:ℝ)*((Z:ℝ)^(-1/3:ℝ))^(1/5:ℝ)=
      fermionicNearConstant*A^(3/5:ℝ)*(Z:ℝ)^(4/3:ℝ) := by
    rw [mul_assoc,global_potential_scale hz hA.le]; ring
  rw [He] at Hl'
  have Hfar : (N+1:ℝ)/(Z:ℝ)^(-1/3:ℝ)≤3*(Z:ℝ)^(4/3:ℝ) := by
    apply (div_le_div_of_nonneg_right hn HR.le).trans_eq
    have he : (Z:ℝ)/(Z:ℝ)^(-1/3:ℝ)=(Z:ℝ)^(4/3:ℝ) := by
      conv_lhs => lhs; rw [←Real.rpow_one (Z:ℝ)]
      rw [←Real.rpow_sub hz]; norm_num
    rw [mul_div_assoc,he]
  rw [hm,mul_one] at H
  push_cast at H
  nlinarith only [H,Hl',Hfar]
end Coulomb

namespace NeutralAtom

theorem atomic_global_master_potential : ∃ C : ℝ,0<C ∧
    ∀ {N : ℕ} (Z : ℕ) (hZ : 1≤Z) (u : Coulomb.H1Vector (N+1)),Coulomb.Antisymmetric u →
    Coulomb.mass u=1 → (N+1:ℝ)≤3*(Z:ℝ) → Coulomb.form (Coulomb.atom Z hZ) u≤(Z:ℝ)^(7/3:ℝ) →
    ∀ (g : 𝓢(Position,ℝ)),(∫ w,g w^2)=1 →
    (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
    ∀ {c r₀ s : ℝ},0<c → 0<r₀ → 0<s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    ∀ y : Position,potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y≤C*(Z:ℝ)^(4/3:ℝ) := by
  obtain ⟨C,hC,HC⟩ := Coulomb.atomic_global_potential
  refine ⟨C,hC,?_⟩
  intro N Z hZ u hu hm hn hf g hgm hrad hgs c r₀ s hc hr hs hq y
  have H := (physical_master_near_deficit u hu hm g hgm hrad hgs hc hr hs hq y).1
  have HC' := HC Z hZ u hu hm hn hf y
  linarith only [H,HC']
end NeutralAtom
end

end

end OAI
