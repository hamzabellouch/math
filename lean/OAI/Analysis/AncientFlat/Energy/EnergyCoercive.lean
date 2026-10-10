import OAI.Analysis.AncientFlat.Energy.EnergyPrincipal

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma principal_lower_young (a : V → ℝ) (u : V → ℂ) (α C : ℝ) (hC : 0≤C)
    (ha : ContDiff ℝ 2 a) (haj : ∀ k : ℕ, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k a x‖≤C)
    (ha0 : ∀ x, α≤a x) (hu : ContDiff ℝ 4 u) (hub : BoundedJets 4 u)
    (η : ℝ) (hη : 0<η) :
    (α-4*C*(Module.finrank ℝ V : ℝ)*η)*mass (Δ u) -
      (2*C*η⁻¹)*gradMass u -(2*C*(Module.finrank ℝ V : ℝ)*η⁻¹)*mass u ≤ principal a u := by
  have hlu := (ClassicalIBP.contDiff_laplacian u 2 hu).continuous
  have hlb := (hub.laplacian 2 hu).zero
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hb2 : BoundedJets 2 u := hub.of_le (by norm_num)
  have hy (i : Fin (Module.finrank ℝ V)) :
      2*cross (dir (basisVec i) u) (Δ u) ≤ η*mass (Δ u)+η⁻¹*mass (dir (basisVec i) u) := by
    rw [cross_comm]
    exact weighted_young hlu (contDiff_dir (n := 1) _ _ hu2).continuous hlb (hb2.dir hu2 _).zero η hη
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hy i)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hs
  have hz := weighted_young hlu hu.continuous hlb hub.zero η hη
  rw [cross_comm] at hz
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0≤2*C)
  have hz' := mul_le_mul_of_nonneg_left hz (by positivity : 0≤2*C*(Module.finrank ℝ V : ℝ))
  have hlower := principal_lower_cross a u α C hC ha haj ha0 hu hub
  unfold gradMass
  nlinarith

lemma exists_energy_constant (α C : ℝ) (hα : 0<α) (hC : 0≤C) :
    ∃ K : ℝ, 0≤K ∧ ∀ (a : V → ℝ) (u : V → ℂ),
      ContDiff ℝ 2 a → (∀ k : ℕ, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k a x‖≤C) →
      (∀ x, α≤a x) → ContDiff ℝ 4 u → BoundedJets 4 u →
      (α/2)*mass (Δ u)-K*mass u ≤ principal a u := by
  let d : ℝ := Module.finrank ℝ V
  have hd : 0≤d := by positivity
  let η : ℝ := α/(16*(C+1)*(d+1))
  have hη : 0<η := by dsimp [η]; positivity
  let L : ℝ := 2*(C+1)*η⁻¹
  have hL : 0<L := by dsimp [L]; positivity
  let ε : ℝ := α/(4*L)
  have hε : 0<ε := by dsimp [ε]; positivity
  let K : ℝ := L*(ε⁻¹+d)+L*d
  refine ⟨K,by dsimp [K]; positivity,fun a u ha haj ha0 hu hub => ?_⟩
  have hcoef : 4*C*d*η≤α/4 := by
    dsimp [η]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<16*(C+1)*(d+1))).2
    have hh : C*d≤(C+1)*(d+1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hα.le]
  have hCL : 2*C*η⁻¹≤L := by
    dsimp [L]
    nlinarith [inv_nonneg.mpr hη.le]
  have hLX : L*ε=α/4 := by dsimp [ε]; field_simp
  have hx := mass_nonneg (Δ u)
  have he := mass_nonneg u
  have hg := gradMass_nonneg u
  have hpre := principal_lower_young a u α C hC ha haj ha0 hu hub η hη
  change (α-4*C*d*η)*mass (Δ u)-(2*C*η⁻¹)*gradMass u-(2*C*d*η⁻¹)*mass u≤principal a u at hpre
  have hpre' : (3*α/4)*mass (Δ u)-L*gradMass u-(L*d)*mass u≤principal a u := by
    have h1 := mul_le_mul_of_nonneg_right hcoef hx
    have h2 := mul_le_mul_of_nonneg_right hCL hg
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL hd) he
    nlinarith
  have hi := gradient_interpolation u (hu.of_le (by norm_num)) (hub.of_le (by norm_num)) ε hε
  change gradMass u≤ε*mass (Δ u)+(ε⁻¹+d)*mass u at hi
  have hi' := mul_le_mul_of_nonneg_left hi hL.le
  dsimp [K]
  nlinarith
end ParametrixUniqueness

end

end OAI
