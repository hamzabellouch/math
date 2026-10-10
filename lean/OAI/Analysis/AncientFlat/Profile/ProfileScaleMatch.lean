import OAI.Analysis.AncientFlat.Profile.ProfileFamilies

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ProfileDecay
open FlatSimilarity ParabolicAnnular
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma arg_scale (r : ℝ) (hr : 0<r) {z : V} (hz : 3/2≤‖z‖) :
    arg (r⁻¹^2,z)=1/‖r • z‖^4 := by
  simp only [arg,q_eq hz,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  simp only [mul_pow,inv_pow,one_div,mul_inv_rev]
  ring
lemma families_scale (G H : ℝ → ℝ) (c : ℝ) (hG : ContDiffOn ℝ ∞ G (Ici 0))
    (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (r : ℝ) (hr : 0<r) {z : V} (hz : 3/2≤‖z‖) :
    familyA H c (r⁻¹^2,z)=profileAf G (r • z)-c^2 ∧
    familyB H (r⁻¹^2,z)=profileBf G (r • z) := by
  have hx : 0<‖r • z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]; positivity
  have hA := compactPrincipal_eq G H hmatch hx (by norm_num : (0:ℝ)<1)
  have hB := compactPotential_eq G H hG hmatch hx (by norm_num : (0:ℝ)<1)
  simp only [compactPrincipal,compactArgument,Real.sqrt_one,div_one] at hA
  simp only [compactPotential,compactArgument,Real.sqrt_one,div_one,inv_one,neg_mul,one_mul] at hB
  refine ⟨?_,?_⟩
  · dsimp [familyA,profileAf]
    rw [arg_scale r hr hz]
    linarith
  · dsimp [familyB]
    rw [arg_scale r hr hz]
    convert hB using 1 <;> first | rfl | ring
lemma family_jet_scale (G H : ℝ → ℝ) (c : ℝ) (κ : ℝ) (hκ : 0<κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hpos : ∀ y : ℝ, 0≤y → κ≤G y)
    (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (n : ℕ) (r : ℝ) (hr : 0<r) (z : V) (hz : 3/2<‖z‖) :
    spaceJet (familyA H c) n (r⁻¹^2,z)=r^n • iteratedFDeriv ℝ n (fun y => profileAf G y-c^2) (r • z) ∧
    spaceJet (familyB H) n (r⁻¹^2,z)=r^n • iteratedFDeriv ℝ n (profileBf G) (r • z) := by
  have hae : (fun w : V => familyA H c (r⁻¹^2,w)) =ᶠ[𝓝 z]
      (fun w => profileAf G (r • w)-c^2) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hz] with w hw
    exact (families_scale G H c hG hmatch r hr hw.le).1
  have hbe : (fun w : V => familyB H (r⁻¹^2,w)) =ᶠ[𝓝 z]
      (fun w => profileBf G (r • w)) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hz] with w hw
    exact (families_scale G H c hG hmatch r hr hw.le).2
  obtain ⟨hA,hB⟩ := profile_smooth (V := V) G κ hκ hG hpos
  have hn : (n:ℕ∞ω)≤(∞:ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl n
  constructor
  · rw [spaceJet,(hae.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
    exact congrFun (iteratedFDeriv_comp_const_smul r ((hA.sub contDiff_const).of_le hn)) z
  · rw [spaceJet,(hbe.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
    exact congrFun (iteratedFDeriv_comp_const_smul r (hB.of_le hn)) z
end ProfileDecay

end

end OAI
