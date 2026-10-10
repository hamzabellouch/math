import OAI.Analysis.AncientFlat.Regularity.ScaledJets
import OAI.Analysis.AncientFlat.Profile.ProfileScaling

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicInterior ParabolicLocalization ParabolicAnnular ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma scaleU_bilaplacian (w r : ℝ) (u : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (p : V × ℝ) :
    Δ (Δ (scaleU w r u p.2)) p.1=(r^(-w)*r^4) • Δ (Δ (u (scale r p).2)) (scale r p).1 := by
  rw [bilaplacian_eq_traceFour _ (scaleU_contDiff w r u hs p.2)]
  unfold scaleU
  rw [iteratedFDeriv_const_smul_apply' (windowValue_contDiff 0 r u hs p.2).contDiffAt,
    map_smul,window_jet 0 r u hs 4 le_rfl,map_smul,smul_smul,window_zero_eq_scale,
    bilaplacian_eq_traceFour _ (hs _)]
omit [FiniteDimensional ℝ V] in
lemma scaleU_hasDerivAt (w r : ℝ) (u ut : ℝ → V → ℂ) (p : V × ℝ)
    (hd : HasDerivAt (fun t => u t (scale r p).1) (ut (scale r p).2 (scale r p).1) (scale r p).2) :
    HasDerivAt (fun t => scaleU w r u t p.1) (scaleUT w r ut p.2 p.1) p.2 := by
  have hh := window_hasDerivAt (0:V × ℝ) r u ut p (by simpa only [window_zero_eq_scale] using hd)
  exact hh.const_smul (r^(-w))
lemma scale_source_factor (w r : ℝ) (hr : 0<r) : r^(-(w-4))=r^(-w)*r^4 := by
  rw [show -(w-4)=-w+4 by ring,Real.rpow_add hr]
  norm_num
lemma scale_equation (G : ℝ → ℝ) (w r : ℝ) (hr : 0<r)
    (u ut : ℝ → V → ℂ) (f : V × ℝ → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (p : V × ℝ)
    (he : ut (scale r p).2 (scale r p).1+(profilePrincipal G (scale r p):ℂ)*
      Δ (Δ (u (scale r p).2)) (scale r p).1+(profilePotential G (scale r p):ℂ)*u (scale r p).2 (scale r p).1=f (scale r p)) :
    scaleUT w r ut p.2 p.1+(profilePrincipal G p:ℂ)*Δ (Δ (scaleU w r u p.2)) p.1+
      (profilePotential G p:ℂ)*scaleU w r u p.2 p.1=scaleValue (w-4) r f p := by
  rw [scaleUT_apply,scaleU_bilaplacian w r u hs p,scaleU_apply]
  unfold scaleValue
  rw [scale_source_factor w r hr,←he,profilePrincipal_scale G r hr,
    ←profilePotential_scale G r hr p]
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring
lemma scale_growth (δ r M : ℝ) (hr : 0<r) (_ : 0≤M)
    (u : ℝ → V → ℂ) (hu : ∀ p : V × ℝ, p.2<0 → ‖u p.2 p.1‖≤M*(-p.2)^((-1+δ)/2)) :
    ∀ p : V × ℝ, p.2<0 → ‖scaleU (-2+2*δ) r u p.2 p.1‖≤M*(-p.2)^((-1+δ)/2) := by
  intro p hp
  rw [scaleU_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hr _)]
  have hh := mul_le_mul_of_nonneg_left (hu (scale r p) ((scale_time_neg r hr p).mpr hp))
    (Real.rpow_pos_of_pos hr (-(-2+2*δ))).le
  have hf : r^(-(-2+2*δ))*(-(scale r p).2)^((-1+δ)/2)=(-p.2)^((-1+δ)/2) := by
    change r^(-(-2+2*δ))*(-(r^4*p.2))^((-1+δ)/2)=_
    rw [show -(r^4*p.2)=r^4*(-p.2) by ring,Real.mul_rpow (pow_nonneg hr.le 4) (neg_pos.mpr hp).le,
      ←Real.rpow_natCast,←Real.rpow_mul hr.le,←mul_assoc,←Real.rpow_add hr]
    norm_num only [Nat.cast_ofNat]
    rw [show -(-2+2*δ)+(4:ℝ)*((-1+δ)/2)=0 by ring]
    simp
  calc
    _ ≤ r^(-(-2+2*δ))*(M*(-(scale r p).2)^((-1+δ)/2)) := hh
    _ = M*(r^(-(-2+2*δ))*(-(scale r p).2)^((-1+δ)/2)) := by ring
    _ = _ := by rw [hf]
end FlatWeighted

end

end OAI
