import OAI.Analysis.LipschitzHilbert.Fourier.PlanarModulatedJet

namespace OAI

/-! The full two-dimensional Schwartz packet and its exact affine-line
restriction. This connects physical spectra to the constructed raw waves. -/

noncomputable section
namespace LipschitzHilbert

def packetCoordinates (l W θ : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun z := (z.1/l,(z.2-θ*z.1)/W)
  invFun z := (l*z.1,W*z.2+θ*(l*z.1))
  left_inv z := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv z := by ext <;> simp [hl,hW]
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' c x := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem physicalPacketCarrier_temperate (a b θ frequency : ℝ) :
    Function.HasTemperateGrowth (fun z : ℝ × ℝ =>
      Complex.exp ((frequency*((z.2-b)-θ*(z.1-a)):ℝ)*Complex.I)) := by
  have hx : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hy : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

def physicalPlanarPacket (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ℝ × ℝ =>
    Complex.exp ((frequency*((z.2-b)-θ*(z.1-a)):ℝ)*Complex.I))
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (packetCoordinates l W θ hl hW) f).compSubConstCLM ℂ (a,b))

theorem physicalPlanarPacket_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (z : ℝ × ℝ) :
    physicalPlanarPacket f a b l W θ frequency hl hW z =
      Complex.exp ((frequency*((z.2-b)-θ*(z.1-a)):ℝ)*Complex.I)*
        f ((z.1-a)/l,((z.2-b)-θ*(z.1-a))/W) := by
  rw [physicalPlanarPacket,SchwartzMap.smulLeftCLM_apply_apply
    (physicalPacketCarrier_temperate a b θ frequency)]
  rfl

theorem physicalPlanarPacket_slice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency c s : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    planarSchwartzSlice (physicalPlanarPacket f a b l W θ frequency hl hW) c s =
      modulatedPlanarSlice f a (b-s*a) l W (s-θ) frequency c hl := by
  ext x
  rw [planarSchwartzSlice_apply,physicalPlanarPacket_apply,modulatedPlanarSlice_apply]
  have hphase : (c+s*x-b)-θ*(x-a) = c-(b-s*a)+(s-θ)*(x-a) := by ring
  rw [hphase]

end LipschitzHilbert

end

end OAI
