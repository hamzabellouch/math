import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupExtensionFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemGauge

namespace OAI

/-! # Explicit kernel corrections of an actual extension section -/

noncomputable section
namespace PolycyclicRecognition.GroupExtensionSection
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

def gaugeSection (E : GroupExtension N G Q) (σ : E.Section) (b : Q → N) : E.Section where
  toFun q := E.inl (b q) * σ q
  rightInverse_rightHom q := by rw [map_mul, E.rightHom_inl, σ.rightHom_section, one_mul]

theorem gaugeSection_one (E : GroupExtension N G Q) (σ : E.Section)
    (hσ : σ 1 = 1) (b : Q → N) (hb : b 1 = 1) : gaugeSection E σ b 1 = 1 := by
  change E.inl (b 1) * σ 1 = 1
  rw [hb, hσ, map_one, one_mul]

theorem factor_gaugeSection (E : GroupExtension N G Q) (σ : E.Section)
    (hσ : σ 1 = 1) (b : Q → N) (hb : b 1 = 1) (q r : Q) :
    factor E (gaugeSection E σ b) q r = ((factorSystem E σ hσ).gauge b hb).factor q r := by
  apply E.inl_injective
  rw [inl_factor]
  change (E.inl (b q) * σ q) * (E.inl (b r) * σ r) * (E.inl (b (q * r)) * σ (q * r))⁻¹ =
    E.inl (b q * E.conjAct (σ q) (b r) * factor E σ q r * (b (q * r))⁻¹)
  simp only [map_mul, map_inv, E.inl_conjAct_comm, inl_factor]
  group

end PolycyclicRecognition.GroupExtensionSection

end

end OAI
